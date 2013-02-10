
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  H.Renamer
-- Copyright   :  (c) Iago Abal, 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Renamer for H!.
-- This module implements a post-parsing phase in which every name is
-- assigned a unique identifier and, additionally, it detects some kind
-- of errors that are more cumbersome to consider during parsing.

module H.Renamer where


#include "bug.h"

import H.Syntax
import H.SrcContext
import H.Monad

import Util.Monad

import Name
import Pretty
import Unique ( getUniq )

import Control.Monad.Error
import Control.Monad.Reader
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Traversable as T



-- * The RnM monad

type RnM a = H RnEnv () () a

data RnEnv
  = RnEnv {
    rnOccMap   :: Map OccName Name
  , rnToplevel :: Set Name
  }

emptyRnEnv :: RnEnv
emptyRnEnv = RnEnv Map.empty Set.empty

getName :: OccName -> RnM Name
getName occ = do
  mbName <- asks (Map.lookup occ . rnOccMap)
  case mbName of
      Nothing   ->
        throwError $  text "Variable" <+> ppQuot occ
                                      <+> text "is not in scope."
      Just name -> return name

getIsToplevel :: Name -> RnM Bool
getIsToplevel n = asks (Set.member n . rnToplevel)

withMapping :: [(OccName,Name)] -> RnM a -> RnM a
withMapping lmaps = local update
  where maps = Map.fromList lmaps
        update rn@RnEnv{rnOccMap} = rn{rnOccMap=maps `Map.union` rnOccMap}

withToplevel :: [Name] -> RnM a -> RnM a
withToplevel lnames = local update
  where names = Set.fromList lnames
        update rn@RnEnv{rnToplevel} = rn{rnToplevel=names `Set.union` rnToplevel}

-- * The 'Rename' and 'RenameBndr' classes

class Rename ast where
  rename :: ast Pr -> RnM (ast Rn)

rnMaybe :: Rename ast => Maybe (ast Pr) -> RnM (Maybe (ast Rn))
rnMaybe Nothing  = return Nothing
rnMaybe (Just a) = liftM Just $ rename a

rnList :: Rename ast => [ast Pr] -> RnM [ast Rn]
rnList xs = mapM rename xs

class RenameBndr b b' | b -> b' where
  renameBndr :: b -> (b' -> RnM a) -> RnM a

instance RenameBndr OccName Name where
  renameBndr occ f = do
    name <- mkUsrName occ `liftM` getUniq
    withMapping [(occ,name)] $
      f name

renameTopBndr :: OccName -> (Name -> RnM a) -> RnM a
renameTopBndr occ f
  = renameBndr occ $ \name ->
      withToplevel [name] $ f name

instance RenameBndr b b' => RenameBndr [b] [b'] where
  renameBndr []     f = f []
  renameBndr (b:bs) f = renameBndr b $ \b' ->
                        renameBndr bs $ \bs' ->
                          f (b':bs')


-- * Modules

rnModule :: Module Pr -> RnM (Module Rn)
rnModule (Module loc modname decls)
  = inContextAt loc (text "In module" <+> ppQuot modname) $ do
      decls' <- decls_rn
      return $ Module loc modname decls'
  where decls_rn = renameBndr decls return


-- * Top-level declarations

instance RenameBndr (Decl Pr) (Decl Rn) where
  renameBndr (TypeDecl loc name typarams htype) f
    = inTypeDeclCtxt loc (ppQuot name) $ do
        inContext (text "In type header") $ checkDupTyParams typarams
        renameBndr name $ \name' -> do
          (typarams', htype') <- renameBndr typarams $ \typarams' -> do
                                   htype' <- rename htype
                                   return (typarams',htype')
          popContext $ f (TypeDecl loc name' typarams' htype')
  renameBndr (DataDecl loc occ typarams constrs) f
    = inDataDeclCtxt loc (ppQuot occ) $ do
        inContext (text "In data header") $ checkDupTyParams typarams
        renameBndr occ $ \name -> do
          (typarams',constrs',cmap)
                        <- renameBndr typarams $ \typarams' -> do
                             (constrs',cmap) <- liftM unzip $ mapM rnConDecl constrs
                             return (typarams',constrs',cmap)
          popContext $ withMapping cmap $
            f (DataDecl loc name typarams' constrs')
  renameBndr (ValDecl bind) f =
    renameGlobalBind bind $ f . ValDecl
  renameBndr (GoalDecl loc gtype gname None prop) f
    = inGoalDeclCtxt loc gtype (ppQuot gname) $
        renameBndr gname $ \gname' -> do
          prop' <- inPropContext $ rename prop
          popContext $ f (GoalDecl loc gtype gname' None prop')


-- * Binds

renameGlobalBind = renameBind True

renameLocalBinds = renameBinds False

renameBinds isTop []     f = f []
renameBinds isTop (b:bs) f = renameBind isTop b $ \b' ->
                      renameBinds isTop bs $ \bs' ->
                        f (b':bs')

renameBndr_ False = renameBndr
renameBndr_ True = renameTopBndr

rnPat_ False = rnPat
rnPat_ True = rnTopPat

renameBind :: Bool -> Bind Pr -> (Bind Rn -> RnM a) -> RnM a
renameBind isTop (FunBind _rec occ sig None matches) f
  = inFunBindCtxt (ppQuot occ) $ do
      sig' <- rename sig
      renameBndr_ isTop occ $ \name -> do
        matches' <- rnList matches
        let rec' = funbind_rec occ matches
        popContext $ f (FunBind rec' name sig' None matches')
  where funbind_rec x ms
          | x `Set.member` fvMatches ms = Rec
          | otherwise                   = NonRec
renameBind isTop (PatBind (Just loc) pat rhs) f
  = inPatBindCtxt loc (ppQuot pat) $ do
      rnPat_ isTop pat $ \pat' -> do
        rhs' <- rename rhs
        popContext $ f (PatBind (Just loc) pat' rhs')
renameBind _isTop _other _f = impossible

instance Rename TypeSig where
  rename NoTypeSig = return NoTypeSig
  rename (TypeSig loc polyty)
    = inContextAt loc (text "In type signature") $
        liftM (TypeSig loc) $ rename polyty

instance Rename Match where
  rename (Match (Just loc) pats rhs)
    = inFunMatchCtxt loc $ do
        checkLinearPat pats
        rnPats pats $ \pats' -> liftM (Match (Just loc) pats') $ rename rhs
  rename _other = impossible

rnConDecl :: ConDecl Pr -> RnM (ConDecl Rn,(OccName,Name))
rnConDecl (ConDeclIn loc occ tys)
  = inConDeclCtxt loc (ppQuot occ) $ do
      let doms = map mk_dom tys
      doms' <- renameBndr doms return
      renameBndr occ $ \name ->
        return (ConDecl loc name doms',(occ,name))
  where
      mk_dom (PredTy pat ty mbProp) = Dom (Just pat) ty mbProp
      mk_dom ty                     = Dom Nothing ty Nothing
rnConDecl _other = impossible


-- * Expressions

instance Rename Exp where
  rename (Var occ) = do
    name <- getName occ
    isTop <- getIsToplevel name
    return $ if isTop then Par name
                      else Var name
  rename (Con con) = liftM Con $ rename con
  rename (Op op)   = return (Op op)
  rename (Lit lit) = return $ Lit lit
  rename ElseGuard = bug "renaming expression: found 'else' guard"
  rename (PrefixApp (Op op) e) = liftM (PrefixApp (Op op)) $ rename e
  rename (InfixApp e1 (Op op) e2)
    = liftM2 (flip InfixApp (Op op)) (rename e1) (rename e2)
  rename (App f n) = liftM2 App (rename f) (rename n)
  rename (Lam (Just loc) pats body)
    = inLambdaAbsCtxt loc pats $
        rnPats pats $ \pats' -> liftM (Lam (Just loc) pats') $ rename body
  rename (Let binds body)
    = renameLocalBinds binds $ \binds' -> liftM (Let binds') $ rename body
  rename (Ite None g t e)
    = inIteExprCtxt g $
        liftM3 (Ite None) (rename g) (rename t) (rename e)
  rename (If None grhss)
    = inIfExprCtxt $
        liftM (If None) $ rename grhss
  rename (Case None e alts)
    = inCaseExprCtxt e $
        liftM2 (Case None) (rename e) (rnList alts)
  rename (Tuple None l) = liftM (Tuple None) $ mapM rename l
  rename (List None l) = liftM (List None) $ mapM rename l
  rename (Paren e) = liftM Paren $ rename e
  rename (LeftSection e (Op op)) = liftM (flip LeftSection (Op op)) $ rename e
  rename (RightSection (Op op) e) = liftM (RightSection (Op op)) $ rename e
  rename (EnumFromTo e1 e2) = liftM2 EnumFromTo (rename e1) (rename e2)
  rename (EnumFromThenTo e1 e2 e3)
    = liftM3 EnumFromThenTo (rename e1) (rename e2) (rename e3)
  rename (Coerc loc e polyty)
    = inCoercExprCtxt loc $
        liftM2 (Coerc loc) (rename e) (rename polyty)
  rename (QP qt qvars body) = do
    check_quantifier_context
    inQPExprCtxt qt qvars $ do
      check_duplicate_qvars
      renameBndr qvars $ \qvars' ->
        liftM (QP qt qvars') $ rename body
    where check_quantifier_context = do
            ctxt <- getContext
            when (not $ isPropContext ctxt) $
              throwError $ quotes (pretty qt)
                <+> text "formulas cannot appear out of propositional context"
          check_duplicate_qvars
            | nub bs == bs = return ()
            | otherwise    = throwError $ text "Duplicated binder(s)"
            where bs = map qVarVar qvars
  rename _other = impossible


instance Rename Con where
  rename (UserCon occ)     = liftM UserCon $ getName occ
  rename (BuiltinCon bcon) = return $ BuiltinCon bcon

instance RenameBndr (QVar Pr) (QVar Rn) where
  renameBndr (QVar occ mb_ty) f = do
    name <- renameBndr occ return
    mb_ty' <- T.mapM rename mb_ty
    withMapping [(occ,name)] $
      f (QVar name mb_ty')

-- ** Right hand side

instance Rename Rhs where
  rename (Rhs None grhs whr)
    = renameLocalBinds whr $ \whr' -> do
        grhs' <- rename grhs
        return $ Rhs None grhs' whr'

instance Rename GRhs where
  rename (UnGuarded e)   = liftM UnGuarded $ rename e
  rename (Guarded grhss) = liftM Guarded $ rename grhss

instance Rename GuardedRhss where
  rename (GuardedRhssIn grhss) = do
    (grhss',elserhs) <- check [] grhss
    return $ GuardedRhss grhss' elserhs
    where
        check :: [GuardedRhs Rn] -> [GuardedRhs Pr] -> RnM ([GuardedRhs Rn],Else Rn)
        check  acc [] = return (reverse acc, NoElse)
        check  acc [GuardedRhs loc ElseGuard e]
          = do e' <- rename e; return (reverse acc, Else loc e')
          -- an @else@ guard appearing in an intermediate alternative
          -- wrong!
        check _acc (GuardedRhs _loc ElseGuard _:_)
          = throwError $
              text "An" <+> quotes (text "else") <+> text "guard can only be used for the last alternative"
        check  acc (GuardedRhs loc g e:rest)
          = do grhs' <- liftM2 (GuardedRhs loc) (rename g) (rename e)
               check (grhs':acc) rest
  rename _other = impossible

instance Rename GuardedRhs where
  rename (GuardedRhs loc g e)
    = inGuardedRhsCtxt loc $
        liftM2 (GuardedRhs loc) (rename g) (rename e)

-- ** Alternatives

instance Rename Alt where
  rename (Alt (Just loc) pat rhs)
    = inCaseAltCtxt loc pat $ do
        checkLinearPat [pat]
        rnPat pat $ \pat' -> liftM (Alt (Just loc) pat') $ rename rhs
  rename _other = impossible

-- ** Patterns

checkLinearPat :: [Pat Pr] -> RnM ()
checkLinearPat pats
  | nub bs == bs = return ()
  | otherwise    = throwError $ text "Duplicated binder(s) in pattern(s)"
  where bs = patsBndrs pats

rn_pats :: [Pat Pr] -> RnM ([Pat Rn],Map OccName Name)
rn_pats ps = mapAccumM (\acc_map pat -> do
                          (pat',pat_map) <- rn_pat pat
                          return (pat',Map.union acc_map pat_map)
                      )
                      Map.empty
                      ps

rn_pat :: Pat Pr -> RnM (Pat Rn,Map OccName Name)
rn_pat (VarPat occ) = do
  name <- renameBndr occ return
  return (VarPat name,Map.fromList [(occ,name)])
rn_pat (LitPat lit) = return (LitPat lit,Map.empty)
rn_pat (InfixCONSPat None p1 p2) = do
  (p1',p1_map) <- rn_pat p1
  (p2',p2_map) <- rn_pat p2
  return (InfixCONSPat None p1' p2',Map.union p1_map p2_map)
rn_pat (ConPat None con ps) = do
    con' <- rename con
    (ps',ps_map) <- rn_pats ps
    return (ConPat None con' ps',ps_map)
rn_pat (TuplePat None ps) = do
  (ps',ps_map) <- rn_pats ps
  return (TuplePat None ps',ps_map)
rn_pat (ListPat None ps) = do
  (ps',ps_map) <- rn_pats ps
  return (ListPat None ps',ps_map)
rn_pat (ParenPat p) = do
  (p',p_map) <- rn_pat p
  return (ParenPat p',p_map)
rn_pat WildPatIn = do
  uniq <- getUniq
  let wild_var = mkSysName (mkOccName VarNS "_x") uniq
  return (WildPat wild_var,Map.empty)
rn_pat (AsPat occ p) = do
  name <- renameBndr occ return
  (p',p_map) <- rn_pat p
  return (AsPat name p',Map.insert occ name p_map)
rn_pat _other = impossible

rnPat :: Pat Pr -> (Pat Rn -> RnM a) -> RnM a
rnPat p f = do
    (p',p_map) <- rn_pat p
    withMapping (Map.toList p_map) $
      f p'

rnPats :: [Pat Pr] -> ([Pat Rn] -> RnM a) -> RnM a
rnPats ps f = do
    (ps',ps_map) <- rn_pats ps
    withMapping (Map.toList ps_map) $
      f ps'

rnTopPat :: Pat Pr -> (Pat Rn -> RnM a) -> RnM a
rnTopPat p f = do
    (p',p_map) <- rn_pat p
    withMapping (Map.toList p_map) $
      withToplevel (Set.toList $ bsPat p') $
        f p'

-- * Types

checkDupTyParams :: TyParams Pr -> RnM ()
checkDupTyParams typs
  | nub typs == typs = return ()
  | otherwise        = throwError $ text "Duplicated type variable(s)"

instance Rename TyName where
  rename (UserTyCon occ) = liftM UserTyCon $ getName occ
  rename (BuiltinTyCon btycon) = return $ BuiltinTyCon btycon

instance Rename (Type c) where
  rename (VarTy occ) = liftM VarTy $ getName occ
  rename (ConTyIn tycon) = liftM ConTyIn $ rename tycon
  rename (AppTyIn s t) = liftM2 AppTyIn (rename s) (rename t)
  rename (PredTy pat ty mbProp) = do
    ty' <- rename ty
    rnPat pat $ \pat' ->
      liftM (PredTy pat' ty') $ inPropContext $ rnMaybe mbProp
  rename (FunTy a b) =
    renameBndr a $ \a' ->
      liftM (FunTy a') $ rename b
  rename (ListTy a) = liftM ListTy $ rename a
  rename (TupleTy ts) = renameBndr ts $ return . TupleTy
  rename (ParenTy a) = rename $ tau2type a
  rename prpty@(ForallTy typarams ty)
    = inTypeCtxt prpty $ do
        checkDupTyParams typarams
        renameBndr typarams $ \typarams' ->
          liftM (ForallTy typarams') $ rename ty
  rename _other = impossible

instance RenameBndr (Dom Pr) (Dom Rn) where
  renameBndr (Dom Nothing ty Nothing) f = do
    ty' <- rename ty
    f (Dom Nothing ty' Nothing)
  renameBndr (Dom (Just pat) ty mbProp) f = do
    ty' <- rename ty
    rnPat pat $ \pat' -> do
      mbProp' <- inPropContext $ rnMaybe mbProp
      f (Dom (Just pat') ty' mbProp')
  renameBndr _other _f = impossible
