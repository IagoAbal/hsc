{-# LANGUAGE MultiParamTypeClasses,
             PatternGuards,
             GADTs,
             NamedFieldPuns,
             FlexibleContexts,
             FlexibleInstances,
             TypeSynonymInstances,
             GeneralizedNewtypeDeriving,
             StandaloneDeriving,
             FunctionalDependencies,
             UndecidableInstances
             #-}

module H.Renamer where

import H.Syntax
import H.FreeVars
import H.SrcContext
import H.Phase
import Pretty
import H.Message
import H.Monad

import Util.Monad

import Name
import Unique

import Control.Monad.Error
import Control.Monad.Reader
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T


rnModule ::Module Pr -> RnM (Module Rn)
rnModule (Module loc modname decls)
  = inContextAt loc (text "In module" <+> ppQuot modname) $ do
      decls' <- decls_rn
      return $ Module loc modname decls'
  where decls_rn = renameBndr decls return


type RnM a = H (Map OccName Name) () () a

emptyRnEnv :: Map OccName Name
emptyRnEnv = Map.empty



class Rename ast where
  rename :: ast Pr -> RnM (ast Rn)

rnMaybe :: Rename ast => Maybe (ast Pr) -> RnM (Maybe (ast Rn))
rnMaybe Nothing  = return Nothing
rnMaybe (Just a) = liftM Just $ rename a

rnList :: Rename ast => [ast Pr] -> RnM [ast Rn]
rnList xs = mapM rename xs

class RenameBndr b b' | b -> b' where
  renameBndr :: b -> (b' -> RnM a) -> RnM a


instance RenameBndr b b' => RenameBndr [b] [b'] where
  renameBndr []     f = f []
  renameBndr (b:bs) f = renameBndr b $ \b' ->
                        renameBndr bs $ \bs' ->
                          f (b':bs')



getName :: OccName -> RnM Name
getName occ = do
  mbName <- asks (Map.lookup occ)
  case mbName of
      Nothing   -> throwError $
                      text "Variable" <+> ppQuot occ <+> text "is not in scope."
      Just name -> return name


withMapping :: [(OccName,Name)] -> RnM a -> RnM a
withMapping maps
  = local (Map.union (Map.fromList maps))

instance RenameBndr OccName Name where
  renameBndr occ f = do
    name <- mkUsrName occ `liftM` getUniq
    withMapping [(occ,name)] $
      f name



                        

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
    renameBndr bind $ f . ValDecl
  renameBndr (GoalDecl loc gtype gname NoPostTc prop) f
    = inGoalDeclCtxt loc gtype (ppQuot gname) $
        renameBndr gname $ \gname' -> do
          prop' <- inPropContext $ rename prop
          popContext $ f (GoalDecl loc gtype gname' NoPostTc prop') 


-- rnBind :: Bind Pr -> RnM (Bind Rn, Map OccName Name)
-- rnBind = undefined
-- renameBndr (FunBind _rec occ sig matches) f
--   = inContext (text "In the definition of" <+> ppQuot occ) $ do
--       sig' <- rename sig
--       renameBndr occ $ \name -> do
--         matches' <- rnList matches
--         let rec' = checkFunBindRec name matches'
--         f (FunBind rec' name sig' matches')
-- renameBndr (PatBind loc pat rhs) f
--   = inContextAt loc (text "In pattern binding" <+> ppQuot pat) $ do
--       renameBndr pat $ \pat' -> do
--         rhs' <- rename rhs
--         f (PatBind loc pat' rhs')

instance RenameBndr (Bind Pr) (Bind Rn) where
  renameBndr (FunBind _rec occ sig NoPostTc matches) f
    = inFunBindCtxt (ppQuot occ) $ do
        sig' <- rename sig
        renameBndr occ $ \name -> do
          matches' <- rnList matches
          let rec' = checkFunBindRec name matches'
          popContext $ f (FunBind rec' name sig' NoPostTc matches')
  renameBndr (PatBind (Just loc) pat rhs) f
    = inPatBindCtxt loc (ppQuot pat) $ do
        rnPat pat $ \pat' -> do
          rhs' <- rename rhs
          popContext $ f (PatBind (Just loc) pat' rhs')

instance Rename TypeSig where
  rename NoTypeSig = return NoTypeSig
  rename (TypeSig loc polyty)
    = inContextAt loc (text "In type signature") $
        liftM (TypeSig loc) $ rename polyty

instance Rename Match where
  rename (Match (Just loc) pats rhs)
    = inFunMatchCtxt loc $ do
        checkDupPatBndrs pats
        rnPats pats $ \pats' -> liftM (Match (Just loc) pats') $ rename rhs


rnConDecl :: ConDecl Pr -> RnM (ConDecl Rn,(OccName,Name))
rnConDecl (ConDeclIn loc occ tys)
  = inConDeclCtxt loc (ppQuot occ) $ do
      let doms = map type2dom tys
      doms' <- renameBndr doms return
      renameBndr occ $ \name ->
        return (ConDecl loc name doms',(occ,name))
  where
      type2dom (PredTy pat ty mbProp) = Dom (Just pat) ty mbProp
      type2dom ty                     = Dom Nothing ty Nothing

instance Rename Exp where
  rename (Var occ) = liftM Var $ getName occ
  rename (Con con) = liftM Con $ rename con
  rename (Op op)   = return (Op op)
  rename (Lit lit) = return $ Lit lit
  rename ElseGuard = undefined  -- bug
  rename (PrefixApp (Op op) e) = liftM (PrefixApp (Op op)) $ rename e
  rename (InfixApp e1 (Op op) e2)
    = liftM2 (flip InfixApp (Op op)) (rename e1) (rename e2)
  rename (App f n) = liftM2 App (rename f) (rename n)
  rename (Lam (Just loc) pats body)
    = inLambdaAbsCtxt loc pats $
        rnPats pats $ \pats' -> liftM (Lam (Just loc) pats') $ rename body
  rename (Let binds body)
    = renameBndr binds $ \binds' -> liftM (Let binds') $ rename body
  rename (Ite NoPostTc g t e)
    = inIteExprCtxt g $
        liftM3 (Ite NoPostTc) (rename g) (rename t) (rename e)
  rename (If NoPostTc grhss)
    = inIfExprCtxt $
        liftM (If NoPostTc) $ rename grhss
  rename (Case e NoPostTc alts)
    = inCaseExprCtxt e $
        liftM2 (flip Case NoPostTc) (rename e) (rnList alts)
  rename (Tuple NoPostTc l) = liftM (Tuple NoPostTc) $ mapM rename l
  rename (List NoPostTc l) = liftM (List NoPostTc) $ mapM rename l
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
    checkQuantifierInPropContext qt
    inQPExprCtxt qt qvars $ do
      checkDupQVars qvars
      renameBndr qvars $ \qvars' ->
        liftM (QP qt qvars') $ rename body

checkQuantifierInPropContext :: Quantifier -> RnM ()
checkQuantifierInPropContext qt = do
  ctxt <- getContext
  when (not $ isPropContext ctxt) $
    throwError $ quotes (pretty qt) <+> text "formulas cannot appear out of propositional context"

instance Rename Con where
  rename (UserCon occ)     = liftM UserCon $ getName occ
  rename (BuiltinCon bcon) = return $ BuiltinCon bcon

instance Rename Rhs where
  rename (Rhs NoPostTc grhs whr)
    = renameBndr whr $ \whr' -> do
        grhs' <- rename grhs
        return $ Rhs NoPostTc grhs' whr'

instance Rename GRhs where
  rename (UnGuarded exp) = liftM UnGuarded $ rename exp
  rename (Guarded grhss) = liftM Guarded $ rename grhss

instance Rename GuardedRhss where
  rename (GuardedRhssIn grhss) = do
    (grhss',elserhs) <- check [] grhss
    return $ GuardedRhss grhss' elserhs
    where
        check :: [GuardedRhs Rn] -> [GuardedRhs Pr] -> RnM ([GuardedRhs Rn],Else Rn)
        check acc [] = return (reverse acc, NoElse)
        check acc [GuardedRhs loc ElseGuard exp]
          = do exp' <- rename exp; return (reverse acc, Else loc exp')
          -- an @else@ guard appearing in an intermediate alternative
          -- wrong!
        check acc (GuardedRhs loc ElseGuard _:_)
          = throwError $
              text "An" <+> quotes (text "else") <+> text "guard can only be used for the last alternative"
        check acc (GuardedRhs loc guard exp:rest)
          = do grhs' <- liftM2 (GuardedRhs loc) (rename guard) (rename exp)
               check (grhs':acc) rest

instance Rename GuardedRhs where
  rename (GuardedRhs loc guard expr)
    = inGuardedRhsCtxt loc $
        liftM2 (GuardedRhs loc) (rename guard) (rename expr)

instance Rename Alt where
  rename (Alt (Just loc) pat rhs)
    = inCaseAltCtxt loc pat $ do
        checkDupPatBndrs [pat]
        rnPat pat $ \pat' -> liftM (Alt (Just loc) pat') $ rename rhs


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
rn_pat (InfixCONSPat NoPostTc p1 p2) = do
  (p1',p1_map) <- rn_pat p1
  (p2',p2_map) <- rn_pat p2
  return (InfixCONSPat NoPostTc p1' p2',Map.union p1_map p2_map)
rn_pat (ConPat con NoPostTc ps) = do
    con' <- rename con
    (ps',ps_map) <- rn_pats ps
    return (ConPat con' NoPostTc ps',ps_map)
rn_pat (TuplePat ps NoPostTc) = do
  (ps',ps_map) <- rn_pats ps
  return (TuplePat ps' NoPostTc,ps_map)
rn_pat (ListPat ps NoPostTc) = do
  (ps',ps_map) <- rn_pats ps
  return (ListPat ps' NoPostTc,ps_map)
rn_pat (ParenPat p) = do
  (p',p_map) <- rn_pat p
  return (ParenPat p',p_map)
rn_pat WildPatIn = do
  uniq <- getUniq
  let wild_var = mkSysName (mkOccName VarNS "_x") uniq
  return (WildPat wild_var,Map.empty)
-- rn_pat (SigPat p t) = do
--   (p',p_map) <- rn_pat p
--   t' <- rename t
--   return (SigPat p' t',p_map)
rn_pat (AsPat occ p) = do
  name <- renameBndr occ return
  (p',p_map) <- rn_pat p
  return (AsPat name p',Map.insert occ name p_map)
rn_pat _other = undefined -- impossible

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

instance RenameBndr (QVar Pr) (QVar Rn) where
  renameBndr (QVar occ mb_ty) f = do
    name <- renameBndr occ return
    mb_ty' <- T.mapM rename mb_ty
    withMapping [(occ,name)] $
      f (QVar name mb_ty')

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
  rename _other = undefined -- impossible

instance RenameBndr (Dom Pr) (Dom Rn) where
  renameBndr (Dom Nothing ty Nothing) f = do
    ty' <- rename ty
    f (Dom Nothing ty' Nothing)
  renameBndr (Dom (Just pat) ty mbProp) f = do
    ty' <- rename ty
    rnPat pat $ \pat' -> do
      mbProp' <- inPropContext $ rnMaybe mbProp
      f (Dom (Just pat') ty' mbProp')
  renameBndr _other _f = undefined -- impossible

instance Rename TyName where
  rename (UserTyCon occ) = liftM UserTyCon $ getName occ
  rename (BuiltinTyCon btycon) = return $ BuiltinTyCon btycon



---

checkDupTyParams :: TyParams Pr -> RnM ()
checkDupTyParams typs
  | nub typs == typs = return ()
  | otherwise        = throwError $ text "Duplicated type variable(s)"

checkDupPatBndrs :: [Pat Pr] -> RnM ()
checkDupPatBndrs pats
  | nub bs == bs = return ()
  | otherwise    = throwError $ text "Duplicated binder(s) in pattern(s)"
  where bs = patsBndrs pats

checkDupQVars :: [QVar Pr] -> RnM ()
checkDupQVars qvars
  | nub bs == bs = return ()
  | otherwise    = throwError $ text "Duplicated binder(s)"
  where bs = map qVarVar qvars

checkFunBindRec :: Name -> [Match Rn] -> IsRec Rn
checkFunBindRec x matches
  | x `Set.member` fvMatches matches = Rec
  | otherwise                       = NonRec
