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
import H.SrcLoc
import H.SrcContext ( SrcContext(..), MonadContext(..) )
import H.Phase
import H.Pretty
import H.Message
import qualified H.Message as Msg
import H.Monad

import Name
import Unique

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set




rnModule :: Module Pr -> IO (Either Message (Module Rn))
rnModule (Module loc modname decls)
  = do res <- runH (renameBndr decls return) (SrcContext loc (text "In module" <+> ppQuot modname) False) newSupply Map.empty ()
       case res of
            Left err -> return $ Left err
            Right (decls',(),()) -> return $ Right $ Module loc modname decls'


-- newtype RnM a = RnM { unRnM :: ReaderT (Map OccName Name) m a }
--     deriving(Functor, Applicative, Monad, MonadUnique, MonadReader (Map OccName Name), MonadContext)

type RnM a = H (Map OccName Name) () () a

-- runRnM :: RnM a -> Map OccName Name -> m a
-- runRnM m = runReaderT (unRnM m) 




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
    = inContextAt loc (text "In type declaration" <+> ppQuot name) $ do
        inContext (text "In type header") $ checkDupTyParams typarams
        renameBndr name $ \name' -> do
          (typarams', htype') <- renameBndr typarams $ \typarams' -> do
                                   htype' <- rename htype
                                   return (typarams',htype')
          popContext $ f (TypeDecl loc name' typarams' htype')
  renameBndr (DataDecl loc occ typarams constrs) f
    = inContextAt loc (text "In data declaration" <+> ppQuot occ) $ do
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
    = inContextAt loc (text "In" <+> pretty gtype <+> ppQuot gname) $
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
  renameBndr (FunBind _rec occ sig matches) f
    = inContext (text "In the definition of" <+> ppQuot occ) $ do
        sig' <- rename sig
        renameBndr occ $ \name -> do
          matches' <- rnList matches
          let rec' = checkFunBindRec name matches'
          popContext $ f (FunBind rec' name sig' matches')
  renameBndr (PatBind loc pat rhs) f
    = inContextAt loc (text "In pattern binding" <+> ppQuot pat) $ do
        renameBndr pat $ \pat' -> do
          rhs' <- rename rhs
          popContext $ f (PatBind loc pat' rhs')

instance Rename TypeSig where
  rename NoTypeSig = return NoTypeSig
  rename (TypeSig loc polyty)
    = inContextAt loc (text "In type signature") $
        liftM (TypeSig loc) $ rename polyty

instance Rename Match where
  rename (Match loc pats rhs)
    = inContextAt loc (text "In function equation") $ do
        checkDupPatBndrs pats
        renameBndr pats $ \pats' -> liftM (Match loc pats') $ rename rhs


rnConDecl :: ConDecl Pr -> RnM (ConDecl Rn,(OccName,Name))
rnConDecl (ConDeclIn loc occ tys)
  = inContextAt loc (text "In data constructor declaration" <+> ppQuot occ) $ do
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
  rename (Lit lit) = return $ Lit lit
  rename ElseGuard = undefined  -- bug
  rename (PrefixApp op e) = liftM (PrefixApp op) $ rename e
  rename (InfixApp e1 op e2)
    = liftM2 (flip InfixApp op) (rename e1) (rename e2)
  rename (App f n) = liftM2 App (rename f) (rename n)
  rename (Lam loc pats body)
    = inContextAt loc (text "In lambda abstraction") $
        renameBndr pats $ \pats' -> liftM (Lam loc pats') $ rename body
  rename (Let binds body)
    = renameBndr binds $ \binds' -> liftM (Let binds') $ rename body
  rename (Ite g t e)
    = inContext (text "In 'if-then-else' expression") $
        liftM3 Ite (rename g) (rename t) (rename e)
  rename (If grhss)
    = inContext (text "In 'if' expression") $
        liftM If $ rename grhss
  rename (Case e NoPostTc alts)
    = inContext (text "In case expression") $
        liftM2 (flip Case NoPostTc) (rename e) (rnList alts)
  rename (Tuple l) = liftM Tuple $ mapM rename l
  rename (List l) = liftM List $ mapM rename l
  rename (Paren e) = liftM Paren $ rename e
  rename (LeftSection e op) = liftM (flip LeftSection op) $ rename e
  rename (RightSection op e) = liftM (RightSection op) $ rename e
  rename (EnumFromTo e1 e2) = liftM2 EnumFromTo (rename e1) (rename e2)
  rename (EnumFromThenTo e1 e2 e3)
    = liftM3 EnumFromThenTo (rename e1) (rename e2) (rename e3)
  rename (Coerc loc e polyty)
    = inContextAt loc (text "Type coercion") $
        liftM2 (Coerc loc) (rename e) (rename polyty)
  rename (QP qt pats body) = do
    checkQuantifierInPropContext qt
    inContext (text "In" <+> quotes (pretty qt) <+> text "formula") $ do
      checkDupPatBndrs pats
      renameBndr pats $ \pats' ->
        liftM (QP qt pats') $ rename body

checkQuantifierInPropContext :: Quantifier -> RnM ()
checkQuantifierInPropContext qt = do
  ctxt <- getContext
  when (not $ isPropContext ctxt) $
    throwError $ quotes (pretty qt) <+> text "formulas cannot appear out of propositional context"

instance Rename Con where
  rename (UserCon occ)     = liftM UserCon $ getName occ
  rename (BuiltinCon bcon) = return $ BuiltinCon bcon

instance Rename Rhs where
  rename (Rhs grhs whr)
--     = undefined
    = renameBndr whr $ \whr' -> liftM (flip Rhs whr') $ rename grhs

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
  rename (GuardedRhs loc guard exp)
    = inContextAt loc (text "In guarded alternative") $
        liftM2 (GuardedRhs loc) (rename guard) (rename exp)

instance Rename Alt where
  rename (Alt loc pat rhs)
    = inContextAt loc (text "In the case alternative" <+> ppQuot pat) $ do
        checkDupPatBndrs [pat]
        renameBndr pat $ \pat' -> liftM (Alt loc pat') $ rename rhs


instance RenameBndr (Pat Pr) (Pat Rn) where
  renameBndr (VarPat occ) f = renameBndr occ $ f . VarPat
  renameBndr (LitPat lit) f = f (LitPat lit)
  renameBndr (InfixPat p1 op p2) f
    = renameBndr p1 $ \p1' ->
      renameBndr p2 $ \p2' ->
        f (InfixPat p1' op p2')
  renameBndr (ConPat con ps) f = do
    con' <- rename con
    renameBndr ps $ f . ConPat con'
  renameBndr (TuplePat ps) f = renameBndr ps $ f . TuplePat
  renameBndr (ListPat ps) f = renameBndr ps $ f . ListPat
  renameBndr (ParenPat p) f = renameBndr p $ f . ParenPat
  renameBndr WildPat f = f WildPat
  renameBndr (SigPat p t) f = do t' <- rename t
                                 renameBndr p $ f . (flip SigPat t')

instance Rename PolyType where
    -- special case for error messages
  rename (ForallTy [] ty)
    = liftM (ForallTy []) $ rename ty
  rename (ForallTy typarams ty)
    = inContext (text "In 'forall' type") $ do
        checkDupTyParams typarams
        renameBndr typarams $ \typarams' ->
          liftM (ForallTy typarams') $ rename ty

instance Rename Type where
  rename (VarTy occ) = liftM VarTy $ getName occ
  rename (ConTy tycon) = liftM ConTy $ rename tycon
  rename (AppTy s t) = liftM2 AppTy (rename s) (rename t)
  rename (PredTy pat ty mbProp) = do
    ty' <- rename ty
    renameBndr pat $ \pat' ->
      liftM (PredTy pat' ty') $ inPropContext $ rnMaybe mbProp
  rename (FunTy a b) =
    renameBndr a $ \a' ->
      liftM (FunTy a') $ rename b
  rename (ListTy a) = liftM ListTy $ rename a
  rename (TupleTy ts) = renameBndr ts $ return . TupleTy
  rename (ParenTy a) = rename a

instance RenameBndr (Dom Pr) (Dom Rn) where
  renameBndr (Dom Nothing ty Nothing) f = do
    ty' <- rename ty
    f (Dom Nothing ty' Nothing)
  renameBndr (Dom (Just pat) ty mbProp) f = do
    ty' <- rename ty
    renameBndr pat $ \pat' -> do
      mbProp' <- inPropContext $ rnMaybe mbProp
      f (Dom (Just pat') ty' mbProp')

instance Rename TyCon where
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

checkFunBindRec :: Name -> [Match Rn] -> IsRec Rn
checkFunBindRec x matches
  | x `Set.member` fvMatches matches = Rec
  | otherwise                       = NonRec
