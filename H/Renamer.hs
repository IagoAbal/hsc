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
import H.Pretty
import H.Message
import H.Monad

import Name
import Unique

import Control.Monad.Error
import Control.Monad.Reader
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set




rnModule :: UniqSupply -> Module Pr -> IO (Either Message (Module Rn),UniqSupply)
rnModule us (Module loc modname decls)
  = do (res,us') <- runH (renameBndr decls return) (SrcContext loc (text "In module" <+> ppQuot modname) False) us Map.empty ()
       case res of
            Left err -> return (Left err,us')
            Right (decls',(),()) -> return (Right $ Module loc modname decls',us')


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
        renameBndr pat $ \pat' -> do
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
        renameBndr pats $ \pats' -> liftM (Match (Just loc) pats') $ rename rhs


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
        renameBndr pats $ \pats' -> liftM (Lam (Just loc) pats') $ rename body
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
  rename (QP qt pats body) = do
    checkQuantifierInPropContext qt
    inQPExprCtxt qt pats $ do
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
  rename (GuardedRhs loc guard expr)
    = inGuardedRhsCtxt loc $
        liftM2 (GuardedRhs loc) (rename guard) (rename expr)

instance Rename Alt where
  rename (Alt (Just loc) pat rhs)
    = inCaseAltCtxt loc pat $ do
        checkDupPatBndrs [pat]
        renameBndr pat $ \pat' -> liftM (Alt (Just loc) pat') $ rename rhs


instance RenameBndr (Pat Pr) (Pat Rn) where
  renameBndr (VarPat occ) f = renameBndr occ $ f . VarPat
  renameBndr (LitPat lit) f = f (LitPat lit)
  renameBndr (InfixPat p1 op NoPostTc p2) f
    = renameBndr p1 $ \p1' ->
      renameBndr p2 $ \p2' ->
        f (InfixPat p1' op NoPostTc p2')
  renameBndr (ConPat con NoPostTc ps) f = do
    con' <- rename con
    renameBndr ps $ f . (ConPat con' NoPostTc)
  renameBndr (TuplePat ps NoPostTc) f = renameBndr ps $ f . (flip TuplePat NoPostTc)
  renameBndr (ListPat ps NoPostTc) f = renameBndr ps $ f . (flip ListPat NoPostTc)
  renameBndr (ParenPat p) f = renameBndr p $ f . ParenPat
  renameBndr WildPatIn f = do
    uniq <- getUniq
    let wild_var = mkSysName (mkOccName VarNS "_x") uniq
    f (WildPat wild_var)
  renameBndr (SigPat p t) f = do t' <- rename t
                                 renameBndr p $ f . (flip SigPat t')
  renameBndr (AsPat x p) f
    = renameBndr p $ \p' ->
      renameBndr x $ \x' ->
        f (AsPat x' p')
  renameBndr _other  _f = undefined -- impossible

instance Rename (Type c) where
  rename (VarTy occ) = liftM VarTy $ getName occ
  rename (ConTyIn tycon) = liftM ConTyIn $ rename tycon
  rename (AppTyIn s t) = liftM2 AppTyIn (rename s) (rename t)
  rename (PredTy pat ty mbProp) = do
    ty' <- rename ty
    renameBndr pat $ \pat' ->
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
    renameBndr pat $ \pat' -> do
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

checkFunBindRec :: Name -> [Match Rn] -> IsRec Rn
checkFunBindRec x matches
  | x `Set.member` fvMatches matches = Rec
  | otherwise                       = NonRec
