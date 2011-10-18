{-# LANGUAGE GADTs, NamedFieldPuns, DoRec #-}

module H.Typecheck.Finalize where

import H.Syntax
import H.Phase
import H.Pretty
import H.SrcContext
import H.Monad
import H.Message ( Message )

import Name
import Unique

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Error
import Data.List ( find )
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Traversable as T


type TiM = H TiEnv () ()

data TiEnv
  = TiEnv {
      tiVarEnv   :: Map (Var Tc) (Var Ti)
    , tiTyConEnv :: Map (TyName Tc) (TyCon Ti)
    , tiConEnv   :: Map (Con Tc) (TcCon Ti)
    }

emptyTiEnv :: TiEnv
emptyTiEnv = TiEnv Map.empty
                (Map.fromList [(unitTyName,unitTyCon)
                              ,(boolTyName,boolTyCon)
                              ,(intTyName,intTyCon)
                              ,(natTyName,natTyCon)])
                (Map.fromList [(unitCon,tcUnitCon)
                              ,(falseCon,tcFalseCon)
                              ,(trueCon,tcTrueCon)
                              ,(nilCon,tcNilCon)
                              ,(consCon,tcConsCon)])


finModule :: UniqSupply -> Module Tc -> IO (Either Message (Module Ti),UniqSupply)
finModule us (Module loc modname decls)
  = do (res,us') <- runH decls_ti (SrcContext loc (text "In module" <+> ppQuot modname) False) us emptyTiEnv ()
       case res of
            Left err -> return (Left err,us')
            Right (decls',(),()) -> return (Right $ Module loc modname decls',us')
  where decls_ti = finDecls decls

lookupTyCon :: TyCon Tc -> TiM (TyCon Ti)
lookupTyCon tc = do
  tyConEnv <- asks tiTyConEnv
  case Map.lookup (tyConName tc) tyConEnv of
      Just tc' -> return tc'
      Nothing -> error $ "Finalize.lookupTyCon tc=" ++ prettyPrint tc

lookupVar :: Var Tc -> TiM (Var Ti)
lookupVar x = do
  varEnv <- asks tiVarEnv
  case Map.lookup x varEnv of
      Just x'  -> return x'
      Nothing -> error $ "Finalize.lookupVar  x=" ++ prettyPrint x

lookupCon :: TcCon Tc -> TiM (TcCon Ti)
lookupCon con = do
  conEnv <- asks tiConEnv
  case Map.lookup (tcConCon con) conEnv of
      Just con' -> return con'
      Nothing   -> error $ "Finalize.lookupCon con" ++ prettyPrint con


extendVarEnv :: [(Var Tc,Var Ti)] -> TiM a -> TiM a
extendVarEnv envl = local (\env@TiEnv{tiVarEnv} -> env{tiVarEnv = Map.union tiVarEnv venv'})
  where venv' = Map.fromList envl
  
extendTyConEnv :: [(TyName Tc,TyCon Ti)] -> TiM a -> TiM a
extendTyConEnv envl = local (\env@TiEnv{tiTyConEnv} -> env{tiTyConEnv = Map.union tiTyConEnv tcenv'})
  where tcenv' = Map.fromList envl

extendConEnv :: [(Con Tc,TcCon Ti)] -> TiM a -> TiM a
extendConEnv envl = local (\env@TiEnv{tiConEnv} -> env{tiConEnv = Map.union tiConEnv cenv'})
  where cenv' = Map.fromList envl

finDecls :: [Decl Tc] -> TiM [Decl Ti]
finDecls [] = return []
finDecls (TypeDecl loc tyname tvs rhs:ds) = do
  rhs' <- inTypeDeclCtxt loc (ppQuot tyname) $
            finType rhs
  extendTyConEnv [(UserTyCon tyname,SynTyCon (UserTyCon tyname) tvs rhs')] $ do
    ds' <- finDecls ds
    return (TypeDecl loc tyname tvs rhs':ds')
finDecls (DataDecl loc tyname tvs constrs:ds)
  = do
    rec {
      let tycon_ti = AlgTyCon (UserTyCon tyname) $ map snd con_env'
          tycon_env = [(UserTyCon tyname,tycon_ti)]
          con_env = [ (con_tc,TcCon con_ti tycon_ti) | (con_tc,con_ti) <- con_env' ]
            -- I think ConEnv should be Con Tc -> TcCon Ti ...
    ; (constrs',con_env') <- inDataDeclCtxt loc (ppQuot tyname) $
                                extendTyConEnv tycon_env $
                                  liftM unzip $ mapM finConDecl constrs
    }
    extendTyConEnv tycon_env $
      extendConEnv con_env $ do
        ds' <- finDecls ds
        return (DataDecl loc tyname tvs constrs':ds')
  where finConDecl :: ConDecl Tc -> TiM (ConDecl Ti,(Con Tc,Con Ti))
        finConDecl (ConDecl loc1 conname doms)
          = inConDeclCtxt loc1 (ppQuot conname) $ do
          doms' <- finDoms doms
          conname' <- finBndr conname return 
          return (ConDecl loc conname' doms',(UserCon conname,UserCon conname'))
        finConDecl _other = undefined -- impossible
finDecls (ValDecl bind:ds)
  = finBind bind $ \bind' -> do
  ds' <- finDecls ds
  return (ValDecl bind':ds')
finDecls (GoalDecl loc gtype gname (PostTc tvs) prop:ds) = do
  prop' <- inGoalDeclCtxt loc gtype (ppQuot gname) $
             finExp prop
  ds' <- finDecls ds
  return (GoalDecl loc gtype gname (PostTc tvs) prop':ds')
finDecls _other = undefined -- impossible


finBinds :: [Bind Tc] -> ([Bind Ti] -> TiM a) -> TiM a
finBinds []     cont = cont []
finBinds (b:bs) cont = finBind b $ \b' ->
                         finBinds bs $ \bs' ->
                           cont (b':bs')

finBind :: Bind Tc -> (Bind Ti -> TiM a) -> TiM a
finBind (PatBind mb_loc pat rhs) cont
  = patBindCtxt $ do
  rhs' <- finRhs rhs
  finPat pat $ \pat' -> popContext $ cont (PatBind mb_loc pat' rhs')
  where patBindCtxt = case mb_loc of
                          Nothing  -> id
                          Just loc -> inPatBindCtxt loc (ppQuot pat)
finBind (FunBind NonRec fun tysig (PostTc typs) matches) cont
  = inFunBindCtxt (ppQuot fun) $ do
  tysig' <- finTypeSig tysig
  matches' <- finMatches matches
  finBndr fun $ \fun' ->
    popContext $ cont (FunBind NonRec fun' tysig' (PostTc typs) matches')
finBind (FunBind Rec fun tysig (PostTc typs) matches) cont
  = inFunBindCtxt (ppQuot fun) $ do
  tysig' <- finTypeSig tysig
  finBndr fun $ \fun' -> do
    matches' <- finMatches matches
    popContext $ cont (FunBind Rec fun' tysig' (PostTc typs) matches')
finBind _other _cont = undefined -- impossible

finTypeSig :: TypeSig Tc -> TiM (TypeSig Ti)
finTypeSig NoTypeSig = return NoTypeSig
finTypeSig (TypeSig loc pty) = liftM (TypeSig loc) $ finType pty

finMatches :: [Match Tc] -> TiM [Match Ti]
finMatches = mapM finMatch

finMatch :: Match Tc -> TiM (Match Ti)
finMatch (Match mb_loc pats rhs)
  = funMatchCtxt $
      finPats pats $ \pats' -> liftM (Match mb_loc pats') $ finRhs rhs
  where funMatchCtxt = case mb_loc of
                           Nothing  -> id
                           Just loc -> inFunMatchCtxt loc

finExps :: [Exp Tc] -> TiM [Exp Ti]
finExps = mapM finExp

finExp :: Exp Tc -> TiM (Exp Ti)
finExp (Var x) = liftM Var $ lookupVar x
finExp (Con con) = liftM Con $ lookupCon con
finExp (Op op) = return (Op op)
finExp (Lit lit) = return (Lit lit)
finExp (PrefixApp op expr) = liftM2 PrefixApp (finExp op) (finExp expr)
finExp (InfixApp e1 op e2)
  = liftM3 InfixApp (finExp e1) (finExp op) (finExp e2)
finExp (App f x) = liftM2 App (finExp f) (finExp x)
-- ...
finExp (TyApp e tys)
  | Just (MetaTy mtv) <- find isMetaTy tys
  = throwError $ text "Cannot infer the" <+> ppQuot (occNameOf mtv)
                    <+> text "type argument of" <+> ppQuot e
finExp (TyApp (Op (BoolOp bop)) [ty])
  | bop `elem` [EqB, NeqB] = do
    ctx <- getContext
    when (not $ isPropContext ctx) check_eq_ty
    liftM (TyApp (Op (BoolOp bop))) $ finTypes [ty]
  where check_eq_ty
          | isFunTy ty = throwError $ text "Extensionality only applies inside a logical context"
          | isVarTy ty = throwError $ text "Equality operators cannot be applied to arbitrary types"
          | otherwise  = return ()
finExp (TyApp e tys) = liftM2 TyApp (finExp e) (finTypes tys)
finExp (Lam mb_loc pats rhs)
  = lambdaAbsCtxt $ finPats pats $ \pats' ->
                      liftM (Lam mb_loc pats') $ finRhs rhs
  where lambdaAbsCtxt = case mb_loc of
                            Nothing  -> inContext (text "In lambda abstraction: \\" <+> (myFsep $ map pretty pats) <+> text "-> ...")
                            Just loc -> inLambdaAbsCtxt loc pats
finExp (Let bs body) = finBinds bs $ \bs' -> liftM (Let bs') $ finExp body
finExp (TyLam tvs expr) = liftM (TyLam tvs) $ finExp expr
finExp (Ite (PostTc ite_ty) g t e)
  = inIteExprCtxt g $ do
  ite_ty' <- finType ite_ty
  liftM3 (Ite (PostTc ite_ty')) (finExp g) (finExp t) (finExp e)
finExp (If (PostTc if_ty) grhss)
  = inIfExprCtxt $ do
  if_ty' <- finType if_ty
  liftM (If (PostTc if_ty')) $ finGuardedRhss grhss
finExp (Case scrut (PostTc case_ty) alts) = do
  scrut' <- finExp scrut
  case_ty' <- finType case_ty
  liftM (Case scrut' (PostTc case_ty')) $ finAlts alts
finExp (Tuple (PostTc tup_ty) es) = do
  tup_ty' <- finType tup_ty
  liftM (Tuple (PostTc tup_ty')) $ finExps es
finExp (List (PostTc list_ty) es) = do
  list_ty' <- finType list_ty
  liftM (List (PostTc list_ty')) $ finExps es
finExp (Paren expr) = liftM Paren $ finExp expr
finExp (LeftSection e1 op) = liftM2 LeftSection (finExp e1) (finExp op)
finExp (RightSection op e2) = liftM2 RightSection (finExp op) (finExp e2)
finExp (EnumFromTo e1 eN) = liftM2 EnumFromTo (finExp e1) (finExp eN)
finExp (EnumFromThenTo e1 e2 eN)
  = liftM3 EnumFromThenTo (finExp e1) (finExp e2) (finExp eN)
finExp (Coerc loc expr pty)
  = inCoercExprCtxt loc $
      liftM2 (Coerc loc) (finExp expr) (finType pty)
finExp (QP qt qvars prop)
  = inQPExprCtxt qt qvars $
      finQVars qvars $ \qvars' ->
        liftM (QP qt qvars') $ finProp prop
finExp _other = undefined -- impossible

finProp :: Prop Tc -> TiM (Prop Ti)
finProp = inPropContext . finExp

finAlts :: [Alt Tc] -> TiM [Alt Ti]
finAlts = mapM finAlt

finAlt :: Alt Tc -> TiM (Alt Ti)
finAlt (Alt (Just loc) pat rhs)
  = inCaseAltCtxt loc pat $
      finPat pat $ \pat'-> liftM (Alt (Just loc) pat') $ finRhs rhs

finRhs :: Rhs Tc -> TiM (Rhs Ti)
finRhs (Rhs (PostTc rhs_ty) grhs whr) = do
  rhs_ty' <- finType rhs_ty
  finBinds whr $ \whr' -> do
    grhs' <- finGRhs grhs
    return $ Rhs (PostTc rhs_ty') grhs' whr'

finGRhs :: GRhs Tc -> TiM (GRhs Ti)
finGRhs (UnGuarded expr) = liftM UnGuarded $ finExp expr
finGRhs (Guarded grhss)  = liftM Guarded $ finGuardedRhss grhss

finGuardedRhss :: GuardedRhss Tc -> TiM (GuardedRhss Ti)
finGuardedRhss (GuardedRhss grhss elserhs)
  = liftM2 GuardedRhss (mapM finGuardedRhs grhss) (finElse elserhs)
finGuardedRhss _other = undefined -- impossible

finGuardedRhs :: GuardedRhs Tc -> TiM (GuardedRhs Ti)
finGuardedRhs (GuardedRhs loc g e)
 = inGuardedRhsCtxt loc $
     liftM2 (GuardedRhs loc) (finExp g) (finExp e)

finElse :: Else Tc -> TiM (Else Ti)
finElse NoElse          = return NoElse
finElse (Else loc expr) = liftM (Else loc) $ finExp expr

finBndr :: Var Tc -> (Var Ti -> TiM a) -> TiM a
finBndr (V name (MetaTy _) _) _cont
  = throwError $ text "Cannot infer the type of" <+> pretty name
finBndr x@(V name pty isSk) cont = do
  x' <- inContext (text "In variable" <+> ppQuot name <+> text "type") $
          liftM (\pty' -> V name pty' isSk) $ finType pty
  extendVarEnv [(x,x')] $ cont x'

finPats :: [Pat Tc] -> ([Pat Ti] -> TiM a) -> TiM a
finPats [] cont = cont []
finPats (p:ps) cont = finPat p $ \p' ->
                      finPats ps $ \ps' ->
                        cont (p':ps')

finPat :: Pat Tc -> (Pat Ti -> TiM a) -> TiM a
finPat (VarPat x) cont = finBndr x $ cont . VarPat
finPat (LitPat lit) cont = cont (LitPat lit)
finPat (InfixCONSPat (PostTc ty) p1 p2) cont = do
  ty' <- finType ty
  finPat p1 $ \p1' ->
    finPat p2 $ \p2' ->
      cont (InfixCONSPat (PostTc ty') p1' p2')
finPat (ConPat con (PostTc tys) ps) cont = do
  con' <- lookupCon con
  tys' <- finTypes tys
  finPats ps $ cont . ConPat con' (PostTc tys')
finPat (TuplePat ps (PostTc ty)) cont = do
  ty' <- finType ty
  finPats ps $ cont . flip TuplePat (PostTc ty')
finPat (ListPat ps (PostTc ty)) cont = do
  ty' <- finType ty
  finPats ps $ cont . flip ListPat (PostTc ty')
finPat (ParenPat p) cont = finPat p $ cont . ParenPat
finPat (WildPat (V _ (MetaTy _) _)) _cont
  = throwError $ text "Cannot infer the type of `_' pattern"
  -- Should we remove wildcard-patterns here ? After all, we may have
  -- introduced uses of such variable for typing purposes...
finPat (WildPat wild_var@(V name pty isSk)) cont = do
  wild_var' <- inContext (text "In `_' pattern type") $
          liftM (\pty' -> V name pty' isSk) $ finType pty
  extendVarEnv [(wild_var,wild_var')] $ cont (WildPat wild_var')
finPat (AsPat x pat) cont
  = finBndr x $ \x' -> finPat pat $ \pat' -> cont (AsPat x' pat')
-- finPat (SigPat pat ty) cont = do
--   ty' <- finType ty
--   finPat pat $ cont . flip SigPat ty'
finPat _other _cont = undefined -- impossible

finQVars :: [QVar Tc] -> ([QVar Ti] -> TiM a) -> TiM a
finQVars []     cont = cont []
finQVars (v:vs) cont = finQVar v $ \v' ->
                       finQVars vs $ \vs' ->
                        cont (v':vs')

finQVar :: QVar Tc -> (QVar Ti -> TiM a) -> TiM a
finQVar (QVar x mb_ty) f = do
  mb_ty' <- T.mapM finType mb_ty
  finBndr x $ \x' -> f (QVar x' mb_ty')

finTypes :: [Type c Tc] -> TiM [Type c Ti]
finTypes = mapM finType

finType :: Type c Tc -> TiM (Type c Ti)
finType (VarTy a) = return (VarTy a)
finType (ConTy tc tys) = liftM2 ConTy (lookupTyCon tc) (finTypes tys)
finType (PredTy pat ty mb_prop) = do
  ty' <- finType ty
  finPat pat $ \pat' ->
    liftM (PredTy pat' ty') (T.mapM finProp mb_prop)
finType (FunTy dom rang)
  = finDom dom $ \dom' -> liftM (FunTy dom') $ finType rang
finType (ListTy ty) = liftM ListTy $ finType ty
finType (TupleTy ds) = liftM TupleTy $ finDoms ds
finType (MetaTy mtv)
  = throwError $ text "Unresolved meta-type:" <+> pretty mtv
finType tcpty@(ForallTy tvs ty)
  = inTypeCtxt tcpty $
      liftM (ForallTy tvs) $ finType ty
finType _other = undefined -- impossible

finDoms :: [Dom Tc] -> TiM [Dom Ti]
finDoms []     = return []
finDoms (d:ds) = finDom d $ \d' ->
                    liftM (d':) $ finDoms ds

finDom :: Dom Tc -> (Dom Ti -> TiM a) -> TiM a
finDom (Dom Nothing ty Nothing) cont = do
  ty' <- finType ty
  cont (Dom Nothing ty' Nothing)
finDom (Dom (Just pat) ty mb_prop) cont = do
  ty' <- finType ty
  finPat pat $ \pat' -> do
    mb_prop' <- T.mapM finProp mb_prop
    cont (Dom (Just pat') ty' mb_prop')
finDom _other _cont = undefined -- imposible
