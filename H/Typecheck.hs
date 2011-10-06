{-# LANGUAGE GADTs, ScopedTypeVariables, NamedFieldPuns #-}

-- I still need to check linearity
module H.Typecheck where

import H.Typecheck.TcM
import H.Typecheck.Unify
import H.Typecheck.Zonk
import H.Typecheck.Utils

import H.Syntax
import H.Phase
import H.Pretty
import H.Monad
import H.Message
import H.SrcContext

import Name
import Unique
import Sorted

import Data.IORef
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Error


tcModule :: UniqSupply -> Module Rn -> IO (Either Message (Module Tc),UniqSupply)
tcModule us (Module loc modname decls)
  = do (res,us') <- runH decls_tc (SrcContext loc (text "In module" <+> ppQuot modname) False) us emptyTcEnv ()
       case res of
            Left err -> return (Left err,us')
            Right (decls',(),()) -> return (Right $ Module loc modname decls',us')
  where decls_tc = tcDecls decls >>= zonkDecls


kcType :: Type c Rn -> TcM (Type c Tc,Kind)
kcType (VarTy n) = do
  tv <- lookupTyVar n
  return (VarTy tv, tyVarKind tv)
--   ConTy :: TyCon p -> Type p
kcType (ConTyIn tn) = do
  tycon <- lookupTyCon tn
  return (ConTy tycon [],kindOf tycon)
--   AppTy :: Type p -> Type p -> Type p
kcType rntype@(AppTyIn t a) = traceDoc (text "AppTyIn" <+> pretty rntype) $ do
  (ConTy tc args,t_ki) <- kcType t
  (a',a_ki) <- kcType a
  case t_ki of
      FunKi k1 k2
        | k1 == a_ki -> return (ConTy tc (args ++ [a']),k2)
        | otherwise  -> throwError $ errCannotUnify "kinds" k1 a_ki
      _other      -> throwError $ text "Cannot unify kind" <+> pretty t_ki <+> text "with ? -> ?"
--   PredTy :: Pat p -> Type p -> Maybe (Prop p) -> Type p
kcType rnty@(PredTy pat ty mbprop)
  = inTypeCtxt rnty $ do
  ty' <- checkKind ty typeKi
  (pat',pat_env) <- tcPat pat (Check ty')
  mbprop' <- extendVarEnv pat_env $
               checkMaybeExpType mbprop boolTy
  return (PredTy pat' ty' mbprop',typeKi)
--   FunTy :: Dom p -> Range p -> Type p
kcType (FunTy dom rang) = do
  (dom',dom_env) <- kcDom dom
  rang' <- extendVarEnv dom_env $
             checkKind rang typeKi
  return (FunTy dom' rang',typeKi)
--   ListTy :: Type p -> Type p
kcType (ListTy ty) = do
  ty' <- checkKind ty typeKi
  return (ListTy ty',typeKi)
--   TupleTy :: [Dom p] -> Type p
kcType (TupleTy ds) = do
  ds' <- kcDoms ds
  return (TupleTy ds',typeKi)
kcType rnpty@(ForallTy ns ty)
  = inTypeCtxt rnpty $ do
  tvs_sk <- mapM skoTyVar tvs
  ty'_sk <- extendTyVarEnv (zip ns tvs_sk) $
              checkKind ty typeKi
  ty'_sk_zo <- zonkType ty'_sk
  ty' <- substType [] (zip tvs_sk vtys) ty'_sk_zo
  return (ForallTy tvs ty',typeKi)
  where tvs = map (flip mkTyVar typeKi) ns
        vtys = map VarTy tvs

checkKind :: Type c Rn -> Kind -> TcM (Type c Tc)
checkKind ty exp_ki = do
  (ty',ty_ki) <- kcType ty
  if ty_ki == exp_ki
    then return ty'
    else throwError $ errCannotUnify "kinds" exp_ki ty_ki

errCannotUnify :: Pretty a => String -> a -> a -> Doc
errCannotUnify what exp inf
  = hang (text "Cannot unify" <+> text what) 2 $
         text "expected" <> colon <+> pretty exp
      $$ text "inferred" <> colon <+> pretty inf

kcDoms :: [Dom Rn] -> TcM [Dom Tc]
kcDoms []     = return []
kcDoms (d:ds) = do
  (d',d_env) <- kcDom d
  ds' <- extendVarEnv d_env $
           kcDoms ds
  return (d':ds')

kcDom :: Dom Rn -> TcM (Dom Tc,[(Name,Var Tc)])
kcDom (Dom Nothing ty Nothing) = do
  ty' <- checkKind ty typeKi
  return (Dom Nothing ty' Nothing,[])
kcDom (Dom (Just pat) ty mbprop) = do
  ty' <- checkKind ty typeKi
  (pat', pat_env) <- tcPat pat (Check ty')
  mbprop' <- extendVarEnv pat_env $
               checkMaybeExpType mbprop boolTy
  return (Dom (Just pat') ty' mbprop',pat_env)
kcDom _other = undefined

  -- Bidirectional typechecking !
data Expected a = Infer (IORef a)
                | Check a

getExpected :: Expected a -> TcM a
getExpected (Check x) = return x
getExpected (Infer ref) = liftIO $ readIORef ref


tcDecls :: [Decl Rn] -> TcM [Decl Tc]
tcDecls [] = return []
tcDecls (tydecl@(TypeDecl _ _ _ _):decls) = do
  (tydecl',tydecl_env) <- kcTypeDecl tydecl
  decls' <- extendTyConEnv tydecl_env $
              tcDecls decls
  return (tydecl':decls')
tcDecls (datadecl@(DataDecl _ _ _ _):decls) = do
  (tydecl',tycon_env,cons_env) <- kcDataDecl datadecl
  decls' <- extendTyConEnv tycon_env $
            extendConEnv cons_env $
              tcDecls decls
  return (tydecl':decls')
tcDecls (ValDecl bind:decls) = do
  ([bind'],var_env) <- tcBinds [bind]
  decls' <- addGlobalVars (map snd var_env) $
            extendVarEnv var_env $
              tcDecls decls
  return (ValDecl bind':decls')
tcDecls (goaldecl@(GoalDecl _ _ _ _ _):decls) = do
  goaldecl' <- tcGoalDecl goaldecl
  decls' <- tcDecls decls
  return (goaldecl':decls')

-- TypeDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> Type p -> Decl p
kcTypeDecl ::	Decl Rn -> TcM (Decl Tc, [(TyName Rn,TyCon Tc)])
kcTypeDecl (TypeDecl loc ty_name ty_params ty_rhs)
  = inTypeDeclCtxt loc (ppQuot ty_name) $ do
      (sig,_) <- kcType $ forallTy ty_params ty_rhs
      let (tvs,ty_rhs') = splitSigma sig
          ty_var = mkTyVar ty_name tc_kind
          tycon = SynTyCon {
                    tyConName = UserTyCon ty_var
                  , tyConParams = tvs
                  , synTyConRhs = ty_rhs'
                  }
      return (TypeDecl loc ty_var tvs ty_rhs',[(UserTyCon ty_name,tycon)])
  where tc_kind = funKi (replicate (length ty_params) typeKi) typeKi

-- DataDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> [ConDecl p] -> Decl p
kcDataDecl :: Decl Rn -> TcM (Decl Tc,[(TyName Rn,TyCon Tc)],[(Con Rn,Con Tc)])
kcDataDecl (DataDecl loc ty_name typarams constrs)
  = inDataDeclCtxt loc (ppQuot ty_name) $ do
    let tvs = map (flip mkTyVar typeKi) typarams
    (constrs',cons_env) <- liftM unzip $
                           extendTyConEnv tycon_env $
                             mapM (tc_constr tvs) constrs
    return (DataDecl loc ty_var tvs constrs',tycon_env,cons_env)
  where ty_kind = funKi (replicate (length typarams) typeKi) typeKi
        ty_var = mkTyVar ty_name ty_kind
        tycon = AlgTyCon $ UserTyCon ty_var
        tycon_env = [(UserTyCon ty_name,tycon)]
        con_res_ty = appTyIn (UserTyCon ty_name) (map VarTy typarams)
--         ConDecl :: Ge p Rn => SrcLoc -> NAME p -> [Dom p] -> ConDecl p
        tc_constr :: [TyVar] -> ConDecl Rn -> TcM (ConDecl Tc,(Con Rn,Con Tc))
        tc_constr ty_tvs (ConDecl loc con_name doms)
          = inConDeclCtxt loc (ppQuot con_name) $ do
          (con_ty,_) <- kcType (forallTy typarams $ funTy doms con_res_ty)
          let (con_tvs,con_tau) = splitSigma con_ty
              con = mkVar con_name con_ty
          con_tau' <- substType [] (zip con_tvs (map VarTy ty_tvs)) con_tau
          let (doms',_) = splitFunTy con_tau
          return (ConDecl loc con doms',(UserCon con_name,UserCon con))


-- maybe we should generalise 'quantify' a little more to don't repeat the code here
-- GoalDecl :: SrcLoc -> GoalType -> GoalNAME p -> PostTcTyParams p -> Prop p -> Decl p
tcGoalDecl :: Decl Rn -> TcM (Decl Tc)
tcGoalDecl (GoalDecl loc gtype g_name NoPostTc prop)
  = inGoalDeclCtxt loc gtype (ppQuot g_name) $ do
  prop' <- checkExpType prop boolTy
  prop'_z <- zonkExp prop'
  let prop_mtvs = Set.toAscList $ propMTV prop'_z
  forall_tvs <- mapM (flip newTyVar typeKi) $ take (length prop_mtvs) tvs_names
  mapM_ bind (zip prop_mtvs forall_tvs)
  prop'' <- zonkExp prop'_z
  return (GoalDecl loc gtype g_name (PostTc forall_tvs) prop')
  where tvs_names = [ [x]          | x <- ['a'..'z'] ] ++
                    [ (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]
        -- 'bind' is just a cunning way of doing the substitution
        bind (mtv,tv) = writeMetaTyVar mtv (VarTy tv)

-- this is not so easy because the type of a  bind may depend on previous binds
tcBinds :: [Bind Rn] -> TcM ([Bind Tc],[(Name,Var Tc)])
tcBinds binds = go [] [] binds
  where go :: [Bind Tc] -> [(Name,Var Tc)] -> [Bind Rn] -> TcM ([Bind Tc],[(Name,Var Tc)])
        go prev_binds env_acc []     = return (prev_binds,env_acc)
        go prev_binds env_acc (b:bs) = do
          (b',b_env) <- tc_bind prev_binds b
          extendVarEnv b_env $
            go (prev_binds ++ [b']) (env_acc++b_env) bs
          

tc_bind :: [Bind Tc] -> Bind Rn -> TcM (Bind Tc,[(Name,Var Tc)])
tc_bind prev_binds (PatBind (Just loc) pat rhs)
  = inPatBindCtxt loc (ppQuot pat) $ do
  (rhs',rhs_ty) <- inferRhs rhs
  rhs_ty' <- letType prev_binds rhs_ty
  (pat',pat_env) <- checkPat pat rhs_ty'
  return (PatBind (Just loc) pat' rhs',pat_env)
tc_bind prev_binds (FunBind NonRec fun (TypeSig loc pty) NoPostTc matches)
  = inFunBindCtxt (ppQuot fun) $ do
  traceDoc (text "FunBind-NonRec-TypeSig" <+> pretty fun <+> text "==============") $ do
  (pty',_) <- kcType pty
--   traceDoc (text "FunBind" <+> pretty fun <+> text "type_sig=" <+> pretty pty') $ do
  let poly_tvs = quantifiedTyVars pty'
  (skol_tvs,sk_ty) <- skolemise pty'
--   traceDoc (text "FunBind" <+> pretty fun <+> text "sk_ty=" <+> pretty sk_ty) $ do
  matches' <- tcMatches matches (Check sk_ty)
  matches'_z <- zonkMatches matches'
  matches'' <- substMatches [] (zip skol_tvs $ map VarTy poly_tvs) matches'_z
  let fun' = mkVar fun pty'
--   traceDoc (text "FunBind" <+> pretty fun <+> text "matches''=" <+> sep (map (ppMatch fun') matches'')) $ do
  return (FunBind NonRec fun' (TypeSig loc pty') (PostTc poly_tvs) matches'',[(fun,fun')])
tc_bind prev_binds (FunBind NonRec fun NoTypeSig NoPostTc matches)
  = inFunBindCtxt (ppQuot fun) $ do
  traceDoc (text "FunBind-NonRec-NoTypeSig" <+> pretty fun <+> text "==============") $ do
  (matches',tau_fun_ty) <- inferMatches matches
  traceDoc (text "FunBind" <+> pretty fun <+> text "tau_fun_ty=" <+> pretty tau_fun_ty) $ do
  (poly_tvs,fun_ty) <- generalise tau_fun_ty
--   traceDoc (text "FunBind" <+> pretty fun <+> text "fun_ty=" <+> pretty fun_ty) $ do
  let fun' = mkVar fun fun_ty
  return (FunBind NonRec fun' NoTypeSig (PostTc poly_tvs) matches',[(fun,fun')])
tc_bind prev_binds (FunBind Rec fun (TypeSig loc pty) NoPostTc matches)
  = inFunBindCtxt (ppQuot fun) $ do
  (pty',_) <- kcType pty
  let poly_tvs = quantifiedTyVars pty'
      fun' = mkVar fun pty'
  (skol_tvs,skol_ty) <- skolemise pty'
  matches' <- extendVarEnv [(fun,fun')] $
                tcMatches matches (Check skol_ty)
  matches'' <- substMatches [] (zip skol_tvs $ map VarTy poly_tvs) matches'
  return (FunBind Rec fun' (TypeSig loc pty') (PostTc poly_tvs) matches'',[(fun,fun')])
tc_bind prev_binds (FunBind Rec fun NoTypeSig NoPostTc matches@[Match _ pats _])
  = inFunBindCtxt (ppQuot fun) $ do
  (pats',pats_tys,_) <- inferPats pats
  res_ty <- newMetaTy "t" typeKi
  let tau_fun_ty = funTy (zipWith patternDom pats' pats_tys) res_ty
      fun_rec    = mkVar fun (tau2sigma tau_fun_ty)
  matches' <- extendVarEnv [(fun,fun_rec)] $
                tcMatches matches (Check tau_fun_ty)
  (poly_tvs,fun_ty) <- generalise tau_fun_ty
  let fun' = mkVar fun fun_ty
  return (FunBind Rec fun' NoTypeSig (PostTc poly_tvs) matches',[(fun,fun')])
tc_bind prev_binds (FunBind Rec fun NoTypeSig NoPostTc matches@(Match _ pats _:_))
  = inFunBindCtxt (ppQuot fun) $ do
  traceDoc (text "FunBind-Rec-NoTypeSig-ManyMatches" <+> pretty fun <+> text "==============") $ do
  (_,pats_tys,_) <- inferPats pats
  traceDoc (text "FunBind-Rec-NoTypeSig-ManyMatches inferred pats_ty =" <+> (sep $ map pretty pats_tys)) $ do
  res_ty <- newMetaTy "t" typeKi
  let tau_fun_ty = funTy (map type2dom pats_tys) res_ty
      fun_rec    = mkVar fun (tau2sigma tau_fun_ty)
  matches' <- extendVarEnv [(fun,fun_rec)] $
                tcMatches matches (Check tau_fun_ty)
  traceDoc (text "FunBind-Rec-NoTypeSig-ManyMatches inferred tau_fun_ty =" <+> pretty tau_fun_ty) $ do
  (poly_tvs,fun_ty) <- generalise tau_fun_ty
  traceDoc (text "FunBind-Rec-NoTypeSig-ManyMatches inferred fun_ty =" <+> pretty fun_ty) $ do
  let fun' = mkVar fun fun_ty
  return (FunBind Rec fun' NoTypeSig (PostTc poly_tvs) matches',[(fun,fun')])


inferMatches :: [Match Rn] -> TcM ([Match Tc],Tau Tc)
inferMatches matches = do
  ref <- liftIO $ newIORef (error "inferMatches: empty result")
  matches' <- tcMatches matches (Infer ref)
  ty <- liftIO $ readIORef ref
  return (matches',ty)

tcMatches :: [Match Rn] -> Expected (Tau Tc) -> TcM [Match Tc]
tcMatches matches (Check exp_ty)
  = mapM (flip checkMatch exp_ty) matches
  -- when we infer the type for one single match then we can
  -- infer pattern types
tcMatches [Match (Just loc) pats rhs] (Infer ref)
  = inFunMatchCtxt loc $ do
  (pats',pats_tys,pats_env) <- inferPats pats
  (rhs',rhs_ty) <- extendVarEnv pats_env $
                     inferRhs rhs
  let doms = zipWith patternDom pats' pats_tys
  liftIO $ writeIORef ref (funTy doms rhs_ty)
  return [Match (Just loc) pats' rhs']
tcMatches (m:ms) (Infer ref) = do
  (m',m_ty) <- inferMatch m
  ms' <- mapM (flip checkMatch m_ty) ms
  liftIO $ writeIORef ref m_ty
  return (m':ms')

checkMatch :: Match Rn -> Tau Tc -> TcM (Match Tc)
checkMatch match ty = tcMatch match (Check ty)

inferMatch :: Match Rn -> TcM (Match Tc,Tau Tc)
inferMatch match = do
  ref <- liftIO $ newIORef (error "inferMatch: empty result")
  match' <- tcMatch match (Infer ref)
  ty <- liftIO $ readIORef ref
  return (match',ty)

-- Match SrcLoc [Pat p] (Rhs p)
tcMatch :: Match Rn -> Expected (Tau Tc) -> TcM (Match Tc)
tcMatch (Match (Just loc) pats rhs) (Check exp_ty)
  = inFunMatchCtxt loc $ do
  traceDoc (text "tcMatch-Check pats=" <+> (sep $ map pretty pats)) $ do
  (pats',pats_env,rhs_exp_ty) <- checkEq pats exp_ty
  rhs' <- extendVarEnv pats_env $
            checkRhs rhs rhs_exp_ty
  traceDoc (text "tcMatch-Check checkRhs done") $ do
  return (Match (Just loc) pats' rhs')
tcMatch (Match (Just loc) pats rhs) (Infer ref)
  = inFunMatchCtxt loc $ do
  (pats',pats_tys,pats_env) <- inferPats pats
  (rhs',rhs_ty) <- extendVarEnv pats_env $
                     inferRhs rhs
  let doms = map type2dom pats_tys
  liftIO $ writeIORef ref (funTy doms rhs_ty)
  return (Match (Just loc) pats' rhs')


checkExpType :: Exp Rn -> Tau Tc -> TcM (Exp Tc)
checkExpType exp ty = tcExp exp (Check ty)

inferExpType :: Exp Rn -> TcM (Exp Tc,Tau Tc)
inferExpType exp = do
  ref <- liftIO $ newIORef (error "inferType: empty result")
  exp' <- tcExp exp (Infer ref)
  ty <- liftIO $ readIORef ref
  return (exp',ty)

checkMaybeExpType :: Maybe (Exp Rn) -> Tau Tc -> TcM (Maybe (Exp Tc))
checkMaybeExpType Nothing    _ty = return Nothing
checkMaybeExpType (Just exp)  ty = liftM Just $ checkExpType exp ty


tcExp :: Exp Rn -> Expected (Tau Tc) -> TcM (Exp Tc)
tcExp (Var n) exp_ty = do
  v <- lookupVar n
  instSigma (Var v) (varType v) exp_ty
tcExp (Con con) exp_ty = do
  con' <- lookupCon con
  instSigma (Con con') (sortOf con') exp_ty
tcExp (Op op) exp_ty = do
  instSigma (Op op) (sortOf op) exp_ty
tcExp (Lit lit) exp_ty = instSigma (Lit lit) intTy exp_ty
--   PrefixApp :: Op -> Exp p -> Exp p
tcExp (PrefixApp op arg) exp_ty = do
  (op',[arg']) <- tcApp op [arg] exp_ty
  return (PrefixApp op' arg')
--   InfixApp :: Exp p -> Op -> Exp p -> Exp p
tcExp rnexp@(InfixApp e1 op e2) exp_ty
  = inExprCtxt rnexp $ do
      (op', [e1',e2']) <- tcApp op [e1,e2] exp_ty
      return (InfixApp e1' op' e2')
--   App :: Exp p -> Exp p -> Exp p
tcExp (App fun arg) exp_ty = do
  (fun',[arg']) <- tcApp fun [arg] exp_ty
  return (App fun' arg')
--   Lam :: SrcLoc -> [Pat p] -> Exp p -> Exp p
tcExp (Lam (Just loc) pats body) (Check exp_ty)
  = inLambdaAbsCtxt loc pats $ do
  (pats',pats_env,resty) <- checkEq pats exp_ty
  body' <- extendVarEnv pats_env $
             checkExpType body resty
  return (Lam (Just loc) pats' body')
  where n_pats = length pats
tcExp (Lam (Just loc) pats body) (Infer ref)
  = inLambdaAbsCtxt loc pats $ do
  (pats',pats_tys,pats_env) <- inferPats pats
  (body',body_ty) <- extendVarEnv pats_env $
                       inferExpType body
  let doms = zipWith patternDom pats' pats_tys
  liftIO $ writeIORef ref (funTy doms body_ty)
  return (Lam (Just loc) pats' body')
--   Let :: [Bind p] -> Exp p -> Exp p
tcExp (Let binds body) (Check exp_ty) = do
  (binds',binds_env) <- tcBinds binds
  body' <- extendVarEnv binds_env $
             checkExpType body exp_ty
  return (Let binds' body')
tcExp (Let binds body) (Infer ref) = do
  (binds',binds_env) <- tcBinds binds
  (body',body_ty) <- extendVarEnv binds_env $
                       inferExpType body
  body_ty' <- letType binds' body_ty
  liftIO $ writeIORef ref body_ty'
  return (Let binds' body')
--   Ite :: Prop p -> Exp p -> Exp p -> Exp p
tcExp (Ite NoPostTc g t e) exp_ty
  = inIteExprCtxt g $ do
  g' <- checkExpType g boolTy
  mty <- newMetaTy "a" typeKi
  t' <- checkExpType t mty
  e' <- checkExpType e mty
  mty ~>? exp_ty
  return (Ite (PostTc mty) g' t' e')
--   If :: GuardedRhss p -> Exp p
tcExp (If NoPostTc grhss) exp_ty
  = inIfExprCtxt $ do
      grhss' <- tcGuardedRhss grhss exp_ty
      if_ty <- getExpected exp_ty
      return (If (PostTc if_ty) grhss')
--   Case :: Exp p -> PostTcType p -> [Alt p] -> Exp p
tcExp (Case scrut NoPostTc alts) exp_ty
  = inCaseExprCtxt scrut $ do
  (scrut',scrut_ty) <- inferExpType scrut
  (alts',case_ty) <- tcAlts alts scrut_ty exp_ty
  return (Case scrut' (PostTc case_ty) alts')
--   Tuple :: [Exp p] -> Exp p
tcExp (Tuple NoPostTc es) exp_ty = do
  mtys <- mapM (\i -> newMetaTy ("a" ++ show i) typeKi) [1..length es]
  let tup_ty = TupleTy [Dom Nothing mty Nothing | mty <- mtys]
  tup_ty ~>? exp_ty
  es' <- zipWithM checkExpType es mtys
  return (Tuple (PostTc tup_ty) es')
--   List :: [Exp p] -> Exp p
tcExp rnexp@(List NoPostTc es) exp_ty
  = inExprCtxt rnexp $ do
  mty <- newMetaTy "a" typeKi
  let list_ty = ListTy mty
  list_ty ~>? exp_ty
  es' <- mapM (flip checkExpType mty) es
  return (List (PostTc list_ty) es')
--   Paren :: Exp p -> Exp p
tcExp (Paren e) exp_ty = liftM Paren $ tcExp e exp_ty
--   LeftSection :: Exp p -> Op -> Exp p
tcExp (LeftSection arg1 op) exp_ty = do
  (op',op_ty) <- inferExpType op
  split_op_ty@([dom1,dom2],rang) <- unifyFuns 2 op_ty
--   traceDoc (text "LeftSection tcArgs") $ do
  ([arg1'],rang') <- tcArgs [arg1] (dom1 \--> (dom2 \--> rang))
--   traceDoc (text "LeftSection res_ty=" <+> pretty (dom2 \--> rang)) $ do
  (dom2 \--> rang') ~>? exp_ty
  return (LeftSection arg1' op')
--   RightSection :: Op -> Exp p -> Exp p
tcExp (RightSection op arg2) exp_ty = do
  (op',op_ty) <- inferExpType op
  split_op_ty@([dom1,dom2],rang) <- unifyFuns 2 op_ty
  ([arg2'],rang') <- tcArgs [arg2] (dom2 \--> rang)
  (dom1 \--> rang') ~>? exp_ty
  return (RightSection op' arg2')
--   EnumFromTo :: Exp p -> Exp p -> Exp p
tcExp (EnumFromTo e1 e2) exp_ty = do
  e1' <- checkExpType e1 intTy
  e2' <- checkExpType e2 intTy
  (ListTy intTy) ~>? exp_ty
  return (EnumFromTo e1' e2')
--   EnumFromThenTo :: Exp p -> Exp p -> Exp p -> Exp p
tcExp (EnumFromThenTo e1 e2 e3) exp_ty = do
  e1' <- checkExpType e1 intTy
  e2' <- checkExpType e2 intTy
  e3' <- checkExpType e3 intTy
  (ListTy intTy) ~>? exp_ty
  return (EnumFromThenTo e1' e2' e3')
--   Coerc :: SrcLoc -> Exp p -> PolyType p -> Exp p
tcExp (Coerc loc exp pty) exp_ty
  = inCoercExprCtxt loc $ do
  (pty',_) <- kcType pty
  traceDoc (text "Coerc pty'=" <+> pretty pty') $ do
  exp' <- checkSigma exp pty'
  let e' = Coerc loc exp' pty'
  e'' <- instSigma e' pty' exp_ty
  return e''
--   QP :: Quantifier -> [Pat p] -> Prop p -> Prop p
tcExp (QP qt pats prop) exp_ty
  = inQPExprCtxt qt pats $ do
  (pats',_,pats_env) <- inferPats pats
  prop' <- extendVarEnv pats_env $
             checkExpType prop boolTy
  boolTy ~>? exp_ty
  return (QP qt pats' prop')


tcApp :: Exp Rn -> [Exp Rn] -> Expected (Tau Tc) -> TcM (Exp Tc,[Exp Tc])
tcApp fun args exp_res_ty = do
  (fun',fun_ty) <- inferExpType fun
  (args',res_ty) <- tcArgs args fun_ty
  res_ty ~>? exp_res_ty
  return (fun',args')

tcArgs :: [Exp Rn] -> Tau Tc -> TcM ([Exp Tc],Range Tc)
tcArgs []         res_ty = return ([],res_ty)
tcArgs (arg:args) fun_ty = do
  split_fun_ty@(dom,_) <- unifyFun fun_ty
--   traceDoc (text "tcArgs checkExpType arg=" <+> pretty arg <+> text "dom" <+> pretty (dom2type dom)) $ do
  arg' <- checkExpType arg (dom2type dom)
  rang' <- instFunTy split_fun_ty arg'
--   traceDoc (text "tcArgs fun_ty=" <+> pretty fun_ty <+> text "arg=" <+> pretty arg <+> text "dom=" <+> pretty (dom2type dom) <+> text "rang'=" <+> pretty rang') $ do
  (args',res_ty) <- tcArgs args rang'
  return (arg':args',res_ty)

tcAlts :: [Alt Rn] -> Tau Tc -> Expected (Tau Tc) -> TcM ([Alt Tc],Tau Tc)
tcAlts alts scrut_ty (Check exp_ty) = do
  alts' <- mapM (\alt -> checkAlt alt scrut_ty exp_ty) alts
  return (alts',exp_ty)
tcAlts (alt:alts) scrut_ty (Infer ref) = do
  (alt',rhs_ty) <- inferAlt alt scrut_ty
  alts' <- mapM (\alt -> checkAlt alt scrut_ty rhs_ty) alts
  liftIO $ writeIORef ref rhs_ty
  return (alt':alts',rhs_ty)

inferAlt :: Alt Rn -> Tau Tc -> TcM (Alt Tc,Tau Tc)
inferAlt alt scrut_ty = do
  ref <- liftIO $ newIORef (error "inferAlt: empty result")
  alt' <- tcAlt alt scrut_ty (Infer ref)
  ty <- liftIO $ readIORef ref
  return (alt',ty)

checkAlt :: Alt Rn -> Tau Tc -> Tau Tc -> TcM (Alt Tc)
checkAlt alt scrut_ty ty = tcAlt alt scrut_ty (Check ty)

-- data Alt p = Alt SrcLoc (Pat p) (Rhs p)
tcAlt :: Alt Rn -> Tau Tc -> Expected (Tau Tc) -> TcM (Alt Tc)
tcAlt (Alt (Just loc) pat rhs) scrut_ty exp_ty
  = inCaseAltCtxt loc pat $ do
  (pat',pat_env) <- checkPat pat scrut_ty
  rhs' <- extendVarEnv pat_env $
            tcRhs rhs exp_ty
  return (Alt (Just loc) pat' rhs')
  

inferRhs :: Rhs Rn -> TcM (Rhs Tc,Tau Tc)
inferRhs rhs = do
  ref <- liftIO $ newIORef (error "inferRhs: empty result")
  rhs' <- tcRhs rhs (Infer ref)
  ty <- liftIO $ readIORef ref
  return (rhs',ty)

checkRhs :: Rhs Rn -> Tau Tc -> TcM (Rhs Tc)
checkRhs rhs ty = tcRhs rhs (Check ty)

-- data Rhs p = Rhs (GRhs p) (WhereBinds p)
tcRhs :: Rhs Rn -> Expected (Tau Tc) -> TcM (Rhs Tc)
tcRhs (Rhs NoPostTc grhs binds) (Check exp_ty) = do
  (binds',binds_env) <- tcBinds binds
  grhs' <- extendVarEnv binds_env $
             checkGRhs grhs exp_ty
  return (Rhs (PostTc exp_ty) grhs' binds')
tcRhs (Rhs NoPostTc grhs binds) (Infer ref) = do
  (binds',binds_env) <- tcBinds binds
  (grhs',grhs_ty) <- extendVarEnv binds_env $
                       inferGRhs grhs
  rhs_ty <- letType binds' grhs_ty
  liftIO $ writeIORef ref rhs_ty
  return (Rhs (PostTc rhs_ty) grhs' binds')

inferGRhs :: GRhs Rn -> TcM (GRhs Tc,Tau Tc)
inferGRhs grhs = do
  ref <- liftIO $ newIORef (error "inferGRhs: empty result")
  grhs' <- tcGRhs grhs (Infer ref)
  ty <- liftIO $ readIORef ref
  return (grhs',ty)

checkGRhs :: GRhs Rn -> Tau Tc -> TcM (GRhs Tc)
checkGRhs grhs ty = tcGRhs grhs (Check ty)

-- data GRhs p
-- 	 = UnGuarded (Exp p)
-- 	 | Guarded (GuardedRhss p)
tcGRhs :: GRhs Rn -> Expected (Tau Tc) -> TcM (GRhs Tc)
tcGRhs (UnGuarded e) exp_ty = liftM UnGuarded $ tcExp e exp_ty
tcGRhs (Guarded grhss) exp_ty = liftM Guarded $ tcGuardedRhss grhss exp_ty

--   GuardedRhss :: Ge p Rn => [GuardedRhs p] -> Else p -> GuardedRhss p
tcGuardedRhss :: GuardedRhss Rn -> Expected (Tau Tc) -> TcM (GuardedRhss Tc)
tcGuardedRhss (GuardedRhss grhss else_rhs) (Check exp_ty) = do
  grhss' <- mapM (flip checkGuardedRhs exp_ty) grhss
  else_rhs' <- tcElse else_rhs exp_ty
  return (GuardedRhss grhss' else_rhs')
tcGuardedRhss (GuardedRhss [] (Else loc e)) (Infer ref) = do
  (e',ty) <- inferExpType e
  liftIO $ writeIORef ref ty
  return (GuardedRhss [] (Else loc e'))
tcGuardedRhss (GuardedRhss (r:rs) else_rhs) (Infer ref) = do
  (r',ty) <- inferGuardedRhs r
  rs' <- mapM (flip checkGuardedRhs ty) rs
  else_rhs' <- tcElse else_rhs ty
  liftIO $ writeIORef ref ty
  return (GuardedRhss (r':rs') else_rhs')


inferGuardedRhs :: GuardedRhs Rn -> TcM (GuardedRhs Tc,Tau Tc)
inferGuardedRhs grhs = do
  ref <- liftIO $ newIORef (error "inferGuardedRhs: empty result")
  grhs' <- tcGuardedRhs grhs (Infer ref)
  ty <- liftIO $ readIORef ref
  return (grhs',ty)

checkGuardedRhs :: GuardedRhs Rn -> Tau Tc -> TcM (GuardedRhs Tc)
checkGuardedRhs grhs ty = tcGuardedRhs grhs (Check ty)

tcGuardedRhs :: GuardedRhs Rn -> Expected (Tau Tc) -> TcM (GuardedRhs Tc)
tcGuardedRhs (GuardedRhs loc g e) exp_ty
  = inGuardedRhsCtxt loc $ do
  g' <- checkExpType g boolTy
  e' <- tcExp e exp_ty
  return (GuardedRhs loc g' e')

tcElse :: Else Rn -> Tau Tc -> TcM (Else Tc)
tcElse NoElse       _exp_ty = return NoElse
tcElse (Else loc e) exp_ty  = liftM (Else loc) $ checkExpType e exp_ty

-- mkDomPatType :: [Pat Rn] -> [Type Tc] -> Range Tc -> TcM (Type Tc)
-- mkDomPatType pats_rn pats_tys res_ty = do
--   pats_rn

tcBndr :: Name -> Expected (Tau Tc) -> TcM (Var Tc,[(Name,Var Tc)])
tcBndr n (Check ty) = return (v,[(n,v)])
  where v = mkVar n (tau2sigma ty)
tcBndr n (Infer ref) = do
  mty <- newMetaTy "a" typeKi
  liftIO $ writeIORef ref mty
  let v = mkVar n (tau2sigma mty)
  return (v,[(n,v)])

checkPat :: Pat Rn -> Tau Tc -> TcM (Pat Tc,[(Name,Var Tc)])
checkPat pat ty = tcPat pat (Check ty)


inferPat :: Pat Rn -> TcM (Pat Tc,Tau Tc,[(Name,Var Tc)])
inferPat pat = do
  ref <- liftIO $ newIORef (error "inferPat: empty result")
  (pat',pat_env) <- tcPat pat (Infer ref)
  pat_ty <- liftIO $ readIORef ref
  return (pat',pat_ty,pat_env)

inferPats :: [Pat Rn] -> TcM ([Pat Tc],[Tau Tc],[(Name,Var Tc)])
inferPats []   = return ([],[],[])
inferPats (pat:pats) = do
  (pat',pat_ty,pat_env) <- inferPat pat
  (pats',pats_tys,pats_env) <- extendVarEnv pat_env $
                                 inferPats pats
  return (pat':pats',pat_ty:pats_tys,pat_env++pats_env)


tcPat :: Pat Rn -> Expected (Tau Tc) -> TcM (Pat Tc,[(Name,Var Tc)])
tcPat (VarPat n) exp_ty = do
  (v,n_env) <- tcBndr n exp_ty
  return (VarPat v,n_env)
tcPat (LitPat lit) exp_ty = do
  intTy ~>? exp_ty
  return (LitPat lit,[])
  -- how this works when the type is dependent ?
tcPat (InfixCONSPat NoPostTc p1 p2) exp_ty = do
  (cons_tau,[typ]) <- instantiate (sortOf ConsCon)
  traceDoc (text "InfixCONSPat" <+> text "cons_tau=" <+> pretty cons_tau) $ do
  ([p1',p2'],ps_env,res_ty) <- checkEq [p1,p2] cons_tau
  res_ty ~>? exp_ty
  return (InfixCONSPat (PostTc typ) p1' p2',ps_env)
  -- how this works when the type is dependent ?
tcPat (ConPat con NoPostTc ps) exp_ty = do
  con' <- lookupCon con
  (con_tau,typs) <- instantiate (sortOf con')
  traceDoc (text "ConPat con=" <+> pretty con <+> text "con_tau=" <+> pretty con_tau) $ do
    when (funTyArity con_tau /= length ps) $
      error "constructor's number of arguments does not match the number of patterns..."
    (ps',ps_env,res_ty) <- checkEq ps con_tau
    res_ty ~>? exp_ty
    return (ConPat con' (PostTc typs) ps',ps_env)
tcPat (TuplePat ps NoPostTc) exp_ty = do
  mtys <- mapM (\i -> newMetaTy ("a" ++ show i) typeKi) [1..length ps]
  let tup_ty = TupleTy [Dom Nothing mty Nothing | mty <- mtys]
  tup_ty ~>? exp_ty
  (ps',ps_envs) <- liftM unzip $ zipWithM (\p mty -> tcPat p (Check mty)) ps mtys
  return (TuplePat ps' (PostTc tup_ty),concat ps_envs)
tcPat (ListPat ps NoPostTc) exp_ty = do
  mty <- newMetaTy "a" typeKi
  let list_ty = ListTy mty
  list_ty ~>? exp_ty
  (ps',ps_envs) <- liftM unzip $ mapM (\p -> tcPat p (Check mty)) ps
  return (ListPat ps' (PostTc list_ty),concat ps_envs)
tcPat (ParenPat p) exp_ty = do
  (p',p_env) <- tcPat p exp_ty
  return (ParenPat p',p_env)
tcPat (WildPat wild_var) exp_ty = do
  (wild_var',wild_var_env) <- tcBndr wild_var exp_ty
  return (WildPat wild_var',wild_var_env)
tcPat (AsPat n p) exp_ty = do
  (v,n_env) <- tcBndr n exp_ty
  v_ty <- getExpected exp_ty
  (p',p_env) <- checkPat p v_ty
  return (AsPat v p',n_env ++ p_env)
tcPat (SigPat p ty) exp_ty = do
  ty' <- checkKind ty typeKi
  (p',p_env) <- tcPat p (Check ty')
  ty' ~>? exp_ty
  return (SigPat p' ty',p_env)


--  check "equation"
checkEq :: [Pat Rn] -> Tau Tc -> TcM ([Pat Tc],[(Name,Var Tc)],Tau Tc)
checkEq [] exp_ty = return ([],[],exp_ty)
checkEq (pat:pats) exp_ty  = do
  fun_ty@(dom,_) <- unifyFun exp_ty
  (pat',pat_env) <- checkPat pat (dom2type dom)
  exp_ty' <- instFunTyWithPat fun_ty pat'
  (pats',pats_env,resty) <- extendVarEnv pat_env $
                              checkEq pats exp_ty'
  return (pat':pats',pat_env++pats_env,resty)



-- * ...

-- inferSigma :: Term Rn -> Typecheck (Term Tc,Sigma Tc)
-- inferSigma e
--    = do (e',exp_ty) <- inferRho e
--         env_tys <- getEnvTypes
--         env_tvs <- getMetaTyVars env_tys
--         res_tvs <- getMetaTyVars [exp_ty]
--         let forall_tvs = res_tvs \\ env_tvs
--         (e'',e_sigmaty) <- quantify forall_tvs e' exp_ty
--         return (e'',e_sigmaty)

generalise :: Tau Tc -> TcM ([TyVar],Sigma Tc)
generalise ty = do
  traceDoc (text "generalise ty=" <> pretty ty) $ do
  env_tys <- getEnvTypes
  env_mtvs <- getMetaTyVars env_tys
  traceDoc (text "generalise ty=" <> pretty ty <+> text "env_mtvs=" <+> (sep $ map pretty $ Set.toList env_mtvs)) $ do
  ty_mtvs <- getMetaTyVars [ty]
  traceDoc (text "generalise ty=" <> pretty ty <+> text "ty_mtvs=" <+> (sep $ map pretty $ Set.toList ty_mtvs)) $ do
  let poly_mtvs = ty_mtvs Set.\\ env_mtvs
  traceDoc (text "generalise ty=" <> pretty ty <+> text "poly_mtvs=" <+> sep (map pretty $ Set.toList poly_mtvs)) $ do
  quantify (Set.toAscList poly_mtvs) ty

checkSigma :: Exp Rn -> Sigma Tc -> TcM (Exp Tc)
checkSigma exp polyty = do
  (skol_tvs,ty) <- skolemise polyty
--   traceDoc (text "checkSigma ty=" <+> pretty ty <+> text "skol_tvs=" <+> sep (map pretty skol_tvs)) $ do
  exp' <- checkExpType exp ty
    -- check ...
  env_tys <- getEnvTypes
  esc_tvs <- getFreeTyVars (polyty : env_tys)
  let bad_tvs = filter (`Set.member` esc_tvs) skol_tvs
  when (not $ null bad_tvs) $
    error "Type not polymorphic enough"
    -- reconstruction
  exp'_z <- zonkExp exp'
  let polyty_tvs = quantifiedTyVars polyty
  exp'' <- substExp [] (zip skol_tvs $ map VarTy polyty_tvs) exp'_z
  return (tyLam polyty_tvs exp'')


-- * Subsumption checking

instSigma :: Exp Tc -> Sigma Tc -> Expected (Tau Tc) -> TcM (Exp Tc)
instSigma exp s1 (Check t2) = do
  (exp',t1) <- instantiateExp exp s1
  t1 ~> t2
  return exp'
instSigma exp s1 (Infer ref)  = do
  (exp',t1) <- instantiateExp exp s1
  liftIO $ writeIORef ref t1
  return exp'


(~>?) :: Tau Tc -> Expected (Tau Tc) -> TcM ()
t1 ~>? (Check t2)  = t1 ~> t2
t1 ~>? (Infer ref) = liftIO $ writeIORef ref t1
