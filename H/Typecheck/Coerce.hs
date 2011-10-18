{-# LANGUAGE GADTs, FlexibleContexts, NamedFieldPuns #-}

module H.Typecheck.Coerce where

import H.Typecheck.TCC
import H.Typecheck.Utils

import H.Syntax
import H.Phase
import H.FreeVars
import H.Pretty
import qualified H.Prop as P
import H.Message
import H.Monad
import H.SrcLoc
import H.SrcContext
import H.Subst1

import Name
import Sorted
import Unique

import Control.Monad
import Control.Monad.RWS
import Control.Monad.Error
import Data.Char ( isLower )
import Data.List ( find, inits, nub, (\\) )
import Data.Sequence ( (|>) )
import qualified Data.Sequence as Seq
import qualified Data.Traversable as T
-- import Data.Maybe ( maybe )
-- import qualified Data.Set as Set



type CoM = H CoEnv [TCC] ()

data CoEnv = CoEnv { propCtxt :: TccPropCtxt }


coModule :: UniqSupply -> Module Ti -> IO (Either Message [TCC],UniqSupply)
coModule us (Module loc modname decls)
  = do (res,us') <- runH (coDecls decls) (SrcContext loc (text "In module" <+> ppQuot modname) False) us emptyCoEnv ()
       case res of
            Left err -> return (Left err,us')
            Right ((),(),tccs) -> return (Right tccs,us')

emptyCoEnv :: CoEnv
emptyCoEnv = CoEnv Seq.empty


  -- Bidirectional typechecking !
data Expected a = Infer
                | Check a

instance Functor Expected where
  fmap f Infer     = Infer
  fmap f (Check x) = Check $ f x


withForall :: [QVar Ti] -> CoM a -> CoM a
withForall [] = id
withForall vs = local addLamVars
  where addLamVars env@CoEnv{propCtxt} = env{propCtxt = propCtxt |> ForAll vs}

withLetIn :: [Bind Ti] -> CoM a -> CoM a
withLetIn []    = id
withLetIn binds = local addLetBinds
  where addLetBinds env@CoEnv{propCtxt} = env{propCtxt = propCtxt |> LetIn binds}

withFacts :: [Prop Ti] -> CoM a -> CoM a
withFacts []    = id
withFacts props = local addFact
  where addFact env@CoEnv{propCtxt} = env{propCtxt = propCtxt |> Facts props}

is_trivial_coercion :: Sigma Ti -> Sigma Ti -> Exp Ti -> CoM Bool
is_trivial_coercion act_ty          exp_ty _expr
  | act_ty == exp_ty = return True
is_trivial_coercion act_ty          exp_ty (Lit (IntLit n))
  | act_ty == intTy && exp_ty == natTy && n >= 0 = return True
is_trivial_coercion (PredTy _ ty _) exp_ty _expr
  | ty == (sigma2tau exp_ty) = return True
is_trivial_coercion act_ty          exp_ty expr
  | isSynTy act_ty = do
    Just act_ty' <- expandSyn act_ty
    is_trivial_coercion act_ty' exp_ty expr
is_trivial_coercion act_ty          exp_ty expr
  | isSynTy exp_ty = do
    Just exp_ty' <- expandSyn exp_ty
    is_trivial_coercion act_ty exp_ty' expr
is_trivial_coercion _act_ty        _exp_ty _expr
  = return False

(~>?) :: Sigma Ti -> Expected (Sigma Ti) -> Exp Ti -> CoM (Sigma Ti)
(~>?) act_ty Infer          _expr = return act_ty
(~>?) act_ty (Check exp_ty)  expr = do
  is_not_trivial <- liftM not $ is_trivial_coercion act_ty exp_ty expr
  when is_not_trivial $ do
    SrcContext{contextDescr} <- getContext
    tccPropCtxt <- asks propCtxt
    tell [CoercionTCC contextDescr tccPropCtxt expr act_ty exp_ty]
  return exp_ty

(->?) :: Tau Ti -> Expected (Tau Ti) -> Exp Ti -> CoM (Tau Ti)
(->?) act_ty exp_ty expr = do
  res_ty <- (tau2sigma act_ty ~>? fmap tau2sigma exp_ty) expr
  return $ sigma2tau res_ty

addCompletenessTCC :: Prop Ti -> CoM ()
addCompletenessTCC prop = do
  SrcContext{contextDescr} <- getContext
  tccPropCtxt <- asks propCtxt
  tell [CompletenessTCC contextDescr tccPropCtxt prop]

coDecls :: [Decl Ti] -> CoM ()
coDecls = mapM_ coDecl

-- data Decl p where
coDecl :: Decl Ti -> CoM ()
coDecl (TypeDecl loc tyname tvs tau) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_tau <- subst_type [] (zip tvs sko_tys) tau
  coType sko_tau
--   DataDecl ::	SrcLoc -> UTyNAME p -> TyParams p -> [ConDecl p] -> Decl p
coDecl (DataDecl loc tyname tvs constrs) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_constrs <- subst_condecls [] (zip tvs sko_tys) constrs
  mapM_ coConDecl sko_constrs
  where coConDecl (ConDecl loc name doms) = mapM_ coDom doms
coDecl (ValDecl bind) = coBind bind
coDecl (GoalDecl loc gtype gname (PostTc tvs) prop) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_prop <- subst_exp [] (zip tvs sko_tys) prop
  void $ coExp sko_prop (Check boolTy)

coBinds :: [Bind Ti] -> CoM ()
coBinds = mapM_ coBind

coBind :: Bind Ti -> CoM ()
coBind (PatBind loc pat rhs@(Rhs (PostTc rhs_ty) _ _)) = coRhs rhs
coBind (FunBind _rec fun fun_tsig (PostTc tvs) matches)
  = inFunBindCtxt (ppQuot fun) $ do
  traceDoc (text "coBind-FunBind " <+> pretty fun <+> char ':' <+> pretty fun_ty <+> text "==============") $ do
  coTypeSig fun_tsig
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  traceDoc (text "coBind-FunBind sko_tys =" <+> sep (map pretty sko_tys)) $ do
  sko_matches <- subst_matches [] (zip tvs sko_tys) matches
  fun_tau <- instSigmaType fun_ty sko_tys
  traceDoc (text "fun-tau =" <+> pretty fun_tau) $ do
  coMatches sko_matches fun_tau
--   -- WRONG: I have to use co_Equations
--   mapM_ (`coMatch` fun_tau) matches
  where fun_ty = sortOf fun

coTypeSig :: TypeSig Ti -> CoM ()
coTypeSig NoTypeSig = return ()
coTypeSig (TypeSig loc sig) = coType sig

coMatches :: [Match Ti] -> Tau Ti -> CoM ()
coMatches matches@(m:_) exp_ty = do
  qs <- matches2eqs matches
  coEquations doms qs
  where arity = matchArity m
        (doms,_) = splitFunTyN arity exp_ty

-- -- WRONG: Use coEquations
-- coMatch :: Match Ti -> Tau Ti -> CoM ()
-- coMatch (Match loc pats rhs) exp_ty = do
--   void $ coEq pats exp_ty
--   withForall pats $
--     coRhs rhs

coExp :: Exp Ti -> Expected (Sigma Ti) -> CoM (Sigma Ti)
coExp e@(Var x) exp_ty = (varType x ~>? exp_ty) e
coExp e@(Con con) exp_ty = (sortOf con ~>? exp_ty) e
coExp e@(Op op) exp_ty = (sortOf op ~>? exp_ty) e
coExp e@(Lit _) exp_ty = (intTy ~>? exp_ty) e
coExp e@(PrefixApp op arg) exp_ty
  = coApp e op [arg] exp_ty
coExp and_exp@(InfixApp e1 (Op (BoolOp AndB)) e2) exp_ty
  = inExprCtxt and_exp $ do
      void $ coExp e1 (Check boolTy)
      withFacts [e1] $
        void $ coExp e2 (Check boolTy)
      (boolTy ~>? exp_ty) and_exp
coExp or_exp@(InfixApp e1 (Op (BoolOp OrB)) e2) exp_ty
  = inExprCtxt or_exp $ do
      void $ coExp e1 (Check boolTy)
      withFacts [P.notP e1] $
        void $ coExp e2 (Check boolTy)
      (boolTy ~>? exp_ty) or_exp
coExp imp_exp@(InfixApp e1 (Op (BoolOp ImpB)) e2) exp_ty
  = inExprCtxt imp_exp $ do
      void $ coExp e1 (Check boolTy)
      withFacts [e1] $
        void $ coExp e2 (Check boolTy)
      (boolTy ~>? exp_ty) imp_exp
coExp expr@(InfixApp e1 op e2) exp_ty
  = coApp expr op [e1,e2] exp_ty
coExp e@(App f t) exp_ty
  = coApp e f [t] exp_ty
coExp tyapp@(TyApp e typs) exp_ty = do
  e_ty <- coExp e Infer
  e_tau <- instSigmaType e_ty typs
  (tau2sigma e_tau ~>? exp_ty) tyapp
coExp (Lam (Just loc) pats rhs) (Check exp_ty) = do
  q <- mkEq loc pats rhs
  coEquations doms [q]
  return exp_ty
  where arity = length pats
        (doms,_) = splitFunTyN arity (sigma2tau exp_ty)
coExp (Lam (Just loc) pats rhs) Infer = do
  pats_tys <- tcPatsTypes pats
  let doms = zipWith patternDom pats pats_tys
      lam_ty = funTy doms rhs_ty
  q <- mkEq loc pats rhs
  coEquations doms [q]
  return lam_ty
  where rhs_ty = tcRhsType rhs
coExp (Let binds body) exp_ty = do
  coBinds binds
  withLetIn binds $
    coExp body exp_ty
coExp (TyLam tvs e) (Check exp_ty) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  e' <- subst_exp [] (zip tvs sko_tys) e
  exp_ty' <- instSigmaType exp_ty sko_tys
  void $ coExp e' (Check $ tau2sigma exp_ty')
  return exp_ty
coExp (TyLam tvs e) Infer = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  e' <- subst_exp [] (zip tvs sko_tys) e
  sko_e_ty <- coExp e' Infer
  e_ty <- subst_type [] (zip sko_tvs $ map VarTy tvs) sko_e_ty
  return (ForallTy tvs $ sigma2tau e_ty)
coExp e@(Ite (PostTc ite_ty) g e1 e2) exp_ty = do
  coExp g (Check boolTy)
  withFacts [g] $
    coExp e1 (Check $ tau2sigma ite_ty)
  withFacts [P.notP g] $
    coExp e2 (Check $ tau2sigma ite_ty)
  (tau2sigma ite_ty ~>? exp_ty) e
coExp e@(If (PostTc if_ty) grhss) exp_ty = do
  coGuardedRhss grhss if_ty
  (tau2sigma if_ty ~>? exp_ty) e
  -- Remember that case_ty is only a 'cached' value
  -- and it matches with the rhs_ty of all alternatives
coExp (Case scrut (PostTc case_ty) alts) exp_ty = do
  scrut_ty <- coExp scrut Infer
  coAlts alts (sigma2tau scrut_ty)
--   -- WRONG: I have to use co_Equations
--   mapM_ (`coAlt` (sigma2tau scrut_ty)) alts
  return $ tau2sigma case_ty
coExp e@(Tuple (PostTc tup_ty) es) exp_ty = do
  let TupleTy ds = tup_ty
  coTuple es ds
  (tau2sigma tup_ty ~>? exp_ty) e
coExp e@(List (PostTc list_ty) es) exp_ty = do
  let ListTy elem_ty = mu_0 list_ty
  zipWithM_ coExp es (repeat $ Check $ tau2sigma elem_ty)
  (tau2sigma list_ty ~>? exp_ty) e
coExp (Paren e) exp_ty = coExp e exp_ty
coExp e@(LeftSection e1 op) exp_ty
  = coApp e op [e1] exp_ty
coExp e@(RightSection op e2) exp_ty = do
  op_ty <- coExp op Infer
  let FunTy d1 (FunTy d2 res_ty) = op_ty
  coExp e2 (Check $ dom2type d2)
  res_ty' <- instFunTy (d2,res_ty) e2
  ((d1 \--> res_ty') ~>? exp_ty) e
coExp e@(EnumFromTo e1 e2) exp_ty = do
  void $ coExp e1 (Check intTy)
  void $ coExp e2 (Check intTy)
  (ListTy intTy ~>? exp_ty) e
coExp e@(EnumFromThenTo e1 e2 e3) exp_ty = do
  void $ coExp e1 (Check intTy)
  void $ coExp e2 (Check intTy)
  void $ coExp e3 (Check intTy)
  (ListTy intTy ~>? exp_ty) e
coExp (Coerc loc e ann_ty) exp_ty = do
  coExp e (Check ann_ty)
  (ann_ty ~>? exp_ty) e
coExp e@(QP qt avars prop) exp_ty
  = inQPExprCtxt qt avars $ do
    withForall avars $
      coExp prop (Check boolTy)
    (boolTy ~>? exp_ty) e
coExp e _exp_ty = traceDoc (text "coExp-impossible?" <+> pretty e) $ undefined

coApp :: Exp Ti -> Exp Ti -> [Exp Ti] -> Expected (Sigma Ti) -> CoM (Sigma Ti)
coApp expr fun args exp_res_ty = do
  fun_sig <- coExp fun Infer
  res_ty <- coArgs args (sigma2tau fun_sig)
  (tau2sigma res_ty ~>? exp_res_ty) expr

coArgs :: [Exp Ti] -> Tau Ti -> CoM (Tau Ti)
coArgs []         res_ty = return res_ty
coArgs (arg:args) fun_ty = do
  coExp arg (Check $ dom2type dom)
  rang' <- instFunTy (dom,rang) arg
  res_ty <- coArgs args rang'
  return res_ty
  where FunTy dom rang = fun_ty


coTuple :: [Exp Ti] -> [Dom Ti] -> CoM ()
coTuple []     []     = return ()
coTuple (e:es) (d:ds) = do
  coExp e (Check $ dom2type d)
  ds_e <- instDoms e d ds
  coTuple es ds_e

coAlts :: [Alt Ti] -> Tau Ti -> CoM ()
coAlts alts scrut_ty = do
  qs <- mapM alt2eq alts
  coEquations [type2dom scrut_ty] qs

-- WRONG
-- coAlt :: Alt Ti -> Tau Ti -> CoM ()
-- coAlt (Alt loc pat rhs) scrut_ty = do
--   void $ coPat pat (Check scrut_ty)
--   coRhs rhs

-- data Rhs p = Rhs (GRhs p) (WhereBinds p)
coRhs :: Rhs Ti -> CoM ()
coRhs rhs@(Rhs (PostTc rhs_ty) grhs binds) = do
  coBinds binds
  withLetIn binds $
    coGRhs grhs rhs_ty

coGRhs :: GRhs Ti -> Tau Ti -> CoM ()
coGRhs (UnGuarded expr) exp_ty = void $ coExp expr (Check $ tau2sigma exp_ty)
coGRhs (Guarded grhss)  exp_ty = coGuardedRhss grhss exp_ty

coGuardedRhss :: GuardedRhss Ti -> Tau Ti -> CoM ()
coGuardedRhss (GuardedRhss grhss elserhs) exp_ty = do
  let not_guards = map (P.notP . get_guard) grhss
  zipWithM_ (\hyps grhs ->
              withFacts hyps $ coGuardedRhs grhs exp_ty
            )
      (inits not_guards)
      grhss
  withFacts not_guards $ coElse elserhs exp_ty
  grhsCompletenessTCC grhss elserhs
  where get_guard (GuardedRhs _ guard _) = guard

grhsCompletenessTCC :: [GuardedRhs Ti] -> Else Ti -> CoM ()
grhsCompletenessTCC _     (Else _ _) = return ()
grhsCompletenessTCC grhss NoElse     = addCompletenessTCC (P.disj $ map get_guard grhss)
  where get_guard (GuardedRhs _ guard _) = guard

coGuardedRhs :: GuardedRhs Ti -> Tau Ti -> CoM ()
coGuardedRhs (GuardedRhs loc guard expr) exp_ty = do
  void $ coExp guard (Check boolTy)
  void $ withFacts [guard] $ coExp expr (Check $ tau2sigma exp_ty)

coElse :: Else Ti -> Tau Ti -> CoM ()
coElse NoElse          _exp_ty = return ()
coElse (Else loc expr)  exp_ty = void $ coExp expr (Check $ tau2sigma exp_ty)


-- -- I think it is WRONG because a pat may have type annotations depending on
-- -- previous pats...
-- coPats :: [Pat Ti] -> CoM [Tau Ti]
-- coPats = mapM (flip coPat Infer)

-- coPat = undefined
-- coPat :: Pat Ti -> Expected (Tau Ti) -> CoM (Tau Ti)
-- coPat (VarPat x) exp_ty = (sigma2tau (varType x) ->? exp_ty) (Var x)
-- coPat (LitPat lit) exp_ty = (intTy ->? exp_ty) (Lit lit)
-- coPat cons_pat@(InfixCONSPat (PostTc typ) p1 p2) exp_ty = do
--   cons_tau <- instSigmaType cons_ty [typ]
--   res_ty <- coEq [p1,p2] cons_tau
--   (res_ty ->? exp_ty) (pat2exp cons_pat)
--   where cons_ty = sortOf ConsCon
-- coPat con_pat@(ConPat con (PostTc typs) ps) exp_ty = do
--   con_tau <- instSigmaType con_ty typs
--   res_ty <- coEq ps con_tau
--   (res_ty ->? exp_ty) (pat2exp con_pat)
--   where con_ty = sortOf con
-- coPat tup_pat@(TuplePat ps (PostTc tup_ty)) exp_ty = do
--   coTuplePat ps ds
--   (tup_ty ->? exp_ty) (pat2exp tup_pat)
--   where TupleTy ds = mu_0 tup_ty
-- coPat list_pat@(ListPat ps (PostTc list_ty)) exp_ty = do
--   zipWithM_ coPat ps (repeat $ Check elem_ty)
--   (list_ty ->? exp_ty) (pat2exp list_pat)
--   where ListTy elem_ty = mu_0 list_ty
-- coPat (ParenPat p) exp_ty = coPat p exp_ty
-- coPat (WildPat wild_var) exp_ty
--   = (sigma2tau (varType wild_var) ->? exp_ty) (Var wild_var)
-- coPat (AsPat x pat) exp_ty = do
--   void $ coPat pat exp_ty
--   (sigma2tau (varType x) ->? exp_ty) (Var x)
-- -- coPat (SigPat pat tau) exp_ty = do
-- --   coType tau
-- --   void $ coPat pat (Check tau)
-- --   (tau ->? exp_ty) (pat2exp pat)

-- coTuplePat :: [Pat Ti] -> [Dom Ti] -> CoM ()
-- coTuplePat []     []     = return ()
-- coTuplePat (p:ps) (d:ds) = do
--   void $ coPat p (Check $ dom2type d)
--     -- FIX Should I generalise patRangeSubst and define instDomsWithPat ?
--   ds_p <- instDoms (pat2exp p) d ds
--   coTuplePat ps ds_p


-- -- I think it is WRONG because a pat may have type annotations depending on
-- -- previous pats, and because when I call instFunWithPat and I get rang', this
-- -- rang' may depend on pat variables...
-- coEq :: [Pat Ti] -> Tau Ti -> CoM (Tau Ti)
-- coEq []         res_ty = return res_ty
-- coEq (pat:pats) fun_ty = do
--   let FunTy dom rang = mu_0 fun_ty
--   void $ coPat pat (Check $ dom2type dom)
--   rang' <- instFunTyWithPat (dom,rang) pat
--   coEq pats rang'


-- * Equations

type SimplePat = Pat

data Equation
  = E {
    eqLoc  :: SrcLoc
  , eqPats :: [SimplePat Ti]
  , eqRhs  :: Rhs Ti
  }

-- eqArity :: Equation -> Int
-- eqArity (E _ pats _) = length pats

mkEq :: SrcLoc -> [Pat Ti] -> LamRHS Ti -> CoM Equation
mkEq loc pats rhs = do
  rhs' <- subst_rhs var_s [] rhs
  return $ E loc pats' rhs'
  where (pats',var_s) = simplifyPats pats

alt2eq :: Alt Ti -> CoM Equation
alt2eq (Alt (Just loc) pat rhs) = mkEq loc [pat] rhs

match2eq :: Match Ti -> CoM Equation
match2eq (Match (Just loc) pats rhs) = mkEq loc pats rhs

matches2eqs :: [Match Ti] -> CoM [Equation]
matches2eqs = mapM match2eq

isVar :: Equation -> Bool
isVar (E _ (VarPat _:_) _) = True
isVar _other               = False

isLit :: Equation -> Bool
isLit (E _ (LitPat _:_) _) = True
isLit _other               = False

getLit :: Equation -> Integer
getLit (E _ (LitPat (IntLit n):_) _) = n
getLit _other                        = undefined -- bug

isTuple :: Equation -> Bool
isTuple (E _ (TuplePat _ _:_) _) = True
isTuple _other                   = False

isCon :: Equation -> Bool
isCon (E _ (ConPat _ _ _:_) _) = True
isCon _other                   = False

getCon :: Equation -> TcCon Ti
getCon (E _ (ConPat con _ _:_) _) = con
getCon _other                     = undefined -- bug

simplifyPats :: [Pat Ti] -> ([SimplePat Ti],[(Var Ti,Exp Ti)])
simplifyPats pats = let (pats',pats_ss) = unzip $ map go pats
                      in (pats',concat pats_ss)
  where go :: Pat Ti -> (SimplePat Ti,[(Var Ti,Exp Ti)])
        go p@(VarPat _) = (p,[])
        go p@(LitPat _) = (p,[])
        go (InfixCONSPat (PostTc typ) p1 p2)
          = (mkCONSPat typ p1' p2',bs)
          where ([p1',p2'],bs) = simplifyPats [p1,p2]
        go (ConPat con ptctyps ps) = (ConPat con ptctyps ps',bs)
          where (ps',bs) = simplifyPats ps
        go (TuplePat ps ptcty) = (TuplePat ps' ptcty,bs)
          where (ps',bs) = simplifyPats ps
        go (ListPat ps (PostTc list_ty)) =
            (foldr (mkCONSPat elem_ty) (mkNILPat elem_ty) ps',bs)
          where ListTy elem_ty = mu_0 list_ty
                (ps',bs) = simplifyPats ps
          -- NB: ParenPat is just convenient for pretty-printing
          -- when we have InfixCONSPat's
        go (ParenPat p) = go p
        go (WildPat wild_var) = (VarPat wild_var,[])
          -- NB: `p' cannot depend on `v' nor vice-versa
        go (AsPat v p) = (p',(v,pat2exp p):bs)
          where (p',bs) = go p
--         go (SigPat p _ty) = go p


coType :: Type c Ti -> CoM ()
coType (VarTy _) = return ()
coType (ConTy _tc tys) = mapM_ coType tys
coType (PredTy pat tau mb_prop) = do
--   coPat pat (Check tau)
  coType tau
  void $ T.mapM (`coExp` (Check boolTy)) mb_prop
coType (FunTy dom rang) = do
  coDom dom
  coType rang
coType (ListTy elem_ty) = coType elem_ty
coType (TupleTy ds) = mapM_ coDom ds
coType (ForallTy tvs tau) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_tau <- subst_type [] (zip tvs sko_tys) tau
  coType sko_tau

coDom :: Dom Ti -> CoM ()
coDom (Dom mb_pat tau mb_prop) = do
--   void $ T.mapM (`coPat` (Check tau)) mb_pat
  coType tau
  void $ T.mapM (`coExp` (Check boolTy)) mb_prop

getEqPat :: Int -> Equation -> SimplePat Ti
getEqPat n (E _ pats _) = pats !! n

coEquations :: [Dom Ti] -> [Equation] -> CoM ()
coEquations ds qs = do
  xs <- pick_variables
  let qxs = map mkQVar xs
  withForall qxs $
    co_Equations xs qs
  where pick_variables = go 0 [] ds
          where go _i vs_rev []     = return $ reverse vs_rev
                go  i vs_rev (d:ds) = do
                  let n = case getNameForPats (map (getEqPat i) qs) of
                              Nothing -> "x" ++ show i
                              Just n1 -> n1
                  v <- newVar n (dom2type d)
                  ds' <- instDoms (Var v) d ds
                  go (i+1) (v:vs_rev) ds'
--   where get_var :: Int -> [SimplePat Ti] -> CoM (Var Ti)
--         get_var i ps = case getNameForPats ps of
--                            Nothing -> undefined
--                            Just n  -> undefined
--         get_eqs_pats :: [Equation] -> [[SimplePat Ti]]
--         get_eqs_pats = go []
--           where go pss    (E _ [] _:_)    = reverse pss
--                 go pss qs@(E _ (p:_) _:_) = go (ps':pss) qs'
--                   where ps' = map (head . eqPats) qs
--                         qs' = map (\q@E{eqPats} -> q{eqPats = tail eqPats}) qs

co_Equations :: [Var Ti] -> [Equation] -> CoM ()
co_Equations [] []  = error "coEquations undefined 1" -- FALSE must hold
co_Equations [] [E _ [] rhs] = coRhs rhs
co_Equations [] (_:_) = error "Non-uniform definition/pattern"
co_Equations xs []    = error "coEquations undefined 2" -- FALSE must hold
co_Equations (x:xs) qs
  | all isVar   qs = matchVar x xs qs
  | all isLit   qs = matchLit x xs qs
  | all isTuple qs = matchTuple x xs qs
  | all isCon   qs = matchCon x xs qs
  | otherwise = error "Non-uniform definition/pattern"
-- match sup [] [] def = def
-- match sup [] [q] def = snd q
-- match sup [] (_:_) def = error "Non-uniform: empty-rule failed"
-- match sup us [] def = def


subst_eq :: [(Var Ti,Exp Ti)] -> Equation -> CoM Equation
subst_eq var_s (E loc pats rhs) = do
  (pats',s') <- substPats s pats
  rhs' <- substRhs s' rhs
  return (E loc pats' rhs')
  where s = mkSubst1_FV var_s []

getNameForPats :: [SimplePat Ti] -> Maybe String
getNameForPats pats = do
  VarPat var <- find is_ok_varpat pats
  return $ clean_str var
  where clean_str = dropWhile (== '_') . occString . occNameOf
        is_ok_varpat (VarPat x) = isLower $ head $ clean_str x
        is_ok_varpat _other     = False


matchVar :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchVar x xs qs = do
  qs' <- sequence [subst_eq [(y,Var x)] q'
                  | E loc (VarPat y:ps) rhs <- qs
                  , let q' = E loc ps rhs
                  ]
  co_Equations xs qs'


matchLit :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchLit x xs qs = do
  addCompletenessTCC (P.oneOfInts (Var x) lits)
  sequence_ [ matchLitClause x lit xs (chooseLit lit qs) | lit <- lits ]
  where lits = nub $ map getLit qs

chooseLit :: Integer -> [Equation] -> [Equation]
chooseLit lit qs = [q | q <- qs, getLit q == lit]

matchLitClause :: Var Ti -> Integer -> [Var Ti] -> [Equation] -> CoM ()
matchLitClause x lit xs qs
  = withFacts [Var x .==. mkInt lit] $
      co_Equations xs [ E loc ps rhs | E loc (LitPat _:ps) rhs <- qs]

matchTuple :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchTuple x xs [E loc (p@(TuplePat ps1 _):ps) rhs]
  | all isVarPat ps1 =
      withForall qxs' $ withFacts [Var x .==. pat2exp p] $
        co_Equations (xs'++xs) [E loc (ps1++ps) rhs]
  where xs' = [ x1 | VarPat x1 <- ps1]
        qxs' = map mkQVar xs'
matchTuple x xs qs = do
  let E _ (TuplePat _ (PostTc tup_ty):_) _ = head qs
      TupleTy ds = mu_0 tup_ty
  (tup_exp,xs') <- instTupleWithVars ds
  let qxs' = map mkQVar xs'
  withForall qxs' $ withFacts [Var x .==. tup_exp] $
    co_Equations (xs'++xs) [E  loc (ps1++ps) rhs | E loc (p@(TuplePat ps1 _):ps) rhs <- qs]

matchCon :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchCon x xs qs = do
  addConCompletenessTCC
  sequence_ [ matchClause x c xs (choose c qs) | c <- cs ]
  where cs = nub $ map getCon qs
        ty_con = tcConTy $ getCon $ head qs
        all_cs = [ TcCon c ty_con | c <- tyConCons ty_con ]
        uncovered_cs = all_cs \\ cs
        typs = let E _ (ConPat _ (PostTc con_typs) _:_) _ = head qs in con_typs
        is_not_con con = do
          (e,ys) <- instWithVars (sortOf con) typs (Con con)
          let qys = map mkQVar ys
          return $ P.mkForall qys (Var x ./=. e)
        addConCompletenessTCC
         | null uncovered_cs = return ()
         | otherwise = do
            no_uncover <- liftM P.conj $ mapM is_not_con uncovered_cs
            addCompletenessTCC no_uncover
          

matchClause :: Var Ti -> TcCon Ti -> [Var Ti] -> [Equation] -> CoM ()
matchClause x con xs [E loc (p@(ConPat _ _ ps1):ps) rhs]
  | all isVarPat ps1 =
      withForall qxs' $ withFacts [Var x .==. pat2exp p] $
        co_Equations (xs'++xs) [E loc (ps1++ps) rhs]
  where xs' = [ x1 | VarPat x1 <- ps1]
        qxs' = map mkQVar xs'
matchClause x con xs qs = do
  let E _ (ConPat _ (PostTc typs) _:_) _ = head qs
  (p_exp,xs') <- instWithVars (sortOf con) typs (Con con)
  let qxs' = map mkQVar xs'
  withForall qxs' $ withFacts [Var x .==. p_exp] $
    co_Equations (xs'++xs) [E  loc (ps1++ps) rhs | E loc (p@(ConPat _ _ ps1):ps) rhs <- qs]

choose :: TcCon Ti -> [Equation] -> [Equation]
choose c qs = [q | q <- qs, getCon q == c]
