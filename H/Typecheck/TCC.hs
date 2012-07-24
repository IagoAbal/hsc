
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}

module H.Typecheck.TCC where

import H.Syntax
import qualified H.Prop as P
import H.Message
import H.Monad
import H.SrcLoc
import H.SrcContext
import H.Typecheck.TCC.Coerce ( coerce )
import H.Typecheck.Utils

import Name
import Sorted
import Pretty

import Control.Monad
import Control.Monad.RWS
import Control.Monad.Error
import Data.Char ( isLower )
import Data.Foldable ( toList )
import Data.List ( find, inits, nub, (\\) )
import qualified Data.Set as Set
import Data.Sequence ( Seq, (|>) )
import qualified Data.Sequence as Seq
import qualified Data.Traversable as T

#include "bug.h"


data TccHypoThing = ForAll [QVar Ti]
                  | LetIn [Bind Ti]
                  | Facts [Prop Ti]

instance Pretty TccHypoThing where
  pretty (ForAll qvs)
    = myFsep $ text "forall" : map pretty qvs
  pretty (LetIn binds)
    = text "let" <+> ppBody letIndent (map pretty binds)
  pretty (Facts props)
    = pretty $ P.conj props
    
type TccPropCtxt = Seq TccHypoThing

data TCC
  = CoercionTCC {
      tccSrcCtxt  :: !Message
    , tccPropCtxt :: TccPropCtxt
    , tccExpr     :: Exp Ti
    , tccActType  :: Sigma Ti
    , tccExpType  :: Sigma Ti
    , tccProp     :: Prop Ti
    }
  | CompletenessTCC {
      tccSrcCtxt  :: !Message
    , tccPropCtxt :: TccPropCtxt
    , tccProp     :: Prop Ti
    }

instance Pretty TCC where
  pretty (CoercionTCC srcCtxt propCtxt expr act_ty exp_ty prop)
    = brackets srcCtxt
    $$ (vcat $ map pretty $ toList propCtxt)
    $$ text "|------------------------------------------------------ (COERCION)"
    $$ pretty act_ty
    $$ text "~~" <+> pretty expr <+> text "~~>"
    $$ pretty exp_ty
    $$ (char '<' <+> pretty prop <+> char '>')
  pretty (CompletenessTCC srcCtxt propCtxt prop)
    = brackets srcCtxt
    $$ (vcat $ map pretty $ toList propCtxt)
    $$ text "|------------------------------------------------------ (COMPLETENESS)"
    $$ pretty prop


type CoM = H CoEnv ModTCCs ()

data CoEnv = CoEnv { propCtxt :: TccPropCtxt }

type ModTCCs = [TCC]

coModule :: Module Ti -> CoM ModTCCs
coModule (Module loc modname decls)
  = liftM snd $ listen $
      inContextAt loc (text "In module" <+> ppQuot modname) $
        coDecls decls

emptyCoEnv :: CoEnv
emptyCoEnv = CoEnv Seq.empty

emptyCoST :: ()
emptyCoST = ()

resetST :: CoM ()
resetST = modify (const emptyCoST)


  -- Bidirectional typechecking !
data Expected a = Infer
                | Check a

instance Functor Expected where
  fmap _f Infer     = Infer
  fmap  f (Check x) = Check $ f x


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
  | ty == (type2tau exp_ty) = return True
is_trivial_coercion (PredTy (VarPat _) ty1 Nothing) exp_ty expr
  = is_trivial_coercion (tau2sigma ty1) exp_ty expr
is_trivial_coercion act_ty (PredTy (VarPat _) ty2 Nothing) expr
  = is_trivial_coercion act_ty (tau2sigma ty2) expr
is_trivial_coercion act_ty          exp_ty expr
  | isSynTy act_ty = is_trivial_coercion (expandSyn act_ty) exp_ty expr
is_trivial_coercion act_ty          exp_ty expr
  | isSynTy exp_ty = is_trivial_coercion act_ty (expandSyn exp_ty) expr
is_trivial_coercion _act_ty        _exp_ty _expr
  = return False

-- getNextTCCId :: CoM Int
-- getNextTCCId = do
--   c <- gets tccCount
--   modify (\st -> st{tccCount = c+1})
--   return c

addTCCToList :: TCC -> CoM ()
addTCCToList tcc = tell [tcc]


(~>?) :: Sigma Ti -> Expected (Sigma Ti) -> Exp Ti -> CoM (Sigma Ti)
(~>?) act_ty Infer          _expr = return act_ty
(~>?) act_ty (Check exp_ty)  expr = do
  is_not_trivial <- liftM not $ is_trivial_coercion act_ty exp_ty expr
  when is_not_trivial $ do
--     traceDoc (text "~>? =============" ) $ do
--     traceDoc (text "act_ty =" <+> pretty act_ty) $ do
--     traceDoc (text "exp_ty =" <+> pretty exp_ty) $ do
--     traceDoc (text "expr =" <+> pretty expr) $ do
--     traceDoc (text "=================" ) $ do
    _POs <- coerce expr act_ty exp_ty
    let prop = P.conj _POs
      -- THE "True" PART COULD BE DONE IN is_trivial_coercion with "matchable*"
    case P.bool prop of
        Just True -> return ()
        Just False -> error "coercion does not hold"
        Nothing -> do
          SrcContext{contextDescr} <- getContext
          tccPropCtxt <- asks propCtxt
--           tccId <- getNextTCCId
          addTCCToList $
            CoercionTCC contextDescr tccPropCtxt expr act_ty exp_ty prop
  return exp_ty

(->?) :: Tau Ti -> Expected (Tau Ti) -> Exp Ti -> CoM (Tau Ti)
(->?) act_ty exp_ty expr = do
  res_ty <- (tau2sigma act_ty ~>? fmap tau2sigma exp_ty) expr
  return $ type2tau res_ty

addCompletenessTCC :: Prop Ti -> CoM ()
addCompletenessTCC prop = do
  SrcContext{contextDescr} <- getContext
  tccPropCtxt <- asks propCtxt
--   tccId <- getNextTCCId
  addTCCToList $ CompletenessTCC contextDescr tccPropCtxt prop

coDecls :: [Decl Ti] -> CoM ()
coDecls = mapM_ coDecl

coDecl :: Decl Ti -> CoM ()
coDecl (TypeDecl loc ty_name tvs tau)
  = inTypeDeclCtxt loc (ppQuot ty_name) $ do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_tau <- subst_type [] (zip tvs sko_tys) tau
  coType sko_tau
coDecl (DataDecl loc ty_name tvs constrs)
  = inDataDeclCtxt loc (ppQuot ty_name) $ do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_constrs <- subst_condecls [] (zip tvs sko_tys) constrs
  mapM_ coConDecl sko_constrs
  where coConDecl (ConDecl loc1 con_name doms)
          = inConDeclCtxt loc1 (ppQuot con_name) $ coDoms doms
coDecl (ValDecl bind) = coBind bind
coDecl (GoalDecl loc gtype g_name tvs prop)
  = inGoalDeclCtxt loc gtype (ppQuot g_name) $ do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_prop <- subst_exp [] (zip tvs sko_tys) prop
  void $ coExp sko_prop (Check boolTy)

coBinds :: [Bind Ti] -> CoM ()
coBinds = mapM_ coBind

coBind :: Bind Ti -> CoM ()
coBind (PatBind (Just loc) pat rhs@(Rhs rhs_ty _ _))
  = inPatBindCtxt loc (ppQuot pat) $ do
  coRhs rhs
  (x,rhs_ctxt) <- getCaseLikeCtxt (rhs2exp rhs) (tau2sigma rhs_ty) [pat]
  rhs_ctxt $
    co_Equations [x] [patbin2eq loc pat]
coBind (FunBind _rec fun fun_tsig tvs matches)
  = inFunBindCtxt (ppQuot fun) $ do
--   traceDoc (text "coBind-FunBind " <+> pretty fun <+> char ':' <+> pretty fun_ty <+> text "==============") $ do
  coTypeSig fun_tsig
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
--   traceDoc (text "coBind-FunBind sko_tys =" <+> sep (map pretty sko_tys)) $ do
  sko_matches <- subst_matches [] (zip tvs sko_tys) matches
  fun_tau <- instSigmaType fun_ty sko_tys
--   traceDoc (text "fun-tau =" <+> pretty fun_tau) $ do
  coMatches sko_matches fun_tau
  where fun_ty = sortOf fun
coBind _other = impossible

coTypeSig :: TypeSig Ti -> CoM ()
coTypeSig NoTypeSig = return ()
coTypeSig (TypeSig loc sig)
  = inContextAt loc (text "In type signature") $ coType sig

-- TODO: Should I eta-expand matches in order to introduce all variables
-- into scope? Some of these variables may have subset types concerning
-- previous ones... otherwise the property which is generated may not be
-- valid.
coMatches :: [Match Ti] -> Tau Ti -> CoM ()
coMatches matches@(m:_) exp_ty = do
  qs <- matches2eqs matches
  coEquations doms qs
  where arity = matchArity m
        (doms,_) = splitFunTy arity exp_ty
coMatches [] _exp_ty = impossible

getCaseLikeCtxt :: Exp Ti -> Sigma Ti -> [Pat Ti] -> CoM (Var Ti,CoM a -> CoM a)
getCaseLikeCtxt (Var x) _ty _pats = return (x,id)
getCaseLikeCtxt scrut    ty  pats = do
  x <- newVarId n ty
  return (x, withForall [toQVar x] . withFacts [Var x ==* scrut])
  where n = case getNameForPats pats of
                Nothing -> "x"
                Just n1 -> n1

coExp :: Exp Ti -> Expected (Sigma Ti) -> CoM (Sigma Ti)
coExp e@(Var x) exp_ty = (varType x ~>? exp_ty) e
coExp e@(Par x) exp_ty = (varType x ~>? exp_ty) e
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
coExp (Lam (Just loc) pats rhs) (Check exp_ty)
  = inLambdaAbsCtxt loc pats $ do
  q <- mkEq loc pats rhs
  coEquations doms [q]
  return exp_ty
  where arity = length pats
        (doms,_) = splitFunTy arity (type2tau exp_ty)
coExp (Lam (Just loc) pats rhs) Infer
  = inLambdaAbsCtxt loc pats $ do
  pats_tys <- tcPatsTypes pats
  let doms = zipWith mkPatDom pats pats_tys
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
  return (ForallTy tvs $ type2tau e_ty)
coExp e@(Ite ite_ty g e1 e2) exp_ty
  = inIteExprCtxt g $ do
  void $ coExp g (Check boolTy)
  withFacts [g] $
    void $ coExp e1 (Check $ tau2sigma ite_ty)
  withFacts [P.notP g] $
    void $ coExp e2 (Check $ tau2sigma ite_ty)
  (tau2sigma ite_ty ~>? exp_ty) e
coExp e@(If if_ty grhss) exp_ty
  = inIfExprCtxt $ do
  coGuardedRhss grhss if_ty
  (tau2sigma if_ty ~>? exp_ty) e
  -- Remember that case_ty is only a 'cached' value
  -- and it matches with the rhs_ty of all alternatives
coExp (Case case_ty scrut alts) _exp_ty
  = inCaseExprCtxt scrut $ do
  scrut_ty <- coExp scrut Infer
  (x,scrut_ctxt) <- getCaseLikeCtxt scrut scrut_ty [ pat | Alt _ pat _ <- alts ]
  scrut_ctxt $
    coAlts x alts
  return $ tau2sigma case_ty
coExp e@(Tuple tup_ty es) exp_ty = do
  let TupleTy ds = tup_ty
  coTuple es ds
  (tau2sigma tup_ty ~>? exp_ty) e
coExp e@(List list_ty es) exp_ty = do
  let ListTy elem_ty = mu_0 list_ty
  zipWithM_ coExp es (repeat $ Check $ tau2sigma elem_ty)
  (tau2sigma list_ty ~>? exp_ty) e
coExp (Paren e) exp_ty = coExp e exp_ty
coExp e@(LeftSection e1 op) exp_ty
  = coApp e op [e1] exp_ty
coExp e@(RightSection op e2) exp_ty = do
  op_ty <- coExp op Infer
  let FunTy d1 (FunTy d2 res_ty) = op_ty
  void $ coExp e2 (Check $ dom2type d2)
  res_ty' <- instFunTy (d2,res_ty) e2
  ((d1 @--> res_ty') ~>? exp_ty) e
coExp e@(EnumFromTo e1 e2) exp_ty = do
  void $ coExp e1 (Check intTy)
  void $ coExp e2 (Check intTy)
  (ListTy intTy ~>? exp_ty) e
coExp e@(EnumFromThenTo e1 e2 e3) exp_ty = do
  void $ coExp e1 (Check intTy)
  void $ coExp e2 (Check intTy)
  void $ coExp e3 (Check intTy)
  (ListTy intTy ~>? exp_ty) e
coExp (Coerc loc e ann_ty) exp_ty
  = inCoercExprCtxt loc $ do
  void $ coExp e (Check ann_ty)
  (ann_ty ~>? exp_ty) e
coExp e@(QP qt xs prop) exp_ty
  = inQPExprCtxt qt xs $ do
    withForall xs $
      void $ coExp prop (Check boolTy)
    (boolTy ~>? exp_ty) e
coExp e _exp_ty = bugDoc (text "coExp: expression not supported:" <+> pretty e)

coApp :: Exp Ti -> Exp Ti -> [Exp Ti] -> Expected (Sigma Ti) -> CoM (Sigma Ti)
coApp expr fun args exp_res_ty = do
  fun_sig <- coExp fun Infer
  res_ty <- coArgs args (type2tau fun_sig)
  (tau2sigma res_ty ~>? exp_res_ty) expr

coArgs :: [Exp Ti] -> Tau Ti -> CoM (Tau Ti)
coArgs []         res_ty = return res_ty
coArgs (arg:args) fun_ty = do
  void $ coExp arg (Check $ dom2type dom)
  rang' <- instFunTy (dom,rang) arg
  res_ty <- coArgs args rang'
  return res_ty
  where Just (dom,rang) = isFunTy fun_ty


coTuple :: [Exp Ti] -> [Dom Ti] -> CoM ()
coTuple []     []     = return ()
coTuple (e:es) (d:ds) = do
  void $ coExp e (Check $ dom2type d)
  ds_e <- instDoms e d ds
  coTuple es ds_e
coTuple _ _ = impossible

coAlts :: Var Ti -> [Alt Ti] -> CoM ()
coAlts scrut_var alts = do
  qs <- mapM alt2eq alts
  co_Equations [scrut_var] qs

coRhs :: Rhs Ti -> CoM ()
coRhs (Rhs rhs_ty grhs binds) = do
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
  where get_guard (GuardedRhs _ g _) = g

grhsCompletenessTCC :: [GuardedRhs Ti] -> Else Ti -> CoM ()
grhsCompletenessTCC _     (Else _ _) = return ()
grhsCompletenessTCC grhss NoElse     = addCompletenessTCC (P.disj $ map get_guard grhss)
  where get_guard (GuardedRhs _ g _) = g

coGuardedRhs :: GuardedRhs Ti -> Tau Ti -> CoM ()
coGuardedRhs (GuardedRhs loc g expr) exp_ty
  = inGuardedRhsCtxt loc $ do
  void $ coExp g (Check boolTy)
  void $ withFacts [g] $ coExp expr (Check $ tau2sigma exp_ty)

coElse :: Else Ti -> Tau Ti -> CoM ()
coElse NoElse          _exp_ty = return ()
coElse (Else loc expr)  exp_ty
  = inElseRhsCtxt loc $ do
  void $ coExp expr (Check $ tau2sigma exp_ty)


-- * Equations

data Equation
  = E {
    eqLoc  :: SrcLoc
  , eqPats :: [SimplePat Ti]
  , eqRhs  :: EqRHS
  }

data EqRHS = NoEqRHS
           | EqRHS (Rhs Ti)

coEqRHS :: EqRHS -> CoM ()
coEqRHS NoEqRHS     = return ()
coEqRHS (EqRHS rhs) = coRhs rhs

mkEq :: SrcLoc -> [Pat Ti] -> Rhs Ti -> CoM Equation
mkEq loc pats rhs = do
  rhs' <- subst_rhs var_s [] rhs
  return $ E loc pats' (EqRHS rhs')
  where (pats',var_s) = simplifyPats pats

alt2eq :: Alt Ti -> CoM Equation
alt2eq (Alt (Just loc) pat rhs) = mkEq loc [pat] rhs
alt2eq _other = impossible

match2eq :: Match Ti -> CoM Equation
match2eq (Match (Just loc) pats rhs) = mkEq loc pats rhs
match2eq _other = impossible

matches2eqs :: [Match Ti] -> CoM [Equation]
matches2eqs = mapM match2eq

patbin2eq :: SrcLoc -> Pat Ti -> Equation
patbin2eq loc pat = E loc [pat'] NoEqRHS
  where ([pat'],_) = simplifyPats [pat]

isVar :: Equation -> Bool
isVar (E _ (VarPat _:_) _) = True
isVar _other               = False

isLit :: Equation -> Bool
isLit (E _ (LitPat _:_) _) = True
isLit _other               = False

getLit :: Equation -> Integer
getLit (E _ (LitPat (IntLit n):_) _) = n
getLit _other                        = bug "not a literal"

isTuple :: Equation -> Bool
isTuple (E _ (TuplePat _ _:_) _) = True
isTuple _other                   = False

isCon :: Equation -> Bool
isCon (E _ (ConPat _ _ _:_) _) = True
isCon _other                   = False

getCon :: Equation -> TcCon Ti
getCon (E _ (ConPat _ con _:_) _) = con
getCon _other                     = bug "not a constructor"

coType :: Type c Ti -> CoM ()
coType (VarTy _) = return ()
coType (ConTy _tc tys) = mapM_ coType tys
coType (PredTy pat tau mb_prop) = do
  withForall qs $ do
    coType tau
    void $ T.mapM (`coExp` (Check boolTy)) mb_prop
  where qs = map toQVar $ Set.elems $ bsPat pat
coType (FunTy dom rang) = coDom dom $ coType rang
coType (ListTy elem_ty) = coType elem_ty
coType (TupleTy ds) = coDoms ds
coType (ForallTy tvs tau) = do
  sko_tvs <- mapM skoTyVar tvs
  let sko_tys = map VarTy sko_tvs
  sko_tau <- subst_type [] (zip tvs sko_tys) tau
  coType sko_tau
coType _other = impossible


coDoms :: [Dom Ti] -> CoM ()
coDoms []     = return ()
coDoms (d:ds) = coDom d $ coDoms ds

coDom :: Dom Ti -> CoM a -> CoM a
coDom (Dom mb_pat tau mb_prop) m = do  
  coType tau
  withForall qs $ do
    void $ T.mapM (`coExp` (Check boolTy)) mb_prop
    with_prop_fact m
  where qs = map toQVar $ Set.elems $ maybe Set.empty bsPat mb_pat
        with_prop_fact = case mb_prop of
                             Nothing -> id
                             Just p  -> withFacts [p]

getEqPat :: Int -> Equation -> SimplePat Ti
getEqPat n (E _ pats _) = pats !! n

coEquations :: [Dom Ti] -> [Equation] -> CoM ()
coEquations ds qs = do
  xs <- pick_variables
  let qxs = map toQVar xs
  withForall qxs $
    co_Equations xs qs
  where pick_variables = go 0 [] ds
          where go _i vs_rev []     = return $ reverse vs_rev
                go  i vs_rev (d:ds) = do
                  let n = case getNameForPats (map (getEqPat i) qs) of
                              Nothing -> "x" ++ show i
                              Just n1 -> n1
                  v <- newVarId n (dom2type d)
                  ds' <- instDoms (Var v) d ds
                  go (i+1) (v:vs_rev) ds'

co_Equations :: [Var Ti] -> [Equation] -> CoM ()
co_Equations [] []  = error "coEquations undefined 1" -- FALSE must hold
co_Equations [] [E _ [] rhs] = coEqRHS rhs
co_Equations [] (_:_) = throwError $ text "Non-uniform definition/pattern(s)"
co_Equations _xs []    = error "coEquations undefined 2" -- FALSE must hold
co_Equations (x:xs) qs
  | all isVar   qs = matchVar x xs qs
  | all isLit   qs = matchLit x xs qs
  | all isTuple qs = matchTuple x xs qs
  | all isCon   qs = matchCon x xs qs
  | otherwise = throwError $ text "Non-uniform definition/pattern(s)"


subst_eq :: [(Var Ti,Exp Ti)] -> Equation -> CoM Equation
subst_eq var_s (E loc pats rhs) = do
  let s = mkSubst1_FV var_s []
  (pats',s') <- substPats s pats
  rhs' <- substEqRHS s' rhs
  return (E loc pats' rhs')
  where substEqRHS _s NoEqRHS        = return NoEqRHS
        substEqRHS  s (EqRHS eq_rhs) = liftM EqRHS $ substRhs s eq_rhs

getNameForPats :: [Pat Ti] -> Maybe String
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
  = withFacts [Var x ==* mkInt lit] $
      co_Equations xs [ E loc ps rhs | E loc (LitPat _:ps) rhs <- qs]

matchTuple :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchTuple x xs [E loc (p@(TuplePat _ ps1):ps) rhs]
  | all isVarPat ps1 =
      withForall qxs' $ withFacts [Var x ==* pat2exp p] $
        co_Equations (xs'++xs) [E loc (ps1++ps) rhs]
  where xs' = [ x1 | VarPat x1 <- ps1]
        qxs' = map toQVar xs'
matchTuple x xs qs = do
  let E _ (TuplePat tup_ty _:_) _ = head qs
      TupleTy ds = mu_0 tup_ty
  (tup_exp,xs') <- instTupleWithVars ds
  let qxs' = map toQVar xs'
  withForall qxs' $ withFacts [Var x ==* tup_exp] $
    co_Equations (xs'++xs) [E  loc (ps1++ps) rhs | E loc (TuplePat _ ps1:ps) rhs <- qs]

matchCon :: Var Ti -> [Var Ti] -> [Equation] -> CoM ()
matchCon x xs qs = do
  addConCompletenessTCC
  sequence_ [ matchClause x c xs (choose c qs) | c <- cs ]
  where cs = nub $ map getCon qs
        ty_con = tcConTy $ getCon $ head qs
        all_cs = [ TcCon c ty_con | c <- tyConCons ty_con ]
        uncovered_cs = all_cs \\ cs
        typs = let E _ (ConPat con_typs _ _:_) _ = head qs in con_typs
        is_not_con con = do
          (e,ys) <- instWithVars (sortOf con) typs (Con con)
          let qys = map toQVar ys
          return $ P.mkForall qys (Var x !=* e)
        addConCompletenessTCC
         | null uncovered_cs = return ()
         | otherwise = do
            no_uncover <- liftM P.conj $ mapM is_not_con uncovered_cs
            addCompletenessTCC no_uncover
          

matchClause :: Var Ti -> TcCon Ti -> [Var Ti] -> [Equation] -> CoM ()
matchClause x _con xs [E loc (p@(ConPat _ _ ps1):ps) rhs]
  | all isVarPat ps1 =
      withForall qxs' $ withFacts [Var x ==* pat2exp p] $
        co_Equations (xs'++xs) [E loc (ps1++ps) rhs]
  where xs' = [ x1 | VarPat x1 <- ps1]
        qxs' = map toQVar xs'
matchClause x con xs qs = do
  let E _ (ConPat typs _ _:_) _ = head qs
  (p_exp,xs') <- instWithVars (sortOf con) typs (Con con)
  let qxs' = map toQVar xs'
  withForall qxs' $ withFacts [Var x ==* p_exp] $
    co_Equations (xs'++xs) [E  loc (ps1++ps) rhs | E loc (ConPat _ _ ps1:ps) rhs <- qs]

choose :: TcCon Ti -> [Equation] -> [Equation]
choose c qs = [q | q <- qs, getCon q == c]
