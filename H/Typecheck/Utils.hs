{-# LANGUAGE GADTs, ScopedTypeVariables, FlexibleContexts #-}

module H.Typecheck.Utils where

import H.Typecheck.TcM
import H.Typecheck.Zonk

import H.Syntax
import H.Pretty
import H.Phase
import H.FreeVars
import H.Subst1 ( subst_exp, subst_type, subst_doms )
import H.TransformPred

import qualified Util.Set as Set

import Sorted
import Unique

import Control.Monad
import Control.Monad.Error
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Foldable as F


getFreeTyVars :: [Type c Tc] -> TcM (Set TyVar)
-- This function takes account of zonking, and returns a set
-- (no duplicates) of free type variables
getFreeTyVars ptys = do
  ptys' <- mapM zonkType ptys
  return (typesFTV ptys')


getMetaTyVars :: [Type c Tc] -> TcM (Set MetaTyVar)
-- This function takes account of zonking, and returns a set
-- (no duplicates) of unbound meta-type variables
getMetaTyVars ptys = traceDoc (text "getMetaTyVars no=" <+> int (length ptys)) $ do
  traceDoc (text "getMetaTyVars pre-zonkPolyType") $ do
  ptys' <- mapM zonkType ptys
  traceDoc (text "getMetaTyVars post-zonkPolyType") $ do
  return (typesMTV ptys')


quantify :: [MetaTyVar] -> Tau Tc -> TcM ([TyVar],Sigma Tc)
quantify [] ty = return ([],tau2sigma ty)
  -- Quantify over the specified type variables (all flexible)
quantify mtvs ty = do
  forall_tvs <- mapM (flip newTyVar typeKi) tvs_names
  mapM_ bind (zip mtvs forall_tvs)
  ty' <- zonkType ty
  return (forall_tvs,forallTy forall_tvs ty')
  where tvs_names = take (length mtvs) $
                      [ [x]          | x <- ['a'..'z'] ] ++
                      [ (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]
        -- 'bind' is just a cunning way of doing the substitution
        bind (mtv,tv) = writeMetaTyVar mtv (VarTy tv)

quantifyExp :: Exp Tc -> [MetaTyVar] -> Tau Tc -> TcM (Exp Tc,Sigma Tc)
quantifyExp expr mtvs ty = do
  (forall_tvs,pty) <- quantify mtvs ty
  return (tyLam forall_tvs expr,pty)


-- * Meta type variables
-- FIX return type must be a list because the order "matters", for example,
-- map type is being inferred as (b -> a) -> [b] -> [a] whilst we would like to
-- see (a -> b) -> [a] -> [b].
-- NOTE
-- We don't want a proper MTV computation, for instance, we don't want
-- to go "inside" predicates to get MTVs, because typeMTV is used
-- to generalise a type, suppose the following
-- {x:?a|(\y:?b -> True) x} -> Int
-- we don't want to generalise ?b !!!

patsMTV :: [Pat Tc] -> Set MetaTyVar
patsMTV = Set.unions . map patMTV

patMTV :: Pat Tc -> Set MetaTyVar
  -- I think we don't need to get MTVs from x type for the typeMTV case, but
  -- it does not hurt, and I think we really need this for the propMTV case.
patMTV (VarPat x) = typeMTV $ varType x
patMTV (LitPat _) = Set.empty
patMTV (InfixCONSPat ptcty p1 p2) = patsMTV [p1,p2] `Set.union` (F.foldMap typeMTV ptcty)
patMTV (ConPat _con ptctys ps) = patsMTV ps  `Set.union` (F.foldMap typesMTV ptctys)
patMTV (TuplePat ps ptcty) = patsMTV ps `Set.union` (F.foldMap typeMTV ptcty)
patMTV (ListPat ps ptcty) = patsMTV ps `Set.union` (F.foldMap typeMTV ptcty)
patMTV (ParenPat p) = patMTV p
patMTV (WildPat wild_var) = typeMTV $ varType wild_var
patMTV (AsPat _x p)  = patMTV p
-- patMTV (SigPat p ty) = patMTV p `Set.union` typeMTV ty

typesMTV :: [Type c Tc] -> Set MetaTyVar
typesMTV = Set.unions . map typeMTV

typeMTV :: Type c Tc -> Set MetaTyVar
typeMTV (VarTy _) = Set.empty
typeMTV (ConTy _ args) = typesMTV args
typeMTV (PredTy pat ty _)  = patMTV pat `Set.union` typeMTV ty
typeMTV (FunTy dom rang) = domMTV dom `Set.union` typeMTV rang
typeMTV (ListTy ty) = typeMTV ty
typeMTV (TupleTy ds) = domsMTV ds
typeMTV (MetaTy mtv) = Set.singleton mtv
typeMTV (ForallTy _tvs ty) = typeMTV ty
typeMTV _other = undefined -- impossible

domsMTV :: [Dom Tc] -> Set MetaTyVar
domsMTV = Set.unions . map domMTV

domMTV :: Dom Tc -> Set MetaTyVar
domMTV (Dom Nothing ty Nothing) = typeMTV ty
domMTV (Dom (Just pat) ty _) = patMTV pat `Set.union` typeMTV ty
domMTV _other = undefined -- impossible

propsMTV :: [Prop Tc] -> Set MetaTyVar
propsMTV = Set.unions . map propMTV

-- used for GoalDecl, that's why I named it propMTV and not expMTV...
-- It just look for forall-patterns
-- now it is limited, dirty... but it suffices... I will extend it
-- in future after thinking on it a little more.
propMTV :: Prop Tc -> Set MetaTyVar
propMTV (Var _)   = Set.empty
propMTV (Con _)   = Set.empty
propMTV (Op _)    = Set.empty
propMTV (Lit _)   = Set.empty
propMTV (PrefixApp _op e) = propMTV e
propMTV (InfixApp e1 _op e2) = propsMTV [e1,e2]
propMTV (App e1 e2) = propsMTV [e1,e2]
propMTV (TyApp e tys) = propMTV e
propMTV (Lam _loc _pats (Rhs _ (UnGuarded body) _))
  = propMTV body
  -- we don't go inside bindings...
propMTV (Let _bs body)
  = propMTV body
propMTV (TyLam tvs body) = propMTV body
propMTV (Ite _ g t e) = Set.empty
propMTV (If _ grhss) = Set.empty
propMTV (Case e _ptcty alts) = propMTV e
propMTV (Tuple _ es) = propsMTV es
propMTV (List _ es) = propsMTV es
propMTV (Paren e) = propMTV e
propMTV (LeftSection e _op) = propMTV e
propMTV (RightSection _op e) = propMTV e
propMTV (EnumFromTo e1 e2) = propsMTV [e1,e2]
propMTV (EnumFromThenTo e1 e2 e3) = propsMTV [e1,e2,e3]
propMTV (Coerc _loc e polyty) = propMTV e
propMTV (QP qt pats body) = patsMTV pats `Set.union` propMTV body
propMTV _other = undefined -- impossible

-- * pat2exp

-- | Converts a pattern to an expression.
-- NB: Such a conversion is not possible in case of wild-card patterns.
pat2exp :: IsPostTc p => Pat p -> Exp p
pat2exp (LitPat lit) = Lit lit
pat2exp (VarPat x)   = Var x
pat2exp (InfixCONSPat (PostTc typ) p1 p2)
  = InfixApp (pat2exp p1) conE (pat2exp p2)
  where conE = tyApp (Op CONSOp) [typ]
pat2exp (ConPat con (PostTc typs) ps)
  = conE `app` map pat2exp ps
  where conE = tyApp (Con con) typs
pat2exp (TuplePat ps tup_ty) = Tuple tup_ty $ map pat2exp ps
pat2exp (ListPat ps list_ty) = List list_ty $ map pat2exp ps
pat2exp (ParenPat p) = Paren $ pat2exp p
pat2exp (WildPat wild_var)
  = Var wild_var
pat2exp (AsPat _ p)  = pat2exp p
-- pat2exp (SigPat p ty) = pat2exp p
pat2exp _other = undefined -- impossible


expandSyn :: (IsPostTc p, MonadUnique m) => Type c p -> m (Maybe (Type c p))
expandSyn (ConTy (SynTyCon _ ps rhs) args)
  = liftM (Just . tau2type) $ subst_type [] (zip ps args) rhs
expandSyn _other = return  Nothing

instSigmaType :: (MonadUnique m, IsPostTc p) => Sigma p -> [Tau p] -> m (Tau p)
instSigmaType (ForallTy tvs ty) typs = subst_type [] (zip tvs typs) ty
instSigmaType ty [] = return $ sigma2tau ty
instSigmaType _ty _typs = error "bug instSigmaType"

instWithVars :: forall m p. (MonadUnique m, IsPostTc p, MonadError Doc m) => Sigma p -> [Tau p] -> Exp p -> m (Exp p,[Var p])
instWithVars sig typs expr = do
  tau <- instSigmaType sig typs
  (expr',vars_rev) <- go 1 [] (tyApp expr typs) tau
  return (expr',reverse vars_rev)
  where go :: Int -> [Var p] -> Exp p -> Tau p -> m (Exp p,[Var p])
        go  i xs e (FunTy d r) = do
          x <- newVar ("x" ++ show i) (dom2type d)
          let v = Var x
          r' <- instFunTy (d,r) v
          go (i+1) (x:xs) (App e v) r'
        go _i xs e _res_ty     = return (e,xs)


instTupleWithVars :: forall m p. (MonadUnique m, IsPostTc p, MonadError Doc m) => [Dom p] -> m (Exp p,[Var p])
instTupleWithVars doms = go 1 [] doms
  where go :: Int -> [Var p] -> [Dom p] -> m (Exp p,[Var p])
        go _i xs_rev []     = return (Tuple (PostTc $ TupleTy doms) (map Var xs), xs)
          where xs = reverse xs_rev
        go  i xs_rev (d:ds) = do
          x <- newVar ("x" ++ show i) (dom2type d)
          let v = Var x
          ds' <- instDoms v d ds
          go (i+1) (x:xs_rev) ds'

-- * Instantiation of function types

instFunTy :: (IsPostTc p, MonadUnique m, MonadError Doc m) => (Dom p,Range p) -> Exp p -> m (Range p)
  -- non-dependent arrow
instFunTy (Dom Nothing _ Nothing,rang) _ = return rang  
instFunTy (Dom (Just p) _ _,rang) _
  | Set.null (bsPat p) = return rang
  -- dependent arrow
instFunTy (Dom (Just p) _ _,rang) e
  | Just s <- patExpSubst e p (fvType rang) = subst_type s [] rang
  | otherwise = do
      when (not $ matchableWith e p) $
        throwError (text "Expression" <+> pretty e <+> text "does not match pattern" <+> pretty p)
      e_ty <- tcExprTau e
      let f prop | bsPat p `Set.disjointWith` fvExp prop = Nothing
                 | otherwise = Just $ Let [PatBind Nothing p (rhsExp e_ty e)] prop
      tpType f rang
instFunTy _other _e = undefined -- impossible

patExpSubst :: forall p. IsPostTc p =>
                Exp p
              -> Pat p   -- ^ domain pattern
              -> Set (Var p)
              -> Maybe [(Var p,Exp p)]    -- ^ substitution for range  
patExpSubst expr pat_dom target_fv = get_subst expr pat_dom
  where get_subst :: Exp p -> Pat p -> Maybe [(Var p,Exp p)]
        get_subst _ (WildPat _) = Just []
        get_subst e (VarPat x) | not (x `Set.member` target_fv) = Just []
                               | otherwise = Just [(x,e)]
        get_subst e (ConPat con' _ ps)
          | (f,args) <- splitApp e
          , Just con <- get_con f
          , con == con' = liftM concat $ zipWithM get_subst args ps
          where get_con (Con con) = Just con
                get_con (TyApp e1 _) = get_con e1
                get_con (Coerc _ e1 _) = get_con e1
                get_con (Paren e1) = get_con e1
                get_con _other    = Nothing
        get_subst (InfixApp e1 (Op CONSOp) e2) (InfixCONSPat _ p1 p2)
          = liftM concat $ sequence [get_subst e1 p1, get_subst e2 p2]
        get_subst (InfixApp e1 (TyApp (Op CONSOp) _) e2) (InfixCONSPat _ p1 p2)
          = liftM concat $ sequence [get_subst e1 p1, get_subst e2 p2]
        get_subst (Tuple _ es) (TuplePat ps _)
          | length es == length ps = liftM concat $ zipWithM get_subst es ps
        get_subst (List _ es) (ListPat ps _)
          | length es == length ps = liftM concat $ zipWithM get_subst es ps
--         get_subst e (SigPat p _) = get_subst e p
        get_subst e (AsPat x p) = liftM ((x,e):) $ get_subst e p
        get_subst (Paren e) p    = get_subst e p
        get_subst e (ParenPat p) = get_subst e p
        get_subst _ _ = Nothing

instFunTyWithPat :: (MonadUnique m, MonadError Doc m, IsPostTc p) => (Dom p,Range p) -> Pat p -> m (Range p)
  -- non-dependent arrow
instFunTyWithPat (Dom Nothing _ Nothing,rang) _lpat = return rang
  -- dependent arrow
instFunTyWithPat (Dom (Just dpat) _ _,rang)   lpat = do
  when (not $ matchablePats lpat dpat) $
    throwError (text "Pattern" <+> pretty lpat <+> text "is not compatible with the expected pattern" <+> pretty dpat)
  (s,bs) <- patPatSubst lpat dpat (fvType rang)
  binds <- sequence [ do e_ty <- tcExprTau e
                         return $ PatBind Nothing p (rhsExp e_ty e)
                    | (p,e) <- bs
                    ]
  rang' <- subst_type s [] rang >>= letType binds
  traceDoc (text "instFunTyWithPat rang'=" <+> pretty rang') $ return rang'
instFunTyWithPat _other _lpat = undefined -- impossible

patPatSubst :: forall m p. (MonadUnique m, IsPostTc p) =>
                 Pat p   -- ^ argument pattern
              -> Pat p   -- ^ domain pattern
              -> Set (Var p)
              -> m ([(Var p,Exp p)],[(Pat p,Exp p)])    -- ^ substitution for range, let-bindings
patPatSubst pat_lam pat_dom target_fv = traceDoc (text "patPatSubst" <+> pretty pat_lam <+> pretty pat_dom) $ get_subst ([],[]) pat_lam pat_dom
  where fvs = target_fv `Set.union` fvPat pat_dom
        get_subst :: ([(Var p,Exp p)],[(Pat p,Exp p)]) -> Pat p -> Pat p -> m ([(Var p,Exp p)],[(Pat p,Exp p)])
          -- dpat bounds no variable
        get_subst (s,bs) _lpat dpat  | Set.null (bsPat dpat) = return (s,bs)
          -- no variable bound by dpat is free in rang
        get_subst (s,bs) _lpat dpat  | bsPat dpat `Set.disjointWith` fvs = return (s,bs)
        get_subst (s,bs) lpat  (VarPat x) = return ((x,e):s,bs)
          where e = pat2exp lpat
        get_subst (s,bs) (WildPat wild_var) dpat = do
          wildexp' <- subst_exp s [] (Var wild_var)
          return (s,bs++[(dpat,wildexp')])
        get_subst (s,bs) (VarPat y) dpat = do
          yexp' <- subst_exp s [] (Var y)
          return (s,bs++[(dpat,yexp')])
        get_subst (s,bs) (LitPat i) (LitPat j) | i == j = return (s,bs)
        get_subst (s,bs) (InfixCONSPat _ q1 q2) (InfixCONSPat _ p1 p2)
          = do (s',bs') <- get_subst (s,bs) q1 p1
               get_subst (s',bs') q2 p2
        get_subst (s,bs) (ConPat con _ qs) (ConPat con' _ ps)
          | con == con' = fold_get_subst (s,bs) qs ps
        get_subst acc    (TuplePat qs _) (TuplePat ps _)
          = fold_get_subst acc qs ps
        get_subst (s,bs) (ListPat qs _) (ListPat ps _)
          = fold_get_subst (s,bs) qs ps
        get_subst acc (ListPat [] _) (ConPat _ _ []) = return acc
        get_subst acc (ConPat _ _ []) (ListPat [] _) = return acc
        get_subst acc (ListPat (q:qs) ptcty) (InfixCONSPat _ p1 p2) = do
          acc' <- get_subst acc q p1
          get_subst acc' (ListPat qs ptcty) p2
        get_subst acc (InfixCONSPat _ q1 q2) (ListPat (p:ps) ptcty) = do
          acc' <- get_subst acc q1 p
          get_subst acc' q2 (ListPat ps ptcty)
        get_subst (s,bs) q           (AsPat x p)
          | not (Set.member x fvs) = get_subst (s,bs) q p
        get_subst (s,bs) (AsPat y q) (AsPat x p) = get_subst ((x,Var y):s,bs) q p
        get_subst (s,bs) q           (AsPat x p)
          =  get_subst ((x,e):s,bs) q p
          where e = pat2exp q
        get_subst acc (AsPat _y q) p           = get_subst acc q p
--         get_subst acc (SigPat q _) p            = get_subst acc q p
--         get_subst acc q            (SigPat p _) = get_subst acc q p
        get_subst acc (ParenPat q) p            = get_subst acc q p
        get_subst acc q            (ParenPat p) = get_subst acc q p
          -- just check preconditions... change it by an earlier assert
        get_subst _acc lpat dpat
         | not (matchablePats lpat dpat) = error "bug found!"
        get_subst _acc _lpat _dpat = undefined -- impossible
          -- Here 'dpat' (hence, 'pat_dom') bounds some variable that is
          -- being used in rang but such (sub-)expression is ignored by
          -- 'pat_lam'.
          -- See [Instantiating domains]
  -- THIS WAS FIXED INTRODUCING SKOLEM VARS
--         get_subst _acc lpat dpat
--           = throwError $ text "Illegal pattern for the given pattern-type: variable(s)"
--                         <+> (sep $ punctuate comma $ map ppQuot $ Set.toList $ bsPat dpat)
--                         <+> text "cannot be bound by pattern" <+> ppQuot lpat
          -- error $ "illegal dependent type, variables X are not being matched ... " ++ prettyPrint lpat ++ " .. " ++ prettyPrint dpat
        fold_get_subst (s,bs) qs ps = foldM (\(s1,bs1) (q,p) -> get_subst (s1,bs1) q p) (s,bs) $ zip qs ps

{- Note [Instantiating domains]

Suppose that the range of a function depends on a variable bound by the domain
that is ignored by the argument pattern, as in:

  foo : {(x::_):[Int]} -> {r:Int|r>x}
  foo _ = e

So, what type must we use for checking 'e'? The only choice is to
quantify 'x' universally and check 'e' against the type {r:Int|forall x. r > x}.
In the VC phase this will lead to the following TCC:
  forall x. e > x
which is not valid. In general, this situation usually lead to non-valid TCCs.
Moreover, to make such quantification we would have to implement a more complex
algorithm, because that cannot be done by a simply substitution.

So, because the above reasons I have decided to ban this case, so it is
considered invalid for an equation or lambda expression to ignore a variable
bound by the domain and used to define the range.

There are other situations, perhaps less intuitive, for instance

  bar : {l@(_::_):[Int]} -> {r:Int|r>head l}
  bar (x::_) = e

but these examples are a bit involved, bad style... and more important, very
easy to fix! In a real-world implementation the user may write @bar (x::_xs) = e@
so the typechecker can perform the substitution (_xs is a valid variable),
but the renaming phase will not complain about _xs being an unused binding because
it is an identifier starting with an underscore.

-}

-- This could be more fine tuned but it is OK
letType :: (MonadUnique m, IsPostTc p) => [Bind p] -> Type c p -> m (Type c p)
letType binds ty
  | [] <- binds' = return ty
  | otherwise    = tpType f ty
  where binds' = map unLocBind $ reverse $ filter_binds $ reverse binds
        unLocBind (PatBind _loc pat rhs) = PatBind Nothing pat rhs
        unLocBind (FunBind rec name sig ptctyps matches)
          = FunBind rec name sig ptctyps (map unLocMatch matches)
        unLocMatch (Match _loc pats rhs) = Match Nothing pats rhs
        ty_fv = fvType ty
        filter_binds []                   = []
        filter_binds rev_binds@(b:bs)
          | bsBind b `Set.disjointWith` ty_fv = filter_binds bs
          | otherwise                         = rev_binds
        f prop | bsBinds binds' `Set.disjointWith` fvExp prop = Nothing
               | otherwise = Just $ Let binds' prop

-- instPredTyProp :: (IsPostTc p, MonadUnique m) =>
--                     Exp p -> Pat p -> Tau p -> Maybe (Prop p) -> m (Maybe (Prop p))
-- instPredTyProp _e pat _ty mb_prop | Set.null (bsPat pat) = return mb_prop
-- instPredTyProp  e pat  ty mb_prop
--  | Just s <- patExpSubst e pat (fvMaybeExp mb_prop) = T.mapM (subst_exp s []) mb_prop
--  | otherwise = do
--     uniq  <- getUniq
--     return $ Just $ Case e (PostTc boolTy)
--                       [Alt Nothing pat (rhsExp prop)
--                       ,Alt Nothing (WildPat uniq (PostTc ty)) (rhsExp P._False_)
--                       ]
--  where prop = maybe P._True_ id mb_prop


instDoms :: (MonadUnique m, MonadError Doc m, IsPostTc p) => Exp p -> Dom p -> [Dom p] -> m [Dom p]
instDoms  _e _dom                    [] = return []
  -- non-dependent
instDoms _e (Dom Nothing _ Nothing) ds = return ds
instDoms _e (Dom (Just pat) _ _)    ds
  | Set.null (bsPat pat) = return ds
  -- dependent arrow
instDoms e (Dom (Just pat) _ _)     ds
  | Just s <- patExpSubst e pat (fvDoms ds) = subst_doms s [] ds
  | otherwise = do
      when (not $ matchableWith e pat) $
        throwError (text "Expression" <+> pretty e <+> text "does not match pattern" <+> pretty pat)
      e_ty <- tcExprTau e
      let f prop | bsPat pat `Set.disjointWith` fvExp prop = Nothing
                 | otherwise = Just $ Let [PatBind Nothing pat (rhsExp e_ty e)] prop
      tpDoms f ds
instDoms _e _other _ds = undefined -- impossible


-- Get expressions type

tcExprType :: (MonadUnique m, MonadError Doc m, IsPostTc p) => Exp p -> m (Sigma p)
tcExprType (Var x) = return $ sortOf x
tcExprType (Con con) = return $ sortOf con
tcExprType (Op op) = return $ sortOf op
tcExprType (Lit _) = return intTy
tcExprType (PrefixApp op e) = liftM tau2sigma $ tcAppType op [e]
tcExprType (InfixApp e1 op e2)
  =  liftM tau2sigma $ tcAppType op [e1,e2]
tcExprType (App f a) = liftM tau2sigma $ tcAppType f [a]
tcExprType (TyApp e tys) = do
  e_sig <- tcExprType e
  e_tau <- instSigmaType e_sig tys
  return $ tau2sigma e_tau
tcExprType (Lam _ pats (Rhs (PostTc rhs_ty) _ _)) = do
  pats_tys <- mapM tcPatType pats
  let doms = zipWith patternDom pats pats_tys
  return $ funTy doms rhs_ty
tcExprType (Let _ e) = tcExprType e
tcExprType (TyLam tvs e) = do
  e_ty <- tcExprType e
  return $ forallTy tvs $ sigma2tau e_ty
tcExprType (Ite (PostTc ite_ty) _ _ _) = return $ tau2sigma ite_ty
tcExprType (If (PostTc if_ty) _) = return $ tau2sigma if_ty
tcExprType (Case _ (PostTc case_ty) _) = return $ tau2sigma case_ty
tcExprType (Tuple (PostTc tup_ty) _) = return $ tau2sigma tup_ty
tcExprType (List (PostTc list_ty) _) = return $ tau2sigma list_ty
tcExprType (Paren e) = tcExprType e
tcExprType (LeftSection e1 op) = liftM tau2sigma $ tcAppType op [e1]
tcExprType (RightSection op e2) = do
  op_ty <- tcExprType op
  let FunTy d1 (FunTy d2 res_ty) = op_ty
  res_ty'  <- instFunTy (d2,res_ty) e2
  return $ d1 \--> res_ty'
tcExprType (EnumFromTo _ _) = return $ ListTy intTy
tcExprType (EnumFromThenTo _ _ _) = return $ ListTy intTy
tcExprType (Coerc _ _ sig) = return sig
tcExprType (QP _ _ _) = return boolTy
tcExprType _other = undefined -- impossible

tcExprTau :: (MonadUnique m, MonadError Doc m, IsPostTc p) => Exp p -> m (Tau p)
tcExprTau = tcExprType >=> return . sigma2tau


tcAppType :: (MonadUnique m, MonadError Doc m, IsPostTc p) => Exp p -> [Exp p] -> m (Tau p)
tcAppType fun args1 = do
  fun_sig <- tcExprType fun
  go args1 (sigma2tau fun_sig)
  where
    go []         res_ty = return res_ty
    go (arg:args) fun_ty = do
      rang' <- instFunTy (dom,rang) arg
      go args rang'
      where FunTy dom rang = mu_0 fun_ty

tcEqType :: (MonadUnique m, MonadError Doc m, IsPostTc p) => [Pat p] -> Tau p -> m (Tau p)
tcEqType []         res_ty = return res_ty
tcEqType (pat:pats) fun_ty = do
  let FunTy dom rang = mu_0 fun_ty
  rang' <- instFunTyWithPat (dom,rang) pat
  tcEqType pats rang'

tcPatType ::  (MonadUnique m, MonadError Doc m, IsPostTc p) => Pat p -> m (Tau p)
tcPatType (VarPat x) = return $ sigma2tau $ varType x
tcPatType (LitPat _) = return intTy
tcPatType (InfixCONSPat (PostTc elem_ty) _ _) = return $ ListTy elem_ty
tcPatType (ConPat con (PostTc typs) ps)  = do
  con_tau <- instSigmaType con_ty typs
  res_ty <- tcEqType ps con_tau
  return res_ty
  where con_ty = sortOf con
tcPatType (TuplePat _ (PostTc tup_ty)) = return tup_ty
tcPatType (ListPat _ (PostTc list_ty)) = return list_ty
tcPatType (ParenPat p) = tcPatType p
tcPatType (WildPat wild_var)
  = return $ sigma2tau $ varType wild_var
tcPatType (AsPat x _) = return $ sigma2tau $ varType x
-- tcPatType (SigPat _ tau) = return tau
tcPatType _other = undefined -- impossible
