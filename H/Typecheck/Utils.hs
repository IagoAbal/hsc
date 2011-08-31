{-# LANGUAGE GADTs #-}

module H.Typecheck.Utils where

import H.Typecheck.TcM
import H.Typecheck.Zonk

import H.Syntax
import H.Pretty
import H.Phase
import H.FreeVars

import Control.Applicative ( pure, (<$>), (<*>), (<|>) )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Foldable as F


getFreeTyVars :: [PolyType Tc] -> TcM (Set TyVar)
-- This function takes account of zonking, and returns a set
-- (no duplicates) of free type variables
getFreeTyVars ptys = do
  ptys' <- mapM zonkPolyType ptys
  return (polyTypesFTV ptys')


getMetaTyVars :: [PolyType Tc] -> TcM (Set MetaTyVar)
-- This function takes account of zonking, and returns a set
-- (no duplicates) of unbound meta-type variables
getMetaTyVars ptys = traceDoc (text "getMetaTyVars no=" <+> int (length ptys)) $ do
  traceDoc (text "getMetaTyVars pre-zonkPolyType") $ do
  ptys' <- mapM zonkPolyType ptys
  traceDoc (text "getMetaTyVars post-zonkPolyType") $ do
  return (polyTypesMTV ptys')


quantify :: [MetaTyVar] -> Type Tc -> TcM ([TyVar],PolyType Tc)
quantify [] ty = return ([],monoTy ty)
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

quantifyExp :: Exp Tc -> [MetaTyVar] -> Type Tc -> TcM (Exp Tc,PolyType Tc)
quantifyExp exp mtvs ty = do
  (forall_tvs,pty) <- quantify mtvs ty
  return (tyLam forall_tvs exp,pty)


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
patMTV (VarPat x) = polyTypeMTV $ varType x
patMTV (LitPat _) = Set.empty
patMTV (InfixPat p1 _op ptctys p2) = patsMTV [p1,p2] `Set.union` (F.foldMap typesMTV ptctys)
patMTV (ConPat _con ptctys ps) = patsMTV ps  `Set.union` (F.foldMap typesMTV ptctys)
patMTV (TuplePat ps ptcty) = patsMTV ps `Set.union` (F.foldMap typeMTV ptcty)
patMTV (ListPat ps ptcty) = patsMTV ps `Set.union` (F.foldMap typeMTV ptcty)
patMTV (ParenPat p) = patMTV p
patMTV (WildPat ptcty)     = F.foldMap typeMTV ptcty
patMTV (AsPat _x p)  = patMTV p
patMTV (SigPat p ty) = patMTV p `Set.union` typeMTV ty

polyTypesMTV :: [PolyType Tc] -> Set MetaTyVar
polyTypesMTV = Set.unions . map polyTypeMTV

polyTypeMTV :: PolyType Tc -> Set MetaTyVar
polyTypeMTV (ForallTy _tvs ty) = typeMTV ty

typesMTV :: [Type Tc] -> Set MetaTyVar
typesMTV = Set.unions . map typeMTV

typeMTV :: Type Tc -> Set MetaTyVar
typeMTV (VarTy _) = Set.empty
typeMTV (ConTy _ args) = typesMTV args
typeMTV (PredTy pat ty _)  = patMTV pat `Set.union` typeMTV ty
typeMTV (FunTy dom rang) = domMTV dom `Set.union` typeMTV rang
typeMTV (ListTy ty) = typeMTV ty
typeMTV (TupleTy ds) = domsMTV ds
typeMTV (MetaTy mtv) = Set.singleton mtv

domsMTV :: [Dom Tc] -> Set MetaTyVar
domsMTV = Set.unions . map domMTV

domMTV :: Dom Tc -> Set MetaTyVar
domMTV (Dom Nothing ty Nothing) = typeMTV ty
domMTV (Dom (Just pat) ty _) = patMTV pat `Set.union` typeMTV ty

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
propMTV (PrefixApp op e) = propMTV e
propMTV (InfixApp e1 op e2) = propsMTV [e1,e2]
propMTV (App e1 e2) = propsMTV [e1,e2]
propMTV (TyApp e tys) = propMTV e
propMTV (Lam _loc _pats body)
  = propMTV body
  -- we don't go inside bindings...
propMTV (Let _bs body)
  = propMTV body
propMTV (TyLam tvs body) = propMTV body
propMTV (Ite g t e) = Set.empty
propMTV (If grhss) = Set.empty
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

-- * pat2exp

-- | Converts a pattern to an expression.
-- NB: Such a conversion is not possible in case of wild-card patterns.
pat2exp :: Pat Tc -> Maybe (Exp Tc)
pat2exp (LitPat lit) = pure $ Lit lit
pat2exp (VarPat x)   = pure $ Var x
pat2exp (InfixPat p1 bcon (PostTc typs) p2)
  = (flip InfixApp conE) <$> pat2exp p1 <*> pat2exp p2
  where conE = tyApp (Op $ ConOp bcon) typs
pat2exp (ConPat con (PostTc typs) ps)
  = (conE `app`) <$> mapM pat2exp ps
  where conE = tyApp (Con con) typs
pat2exp (TuplePat ps tup_ty) = Tuple tup_ty <$> mapM pat2exp ps
pat2exp (ListPat ps list_ty) = List list_ty <$> mapM pat2exp ps
pat2exp (ParenPat p) = Paren <$> pat2exp p
pat2exp (WildPat _)     = Nothing
pat2exp (AsPat _ p)  = pat2exp p
pat2exp (SigPat p ty) = pat2exp p
