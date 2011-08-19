{-# LANGUAGE TypeFamilies, FlexibleContexts, GADTs #-}

module H.FreeVars where

import H.Syntax
import H.Phase

import Data.Set ( Set )
import qualified Data.Set as Set



fvBinds :: Ord (VAR p) => [Bind p] -> Set (VAR p)
fvBinds = Set.unions . map fvBind

fvBind :: Ord (VAR p) => Bind p -> Set (VAR p)
fvBind (FunBind _rec fun sig matches)
  = fvTypeSig sig `Set.union` (Set.delete fun $ fvMatches matches)
fvBind (PatBind _loc pat rhs) = fvPat pat `Set.union` (fvRhs rhs Set.\\ bsPat pat)

bsBinds :: Ord (VAR p) => [Bind p] -> Set (VAR p)
bsBinds = Set.unions . map bsBind

bsBind :: Ord (VAR p) => Bind p -> Set (VAR p)
bsBind (FunBind _rec fun _sig _matches) = Set.singleton fun
bsBind (PatBind _loc pat rhs)           = bsPat pat

fvTypeSig :: Ord (VAR p) => TypeSig p -> Set (VAR p)
fvTypeSig NoTypeSig             = Set.empty
fvTypeSig (TypeSig _loc polyty) = fvPolyType polyty

fvMatches :: Ord (VAR p) => [Match p] -> Set (VAR p)
fvMatches = Set.unions . map fvMatch

fvMatch :: Ord (VAR p) => Match p -> Set (VAR p)
fvMatch (Match _loc pats rhs) = fvPats pats `Set.union` (fvRhs rhs Set.\\ bsPats pats)

fvExps :: Ord (VAR p) => [Exp p] -> Set (VAR p)
fvExps = Set.unions . map fvExp

fvMaybeExp :: Ord (VAR p) => Maybe (Exp p) -> Set (VAR p)
fvMaybeExp = maybe Set.empty fvExp

fvExp :: Ord (VAR p) => Exp p -> Set (VAR p)
fvExp (Var x)   = Set.singleton x
fvExp (Con _)   = Set.empty          -- ?
fvExp (Lit _)   = Set.empty
fvExp ElseGuard = Set.empty
fvExp (PrefixApp op e) = fvExp e
fvExp (InfixApp e1 op e2) = fvExps [e1,e2]
fvExp (App e1 e2) = fvExps [e1,e2]
fvExp (TyApp e tys) = fvExp e `Set.union` fvTypes tys
fvExp (Lam _loc pats body)
  = fvPats pats `Set.union` (fvExp body Set.\\ bsPats pats)
fvExp (Let bs body)
  = fvBinds bs `Set.union` (fvExp body Set.\\ bsBinds bs)
fvExp (TyLam tvs body) = fvExp body
fvExp (Ite g t e) = fvExps [g,t,e]
fvExp (If grhss) = fvGuardedRhss grhss
fvExp (Case e _ptcty alts) = fvExp e `Set.union` fvAlts alts
fvExp (Tuple es) = fvExps es
fvExp (List es) = fvExps es
fvExp (Paren e) = fvExp e
fvExp (LeftSection e _op) = fvExp e
fvExp (RightSection _op e) = fvExp e
fvExp (EnumFromTo e1 e2) = fvExps [e1,e2]
fvExp (EnumFromThenTo e1 e2 e3) = fvExps [e1,e2,e3]
fvExp (Coerc _loc e polyty) = fvExp e `Set.union` fvPolyType polyty
fvExp (QP qt pats body) = fvPats pats `Set.union` (fvExp body Set.\\ bsPats pats)


fvPats :: Ord (VAR p) => [Pat p] -> Set (VAR p)
fvPats = Set.unions . map fvPat

fvPat :: Ord (VAR p) => Pat p -> Set (VAR p)
  -- I think it should be 'fvPolyType $ varType x' but that would require
  -- to fix the algorithm to work just with 'Var p'
  -- other way would be to use type-classes... but it may have problems
fvPat (VarPat x) = Set.empty
fvPat (LitPat _) = Set.empty
fvPat (InfixPat p1 _op p2) = fvPats [p1,p2]
fvPat (ConPat _con ps) = fvPats ps
fvPat (TuplePat ps) = fvPats ps
fvPat (ListPat ps) = fvPats ps
fvPat (ParenPat p) = fvPat p
fvPat WildPat      = Set.empty
fvPat (AsPat _x p)  = fvPat p
fvPat (SigPat p ty) = fvPat p `Set.union` fvType ty

bsPats :: Ord (VAR p) => [Pat p] -> Set (VAR p)
bsPats = Set.unions . map bsPat

bsPat :: Ord (VAR p) => Pat p -> Set (VAR p)
bsPat (VarPat x) = Set.singleton x
bsPat (LitPat _) = Set.empty
bsPat (InfixPat p1 _op p2) = bsPats [p1,p2]
bsPat (ConPat _con ps) = bsPats ps
bsPat (TuplePat ps) = bsPats ps
bsPat (ListPat ps) = bsPats ps
bsPat (ParenPat p) = bsPat p
bsPat WildPat      = Set.empty
bsPat (AsPat x p)  = Set.insert x $ bsPat p
bsPat (SigPat p _ty) = bsPat p

fvAlts :: Ord (VAR p) => [Alt p] -> Set (VAR p)
fvAlts = Set.unions . map fvAlt

fvAlt :: Ord (VAR p) => Alt p -> Set (VAR p)
fvAlt (Alt _loc pat rhs) = fvPat pat `Set.union` (fvRhs rhs Set.\\ bsPat pat)

fvRhs :: Ord (VAR p) => Rhs p -> Set (VAR p)
fvRhs (Rhs grhs whr) = fvBinds whr `Set.union` (fvGRhs grhs Set.\\ bsBinds whr)

fvGRhs :: Ord (VAR p) => GRhs p -> Set (VAR p)
fvGRhs (UnGuarded e)   = fvExp e
fvGRhs (Guarded grhss) = fvGuardedRhss grhss

fvGuardedRhss :: Ord (VAR p) => GuardedRhss p -> Set (VAR p)
fvGuardedRhss (GuardedRhssIn grhss) = Set.unions $ map fvGuardedRhs grhss 
fvGuardedRhss (GuardedRhss grhss elserhs)
  = Set.unions $ fvElse elserhs : map fvGuardedRhs grhss 

fvGuardedRhs :: Ord (VAR p) => GuardedRhs p -> Set (VAR p)
fvGuardedRhs (GuardedRhs _loc g e) = fvExps [g,e]

fvElse :: Ord (VAR p) => Else p -> Set (VAR p)
fvElse NoElse        = Set.empty
fvElse (Else _loc e) = fvExp e

fvPolyType :: Ord (VAR p) => PolyType p -> Set (VAR p)
fvPolyType (ForallTy tvs ty) = fvType ty

fvTypes :: Ord (VAR p) => [Type p] -> Set (VAR p)
fvTypes = Set.unions . map fvType

fvType :: Ord (VAR p) => Type p -> Set (VAR p)
fvType (VarTy _) = Set.empty
fvType (ConTyIn _) = Set.empty
fvType (AppTyIn a b) = fvTypes [a,b]
fvType (ConTy _ args) = fvTypes args
fvType (PredTy pat ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)
fvType (FunTy dom range)
  = fvDom dom `Set.union` (fvType range Set.\\ bsDom dom)
fvType (ListTy ty) = fvType ty
fvType (TupleTy ds) = fvDoms ds
fvType (ParenTy ty) = fvType ty
  -- this case may be tricky ...
fvType (MetaTy _) = Set.empty

fvDoms :: Ord (VAR p) => [Dom p] -> Set (VAR p)
fvDoms []     = Set.empty
fvDoms (d:ds) = fvDom d `Set.union` (fvDoms ds Set.\\ bsDom d)

fvDom :: Ord (VAR p) => Dom p -> Set (VAR p)
fvDom (Dom Nothing ty Nothing) = fvType ty
fvDom (Dom (Just pat) ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)


bsDom :: Ord (VAR p) => Dom p -> Set (VAR p)
bsDom (Dom mbpat _ty _mbprop) = maybe Set.empty bsPat mbpat


-- * Free type variables
-- This is an incomplete implementation, but it suffices for checkSigma.
-- We should go inside type predicates looking for free type variables.

patsFTV :: Ord (TyVAR p) => [Pat p] -> Set (TyVAR p)
patsFTV = Set.unions . map patFTV

patFTV :: Ord (TyVAR p) => Pat p -> Set (TyVAR p)
patFTV (VarPat x) = Set.empty     -- same than for fvPat
patFTV (LitPat _) = Set.empty
patFTV (InfixPat p1 _op p2) = patsFTV [p1,p2]
patFTV (ConPat _con ps) = patsFTV ps
patFTV (TuplePat ps) = patsFTV ps
patFTV (ListPat ps) = patsFTV ps
patFTV (ParenPat p) = patFTV p
patFTV WildPat      = Set.empty
patFTV (AsPat _x p)  = patFTV p
patFTV (SigPat p ty) = patFTV p `Set.union` typeFTV ty

polyTypesFTV :: Ord (TyVAR p) => [PolyType p] -> Set (TyVAR p)
polyTypesFTV = Set.unions . map polyTypeFTV

polyTypeFTV :: Ord (TyVAR p) => PolyType p -> Set (TyVAR p)
polyTypeFTV (ForallTy tvs ty) = typeFTV ty Set.\\ (Set.fromList tvs)

typesFTV :: Ord (TyVAR p) => [Type p] -> Set (TyVAR p)
typesFTV = Set.unions . map typeFTV

typeFTV :: Ord (TyVAR p) => Type p -> Set (TyVAR p)
typeFTV (VarTy tv) = Set.singleton tv
typeFTV (ConTyIn _) = Set.empty           -- go into TyCON ?
typeFTV (AppTyIn t a) = typesFTV [t,a]
typeFTV (ConTy _ args) = typesFTV args    -- go into TyCON ?
typeFTV (PredTy pat ty _)  = patFTV pat `Set.union` typeFTV ty
typeFTV (FunTy dom rang) = domFTV dom `Set.union` typeFTV rang
typeFTV (ListTy ty) = typeFTV ty
typeFTV (TupleTy ds) = domsFTV ds
typeFTV (ParenTy ty) = typeFTV ty
typeFTV (MetaTy _)   = Set.empty

domsFTV :: Ord (TyVAR p) => [Dom p] -> Set (TyVAR p)
domsFTV = Set.unions . map domFTV

domFTV :: Ord (TyVAR p) => Dom p -> Set (TyVAR p)
domFTV (Dom Nothing ty Nothing) = typeFTV ty
domFTV (Dom (Just pat) ty _) = patFTV pat `Set.union` typeFTV ty
