{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      :  H.Syntax.FV
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- FV and BV
-- Note that types inferred during type-checking are not considered for
-- this purpose. This should be OK for now but it would be nice to
-- fix this in the future, since a type predicate may contain references
-- to global variables that won't be detected otherwise.

module H.Syntax.FV where

import H.Syntax.AST

import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Foldable

#include "bug.h"



-- * Binds

fvBind :: Ord (VAR p) => Bind p -> Set (VAR p)
fvBind (FunBind _rec fun sig _typs matches)
  = fvTypeSig sig `Set.union` (Set.delete fun $ fvMatches matches)
    -- NB: A pattern-binding cannot be recursive
fvBind (PatBind _loc pat rhs) = fvPat pat `Set.union` fvRhs rhs

fvBinds :: Ord (VAR p) => [Bind p] -> Set (VAR p)
fvBinds = foldMap fvBind

bsBind :: Ord (VAR p) => Bind p -> Set (VAR p)
bsBind (FunBind _rec fun _sig _ptctyps _matches) = Set.singleton fun
bsBind (PatBind _loc pat _rhs)                   = bsPat pat

bsBinds :: Ord (VAR p) => [Bind p] -> Set (VAR p)
bsBinds = foldMap bsBind

fvTypeSig :: Ord (VAR p) => TypeSig p -> Set (VAR p)
fvTypeSig NoTypeSig         = Set.empty
fvTypeSig (TypeSig _loc ty) = fvType ty

fvMatch :: Ord (VAR p) => Match p -> Set (VAR p)
fvMatch (Match _loc pats rhs)
  = fvPats pats `Set.union` (fvRhs rhs Set.\\ bsPats pats)

fvMatches :: Ord (VAR p) => [Match p] -> Set (VAR p)
fvMatches = foldMap fvMatch


-- * Expressions

fvExp :: Ord (VAR p) => Exp p -> Set (VAR p)
fvExp (Var x)    = Set.singleton x
fvExp (Par _)    = Set.empty
fvExp (Con _con) = Set.empty
fvExp (Op _op)   = Set.empty
fvExp (Lit _lit) = Set.empty
fvExp ElseGuard  = Set.empty
fvExp (PrefixApp _op e)    = fvExp e
fvExp (InfixApp e1 _op e2) = fvExps [e1,e2]
fvExp (App e1 e2)          = fvExps [e1,e2]
fvExp (TyApp e tys)        = fvExp e `Set.union` fvTypes tys
fvExp (Lam _loc pats rhs)
  = fvPats pats `Set.union` (fvRhs rhs Set.\\ bsPats pats)
fvExp (Let bs body)
  = fvBinds bs `Set.union` (fvExp body Set.\\ bsBinds bs)
fvExp (TyLam _tvs e)       = fvExp e
fvExp (Ite _ty g e1 e2)    = fvExps [g,e1,e2]
fvExp (If _ty grhss)       = fvGuardedRhss grhss
fvExp (Case _ty scrut alts) = fvExp scrut `Set.union` fvAlts alts
fvExp (Tuple _ty es)       = fvExps es
fvExp (List _ty es)        = fvExps es
fvExp (Paren e)            = fvExp e
fvExp (LeftSection e _op)  = fvExp e
fvExp (RightSection _op e) = fvExp e
fvExp (EnumFromTo e1 e2)   = fvExps [e1,e2]
fvExp (EnumFromThenTo e1 e2 e3) = fvExps [e1,e2,e3]
fvExp (Coerc _loc e ty)    = fvExp e `Set.union` fvType ty
fvExp (LetP pat e prop)
  = fvExp e `Set.union` (fvExp prop Set.\\ bsPat pat)
fvExp (QP _qt xs p)
  = fvQVars xs `Set.union` (fvExp p Set.\\ bsQVars xs)

fvExps :: Ord (VAR p) => [Exp p] -> Set (VAR p)
fvExps = foldMap fvExp

fvMaybeExp :: Ord (VAR p) => Maybe (Exp p) -> Set (VAR p)
fvMaybeExp = maybe Set.empty fvExp

fvAlt :: Ord (VAR p) => Alt p -> Set (VAR p)
fvAlt (Alt _loc pat rhs) = fvPat pat `Set.union` (fvRhs rhs Set.\\ bsPat pat)

fvAlts :: Ord (VAR p) => [Alt p] -> Set (VAR p)
fvAlts = foldMap fvAlt

fvQVar :: Ord (VAR p) => QVar p -> Set (VAR p)
fvQVar (QVar _x mb_ty) = foldMap fvType mb_ty

fvQVars :: Ord (VAR p) => [QVar p] -> Set (VAR p)
fvQVars = foldMap fvQVar

bsQVar :: Ord (VAR p) => QVar p -> Set (VAR p)
bsQVar (QVar x _mb_ty) = Set.singleton x

bsQVars :: Ord (VAR p) => [QVar p] -> Set (VAR p)
bsQVars = foldMap bsQVar

-- ** Right hand side

fvRhs :: Ord (VAR p) => Rhs p -> Set (VAR p)
fvRhs (Rhs _ grhs whr)
  = fvBinds whr `Set.union` (fvGRhs grhs Set.\\ bsBinds whr)

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


-- * Patterns

fvPat :: Ord (VAR p) => Pat p -> Set (VAR p)
  -- TODO: I think it should be 'fvPolyType $ varType x' but that would
  -- require to fix the algorithm to work just with 'Var p';
  -- other way would be to use type-classes... but it may have problems.
fvPat (VarPat _) = Set.empty
fvPat (LitPat _) = Set.empty
fvPat (InfixCONSPat _ p1 p2) = fvPats [p1,p2]
fvPat (ConPat _ _con ps) = fvPats ps
fvPat (TuplePat _ ps) = fvPats ps
fvPat (ListPat _ ps)  = fvPats ps
fvPat (ParenPat p)    = fvPat p
fvPat WildPatIn       = Set.empty
fvPat (WildPat _)     = Set.empty
fvPat (AsPat _x p)    = fvPat p

fvPats :: Ord (VAR p) => [Pat p] -> Set (VAR p)
fvPats = foldMap fvPat

bsPat :: Ord (VAR p) => Pat p -> Set (VAR p)
bsPat (VarPat x) = Set.singleton x
bsPat (LitPat _) = Set.empty
bsPat (InfixCONSPat _ p1 p2) = bsPats [p1,p2]
bsPat (ConPat _ _con ps) = bsPats ps
bsPat (TuplePat _ ps) = bsPats ps
bsPat (ListPat _ ps) = bsPats ps
bsPat (ParenPat p) = bsPat p
bsPat WildPatIn      = Set.empty
bsPat (WildPat wild_var)      = Set.singleton wild_var
bsPat (AsPat x p)  = Set.insert x $ bsPat p

bsPats :: Ord (VAR p) => [Pat p] -> Set (VAR p)
bsPats = foldMap bsPat


-- * Types

fvTypes :: Ord (VAR p) => [Type c p] -> Set (VAR p)
fvTypes = foldMap fvType

fvType :: Ord (VAR p) => Type c p -> Set (VAR p)
fvType (VarTy _) = Set.empty
fvType (ConTyIn _) = Set.empty
fvType (AppTyIn a b) = fvTypes [a,b]
fvType (ConTy _ args) = fvTypes args
fvType (PredTy pat ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)
fvType (FunTy d r) = fvDom d `Set.union` (fvType r Set.\\ bsDom d)
fvType (ListTy ty) = fvType ty
fvType (TupleTy ds) = fvDoms ds
fvType (ParenTy ty) = fvType ty
  -- this case may be tricky ...
fvType (MetaTy _) = Set.empty
fvType (ForallTy _tvs ty) = fvType ty

fvDoms :: Ord (VAR p) => [Dom p] -> Set (VAR p)
fvDoms []     = Set.empty
fvDoms (d:ds) = fvDom d `Set.union` (fvDoms ds Set.\\ bsDom d)

fvDom :: Ord (VAR p) => Dom p -> Set (VAR p)
fvDom (Dom Nothing ty Nothing) = fvType ty
fvDom (Dom (Just pat) ty mbprop)
  = fvType ty `Set.union` (fvMaybeExp mbprop Set.\\ bsPat pat)
fvDom _other = impossible

bsDom :: Ord (VAR p) => Dom p -> Set (VAR p)
bsDom (Dom mbpat _ty _mbprop) = maybe Set.empty bsPat mbpat
