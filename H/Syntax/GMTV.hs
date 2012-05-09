
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}


module H.Syntax.GMTV
  ( MTVs
  , GMTV(..)
  ) where

import H.Syntax.AST
import H.Syntax.Expr ( lamRhs )
import H.Syntax.Phase

import Data.List ( nub )
import Data.Foldable ( foldMap )

#include "bug.h"

type MTVs = [MetaTyVar]

empty :: MTVs
empty = []

singleton :: MetaTyVar -> MTVs
singleton x = [x]

union :: MTVs -> MTVs -> MTVs
union x y = nub (x ++ y)

unions :: [MTVs] -> MTVs
unions = nub . concat

class GMTV t where
  gmtvOf :: t -> MTVs

instance GMTV t => GMTV [t] where
  gmtvOf = unions . map gmtvOf


instance GMTV (Pat Tc) where
  gmtvOf (VarPat x) = gmtvOf $ varType x
  gmtvOf (LitPat _) = empty
  gmtvOf (InfixCONSPat typ p1 p2) = gmtvOf typ `union` gmtvOf [p1,p2]
  gmtvOf (ConPat typs _con ps)    = gmtvOf typs `union` gmtvOf ps
  gmtvOf (TuplePat ty ps) = gmtvOf ty `union` gmtvOf ps
  gmtvOf (ListPat ty ps)  = gmtvOf ty `union` gmtvOf ps
  gmtvOf (ParenPat p) = gmtvOf p
  gmtvOf (WildPat x)  = gmtvOf $ varType x
  gmtvOf (AsPat x p)  = gmtvOf (varType x) `union` gmtvOf p

instance GMTV (QVar Tc) where
  gmtvOf (QVar x mb_ty) = gmtvOf (varType x) `union` (foldMap gmtvOf mb_ty)

-- NOTE
-- We don't want a proper GMTV computation, for instance, we don't want
-- to go "inside" predicates to get MTVs, because gmtvOf is used
-- to generalise a type, suppose the following
-- {x:?a|(\y:?b -> True) x} -> Int
-- we don't want to generalise ?b !!!

instance GMTV (Type c Tc) where
  gmtvOf (VarTy _) = empty
  gmtvOf (ConTy _ args) = gmtvOf args
  gmtvOf (PredTy _ ty _)  = gmtvOf ty
  gmtvOf (FunTy d r) = gmtvOf d `union` gmtvOf r
  gmtvOf (ListTy ty) = gmtvOf ty
  gmtvOf (TupleTy ds) = gmtvOf ds
  gmtvOf (MetaTy mtv) = singleton mtv
  gmtvOf (ForallTy _tvs ty) = gmtvOf ty
  gmtvOf _other = impossible

instance GMTV (Dom Tc) where  
  gmtvOf (Dom _ ty _) = gmtvOf ty


-- -- used for GoalDecl, that's why I named it gmtvOf and not expMTV...
-- -- It just look for forall-patterns
-- -- now it is limited, dirty... but it suffices... I will extend it
-- -- in future after thinking on it a little more.

instance GMTV (Exp Tc) where
  gmtvOf (Var _) = empty
  gmtvOf (Con _) = empty
  gmtvOf (Op _)  = empty
  gmtvOf (Lit _) = empty
  gmtvOf (PrefixApp _op e)    = gmtvOf e
  gmtvOf (InfixApp e1 _op e2) = gmtvOf [e1,e2]
  gmtvOf (App e1 e2) = gmtvOf [e1,e2]
  gmtvOf (TyApp e tys) = gmtvOf e `union` gmtvOf tys
  gmtvOf (Lam _loc _pats (lamRhs -> e)) = gmtvOf e
  gmtvOf (Let _bs e) = gmtvOf e
  gmtvOf (TyLam _tvs e) = gmtvOf e
  gmtvOf (Ite _ty _g _t _e) = empty
  gmtvOf (If _ty _grhss) = empty
  gmtvOf (Case _ty scrut _alts) = gmtvOf scrut
  gmtvOf (Tuple _ es) = gmtvOf es
  gmtvOf (List _ es) = gmtvOf es
  gmtvOf (Paren e) = gmtvOf e
  gmtvOf (LeftSection e _op) = gmtvOf e
  gmtvOf (RightSection _op e) = gmtvOf e
  gmtvOf (EnumFromTo e1 e2) = gmtvOf [e1,e2]
  gmtvOf (EnumFromThenTo e1 e2 e3) = gmtvOf [e1,e2,e3]
  gmtvOf (Coerc _loc e _ty) = gmtvOf e
  gmtvOf (QP _qt xs prop) = gmtvOf xs `union` gmtvOf prop
