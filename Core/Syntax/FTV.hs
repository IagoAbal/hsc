{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Core.Syntax.FTV where

import Core.Syntax.AST

import Data.Foldable ( foldMap )
import Data.Set ( Set )
import qualified Data.Set as Set

#include "bug.h"


class FTV t where
  ftvOf :: t -> Set TyVar

instance FTV t => FTV [t] where
  ftvOf = foldMap ftvOf
  
instance FTV t => FTV (Maybe t) where
  ftvOf = foldMap ftvOf

instance FTV Var where
  ftvOf = ftvOf . varType

instance FTV Bind where
  ftvOf (FunBind _ _f tvs _xs rhs) = ftvOf rhs Set.\\ Set.fromList tvs

instance FTV Exp where
  ftvOf (Var x) = ftvOf x
  ftvOf (Con _) = Set.empty
  ftvOf (Lit _) = Set.empty
  ftvOf (PrefixApp op e) = ftvOf op `Set.union` ftvOf e
  ftvOf (InfixApp e1 op e2) = Set.unions [ftvOf e1, ftvOf op, ftvOf e2]
  ftvOf (App e1 e2) = ftvOf [e1,e2]
  ftvOf (TyApp e tys) = ftvOf e `Set.union` ftvOf tys
  ftvOf (Lam xs rhs) = ftvOf xs `Set.union` ftvOf rhs
  ftvOf (Let bs e) = ftvOf bs `Set.union` ftvOf e
  ftvOf (TyLam tvs e) = ftvOf e Set.\\ Set.fromList tvs
  ftvOf (Ite _ty g e1 e2) = ftvOf [g,e1,e2]
  ftvOf (If _ty grhss) = ftvOf grhss
  ftvOf (Case _ty scrut alts) = ftvOf scrut `Set.union` ftvOf alts
  ftvOf (Tuple _ty es) = ftvOf es
  ftvOf (List _ty es) = ftvOf es
  ftvOf (Paren e) = ftvOf e
  ftvOf (EnumFromTo e1 e2) = ftvOf [e1,e2]
  ftvOf (EnumFromThenTo e1 e2 e3) = ftvOf [e1,e2,e3]
  ftvOf (Coerc e _ty) = ftvOf e
  ftvOf (LetP pat e prop) = Set.unions [ftvOf pat, ftvOf e, ftvOf prop]
  ftvOf (QP _qt xs prop) = ftvOf xs `Set.union` ftvOf prop

instance FTV OpExp where
  ftvOf (OpExp tys _op) = ftvOf tys

instance FTV Rhs where
 ftvOf (Rhs ty e) = ftvOf ty `Set.union` ftvOf e

instance FTV GuardedRhss where
  ftvOf (GuardedRhss grhss mb_else)
    = ftvOf grhss `Set.union` ftvOf mb_else

instance FTV GuardedRhs where
  ftvOf (GuardedRhs g e) = ftvOf [g,e]

instance FTV Alt where
  ftvOf (Alt pat rhs) = ftvOf pat `Set.union` ftvOf rhs

instance FTV Pat where
  ftvOf (VarPat x) = ftvOf x
  ftvOf (LitPat _) = Set.empty
  ftvOf (ConPat tys _con ps) = ftvOf tys `Set.union` ftvOf ps
  ftvOf (TuplePat ty ps) = ftvOf ty `Set.union` ftvOf ps
  ftvOf (ParenPat p) = ftvOf p

instance FTV (Type c) where
  ftvOf (VarTy tv)  = Set.singleton tv
  ftvOf (ConTy _ args) = ftvOf args
  ftvOf (PredTy pat ty prop)
    = Set.unions [ftvOf pat, ftvOf ty, ftvOf prop]
  ftvOf (FunTy d r) = ftvOf d `Set.union` ftvOf r
  ftvOf (ListTy ty) = ftvOf ty
  ftvOf (TupleTy ds) = ftvOf ds
  ftvOf (ForallTy tvs ty) = ftvOf ty Set.\\ (Set.fromList tvs)

instance FTV Dom where
  ftvOf (Dom Nothing ty Nothing) = ftvOf ty
  ftvOf (Dom (Just pat) ty _) = ftvOf pat `Set.union` ftvOf ty
  ftvOf _other = impossible
