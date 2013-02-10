
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module H.Syntax.MTV
  ( MTV(..) )
  where

import H.Syntax.AST
import H.Syntax.Phase

import Data.Set ( Set )
import qualified Data.Set as Set

#include "bug.h"


class MTV t where
  mtvOf :: t -> Set MetaTyVar

instance MTV t => MTV [t] where
  mtvOf = Set.unions . map mtvOf

instance MTV t => MTV (Maybe t) where
  mtvOf = maybe Set.empty mtvOf

instance MTV (Bind Tc) where
  mtvOf (FunBind _rec fun sig _ptctyps matches)
    = Set.unions [mtvOf fun, mtvOf sig, mtvOf matches]
  mtvOf (PatBind _loc pat rhs) = mtvOf pat `Set.union` mtvOf rhs

instance MTV (TypeSig Tc) where
  mtvOf NoTypeSig             = Set.empty
  mtvOf (TypeSig _loc polyty) = mtvOf polyty

instance MTV (Match Tc) where
  mtvOf (Match _loc pats rhs) = mtvOf pats `Set.union` mtvOf rhs

instance MTV (Var Tc) where
  mtvOf = mtvOf . varType

instance MTV (TcCon Tc) where
  mtvOf (tcConCon -> UserCon ucon) = mtvOf ucon
  mtvOf (tcConCon -> BuiltinCon _) = Set.empty
  mtvOf _other                     = impossible

instance MTV (Exp Tc) where
  mtvOf (Var x)   = mtvOf x
  mtvOf (Par x)   = mtvOf x
  mtvOf (Con con) = mtvOf con
  mtvOf (Op _) = Set.empty
  mtvOf (Lit _)   = Set.empty
  mtvOf (PrefixApp op e) = mtvOf op `Set.union` mtvOf e
  mtvOf (InfixApp e1 op e2) = mtvOf op `Set.union` mtvOf [e1,e2]
  mtvOf (App e1 e2) = mtvOf [e1,e2]
  mtvOf (TyApp e tys) = mtvOf e `Set.union` mtvOf tys
  mtvOf (Lam _loc pats rhs)
    = mtvOf pats `Set.union` mtvOf rhs
  mtvOf (Let bs body)
    = mtvOf bs `Set.union` mtvOf body
  mtvOf (TyLam _tvs body) = mtvOf body
  mtvOf (Ite ty g t e) = mtvOf [g,t,e] `Set.union` mtvOf ty
  mtvOf (If ty grhss) = mtvOf grhss `Set.union` mtvOf ty
  mtvOf (Case ty scrut alts)
    = Set.unions [mtvOf ty, mtvOf scrut, mtvOf alts]
  mtvOf (Tuple ty es) = mtvOf es `Set.union` mtvOf ty
  mtvOf (List ty es) = mtvOf es `Set.union` mtvOf ty
  mtvOf (Paren e) = mtvOf e
  mtvOf (LeftSection e _op) = mtvOf e
  mtvOf (RightSection _op e) = mtvOf e
  mtvOf (EnumFromTo e1 e2) = mtvOf [e1,e2]
  mtvOf (EnumFromThenTo e1 e2 e3) = mtvOf [e1,e2,e3]
  mtvOf (Coerc _loc e polyty) = mtvOf e `Set.union` mtvOf polyty
  mtvOf (LetP pat e prop) = mtvOf pat `Set.union` mtvOf [e,prop]
  mtvOf (QP _qt xs prop) = mtvOf xs `Set.union` mtvOf prop

instance MTV (Pat Tc) where
  mtvOf (VarPat x) = mtvOf x
  mtvOf (LitPat _) = Set.empty
  mtvOf (InfixCONSPat typ p1 p2) = mtvOf [p1,p2] `Set.union` mtvOf typ
  mtvOf (ConPat typs con ps) = mtvOf con `Set.union` mtvOf ps `Set.union` mtvOf typs
  mtvOf (TuplePat ty ps) = mtvOf ps `Set.union` mtvOf ty
  mtvOf (ListPat ty ps) = mtvOf ps `Set.union` mtvOf ty
  mtvOf (ParenPat p) = mtvOf p
  mtvOf (WildPat wild_var)     = mtvOf wild_var
  mtvOf (AsPat x p)  = mtvOf x `Set.union` mtvOf p

instance MTV (QVar Tc) where
  mtvOf (QVar x mb_ty) = mtvOf x `Set.union` mtvOf mb_ty

instance MTV (Alt Tc) where
  mtvOf (Alt _loc pat rhs) = mtvOf pat `Set.union` mtvOf rhs

instance MTV (Rhs Tc) where
  mtvOf (Rhs ty grhs whr)
    = mtvOf whr `Set.union` mtvOf grhs `Set.union` mtvOf ty

instance MTV (GRhs Tc) where
  mtvOf (UnGuarded e)   = mtvOf e
  mtvOf (Guarded grhss) = mtvOf grhss

instance MTV (GuardedRhss Tc) where
  mtvOf (GuardedRhss grhss elserhs)
    = Set.unions $ mtvOf elserhs : map mtvOf grhss

instance MTV (GuardedRhs Tc) where
  mtvOf (GuardedRhs _loc g e) = mtvOf [g,e]

instance MTV (Else Tc) where
  mtvOf NoElse        = Set.empty
  mtvOf (Else _loc e) = mtvOf e

instance MTV (Type c Tc) where
  mtvOf (VarTy _)      = Set.empty
  mtvOf (ConTy _ args) = mtvOf args
  mtvOf (PredTy pat ty mb_prop)
    = Set.unions [mtvOf pat, mtvOf ty,  mtvOf mb_prop]
  mtvOf (FunTy dom rang)
    = mtvOf dom `Set.union` mtvOf rang
  mtvOf (ListTy ty)  = mtvOf ty
  mtvOf (TupleTy ds) = mtvOf ds
  mtvOf (MetaTy mtv) = Set.singleton mtv
  mtvOf (ForallTy _tvs ty) = mtvOf ty
  mtvOf _other       = impossible

instance MTV (Dom Tc) where
  mtvOf (Dom Nothing ty Nothing) = mtvOf ty
  mtvOf (Dom (Just pat) ty mb_prop)
    = Set.unions [mtvOf pat, mtvOf ty, mtvOf mb_prop]
  mtvOf _other = impossible
