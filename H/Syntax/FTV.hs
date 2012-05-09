
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module H.Syntax.FTV where

import H.Syntax.AST
import H.Syntax.Phase

import Name ( Name, OccName )

import Data.Foldable ( foldMap )
import Data.Set ( Set )
import qualified Data.Set as Set

#include "bug.h"


class FTV t where
  ftvOf :: (PhaseOf t ~ p, Ord (TyVAR p)) => t -> Set (TyVAR p)

class ( PhaseOf (VAR p) ~ p, FTV (VAR p)
      , PhaseOf (TcTAU p) ~ p, FTV (TcTAU p)
      , PhaseOf (TcTAUs p) ~ p, FTV (TcTAUs p) ) => HasFTV p where

instance HasFTV Pr
instance HasFTV Rn
instance HasFTV Tc
instance HasFTV Ti

instance (HasFTV p, PhaseOf t ~ p, PhaseOf [t] ~ p, FTV t) => FTV [t] where
  ftvOf = foldMap ftvOf

instance FTV (None p) where
  ftvOf = const Set.empty

instance FTV OccName where
  ftvOf = const Set.empty

instance FTV Name where
  ftvOf = const Set.empty

instance HasFTV p => FTV (Var p) where
  ftvOf = ftvOf . varType

instance HasFTV p => FTV (Pat p) where
  ftvOf (VarPat x) = ftvOf x
  ftvOf (LitPat _) = Set.empty
  ftvOf (InfixCONSPat _ty p1 p2) = ftvOf [p1,p2]
  ftvOf (ConPat tys _con ps) = ftvOf tys `Set.union` ftvOf ps
  ftvOf (TuplePat ty ps) = ftvOf ty `Set.union` ftvOf ps
  ftvOf (ListPat ty ps) = ftvOf ty `Set.union` ftvOf ps
  ftvOf (ParenPat p) = ftvOf p
  ftvOf WildPatIn     = Set.empty
  ftvOf (WildPat x) = ftvOf x
  ftvOf (AsPat x p)  = ftvOf x `Set.union` ftvOf p

instance HasFTV p => FTV (Type c p) where
  ftvOf (VarTy tv)  = Set.singleton tv
  ftvOf (ConTyIn _) = Set.empty
  ftvOf (AppTyIn t a) = ftvOf [t,a]
  ftvOf (ConTy _ args) = ftvOf args
  ftvOf (PredTy pat ty _)  = ftvOf pat `Set.union` ftvOf ty
  ftvOf (FunTy d r) = ftvOf d `Set.union` ftvOf r
  ftvOf (ListTy ty) = ftvOf ty
  ftvOf (TupleTy ds) = ftvOf ds
  ftvOf (ParenTy ty) = ftvOf ty
  ftvOf (MetaTy _)   = Set.empty
  ftvOf (ForallTy tvs ty) = ftvOf ty Set.\\ (Set.fromList tvs)

instance HasFTV p => FTV (Dom p) where
  ftvOf (Dom Nothing ty Nothing) = ftvOf ty
  ftvOf (Dom (Just pat) ty _) = ftvOf pat `Set.union` ftvOf ty
  ftvOf _other = impossible
