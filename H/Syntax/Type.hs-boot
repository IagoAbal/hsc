{-# LANGUAGE FlexibleContexts #-}

module H.Syntax.Type where

import H.Syntax.AST
import H.Syntax.IsTc
import H.Syntax.Phase

import Unique ( MonadUnique )


cloneTyVar :: MonadUnique m => TyVar -> m TyVar

type2tau :: Type c p -> Tau p
type2sigma :: Type c p -> Sigma p
tau2sigma :: Tau p -> Sigma p
tau2type :: Tau p -> Type c p
dom2type :: Ge p Tc => Dom p -> Type c p
type2dom :: Type c p -> Dom p

infixr @-->, -->

(@-->) :: Dom p -> Range p -> Type c p
(-->) :: Tau p -> Tau p -> Type c p

mkForallTy :: TyParams p -> Tau p -> Sigma p

mkPatTy :: Pat p -> Tau p -> Type c p
mkPredTy :: Pat p -> Tau p -> Maybe (Prop p) -> Type c p

mu_0 :: Tau p -> Tau p

-- ** Domains

mkDom :: Pat p -> Tau p -> Prop p -> Dom p
mkDomVar :: VAR p -> Tau p -> Prop p -> Dom p
mkPatDom :: Pat p -> Tau p -> Dom p
mkVarDom :: VAR p -> Tau p -> Dom p

unitTyCon, boolTyCon, intTyCon, natTyCon, listTyCon :: IsTc p => TyCon p

unitTy, boolTy, intTy, natTy :: IsTc p => Type c p


typeKi :: Kind

infixr ++>

(++>) :: Kind -> Kind -> Kind

mkFunKi :: [Kind] -> Kind -> Kind
