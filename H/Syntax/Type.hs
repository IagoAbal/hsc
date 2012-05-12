
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  H.Syntax.Type
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--

module H.Syntax.Type
  where


import H.Syntax.AST
import {-# SOURCE #-} H.Syntax.Expr
import H.Syntax.IsTc
import H.Syntax.Phase
import H.Syntax.Subst1 ( subst_type )

import Name
import Sorted
import Unique( MonadUnique(..), evalUnique )

import Data.IORef( newIORef )
import Control.Monad ( liftM )
import Control.Monad.IO.Class ( MonadIO(..) )

import Unsafe.Coerce ( unsafeCoerce )

#include "bug.h"



typeOf :: Sorted a (Type c p) => a -> Type c p
typeOf = sortOf

kindOf :: Sorted a Kind => a -> Kind
kindOf = sortOf


-- * Variables

mkTyVar :: Name -> Kind -> TyVar
mkTyVar nm ki = TyV nm ki False

-- ** Fresh variables

newTyVar :: MonadUnique m => String -> Kind -> m TyVar
newTyVar str ki = do
  name <- newName TyVarNS str
  return $ TyV name ki False

cloneTyVar :: MonadUnique m => TyVar -> m TyVar
cloneTyVar (TyV name ki isSk) = do
  name' <- newNameFrom name
  return $ TyV name' ki isSk

-- ** Skolemization

skoTyVar :: MonadUnique m => TyVar -> m TyVar
skoTyVar (TyV name kind False) = do
  name' <- newNameFrom name
  return (TyV name' kind True)
skoTyVar _other
  = bug "skoTyVar: already a skolem type variable"


-- ** Conversions

type2tau :: Type c p -> Tau p
type2tau (ForallTy _ _) = bug "type2tau: not a tau type"
type2tau ty             = unsafeCoerce ty

type2sigma :: Type c p -> Sigma p
type2sigma = unsafeCoerce

tau2sigma :: Tau p -> Sigma p
tau2sigma = type2sigma

tau2type :: Tau p -> Type c p
tau2type = unsafeCoerce

dom2type :: Ge p Tc => Dom p -> Type c p
dom2type (Dom Nothing ty Nothing)    = tau2type ty
dom2type (Dom (Just pat) ty mb_prop) = mkPredTy pat ty mb_prop
dom2type _other                      = impossible

type2dom :: Type c p -> Dom p
type2dom (ForallTy _ _) = bug "type2dom: not a tau type"
type2dom ty             = Dom Nothing (type2tau ty) Nothing


-- * Types

isVarTy :: Type c p -> Bool
isVarTy (VarTy _) = True
isVarTy _ty       = False

isFunTy :: IsTc p => Tau p -> Maybe (Dom p,Tau p)
isFunTy (FunTy d r)     = Just (d,r)
isFunTy (PredTy _ ty _) = isFunTy ty
isFunTy ty | isSynTy ty = isFunTy $ expandSyn ty
isFunTy _other          = Nothing

unFunTy :: IsTc p => Tau p -> ([Dom p],Tau p)
unFunTy ty
  | Just (d,t) <- isFunTy ty
  , (ds,r) <- unFunTy t
  = (d:ds,r)
  | otherwise
  = ([],ty)

splitFunTy :: IsTc p =>  Int -> Tau p -> ([Dom p],Tau p)
splitFunTy 0  ty = ([],ty)
splitFunTy n  ty
 | Just (a,t) <- isFunTy ty
 , let (as,r) = splitFunTy (n-1) t
 = (a:as,r)
splitFunTy _ _ty = bug "splitFunTy: insufficient arity"

funTyArity :: IsTc p => Tau p -> Int
funTyArity = length . fst . unFunTy

splitSigma :: Sigma p -> (TyParams p,Tau p)
splitSigma (ForallTy tvs tau) = (tvs,tau)
splitSigma ty                 = ([],type2tau ty)

quantifiedTyVars :: Sigma p -> [TyVAR p]
quantifiedTyVars (ForallTy tvs _) = tvs
quantifiedTyVars _other           = []

isSynTy :: (Ge p Tc, VAR p ~ Var p, TyCON p ~ TyCon p) => Type c p -> Bool
isSynTy (ConTy SynTyCon{} _) = True
isSynTy _other               = False

isMetaTy :: Type c Tc -> Bool
isMetaTy (MetaTy _) = True
isMetaTy _other     = False

mkAppTyIn :: (Lt p Tc, TyCON p ~ TyName p) => TyName p -> [Tau p] -> Type c p
mkAppTyIn tc args = tau2type $ foldl AppTyIn (ConTyIn tc) args

infixr @-->, -->

(@-->) :: Dom p -> Range p -> Type c p
(@-->) = FunTy

(-->) :: Tau p -> Tau p -> Type c p
arg --> res = type2dom arg @--> res

funTy :: [Dom p] -> Range p -> Type c p
funTy doms rang = tau2type $ foldr (@-->) rang doms

mkForallTy :: TyParams p -> Tau p -> Sigma p
mkForallTy []   tau = tau2sigma tau
mkForallTy typs tau = ForallTy typs tau

-- ** Subset types

mkPatTy :: Pat p -> Tau p -> Type c p
mkPatTy WildPatIn   ty = tau2type ty
mkPatTy (WildPat _) ty = tau2type ty
mkPatTy (VarPat _)  ty = tau2type ty
mkPatTy pat         ty = PredTy pat ty Nothing

mkPredTy :: Pat p -> Tau p -> Maybe (Prop p) -> Type c p
mkPredTy pat ty Nothing = mkPatTy pat ty
mkPredTy pat ty mb_prop = PredTy pat ty mb_prop

-- | Removes outermost predicate-types
mu_0 :: Tau p -> Tau p
mu_0 (PredTy _ ty _) = mu_0 ty
mu_0 ty              = ty

-- ** Domains

mkDom :: Pat p -> Tau p -> Prop p -> Dom p
mkDom pat ty prop = Dom (Just pat) ty (Just prop)

mkDomVar :: VAR p -> Tau p -> Prop p -> Dom p
mkDomVar x ty prop = mkDom (VarPat x) ty prop

mkPatDom :: Pat p -> Tau p -> Dom p
mkPatDom WildPatIn   ty = Dom Nothing ty Nothing
mkPatDom (WildPat _) ty = Dom Nothing ty Nothing
mkPatDom pat         ty = Dom (Just pat) ty Nothing

mkVarDom :: VAR p -> Tau p -> Dom p
mkVarDom x = mkPatDom (VarPat x)

-- ** Meta type variables

instTyVar :: (MonadUnique m, MonadIO m) => TyVar -> m (Type c Tc)
instTyVar (TyV name kind False) = do
  name' <- newNameFrom name
  ref <- liftIO $ newIORef Nothing
  return $ MetaTy $ MetaTyV name' kind ref
instTyVar _other
  = bug "instTyVar: cannot instantiate a skolem type variable"

newMetaTyVar :: (MonadUnique m, MonadIO m) => String -> Kind -> m MetaTyVar
newMetaTyVar str kind = do
  name <- newName TyVarNS str
  ref <- liftIO $ newIORef Nothing
  return $ MetaTyV name kind ref

newMetaTy :: (MonadUnique m, MonadIO m) => String -> Kind -> m (Tau Tc)
newMetaTy str kind = liftM MetaTy $ newMetaTyVar str kind


-- * Type constructors

instance Sorted BuiltinTyCon Kind where
  sortOf UnitTyCon = typeKi
  sortOf BoolTyCon = typeKi
  sortOf IntTyCon  = typeKi
  sortOf NatTyCon  = typeKi
  sortOf ListTyCon = typeKi ++> typeKi

instance Sorted (UTyNAME p) Kind => Sorted (TyName p) Kind where
  sortOf (UserTyCon utycon)    = sortOf utycon
  sortOf (BuiltinTyCon btycon) = sortOf btycon

instance Sorted (TyName p) Kind => Sorted (TyCon p) Kind where
  sortOf = sortOf . tyConName

instance Sorted MetaTyVar Kind where
  sortOf = mtvKind


unitTyName, boolTyName, intTyName, natTyName :: TyName p
unitTyName = BuiltinTyCon UnitTyCon
boolTyName = BuiltinTyCon BoolTyCon
intTyName  = BuiltinTyCon IntTyCon
natTyName  = BuiltinTyCon NatTyCon

mkSynTyCon :: (MonadUnique m, IsTc p) => UTyNAME p -> TyParams p -> Tau p -> m (TyCon p)
mkSynTyCon name typs rhs = do
  mb_us <- case typs of
               [] -> return Nothing
               _  -> liftM Just forkSupply
  return $ SynTyCon {
             tyConName   = UserTyCon name
           , tyConParams = typs
           , synTyConRhs = rhs
           , synTySupply = mb_us
           }

expandSyn :: IsTc p => Type c p -> Type c p
expandSyn (ConTy (SynTyCon _   [] rhs Nothing)   [])
  = tau2type rhs
expandSyn (ConTy (SynTyCon _ typs rhs (Just us)) args)
  = tau2type $ evalUnique (subst_type [] (zip typs args) rhs) us
expandSyn _other = bug "expandSyn: not an expandable type synonym"

unitTyCon, boolTyCon, intTyCon, natTyCon, listTyCon :: IsTc p => TyCon p
unitTyCon = AlgTyCon {
              tyConName = unitTyName
            , tyConCons = [unitCon]
            }
boolTyCon = AlgTyCon {
              tyConName   = boolTyName
            , tyConCons = [falseCon,trueCon]
            }
intTyCon  = AlgTyCon {
              tyConName   = intTyName
            , tyConCons = []  -- special case, infinite constructors!
            }
natTyCon  = SynTyCon {
              tyConName   = natTyName
            , tyConParams = []
            , synTyConRhs = mkPredTy (VarPat n) intTy (Just $ (Var n) .>=. zero)
            , synTySupply = Nothing
            }
  where n = mkVarId n_nm intTy
        n_nm = mkSysName (mkOccName VarNS "n") n_uniq
        n_uniq = -41
listTyCon = AlgTyCon {
              tyConName   = BuiltinTyCon ListTyCon
            , tyConCons = [nilCon,consCon]
            }

unitTy, boolTy, intTy, natTy :: IsTc p => Type c p
unitTy = ConTy unitTyCon []
boolTy = ConTy boolTyCon []
intTy  = ConTy intTyCon []
natTy  = ConTy natTyCon []


-- * Kinds

typeKi :: Kind
typeKi = TypeKi

infixr ++>

(++>) :: Kind -> Kind -> Kind
(++>) = FunKi

mkFunKi :: [Kind] -> Kind -> Kind
mkFunKi doms rang =  foldr (++>) rang doms
