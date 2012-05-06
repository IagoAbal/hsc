{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{- TODO: Implement proper coercion for inductive types and tuples.
E.g. [Int] ~l~> [Nat] should be something like forall x in l, Int ~x~> Nat
One possibility is to introduce a builtin 'all' function and proj_k for tuples.
-}
module H.Typecheck.TCC.Coerce where


import H.Syntax
import qualified H.Prop as P
import H.Typecheck.Utils

import Pretty
import Unique

import Control.Monad.Error


map_forall :: Monad m => [Var Ti] -> m [Prop Ti] -> m [Prop Ti]
map_forall xs = liftM (map $ mkForall xs)


coerce :: (MonadUnique m, MonadError Doc m) =>
              Exp Ti
              -> Type c Ti  -- ^ actual type
              -> Type c Ti  -- ^ expected type
              -> m [Prop Ti]

coerce t (ForallTy tvs1 ty1) (ForallTy tvs2 ty2) = do
  let typs = map VarTy tvs2
      t' = mkTyApp t typs
  ty1' <- subst_type [] (zip tvs1 typs) ty1
  coerce t' ty1' ty2 

coerce _t  (VarTy tv1)      (VarTy tv2) | tv1 == tv2
  = return []

coerce  t  (ConTy tc1 tys1) (ConTy tc2 tys2) | tc1 == tc2
  = coerceConTys t tys1 tys2
coerce  t  (ListTy ty1)     (ListTy ty2)
  = coerceListTys t ty1 ty2
coerce  t  (TupleTy ds1)    (TupleTy ds2)
  = coerceTupleTys t ds1 ds2

coerce t   ty1              ty2 | isSynTy ty1 = do
  Just ty1_def <- expandSyn ty1
  coerce t ty1_def ty2

coerce t   ty1              ty2 | isSynTy ty2 = do
  Just ty2_def <- expandSyn ty2
  coerce t ty1 ty2_def

coerce t   (PredTy pat1 ty1 mb_prop1) ty2 = do
  mb_prop1_t <- instPredTyProp t pat1 ty1 mb_prop1
  let intro_t_hypo = maybe id (map . P.hypo) mb_prop1_t
  liftM intro_t_hypo $ coerce t (tau2type ty1) ty2

coerce t  ty1 (PredTy pat2 ty2 mb_prop2) = do
  ty1_ty2_POs <- coerce t ty1 (tau2type ty2)
  mb_prop2_t <- instPredTyProp t pat2 ty2 mb_prop2
  let t_prop2_POs = case mb_prop2_t of
                        Nothing -> []
                        Just p2 -> [P.hypos ty1_ty2_POs $ p2]
  return (ty1_ty2_POs ++ t_prop2_POs)

coerce f (FunTy dom1 rang1) (FunTy dom2 rang2) = do
  x <- newVarId "x" (dom2type dom2)
  let v_x = Var x
  domain_POs <- map_forall [x] $ coerce v_x (dom2type dom2) (dom2type dom1)
  let f_x = mkApp f [v_x]
  rang1_x <- instFunTy (dom1,rang1) v_x
  rang2_x <- instFunTy (dom2,rang2) v_x
  range_POs <- liftM (map (P.hypos domain_POs)) $ coerce f_x rang1_x rang2_x
  return (domain_POs ++ range_POs)

coerce _t _ty1 _ty2 = undefined -- bug 


coerceTypes :: (MonadUnique m, MonadError Doc m) => [Tau Ti] -> [Tau Ti] -> m [Prop Ti]
coerceTypes [] [] = return []
coerceTypes (ty1:tys1) (ty2:tys2) = do
    -- TO DO: I may define a function for the individual case, like typePred...
    -- forall x
  t <- newVarId "t" (tau2sigma ty1)
  ty1_ty2_POs <- map_forall [t] $ coerce (Var t) ty1 ty2
  tys1_tys2_POs <- coerceTypes tys1 tys2
  return (ty1_ty2_POs ++ tys1_tys2_POs)
coerceTypes _tys1 _tys2 = undefined -- bug

-- For now we implement a basic version of coercion between ConTy types
-- so List Int ~xs~> List Nat will be equivalent to "forall x:Int, Int ~x~> Nat".
-- but this is something we should change in future.
coerceConTys :: (MonadUnique m, MonadError Doc m) => Exp Ti -> [Tau Ti] -> [Tau Ti] -> m [Prop Ti]
coerceConTys _t = coerceTypes

coerceListTys :: (MonadUnique m, MonadError Doc m) => Exp Ti -> Tau Ti -> Tau Ti -> m [Prop Ti]
coerceListTys _t ty1 ty2 = do
  t <- newVarId "t" (tau2sigma $ ty1)
  map_forall [t] $ coerce (Var t) ty1 ty2

-- We would need 'proj' functions to implement this properly
coerceTupleTys :: (MonadUnique m, MonadError Doc m) => Exp Ti -> [Dom Ti] -> [Dom Ti] -> m [Prop Ti]
coerceTupleTys _e = go
  where go []       []       = return []
        go (d1:ds1) (d2:ds2) = do
          x <- newVarId "x" (dom2type d1)
          let v_x = Var x
          d1_d2_POs <- map_forall [x] $ coerce v_x (dom2type d1) (dom2type d2)
          ds1_x <- instDoms v_x d1 ds1
          ds2_x <- instDoms v_x d2 ds2
          ds1_ds2_POs <- go ds1_x ds2_x
          return (d1_d2_POs ++ ds1_ds2_POs)
        go _ds1      _ds2    = undefined -- impossible
