
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module Core.Cert.QuickCheck
  ( checkProp )
  where

import Core.Cert.QuickCheck.Supported

import Core.Syntax
import Core.Eval

import Pretty
import Sorted ( sortOf )

import Control.Applicative ( (<$>) )
import qualified Data.Map as Map
import qualified Test.QuickCheck as QC

#include "bug.h"


aBool :: QC.Gen Exp
aBool = bool2exp <$> QC.arbitrary

anInt :: QC.Gen Exp
anInt = mkInt <$> QC.arbitrary

aNat :: QC.Gen Exp
aNat = mkInt . abs <$> QC.arbitrary

aList :: (?mod :: Module, ?env :: [(Var,Exp)]) => Tau -> QC.Gen Exp
aList ty = List ty <$> QC.listOf (typeGen ty)

aPredTy :: (?mod :: Module, ?env :: [(Var,Exp)]) => Var -> Tau -> Prop -> QC.Gen Exp
aPredTy x ty prop
  = QC.suchThat (typeGen ty) (\e -> val2bool $ eval ?mod ((x,e) : ?env) prop)

aPat :: (?mod :: Module, ?env :: [(Var,Exp)]) => Pat -> QC.Gen (Exp,[(Var,Exp)])
aPat (VarPat x) = do
  e <- typeGen $ varTau x
  return (e,[(x,e)])
aPat (LitPat lit) = return (Lit lit,[])
aPat (ConPat typs con ps) = do
  (es,ps_env) <- aPats ps
  return (instCon con typs es,ps_env)
aPat (TuplePat ty ps) = do
  (es,ps_env) <- aPats ps
  return (Tuple ty es,ps_env)
aPat (ParenPat p) = do
  (e,p_env) <- aPat p
  return (Paren e,p_env)

aPats :: (?mod :: Module, ?env :: [(Var,Exp)]) => [Pat] -> QC.Gen ([Exp],[(Var,Exp)])
aPats [] = return ([],[])
aPats (p:ps) = do
  (e,p_env) <- aPat p
  let ?env = p_env ++ ?env
  (es,ps_env) <- aPats ps
  return (e:es,p_env++ps_env)

aPatTy :: (?mod :: Module, ?env :: [(Var,Exp)]) => Pat -> Tau -> QC.Gen Exp
aPatTy pat ty | isMuTy ty = fst <$> aPat pat

aTupleTy :: (?mod :: Module, ?env :: [(Var,Exp)]) => Tau -> [Dom] -> QC.Gen Exp
aTupleTy ty doms = Tuple ty <$> aDoms doms

aDataTy :: (?mod :: Module, ?env :: [(Var,Exp)]) => TyCon -> [Tau] -> QC.Gen Exp
aDataTy tycon tys
  = QC.oneof $ map (\con -> aCon con tys) constrs
  where constrs = typeConstrs ?mod tycon

aCon :: (?mod :: Module, ?env :: [(Var,Exp)]) => Con -> [Tau] -> QC.Gen Exp
aCon con tys = instCon con tys <$> aDoms doms
  where (doms,_) = unFunTy $ instSigma (sortOf con) tys

aDoms :: (?mod :: Module, ?env :: [(Var,Exp)]) => [Dom] -> QC.Gen [Exp]
aDoms [] = return []
aDoms (Dom Nothing ty Nothing:ds) = do
  a <- typeGen ty
  as <- aDoms ds
  return (a:as)
aDoms (d@(Dom (Just (VarPat x)) _ _):ds) = do
  a <- typeGen $ dom2type d
  let ?env = (x,a) : ?env
  as <- aDoms ds
  return (a:as)
aDoms (_d:_) = traceDoc (text "aDoms dom=" <> pretty _d) $ bug "unsupported domain-type"


typeGen :: (?mod :: Module, ?env :: [(Var,Exp)]) => Tau -> QC.Gen Exp
typeGen ty | ty == boolTy = aBool
           | ty == intTy  = anInt
           | ty == natTy  = aNat
typeGen ty | isSynTy ty = typeGen $ expandSyn ty
typeGen (ListTy ty) = aList ty
typeGen ty@(TupleTy ds) = aTupleTy ty ds
typeGen (PredTy pat ty Nothing) = aPatTy pat ty
typeGen (PredTy (VarPat x) ty (Just prop)) = aPredTy x ty prop
typeGen (ConTy tc tys) = aDataTy tc tys
typeGen _ty = bug "unsupported type"

param_ :: (?mod :: Module, ?env :: [(Var,Exp)]) => Var -> QC.Gen (Var,Exp)
param_ x = do
  t <- typeGen $ varTau x
  {- traceDoc (text $ "param " ++ show (x,t)) $ do -}
  return (x,t)

params_ :: (?mod :: Module, ?env :: [(Var,Exp)]) => [Var] -> QC.Gen [(Var,Exp)]
params_ [] = return []
params_ (x:xs) = do
  p <- param_ x
  let ?env = p : ?env
  ps <- params_ xs
  return (p:ps)

mkProperty :: Module -> Prop -> QC.Property
mkProperty mod (QP ForallQ xs p)
  = QC.forAll anEnv $ \env ->
      val2bool $ eval mod env p
  where anEnv = let ?mod = mod
                    ?env = []
                  in params_ xs
mkProperty _mod _other = bug "mkProperty: unsupported property"

checkGround :: Module -> Prop -> IO ()
checkGround mod p
  | val2bool $ eval mod [] p = putStrLn "Q.E.D."
  | otherwise                = putStrLn "Invalid!"

checkProp :: Module -> Prop -> IO ()
checkProp mod p@(QP _ _ _)
  | supProp mod p' = QC.quickCheck $ mkProperty mod p'
  | otherwise = traceDoc (pretty p') $ putStrLn "Sorry, property not supported :-("
  where p' = toQuickProp p
checkProp mod p
  | supProp mod p' = checkGround mod p'
  | otherwise  = traceDoc (pretty p') $ putStrLn "Sorry, property not supported :-("
  where p' = toQuickProp p
