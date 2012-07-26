
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module Core.Cert.QuickCheck
  ( checkProp )
  where

import Core.Cert.QuickCheck.Supported

import Core.Syntax
import Core.Eval

import Pretty

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

aList :: (?mod :: Module) => Tau -> QC.Gen Exp
aList ty = List ty <$> QC.listOf (typeGen ty)

aPredTy :: (?mod :: Module) => Var -> Tau -> Prop -> QC.Gen Exp
aPredTy x ty prop
  = QC.suchThat (typeGen ty) (\e -> val2bool $ eval ?mod [(x,e)] prop)

typeGen :: (?mod :: Module) => Type c -> QC.Gen Exp
typeGen ty | ty == boolTy = aBool
           | ty == intTy  = anInt
           | ty == natTy  = aNat
typeGen ty | isSynTy ty = typeGen $ expandSyn ty
typeGen (ListTy ty) = aList ty
typeGen (PredTy (VarPat x) ty (Just prop)) = aPredTy x ty prop
typeGen _ty = bug "unsupported type"

param_ :: (?mod :: Module) => Var -> QC.Gen (Var,Exp)
param_ x = do
  t <- typeGen $ varType x
  return (x,t)

params_ :: (?mod :: Module) => [Var] -> QC.Gen [(Var,Exp)]
params_ = mapM param_

mkProperty :: Module -> Prop -> QC.Property
mkProperty mod (QP ForallQ xs p)
  = QC.forAll anEnv $ \env ->
      val2bool $ eval mod env p
  where anEnv = let ?mod = mod in params_ xs
mkProperty _mod _other = bug "mkProperty: unsupported property"

checkGround :: Module -> Prop -> IO ()
checkGround mod p
  | val2bool $ eval mod [] p = putStrLn "Q.E.D."
  | otherwise                = putStrLn "Invalid"

checkProp :: Module -> Prop -> IO ()
checkProp mod p@(QP _ _ _)
  | supProp p' = QC.quickCheck $ mkProperty mod p'
  | otherwise = traceDoc (pretty p') $ putStrLn "Sorry, property not supported :-("
  where p' = toQuickProp p
checkProp mod p
  | supProp p' = checkGround mod p'
  | otherwise  = traceDoc (pretty p') $ putStrLn "Sorry, property not supported :-("
  where p' = toQuickProp p
