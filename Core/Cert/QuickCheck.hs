
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module Core.Cert.QuickCheck
  ( checkProp )
  where

import Core.Cert.QuickCheck.Supported

import Core.Syntax
import Core.Eval

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


typeGen :: Type c -> QC.Gen Exp
typeGen ty | ty == boolTy = aBool
           | ty == intTy  = anInt
           | ty == natTy  = aNat
typeGen _ty = bug "unsupported type"

param_ :: Var -> QC.Gen (Var,Exp)
param_ x = do
  t <- typeGen $ varType x
  return (x,t)

params_ :: [Var] -> QC.Gen [(Var,Exp)]
params_ = mapM param_

mkProperty :: Module -> Prop -> QC.Property
mkProperty mod (QP ForallQ xs p)
  = QC.forAll anEnv $ \env ->
      val2bool $ eval mod env p
  where anEnv = params_ xs
mkProperty _mod _other = bug "mkProperty: unsupported property"

checkProp :: Module -> Prop -> IO ()
checkProp mod p
  | supProp p = QC.quickCheck $ mkProperty mod p
  | otherwise = putStrLn "Sorry, property not supported :-("
