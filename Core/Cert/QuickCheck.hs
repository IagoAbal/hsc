{-# LANGUAGE ImplicitParams #-}

module Core.Cert.QuickCheck where

import Core.Syntax
import Core.Syntax.Built
import Core.Eval
import Core.Cert.Supported

import Control.Applicative ( (<$>) )
import qualified Data.Map as Map
import qualified Test.QuickCheck as QC


aBool :: QC.Gen Exp
aBool = bool2exp <$> QC.arbitrary

anInt :: QC.Gen Exp
anInt = mkInt <$> QC.arbitrary

aNat :: QC.Gen Exp
aNat = QC.sized $ \n -> mkInt . abs <$> QC.arbitrary


typeGen :: Type c -> QC.Gen Exp
typeGen ty | ty == boolTy = aBool
           | ty == intTy  = anInt
           | ty == natTy  = aNat

param_ :: Var -> QC.Gen (Var,Exp)
param_ x = do
  t <- typeGen $ varType x
  return (x,t)

params_ :: [Var] -> QC.Gen [(Var,Exp)]
params_ = mapM param_

mkProperty :: Prop -> QC.Property
mkProperty (QP ForallQ xs p)
  = QC.forAll anEnv $ \env ->
      let ?env = Map.fromList env
        in val2bool $ eval p
  where anEnv = params_ xs

checkProp :: Prop -> IO ()
checkProp p
  | supProp p = QC.quickCheck $ mkProperty p
  | otherwise = print "Sorry, property not supported :-("
