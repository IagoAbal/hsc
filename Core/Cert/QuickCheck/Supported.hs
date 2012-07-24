{-# LANGUAGE NamedFieldPuns #-}

module Core.Cert.QuickCheck.Supported
  ( toQuickProp
  , supProp )
  where

import Core.Syntax
import Core.Prop ( instFTV ) 

import qualified Data.Set as Set

-- | Makes a proposition more suitable for quick-testing.
toQuickProp :: Prop -> Prop
toQuickProp p
  | Set.null $ ftvOf p = p
  | otherwise          = instFTV intTy p

supProp :: Prop -> Bool
supProp (QP ForallQ xs p)
  = supVars xs && supExp p
supProp p  = supExp p

supVar :: Var -> Bool
supVar V{varType} = supType varType

supVars :: [Var] -> Bool
supVars = and . map supVar

supType :: Type c -> Bool
supType ty | ty == boolTy = True
supType ty | ty == intTy = True
supType ty | ty == natTy = True
supType (ListTy ty) = supType ty
supType (PredTy (VarPat _) ty (Just prop)) = supType ty && supExp prop
supType _other = False

supExp :: Exp -> Bool
supExp (Var _) = True
supExp (Par _) = True
supExp (Con _) = True
supExp (Lit _) = True
supExp (PrefixApp _ e) = supExp e
supExp (InfixApp e1 _ e2) = supExp e1 && supExp e2
supExp (App _ _) = True
supExp (TyApp _ _) = True
supExp (Lam _ _) = True
supExp (Let _ _) = True
supExp (TyLam _ _) = True
supExp (Ite _ g e1 e2) = supExp g && supExp e1 && supExp e2
supExp (If _ _) = True
supExp (Case _ _ _) = True
supExp (Tuple _ es) = and $ map supExp es
supExp (List _ es) = and $ map supExp es
supExp (Paren e) = supExp e
supExp (EnumFromTo _ _) = True
supExp (EnumFromThenTo _ _ _) = True
supExp (Coerc e _) = supExp e
supExp (LetP _ _ _) = False
supExp (QP _ _ _) = False
