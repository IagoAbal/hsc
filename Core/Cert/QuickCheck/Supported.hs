{-# LANGUAGE NamedFieldPuns #-}

module Core.Cert.QuickCheck.Supported
  ( supProp )
  where

import Core.Syntax

import qualified Data.Set as Set



supProp :: Prop -> Bool
supProp (QP ForallQ xs p)
  = supVars xs && supExp p && fvExp p `Set.isSubsetOf` Set.fromList xs
supProp p  = supExp p

supVar :: Var -> Bool
supVar V{varType} = varType == boolTy || varType == intTy || varType == natTy

supVars :: [Var] -> Bool
supVars = and . map supVar

supExp :: Exp -> Bool
supExp (Var _) = True
supExp (Con _) = True
supExp (Lit _) = True
supExp (PrefixApp _ e) = supExp e
supExp (InfixApp e1 _ e2) = supExp e1 && supExp e2
supExp (App _ _) = False
supExp (TyApp _ _) = False
supExp (Lam _ _) = False
supExp (Let _ _) = False
supExp (TyLam _ _) = False
supExp (Ite _ g e1 e2) = supExp g && supExp e1 && supExp e2
supExp (If _ _) = False
supExp (Case _ _ _) = False
supExp (Tuple _ es) = and $ map supExp es
supExp (List _ es) = and $ map supExp es
supExp (Paren e) = supExp e
supExp (EnumFromTo _ _) = False
supExp (EnumFromThenTo _ _ _) = False
supExp (Coerc e _) = supExp e
supExp (LetP _ _ _) = False
supExp (QP _ _ _) = False
