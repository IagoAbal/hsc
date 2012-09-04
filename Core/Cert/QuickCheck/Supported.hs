{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}

module Core.Cert.QuickCheck.Supported
  ( toQuickProp
  , supProp )
  where

import Core.Syntax
import Core.Prop ( instFTV )

import Pretty
import Sorted ( sortOf )

import qualified Data.Set as Set

-- | Makes a proposition more suitable for quick-testing.
toQuickProp :: Prop -> Prop
toQuickProp p
  | Set.null $ ftvOf p = p
  | otherwise          = instFTV intTy p

supProp :: Module -> Prop -> Bool
supProp mod (QP ForallQ xs p)
  = supVars xs && supExp p
  where ?mod = mod
supProp _mod p  = supExp p

supVar :: (?mod :: Module) => Var -> Bool
supVar V{varType} = supType varType

supVars :: (?mod :: Module) => [Var] -> Bool
supVars = and . map supVar

supType :: (?mod :: Module) => Type c -> Bool
supType ty | ty == boolTy = True
supType ty | ty == intTy = True
supType ty | ty == natTy = True
supType ty | isSynTy ty = supType $ expandSyn ty
supType (ListTy ty) = supType ty
supType (TupleTy ds) = supDoms ds
supType (PredTy _ ty Nothing) = supType ty && isMuTy ty
supType (PredTy (VarPat _) ty (Just prop)) = supType ty && supExp prop
supType (ConTy tc tys) = True
--       and [ traceDoc (text "supType con=" <+> pretty con) $ supDoms doms
--           | con <- typeConstrs ?mod tc
--           , let (doms,_) = unFunTy $ instSigma (sortOf con) tys
--           ]
supType _other = False

supDom :: (?mod :: Module) => Dom -> Bool
supDom (Dom Nothing ty Nothing) = supType ty
supDom (Dom (Just (VarPat _)) ty (Just prop)) = supType ty && supExp prop
supDom _other = False

supDoms :: (?mod :: Module) => [Dom] -> Bool
supDoms = and . map supDom

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
supExp (LetP _ _ _) = True
supExp (QP _ _ _) = False
