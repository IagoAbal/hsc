
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Prop where

import Core.Syntax.AST
import Core.Syntax.Built
import Core.Syntax.FreeVars
import Core.Syntax.FTV
import Core.Syntax.Subst1.Direct ( substExp )


import Data.Data ( Data )
import qualified Data.Generics.Uniplate.Data as G
import Data.List ( tails )
import Data.Set ( Set )
import qualified Data.Set as Set

import qualified Util.Set as Set


isNat :: Exp -> Maybe Bool
isNat (Var x) | varType x == natTy = Just True
isNat (isIntLit -> Just i) | i >= 0 = Just True
isNat (isPlus -> Just (e1,e2))
  | Just True <- isNat e1
  , Just True <- isNat e2
  = Just True
isNat (isMult -> Just (e1,e2))
  | Just True <- isNat e1
  , Just True <- isNat e2
  = Just True
isNat _other = Nothing


cleanup :: Exp -> Exp
cleanup = G.transform f . removeUncons
  where f (QP _qt _xs p)
          | p == mkTrue = mkTrue
          | p == mkFalse = mkFalse
        f (QP qt xs (QP qt1 ys p))
          | qt == qt1 = cleanup $ mkQP qt (xs++ys) p
        f (QP qt xs (isImp -> Just (p,QP qt1 ys q)))
          | qt == qt1 = cleanup $ mkQP qt (xs++ys) $ p .==>. q
        f (QP qt xs p)
          | xs /= xs' = mkQP qt xs' p
          where xs' = filterVars p xs
        f (isImp -> Just(p,(QP qt xs q)))
          | Set.fromList xs `Set.disjointWith` fvExp p = QP qt xs (p .==>. q)
        f (Let bs (QP qt xs p))
          | fvBndrs xs `Set.disjointWith` bsBinds bs = QP qt xs (Let bs p)
        f (Let _ e)
          | e == mkFalse = mkFalse
          | e == mkTrue = mkTrue
        f (CaseP def _ _ e)
          | e == mkTrue  && def     = mkTrue
          | e == mkFalse && not def = mkFalse
        f (Paren e@(Lit _)) = e
        f (Paren e@(Con _)) = e
        f (isNeg -> Just (isIntLit -> Just a)) = mkInt(-a)
        f (isNot -> Just e)
          | e == mkTrue = mkFalse
          | e == mkFalse = mkTrue
        f (isNot -> Just (isLe -> Just (e1,e2)))
          = e2 .<. e1
        f (isNot -> Just (isLt -> Just (e1,e2)))
          = e2 .<=. e1
        f (isLe -> Just (e1,e2))
          | Just a <- isIntLit e1
          , Just b <- isIntLit e2
          = bool2exp $ a <= b
          | e1 == e2 = mkTrue
        f (isLe -> Just (e1,e2))
          | Just 0 <- isIntLit e1
          , Just True <- isNat e2
          = mkTrue
        f (isOr -> Just (e1,e2))
          | e1 == e2      = e1
          | e1 == mkTrue  = mkTrue
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = e2
          | e2 == mkFalse = e1
        f (isAnd -> Just (e1,e2))
          | e1 == e2 = e1
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = e1
          | e1 == mkFalse = mkFalse
          | e2 == mkFalse = mkFalse
        f (isImp -> Just (e1,e2))
          | e1 == e2 = mkTrue
          | e1 == mkTrue  = e2
          | e2 == mkTrue  = mkTrue
          | e1 == mkFalse = mkTrue
          | e2 == mkFalse = mkNot e1
        f (isImp -> Just (p,isImp -> Just (q,r)))
          | p == q = q .==>. r
  -- this rule is mainly useful for QuickCheck
--           = (p .&&. q) .==>. r
        f (isEq -> Just (e1,e2))
          | e1 == e2 = mkTrue
        f (isNeq -> Just (e1,e2))
          | e1 == e2 = mkFalse
        f t = t

instFTV :: Tau -> Exp -> Exp
instFTV ty e = substExp [] s e
  where e_ftv = ftvOf e
        s = map (,ty) $ Set.toList e_ftv

-- * TCCs

-- tcc2prop :: TCC -> Prop
-- tcc2prop (CoercionTCC _ ctxt _ _ _ prop)
--   = cleanup $ mkTccCtxtProp ctxt prop
-- tcc2prop (CompletenessTCC _ ctxt prop)
--   = cleanup $ mkTccCtxtProp ctxt prop

mkTccPO :: TccPropCtxt -> Prop -> Prop
mkTccPO ctxt prop = cleanup $ mkTccCtxtProp ctxt prop

-- * Unconstrained terms

{- [Remove unconstrained terms]

In

  forall x0 _x xs ,
    x0 == (::) @'a _x xs ==> 1 + length @'a xs >= 0

is equivalent to

  forall xs , 1 + length @'a xs >= 0

since x0 is an unconstrained variable. The former is likely to give
some headaches to QuickCheck while generating values satisfying the
antecedent of the implication. The latter should be easily tested by
QuickCheck and can be also tested efficiently by a SMT solver encoding
'length' as an uninterpreted function.

-}

removeUncons :: Exp -> Exp
removeUncons e = let ?uvars = Set.empty in go e
  where go :: (?uvars :: Set Var) => Exp -> Exp
        go (QP ForallQ xs prop)
          | not (null xs_u)
          = let ?uvars = Set.fromList xs_u `Set.union` ?uvars
              in mkForall xs (go prop)
          where xs_u = map fst $ filter (\(y,ys) -> isUnconsVar (prop,ys) y) $
                        zip xs (tail $ tails xs)
        go (isOr -> Just (e1,e2))
          | isUnconsExp e1 = mkTrue
          | isUnconsExp e2 = mkTrue
        go (isAnd -> Just (e1,e2))
          | isUnconsExp e1 = e2
          | isUnconsExp e2 = e1
        go (isImp -> Just (e1,e2))
          | isUnconsExp e1 = e2
          | isUnconsExp e2 = mkTrue
        go t = G.descend go t

isUnconsVar :: Data t => t -> Var -> Bool
isUnconsVar t x = length [ y | Var y <- G.universeBi t, y == x ] == 1
                && isMuTy (varType x)

isUnconsExp :: (?uvars :: Set Var) => Exp -> Bool
isUnconsExp (Var x) = x `Set.member` ?uvars
isUnconsExp (Con _) = False
isUnconsExp (Lit _) = False
isUnconsExp (PrefixApp _op e) = isUnconsExp e
isUnconsExp (isOr -> Just (p,q)) = isUnconsExp p || isUnconsExp q
isUnconsExp (isAnd -> Just (p,q))
  | p == mkTrue = isUnconsExp q
  | q == mkTrue = isUnconsExp p
-- isUnconsExp (isEq -> Just (isVar -> Just x,e2))
--   | isMuTy (varType x) = x `Set.member` ?uvars
-- isUnconsExp t@(isEq -> Just (e1,e2))
--   | all isMuTy $ typesIn t = isUnconsExp e1 || isUnconsExp e2
isUnconsExp (isEq -> Just (e1,e2)) = isUnconsExp e1 || isUnconsExp e2
isUnconsExp _other = False
