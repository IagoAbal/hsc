
module H.Prop where

import H.Syntax

import Unique


_True_ :: Prop p
_True_ = Con (BuiltinCon TrueCon)

_False_ :: Prop p
_False_ = Con (BuiltinCon FalseCon)

infixr .==>.

(.&&.), (.||.), (.==>.), (.<=>.) :: Prop p -> Prop p -> Prop p
p .&&. q = InfixApp p (Op andOp) q
p .||. q = InfixApp p (Op orOp) q
p .==>. q = InfixApp p (Op impOp) q
p .<=>. q = InfixApp p (Op iffOp) q

hypo :: Prop p -> Prop p -> Prop p
hypo p = (p .==>.)

-- | Splits a proposition into conjunctions
-- e.g. @splitAnd (p1 && p2 && ... && pN) == [p1,p2,...,pN]@
splitConj :: Prop p -> [Prop p]
splitConj (InfixApp p (Op (BoolOp AndB)) q)
  = splitConj p ++ splitConj q
splitConj p = [p]

conj :: [Prop p] -> Prop p
conj = foldr (.&&.) _True_

hypos :: [Prop p] -> Prop p -> Prop p
hypos [] p = p
hypos hs p = hypo (conj hs) p

mkConj :: [Prop p] -> Maybe (Prop p)
mkConj [] = Nothing
mkConj ps = Just $ foldr1 (.&&.) ps


filterProp :: (Prop p -> Bool) -> Prop p -> Maybe (Prop p)
filterProp pred = mkConj . filter pred . splitConj

