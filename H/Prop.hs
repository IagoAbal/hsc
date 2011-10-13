{-# LANGUAGE PatternGuards  #-}
module H.Prop where

import H.Syntax

import Data.List  ( sort )


_True_ :: Prop p
_True_ = Con (BuiltinCon TrueCon)

_False_ :: Prop p
_False_ = Con (BuiltinCon FalseCon)

infixr .==>.

notP :: Prop p -> Prop p
notP (PrefixApp (Op (BoolOp NotB)) p) = p
notP p                                = PrefixApp (Op notOp) p

(.&&.), (.||.), (.==>.), (.<=>.) :: Prop p -> Prop p -> Prop p
p .&&. q = InfixApp p (Op andOp) q
p .||. q = InfixApp p (Op orOp) q
p .==>. q = InfixApp p (Op impOp) q
p .<=>. q = InfixApp p (Op iffOp) q

mkForall :: [Pat p] -> Prop p -> Prop p
mkForall [] prop = prop
mkForall ps prop = QP ForallQ ps prop

hypo :: Prop p -> Prop p -> Prop p
hypo p = (p .==>.)

-- | Splits a proposition into conjunctions
-- e.g. @splitAnd (p1 && p2 && ... && pN) == [p1,p2,...,pN]@
splitConj :: Prop p -> [Prop p]
splitConj (InfixApp p (Op (BoolOp AndB)) q)
  = splitConj p ++ splitConj q
splitConj p = [p]

conj :: [Prop p] -> Prop p
conj [] = _True_
conj ps = foldr1 (.&&.) ps

disj :: [Prop p] -> Prop p
disj [] = _False_
disj ps = foldr1 (.||.) ps

hypos :: [Prop p] -> Prop p -> Prop p
hypos [] p = p
hypos hs p = hypo (conj hs) p

mkConj :: [Prop p] -> Maybe (Prop p)
mkConj [] = Nothing
mkConj ps = Just $ foldr1 (.&&.) ps


filterProp :: (Prop p -> Bool) -> Prop p -> Maybe (Prop p)
filterProp p = mkConj . filter p . splitConj

oneOfInts :: IsPostTc p => Exp p -> [Integer] -> Prop p
oneOfInts t []  = _False_
oneOfInts t [n] = t .==. mkInt n
oneOfInts t ns  = disj $ build_prop $ sort ns
  where
    build_prop ns@(a:rest)
      | ns == [a..b] = [mkInt a .<=. t .&&. t .<=. mkInt b]
      | otherwise    = [t .==. mkInt a | a <- ns]
      where b = last rest

