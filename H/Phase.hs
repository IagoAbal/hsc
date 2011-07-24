{-# LANGUAGE EmptyDataDecls,
             MultiParamTypeClasses,
             GADTs,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances
             #-}

module H.Phase where


-- * Front-end phases

data Pr   -- ^ Parsing
data Rn   -- ^ Renaming
data Tc   -- ^ Type checking
data Ti   -- ^ Type inference
data Vc   -- ^ Generation of VCs

-- ** Order between phases

class Lt a b where
  -- Lt is a transitive relation
instance Lt Pr Rn where
instance Lt Pr Tc where
instance Lt Pr Ti where
instance Lt Pr Vc where
instance Lt Rn Tc where
instance Lt Rn Ti where
instance Lt Rn Vc where
instance Lt Tc Ti where
instance Lt Tc Vc where
instance Lt Ti Vc where

class Le a b where
  -- reflexivity
instance Le a a where
instance Lt a b => Le a b where

class Gt a b where
instance Lt b a => Gt a b where

class Ge a b where
instance Le b a => Ge a b where


-- * PostTc

-- | Something that it is only known after typechecking.
-- A common usage would be @PostTc p (Type p)@ to denote a type hole to be
-- filled by the typechecker.
data PostTc p a where
  NoPostTc :: Lt p Tc => PostTc p a
  PostTc   :: a -> PostTc Tc a

instance Eq a => Eq (PostTc p a) where
  NoPostTc   == NoPostTc   = True
  (PostTc x) == (PostTc y) = x == y
  _other1    == _other2    = False

instance Functor (PostTc p) where
  fmap _f NoPostTc   = NoPostTc
  fmap  f (PostTc x) = PostTc (f x)
