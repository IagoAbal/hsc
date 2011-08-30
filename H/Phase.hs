{-# LANGUAGE EmptyDataDecls,
             MultiParamTypeClasses,
             GADTs,
             FlexibleContexts,
             FlexibleInstances,
             UndecidableInstances
             #-}

module H.Phase where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable


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
  --
instance Le Pr Pr where
instance Le Pr Rn where
instance Le Pr Tc where
instance Le Pr Ti where
instance Le Pr Vc where
instance Le Rn Rn where
instance Le Rn Tc where
instance Le Rn Ti where
instance Le Rn Vc where
instance Le Tc Tc where
instance Le Tc Ti where
instance Le Tc Vc where
instance Le Ti Vc where
instance Le Ti Ti where
instance Le Vc Vc where

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
  PostTc   :: Ge p Tc => a -> PostTc p a

instance Eq a => Eq (PostTc p a) where
  NoPostTc   == NoPostTc   = True
  (PostTc x) == (PostTc y) = x == y
  _other1    == _other2    = False

instance Functor (PostTc p) where
  fmap _f NoPostTc   = NoPostTc
  fmap  f (PostTc x) = PostTc (f x)

instance Foldable (PostTc p) where
  foldMap _f NoPostTc  = mempty
  foldMap f (PostTc x) = f x

instance Traversable (PostTc p) where
  traverse f NoPostTc   = pure NoPostTc
  traverse f (PostTc x) = PostTc <$> f x
