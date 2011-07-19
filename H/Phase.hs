{-# LANGUAGE EmptyDataDecls,
             MultiParamTypeClasses,
             GADTs,
             FlexibleContexts
             #-}

module H.Phase where


-- * Front-end phases

data Pr    -- ^ Parsing
data Rn    -- ^ Renaming
data Tc    -- ^ Typechecking

-- ** Order between phases

class Lt a b where

instance Lt Pr Rn where
instance Lt Pr Tc where
instance Lt Rn Tc where


-- * PostTc

-- | Something that it is only known after typecheck.
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
