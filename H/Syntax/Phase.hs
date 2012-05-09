{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  H.Syntax.Phase
-- Copyright   :  (c) Iago Abal 2011-2012
-- License     :  BSD3
--
-- Maintainer  :  Iago Abal, iago.abal@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--

module H.Syntax.Phase where



-- * Front-end phases

data Pr   -- ^ Parsing
data Rn   -- ^ Renaming
data Tc   -- ^ Type checking
data Ti   -- ^ Type inference

type family PhaseOf t
type instance PhaseOf [t] = PhaseOf t

-- ** Order between phases

class Lt a b where
  -- Lt is a transitive relation
instance Lt Pr Rn where
instance Lt Pr Tc where
instance Lt Pr Ti where
instance Lt Rn Tc where
instance Lt Rn Ti where
instance Lt Tc Ti where

class Le a b where
  --
instance Le Pr Pr where
instance Le Pr Rn where
instance Le Pr Tc where
instance Le Pr Ti where
instance Le Rn Rn where
instance Le Rn Tc where
instance Le Rn Ti where
instance Le Tc Tc where
instance Le Tc Ti where
instance Le Ti Ti where

class Gt a b where
instance Lt b a => Gt a b where

class Ge a b where
instance Le b a => Ge a b where

-- * None

data None p = None

type instance PhaseOf (None p) = p
