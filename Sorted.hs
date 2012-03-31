{-# LANGUAGE TypeOperators,
             MultiParamTypeClasses,
             FlexibleInstances
             #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Sorted where

import Data.Data


  -- | Sort annotation
data (:::) obj sort = (:::) { obj :: obj
                            , srt :: sort
                            }


class Sorted obj sort where
  sortOf :: obj -> sort

instance Sorted (obj ::: sort) sort where
  sortOf = srt



data TAU
data SIGMA

deriving instance Data TAU
deriving instance Typeable TAU
deriving instance Data SIGMA
deriving instance Typeable SIGMA
