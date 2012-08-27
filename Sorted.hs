
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

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
