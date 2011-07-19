{-# LANGUAGE TypeOperators,
             MultiParamTypeClasses,
             FlexibleInstances
             #-}

module Sorted where


  -- | Sort annotation
data (:::) obj sort = (:::) { obj :: obj
                            , srt :: sort
                            }


class Sorted obj sort where
  sortOf :: obj -> sort

instance Sorted (obj ::: sort) sort where
  sortOf = srt
