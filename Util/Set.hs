module Util.Set where

import Data.Set ( Set )
import qualified Data.Set as Set


-- | Determines if two sets are disjoint.
disjointWith :: Ord a => Set a -> Set a -> Bool
disjointWith s1 s2 = Set.null (s1 `Set.intersection` s2)
