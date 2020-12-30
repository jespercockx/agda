-- | Missing functions for strict hashmaps

module Agda.Utils.HashMap.Strict
  ( module Data.HashMap.Strict
  , insertLookupWithKey
  ) where

import Prelude hiding (lookup)
import Data.Hashable
import Data.HashMap.Strict

insertLookupWithKey :: (Hashable k, Ord k)
                    => (k -> a -> a -> a) -> k -> a -> HashMap k a -> (Maybe a, HashMap k a)
insertLookupWithKey f k v m =
        v' `seq` (mold, insert k v' m)
      where
        (mold, v') =
            case lookup k m of
                Nothing -> (Nothing, v)
                Just vold -> (Just vold, f k v vold)
