{-# LANGUAGE DeriveGeneric      #-}

-- | A strict version of the list type
--
--   Import qualified, as in
--   @
--     import qualified Agda.Utils.List.Strict as Strict
--   @

module Agda.Utils.List.Strict where

import Prelude hiding (reverse)
import qualified Prelude as Lazy

import Control.DeepSeq (NFData (..))
import Data.Binary (Binary (..))
import Data.Data (Data (..))
import GHC.Generics (Generic (..))

import Agda.Utils.Null (Null (..))

data List a = Empty | !a :! !(List a)

toStrictList :: [a] -> List a
toStrictList = foldr (:!) Empty

toLazyList :: List a -> [a]
toLazyList Empty   = []
toLazyList (x:!xs) = x : toLazyList xs

deriving instance Data a => Data (List a)
deriving instance Generic (List a)
deriving instance Eq a => Eq (List a)

instance Eq a => Null (List a) where
  empty = Empty
  null Empty  = True 
  null (_:!_) = False

instance Foldable List where
    foldr cons nil = \case
      Empty     -> nil
      (x :! xs) -> cons x (foldr cons nil xs)

reverse :: List a -> List a
reverse = toStrictList . Lazy.reverse . toLazyList

-- TODO: expand with standard list functionality
