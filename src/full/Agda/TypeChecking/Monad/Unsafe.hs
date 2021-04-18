
module Agda.TypeChecking.Monad.Unsafe
  ( UnsafePragma (..)
  , UnsafeThings (..)
  , tellPostulate
  , tellUnsolvedMetas
  , tellUnsafePragma
  , tellUnsafeErasedEquality
  , tellUnsafeFlags
  ) where

import Agda.Interaction.UnsafeThings

import Agda.TypeChecking.Monad.Base

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name ( TopLevelModuleName )

import Agda.Utils.Impossible
import Agda.Utils.Lens

-- TODO: the following functions should raise a warning or error when
-- they are called while `--safe` is already enabled. Currently this
-- is still done separately at each call site.

tellPostulate :: MonadTCState m => QName -> m ()
tellPostulate f = modifyTCLens stUnsafePostulates $ Set.insert f

tellUnsolvedMetas :: MonadTCState m => TopLevelModuleName -> (Set MetaId) -> m ()
tellUnsolvedMetas m mids = modifyTCLens stUnsafeUnsolvedMetas $ Map.insertWith __IMPOSSIBLE__ m mids

tellUnsafePragma :: MonadTCState m => QName -> UnsafePragma -> m ()
tellUnsafePragma f pr = modifyTCLens stUnsafePragmas $ Map.insertWith (++) f [pr]

tellUnsafeErasedEquality :: MonadTCState m => ModuleName -> m ()
tellUnsafeErasedEquality mod = modifyTCLens stUnsafeErasedEquality $ Set.insert mod

tellUnsafeFlags :: MonadTCState m => TopLevelModuleName -> [String] -> m ()
tellUnsafeFlags mod flags = modifyTCLens stUnsafeFlags $ Map.insertWith __IMPOSSIBLE__ mod flags
