
module Agda.Interaction.UnsafeThings where

import Prelude hiding (null)

import Control.DeepSeq

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import GHC.Generics (Generic)

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name ( TopLevelModuleName )

import Agda.Utils.Lens
import Agda.Utils.Impossible
import Agda.Utils.Null

data UnsafePragma
  = UnsafeTerminatingPragma
  | UnsafeNonTerminatingPragma
  | UnsafeNoPositivityCheckPragma
  | UnsafeNoUniverseCheckPragma
  | UnsafeCompilePragma
  | UnsafePolarityPragma
  | UnsafeInjectivePragma
  | UnsafeEtaPragma
  deriving (Eq, Show, Enum, Generic)

instance NFData UnsafePragma

data UnsafeThings = UnsafeThings
  { _unsafePostulates         :: !(Set QName)                        -- both actual postulates and missing definitions
  , _unsafeUnsolvedMetas      :: !(Map TopLevelModuleName (Set MetaId))
  , _unsafePragmas            :: !(Map QName [UnsafePragma])
  , _unsafeErasedEquality     :: !(Set ModuleName)                   -- only unsafe in modules that use --without-K
  , _unsafeFlags              :: !(Map TopLevelModuleName [String])  -- as computed by `unsafePragmaOptions` from Agda.Interaction.Options.Base
  } deriving (Eq, Show, Generic)

instance NFData UnsafeThings

instance Null UnsafeThings where
  empty = UnsafeThings empty empty empty empty empty
  null (UnsafeThings a b c d e) = null a && null b && null c && null d && null e

instance Semigroup UnsafeThings where
  (UnsafeThings a1 b1 c1 d1 e1) <> (UnsafeThings a2 b2 c2 d2 e2) =
    UnsafeThings
      { _unsafePostulates         = a1 <> a2
      , _unsafeUnsolvedMetas      = Map.unionWith __IMPOSSIBLE__ b1 b2
      , _unsafePragmas            = Map.unionWith (<>) c1 c2
      , _unsafeErasedEquality     = d1 <> d2
      , _unsafeFlags              = Map.unionWith (<>) e1 e2
      }

instance Monoid UnsafeThings where
  mempty  = empty
  mappend = (<>)

unsafePostulates :: Lens' (Set QName) UnsafeThings
unsafePostulates f s =
  f (_unsafePostulates s) <&> \x -> s {_unsafePostulates = x}

unsafeUnsolvedMetas :: Lens' (Map TopLevelModuleName (Set MetaId)) UnsafeThings
unsafeUnsolvedMetas f s =
  f (_unsafeUnsolvedMetas s) <&> \x -> s {_unsafeUnsolvedMetas = x}

unsafePragmas :: Lens' (Map QName [UnsafePragma]) UnsafeThings
unsafePragmas f s =
  f (_unsafePragmas s) <&> \x -> s {_unsafePragmas = x}

unsafeErasedEquality :: Lens' (Set ModuleName) UnsafeThings
unsafeErasedEquality f s =
  f (_unsafeErasedEquality s) <&> \x -> s {_unsafeErasedEquality = x}

unsafeFlags :: Lens' (Map TopLevelModuleName [String]) UnsafeThings
unsafeFlags f s =
  f (_unsafeFlags s) <&> \x -> s {_unsafeFlags = x}
