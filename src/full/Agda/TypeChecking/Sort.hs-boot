
module Agda.TypeChecking.Sort where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

sortOf' :: Term -> ReduceM Sort
