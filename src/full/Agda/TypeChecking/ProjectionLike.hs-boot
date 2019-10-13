module Agda.TypeChecking.ProjectionLike where

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal (Term)
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (HasConstInfo)

makeProjection :: QName -> TCM ()
eligibleForProjectionLike :: (HasConstInfo m) => QName -> m Bool
elimView :: (MonadReduce m, MonadTCEnv m, HasConstInfo m) => Bool -> Term -> m Term
