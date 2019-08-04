
module Agda.TypeChecking.Conversion where

import qualified Control.Monad.Fail as Fail

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Warnings
import Agda.Utils.Except ( MonadError )

type MonadConversion m =
  ( MonadReduce m
  , MonadAddContext m
  , MonadConstraint m
  , MonadMetaSolver m
  , MonadError TCErr m
  , MonadWarning m
  , MonadDebug m
  , MonadStatistics m
  , MonadFresh ProblemId m
  , MonadFresh Int m
  , HasBuiltins m
  , HasConstInfo m
  , HasOptions m
  , Fail.MonadFail m
  )

compareTerm  :: MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareTermOnFace :: MonadConversion m => Comparison -> Term -> Type -> Term -> Term -> m ()
compareAtom  :: MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareArgs  :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> m ()
compareElims :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> m ()
compareType  :: MonadConversion m => Comparison -> Type -> Type -> m ()
compareTel   :: MonadConversion m => Type -> Type -> Comparison -> Telescope -> Telescope -> m ()
compareSort  :: MonadConversion m => Comparison -> RegardRelevance -> Sort -> Sort -> m ()
compareLevel :: MonadConversion m => Comparison -> Level -> Level -> m ()
equalTerm    :: MonadConversion m => Type -> Term -> Term -> m ()
equalTermOnFace :: MonadConversion m => Term -> Type -> Term -> Term -> m ()
equalType    :: MonadConversion m => Type -> Type -> m ()
equalSort    :: MonadConversion m => RegardRelevance -> Sort -> Sort -> m ()
equalLevel   :: MonadConversion m => Level -> Level -> m ()
leqType      :: MonadConversion m => Type -> Type -> m ()
leqLevel     :: MonadConversion m => Level -> Level -> m ()
