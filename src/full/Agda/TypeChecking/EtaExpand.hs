
-- | Compute eta long normal forms.
module Agda.TypeChecking.EtaExpand where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Maybe

-- | Eta-expand a term if its type is a function type or an eta-record type.
etaExpandOnce :: PureTCM m => Type -> Term -> m Term
etaExpandOnce a v = fromMaybeM (return v) $ etaExpandOnce' a v

-- | Eta-expand functions and expressions of eta-record
-- type wherever possible.
deepEtaExpand :: Term -> Type -> TCM Term
deepEtaExpand v a = checkInternal' etaExpandAction v CmpLeq a

etaExpandAction :: PureTCM m => Action m
etaExpandAction = defaultAction { preAction = etaExpandOnce  }
