{-# LANGUAGE NondecreasingIndentation #-}

{- | Various utility functions dealing with the non-linear, higher-order
     patterns used for rewrite rules.
-}

module Agda.TypeChecking.Rewriting.NonLinPattern where

import Prelude hiding ( null )

import Control.Monad        ( (>=>), forM )
import Control.Monad.Reader ( asks )

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Internal.MetaVars ( AllMetas, unblockOnAllMetasIn )

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Irrelevance (workOnTypes, isPropM)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Primitive.Cubical.Base

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first argument is the number of bound variables (from pattern lambdas).

class PatternFrom a b where
  patternFrom :: Int -> a -> TCM b

instance (PatternFrom a b) => PatternFrom (Arg a) (Arg b) where
  patternFrom k u = traverse (patternFrom k) u

instance PatternFrom Elims [Elim' NLPat] where
  patternFrom k = \case
    [] -> return []
    (Apply u : es) -> do
      p   <- patternFrom k u
      ps  <- patternFrom k es
      return $ Apply p : ps
    (IApply x y i : es) -> do
      p   <- patternFrom k i
      ps  <- patternFrom k es
      return $ IApply (PTerm x) (PTerm y) p : ps
    (Proj o f : es) -> do
      ps  <- patternFrom k es
      return $ Proj o f : ps

instance (PatternFrom a b) => PatternFrom (Dom a) (Dom b) where
  patternFrom k = traverse $ patternFrom k

instance PatternFrom Type NLPType where
  patternFrom k a = workOnTypes $
    NLPType <$> patternFrom k (getSort a)
            <*> patternFrom k (unEl a)

instance PatternFrom Sort NLPSort where
  patternFrom k s = do
    s <- abortIfBlocked s
    case s of
      Type l   -> PType <$> patternFrom k l
      Prop l   -> PProp <$> patternFrom k l
      SSet l   -> PSSet <$> patternFrom k l
      Inf f n  -> return $ PInf f n
      SizeUniv -> return PSizeUniv
      LockUniv -> return PLockUniv
      IntervalUniv -> return PIntervalUniv
      PiSort _ _ _ -> __IMPOSSIBLE__
      FunSort _ _ -> __IMPOSSIBLE__
      UnivSort _ -> __IMPOSSIBLE__
      MetaS{}  -> __IMPOSSIBLE__
      DefS{}   -> __IMPOSSIBLE__
      DummyS s -> do
        reportS "impossible" 10
          [ "patternFrom: hit dummy sort with content:"
          , s
          ]
        __IMPOSSIBLE__

instance PatternFrom Level NLPat where
  patternFrom k l = do
    v <- reallyUnLevelView l
    patternFrom k v

instance PatternFrom Term NLPat where
  patternFrom k v = do
    v <- unLevel =<< abortIfBlocked v
    reportSDoc "rewriting.build" 60 $ sep
      [ "building a pattern from term v = " <+> prettyTCM v
      ]
    let done = blockOnMetasIn v >> return (PTerm v)
    case stripDontCare v of
      Var i es
       | i < k     -> do
           PBoundVar i <$> patternFrom k es
       -- The arguments of `var i` should be distinct bound variables
       -- in order to build a Miller pattern
       | Just vs <- allApplyElims es -> do
           TelV tel rest <- telViewPath =<< typeOfBV i
           unless (size tel >= size vs) $ blockOnMetasIn rest >> __IMPOSSIBLE__
           let ts = applySubst (parallelS $ reverse $ map unArg vs) $ map unDom $ flattenTel tel
           mbvs <- forM (zip ts vs) $ \(t , v) -> do
             blockOnMetasIn (v,t)
             isEtaVar (unArg v) t >>= \case
               Just j | j < k -> return $ Just $ v $> j
               _              -> return Nothing
           case sequence mbvs of
             Just bvs | fastDistinct bvs -> return (PVar i bvs)
             _ -> done
       | otherwise -> done
      Lam i t -> underAbstraction_ t $ \body ->
        PLam i . Abs (absName t) <$> patternFrom (k+1) body
      Lit{}   -> done
      Def f es -> do
        Def lsuc [] <- primLevelSuc
        Def lmax [] <- primLevelMax
        case es of
          [x]     | f == lsuc -> done
          [x , y] | f == lmax -> done
          _                   -> do
            PDef f <$> patternFrom k es
      Con c ci vs ->
        PDef (conName c) <$> patternFrom k vs
      Pi a b -> do
        pa <- patternFrom k a
        pb <- addContext a (patternFrom (k+1) $ absBody b)
        return $ PPi pa (Abs (absName b) pb)
      Sort s     -> PSort <$> patternFrom k s
      Level l    -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__
      MetaV m _  -> __IMPOSSIBLE__
      Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

-- | Convert from a non-linear pattern to a term.

class NLPatToTerm p a where
  nlPatToTerm :: PureTCM m => p -> m a

  default nlPatToTerm ::
    ( NLPatToTerm p' a', Traversable f, p ~ f p', a ~ f a'
    , PureTCM m
    ) => p -> m a
  nlPatToTerm = traverse nlPatToTerm

instance NLPatToTerm p a => NLPatToTerm [p] [a] where
instance NLPatToTerm p a => NLPatToTerm (Arg p) (Arg a) where
instance NLPatToTerm p a => NLPatToTerm (Dom p) (Dom a) where
instance NLPatToTerm p a => NLPatToTerm (Elim' p) (Elim' a) where
instance NLPatToTerm p a => NLPatToTerm (Abs p) (Abs a) where

instance NLPatToTerm Nat Term where
  nlPatToTerm = return . var

instance NLPatToTerm NLPat Term where
  nlPatToTerm = \case
    PVar i xs      -> Var i . map Apply <$> nlPatToTerm xs
    PTerm u        -> return u
    PDef f es      -> (theDef <$> getConstInfo f) >>= \case
      Constructor{ conSrcCon = c } -> Con c ConOSystem <$> nlPatToTerm es
      _                            -> Def f <$> nlPatToTerm es
    PLam i u       -> Lam i <$> nlPatToTerm u
    PPi a b        -> Pi    <$> nlPatToTerm a <*> nlPatToTerm b
    PSort s        -> Sort  <$> nlPatToTerm s
    PBoundVar i es -> Var i <$> nlPatToTerm es

instance NLPatToTerm NLPat Level where
  nlPatToTerm = nlPatToTerm >=> levelView

instance NLPatToTerm NLPType Type where
  nlPatToTerm (NLPType s a) = El <$> nlPatToTerm s <*> nlPatToTerm a

instance NLPatToTerm NLPSort Sort where
  nlPatToTerm (PType l) = Type <$> nlPatToTerm l
  nlPatToTerm (PProp l) = Prop <$> nlPatToTerm l
  nlPatToTerm (PSSet l) = SSet <$> nlPatToTerm l
  nlPatToTerm (PInf f n) = return $ Inf f n
  nlPatToTerm PSizeUniv = return SizeUniv
  nlPatToTerm PLockUniv = return LockUniv
  nlPatToTerm PIntervalUniv = return IntervalUniv

-- | Gather the set of pattern variables of a non-linear pattern
class NLPatVars a where
  nlPatVarsUnder :: Int -> a -> IntSet

  nlPatVars :: a -> IntSet
  nlPatVars = nlPatVarsUnder 0

instance {-# OVERLAPPABLE #-} (Foldable f, NLPatVars a) => NLPatVars (f a) where
  nlPatVarsUnder k = foldMap $ nlPatVarsUnder k

instance NLPatVars NLPType where
  nlPatVarsUnder k (NLPType l a) = nlPatVarsUnder k (l, a)

instance NLPatVars NLPSort where
  nlPatVarsUnder k = \case
    PType l   -> nlPatVarsUnder k l
    PProp l   -> nlPatVarsUnder k l
    PSSet l   -> nlPatVarsUnder k l
    PInf f n  -> empty
    PSizeUniv -> empty
    PLockUniv -> empty
    PIntervalUniv -> empty

instance NLPatVars NLPat where
  nlPatVarsUnder k = \case
      PVar i _  -> singleton $ i - k
      PDef _ es -> nlPatVarsUnder k es
      PLam _ p  -> nlPatVarsUnder k p
      PPi a b   -> nlPatVarsUnder k (a, b)
      PSort s   -> nlPatVarsUnder k s
      PBoundVar _ es -> nlPatVarsUnder k es
      PTerm{}   -> empty

instance (NLPatVars a, NLPatVars b) => NLPatVars (a,b) where
  nlPatVarsUnder k (a,b) = nlPatVarsUnder k a `mappend` nlPatVarsUnder k b

instance NLPatVars a => NLPatVars (Abs a) where
  nlPatVarsUnder k = \case
    Abs   _ v -> nlPatVarsUnder (k+1) v
    NoAbs _ v -> nlPatVarsUnder k v

-- | Get all symbols that a non-linear pattern matches against
class GetMatchables a where
  getMatchables :: a -> [QName]

  default getMatchables :: (Foldable f, GetMatchables a', a ~ f a') => a -> [QName]
  getMatchables = foldMap getMatchables

instance GetMatchables a => GetMatchables [a] where
instance GetMatchables a => GetMatchables (Arg a) where
instance GetMatchables a => GetMatchables (Dom a) where
instance GetMatchables a => GetMatchables (Elim' a) where
instance GetMatchables a => GetMatchables (Abs a) where

instance (GetMatchables a, GetMatchables b) => GetMatchables (a,b) where
  getMatchables (x,y) = getMatchables x ++ getMatchables y

instance GetMatchables NLPat where
  getMatchables p =
    case p of
      PVar _ _       -> empty
      PDef f _       -> singleton f
      PLam _ x       -> getMatchables x
      PPi a b        -> getMatchables (a,b)
      PSort s        -> getMatchables s
      PBoundVar i es -> getMatchables es
      PTerm u        -> getMatchables u

instance GetMatchables NLPType where
  getMatchables = getMatchables . nlpTypeUnEl

instance GetMatchables NLPSort where
  getMatchables = \case
    PType l   -> getMatchables l
    PProp l   -> getMatchables l
    PSSet l   -> getMatchables l
    PInf f n  -> empty
    PSizeUniv -> empty
    PLockUniv -> empty
    PIntervalUniv -> empty

instance GetMatchables Term where
  getMatchables = getDefs' __IMPOSSIBLE__ singleton

instance GetMatchables RewriteRule where
  getMatchables = getMatchables . rewPats

-- | Only computes free variables that are not bound (see 'nlPatVars'),
--   i.e., those in a 'PTerm'.

instance Free NLPat where
  freeVars' = \case
    PVar _ _       -> mempty
    PDef _ es      -> freeVars' es
    PLam _ u       -> freeVars' u
    PPi a b        -> freeVars' (a,b)
    PSort s        -> freeVars' s
    PBoundVar _ es -> freeVars' es
    PTerm t        -> freeVars' t

instance Free NLPType where
  freeVars' (NLPType s a) =
    ifM (asks ((IgnoreNot ==) . feIgnoreSorts))
      {- then -} (freeVars' (s, a))
      {- else -} (freeVars' a)

instance Free NLPSort where
  freeVars' = \case
    PType l   -> freeVars' l
    PProp l   -> freeVars' l
    PSSet l   -> freeVars' l
    PInf f n  -> mempty
    PSizeUniv -> mempty
    PLockUniv -> mempty
    PIntervalUniv -> mempty

-- Throws a pattern violation if the given term contains any
-- metavariables.
blockOnMetasIn :: (MonadBlock m, AllMetas t) => t -> m ()
blockOnMetasIn t = case unblockOnAllMetasIn t of
  UnblockOnAll ms | null ms -> return ()
  b -> patternViolation b
