
module Agda.TypeChecking.Monad.Caching
  ( -- * Log reading/writing operations
    writeToCurrentLog
  , readFromCachedLog
  , cleanCachedLog
  , cacheCurrentLog

    -- * Activating/deactivating
  , activateLoadedFileCache
  , cachingStarts
  , areWeCaching
  , localCache, withoutCache

    -- * Restoring the 'PostScopeState'
  , restorePostScopeState
  ) where


import qualified Data.Map as Map
import Data.Strict.Tuple (Pair(..))
import qualified Data.Strict.Tuple as Strict

import Agda.Syntax.Common

import Agda.Interaction.Options

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug

import qualified Agda.Utils.HashMap.Strict as HMap
import Agda.Utils.Lens
import Agda.Utils.List.Strict (List(..))
import qualified Agda.Utils.List.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null (empty)

import Agda.Utils.Impossible

-- | To be called before any write or restore calls.
{-# INLINE cachingStarts #-}
cachingStarts :: TCM ()
cachingStarts = do
    NameId _ m <- useTC stFreshNameId
    stFreshNameId `setTCLens` NameId 1 m
    stAreWeCaching `setTCLens` True
    validateCache m -- fixes issue #4835
    where
      validateCache m = (localCache readFromCachedLog) >>= \case
        Just (_ , s) -> do
          let NameId _ m' = stPostFreshNameId s
          when (m' /= m) cleanCachedLog
        _ -> do
          return ()

{-# INLINE  areWeCaching #-}
areWeCaching :: TCM Bool
areWeCaching = useR stAreWeCaching

-- | Writes a 'TypeCheckAction' to the current log, using the current
-- 'PostScopeState'
{-# INLINE writeToCurrentLog #-}
writeToCurrentLog :: TypeCheckAction -> TCM ()
writeToCurrentLog !d = do
  reportSLn "cache" 10 $ "cachePostScopeState"
  !l <- getsTC stPostScopeState
  modifyCache $ fmap $ \lfc -> lfc{ lfcCurrent = (d :!: l) :! lfcCurrent lfc}

{-# INLINE restorePostScopeState #-}
restorePostScopeState :: PostScopeState -> TCM ()
restorePostScopeState pss = do
  reportSLn "cache" 10 $ "restorePostScopeState"
  modifyTC $ \s ->
    let ipoints = s^.stInteractionPoints
        ws = s^.stTCWarnings
        pss' = pss{stPostInteractionPoints = stPostInteractionPoints pss `mergeIPMap` ipoints
                  ,stPostTCWarnings = stPostTCWarnings pss `mergeWarnings` ws
                  }
    in  s{stPostScopeState = pss'}
  where
    mergeIPMap lm sm = HMap.mapWithKey (\k v -> maybe v (`mergeIP` v) (HMap.lookup k lm)) sm
    -- see #1338 on why we need to use the new ranges.
    mergeIP li si = li { ipRange = ipRange si }

    mergeWarnings loading current = [ w | w <- current, not $ tcWarningCached w ]
                                 ++ [ w | w <- loading,       tcWarningCached w ]

{-# INLINE modifyCache #-}
modifyCache
  :: (Maybe LoadedFileCache -> Maybe LoadedFileCache)
  -> TCM ()
modifyCache = modifyTCLens stLoadedFileCache

{-# INLINE getCache #-}
getCache :: TCM (Maybe LoadedFileCache)
getCache = useTC stLoadedFileCache

{-# INLINE putCache #-}
putCache :: Maybe LoadedFileCache -> TCM ()
putCache = setTCLens stLoadedFileCache

-- | Runs the action and restores the current cache at the end of it.
{-# INLINE localCache #-}
localCache :: TCM a -> TCM a
localCache = bracket_ getCache putCache

-- | Runs the action without cache and restores the current cache at
-- the end of it.
{-# INLINE withoutCache #-}
withoutCache :: TCM a -> TCM a
withoutCache m = localCache $ do
    putCache empty
    m

-- | Reads the next entry in the cached type check log, if present.
{-# INLINE readFromCachedLog #-}
readFromCachedLog :: TCM (Maybe (TypeCheckAction, PostScopeState))
readFromCachedLog = do
  reportSLn "cache" 10 $ "getCachedTypeCheckAction"
  getCache >>= \case
    Just lfc | (entry@(act :!: s) :! entries) <- lfcCached lfc -> do
      putCache $ Just lfc{lfcCached = entries}
      return (Just (act,s))
    _ -> do
      return Nothing

-- | Empties the "to read" CachedState. To be used when it gets invalid.
{-# INLINE cleanCachedLog #-}
cleanCachedLog :: TCM ()
cleanCachedLog = do
  reportSLn "cache" 10 $ "cleanCachedLog"
  modifyCache $ fmap $ \lfc -> lfc{lfcCached = Empty}

-- | Makes sure that the 'stLoadedFileCache' is 'Just', with a clean
-- current log. Crashes is 'stLoadedFileCache' is already active with a
-- dirty log.  Should be called when we start typechecking the current
-- file.
{-# INLINE activateLoadedFileCache #-}
activateLoadedFileCache :: TCM ()
activateLoadedFileCache = do
  reportSLn "cache" 10 $ "activateLoadedFileCache"

  whenM (optGHCiInteraction <$> commandLineOptions) $
    whenM enableCaching $ do
      modifyCache $ \case
         Nothing                          -> Just $ LoadedFileCache Empty Empty
         Just lfc | null (lfcCurrent lfc) -> Just lfc
         _                                -> __IMPOSSIBLE__

-- | Caches the current type check log.  Discardes the old cache.  Does
-- nothing if caching is inactive.
{-# INLINE cacheCurrentLog #-}
cacheCurrentLog :: TCM ()
cacheCurrentLog = do
  reportSLn "cache" 10 $ "cacheCurrentTypeCheckLog"
  modifyCache $ fmap $ \lfc ->
    lfc{lfcCached = Strict.reverse (lfcCurrent lfc), lfcCurrent = Empty}
