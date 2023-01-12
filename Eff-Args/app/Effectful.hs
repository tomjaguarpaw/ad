{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}

module Effectful where

import Prelude hiding (return)
import Control.Monad (when)
import Data.Foldable (for_)
import Data.Void (Void, absurd)
import "effectful-core" Effectful (Eff, runPureEff)
import qualified "effectful-core" Effectful as Eff
import Effectful.Error.Static (Error)
import qualified Effectful.Error.Static as Eff
import Effectful.State.Static.Local (State)
import qualified Effectful.State.Static.Local as Eff
import Unsafe.Coerce

class a Eff.:> b => a :> b

instance (e :> es) => e :> (x : es)

-- This seems a bit wobbly
instance {-# INCOHERENT #-} e :> (e : es)

data Dict c where
  Dict :: c => Dict c

newtype Has (eff :: k) (s :: k) = Have# (# #)

has :: (Has a a -> r) -> r
has f = f (Have# (##))

{-# INLINE have #-}
-- This is the only thing that's potentially unsafe
have :: Has eff s -> Dict (eff ~ s)
have _ = unsafeCoerce (Dict :: Dict (s ~ s))

thisDivergesFortunately :: ()
thisDivergesFortunately = have undefined `seq` ()

to :: (eff :> es => t es r) -> s :> es => Has eff s -> t es r
to k h = case have h of Dict -> k

from ::
  (t (eff : es) a -> t es b) ->
  (forall s. Has eff s -> t (s : es) a) ->
  t es b
from f k = f (has k)

throwError :: s :> es => Has (Error e) s -> e -> Eff es a
throwError h e = to (Eff.throwError e) h

withReturn ::
  (forall err. Has (Error r) err -> Eff (err : effs) Void) ->
  Eff effs r
withReturn f = do
  r1 <- runErrorNoCallStack f
  pure $ case r1 of
    Right r -> absurd r
    Left l -> l

runErrorNoCallStack ::
  (forall s. Has (Error e) s -> Eff (s : es) a) ->
  Eff es (Either e a)
runErrorNoCallStack = from Eff.runErrorNoCallStack

get :: s :> es => Has (State st) s -> Eff es st
get = to Eff.get

put :: s :> es => Has (State st) s -> st -> Eff es ()
put h st = to (Eff.put st) h

evalState ::
  s ->
  (forall e. Has (State s) e -> Eff (e : es) a) ->
  Eff es a
evalState s = from (Eff.evalState s)

(!?) :: [a] -> Int -> Maybe a
xs !? i = runPureEff $
  withReturn $ \return -> do
    evalState 0 $ \s -> do
      for_ xs $ \x -> do
        i' <- get s
        when (i == i') (throwError return (Just x))
        put s (i' + 1)
      throwError return Nothing

{-
def lookup(xs, i):
  try:
    s = 0
    for a in xs:
      i_ = s
      if (i == i_): return (Just a)
      s = i_ + 1
      return Nothing
-}

twoState :: (Int, Int)
twoState = runPureEff $
  evalState 1 $ \s1 -> do
    evalState 2 $ \s2 -> do
      put s1 10
      put s2 20
      s1' <- get s1
      s2' <- get s2
      pure (s1', s2')
