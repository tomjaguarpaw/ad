{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}

module RoseMTL where

import Control.Monad (when)
import qualified Control.Monad.Except as TransExcept
import qualified Control.Monad.State.Strict as TransState
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.Except (ExceptT)
import qualified Control.Monad.Trans.Except as Except
import qualified Control.Monad.Trans.Identity as Identity
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import Data.Coerce (coerce)
import Data.Foldable (for_)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Constraint, Type)
import Data.Void (Void, absurd)
import Prelude hiding (read)

data Effects = Branch Effects Effects | Leaf ((Type -> Type) -> Type -> Type) | Empty

data SEffects i where
  SBranch :: (SingI i1, SingI i2) => SEffects (Branch i1 i2)
  SLeaf :: (MonadTrans t) => SEffects (Leaf t)
  SEmpty :: SEffects Empty

class SingI i where
  sing :: SEffects i

instance (MonadTrans t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

type (:&) = 'Branch

type (:>) :: Effects -> Effects -> Constraint
class a :> b where
  embed :: (Monad m) => (forall m'. (Monad m') => Eff a m' r) -> Eff b m r

instance {-# INCOHERENT #-} e :> e where
  embed = id
  {-# INLINE embed #-}

instance (SingI x, SingI es, (e :> es)) => e :> (x :& es) where
  embed x = MkEff (lift (embed x))
  {-# INLINE embed #-}

-- Do we want this?
-- instance {-# incoherent #-} (e :> es) => (e' :& e) :> (e' :> es)

-- This seems a bit wobbly
instance {-# INCOHERENT #-} (SingI e, SingI es) => e :> (e :& es) where
  embed = MkEff
  {-# INLINE embed #-}

newtype Eff es m a = MkEff {unMkEff :: EffF es m a}

type family EffF (es :: Effects) m where
  EffF Empty m = m
  EffF (Leaf t) m = t m
  EffF (Branch s1 s2) m = Eff s1 (Eff s2 m)

effLeaf ::
  forall m t a.
  (Monad m) =>
  (forall m'. (Monad m') => t m' a) ->
  Eff (Leaf t) m a
effLeaf x = coerce (x @m)
{-# INLINE effLeaf #-}

effBranch ::
  (Monad m) => (forall m'. (Monad m') => Eff t1 (Eff t2 m') a) -> Eff (t1 :& t2) m a
effBranch = MkEff

runEffPure :: Eff Empty Identity a -> a
runEffPure = coerce
{-# INLINE runEffPure #-}

coerceFmapEmpty ::
  forall a b m. (Functor m) => (a -> b) -> Eff Empty m a -> Eff Empty m b
coerceFmapEmpty = coerce (fmap @m @a @b)

coerceFmapLeaf ::
  forall a b t m.
  (MonadTrans t, Monad m) =>
  (a -> b) ->
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b
coerceFmapLeaf = coerce (fmap @(t m) @a @b)

coerceFmapBranch ::
  forall a b s1 s2 m.
  (SingI s1, SingI s2, Monad m) =>
  (a -> b) ->
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b
coerceFmapBranch = coerce (fmap @(Eff s1 (Eff s2 m)) @a @b)

instance (SingI es, Monad m) => Functor (Eff es m) where
  fmap = case sing @es of
    SEmpty -> coerceFmapEmpty
    SBranch -> coerceFmapBranch
    SLeaf -> coerceFmapLeaf
  {-# INLINE fmap #-}

coercePureEmpty :: forall a m. (Applicative m) => a -> Eff Empty m a
coercePureEmpty = coerce (pure :: a -> m a)

coercePureLeaf ::
  forall a t m.
  (MonadTrans t, Monad m) =>
  a ->
  Eff (Leaf t) m a
coercePureLeaf = coerce (pure :: a -> t m a)

coercePureBranch ::
  forall a s1 s2 m.
  (Monad m, SingI s1, SingI s2) =>
  a ->
  Eff (Branch s1 s2) m a
coercePureBranch = coerce (pure :: a -> Eff s1 (Eff s2 m) a)

coerceAndThenEmpty ::
  forall m a b. (Applicative m) => Eff Empty m a -> Eff Empty m b -> Eff Empty m b
coerceAndThenEmpty = coerce ((*>) :: m a -> m b -> m b)

coerceAndThenLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b ->
  Eff (Leaf t) m b
coerceAndThenLeaf = coerce ((*>) :: t m a -> t m b -> t m b)

coerceAndThenBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b ->
  Eff (Branch s1 s2) m b
coerceAndThenBranch =
  coerce
    ( (*>) ::
        Eff s1 (Eff s2 m) a ->
        Eff s1 (Eff s2 m) b ->
        Eff s1 (Eff s2 m) b
    )

coerceBindEmpty ::
  forall m a b. (Monad m) => Eff Empty m a -> (a -> Eff Empty m b) -> Eff Empty m b
coerceBindEmpty = coerce ((>>=) @m @a @b)

coerceBindLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m a ->
  (a -> Eff (Leaf t) m b) ->
  Eff (Leaf t) m b
coerceBindLeaf = coerce ((>>=) @(t m) @a @b)

coerceBindBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m a ->
  (a -> Eff (Branch s1 s2) m b) ->
  Eff (Branch s1 s2) m b
coerceBindBranch =
  coerce ((>>=) @(Eff s1 (Eff s2 m)) @a @b)

instance (SingI es, Monad m) => Applicative (Eff es m) where
  pure = case sing @es of
    SEmpty -> coercePureEmpty
    SLeaf -> coercePureLeaf
    SBranch -> coercePureBranch
  {-# INLINE pure #-}

  (<*>) = case sing @es of
    SEmpty -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
    SLeaf -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
    SBranch -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
  {-# INLINE (<*>) #-}

  (*>) = case sing @es of
    SEmpty -> coerceAndThenEmpty
    SLeaf -> coerceAndThenLeaf
    SBranch -> coerceAndThenBranch
  {-# INLINE (*>) #-}

instance (SingI es, Monad m) => Monad (Eff es m) where
  (>>=) = case sing @es of
    SEmpty -> coerceBindEmpty
    SLeaf -> coerceBindLeaf
    SBranch -> coerceBindBranch
  {-# INLINE (>>=) #-}

instance (SingI es) => MonadTrans (Eff es) where
  lift = case sing @es of
    SEmpty -> MkEff
    SLeaf -> MkEff . lift
    SBranch -> MkEff . lift . lift
  {-# INLINE lift #-}

type EmbedT =
  forall t m a effs.
  (Leaf t :> effs) =>
  (SingI effs) =>
  (Monad m) =>
  t m a ->
  Eff effs m a

data State s st where
  MkState :: State s (Leaf (StateT s))

data Error e err where
  MkError :: Error e (Leaf (ExceptT e))

embedT ::
  (Monad m, Leaf t :> effs) => (forall m'. (Monad m') => t m' r) -> Eff effs m r
embedT x = embed (effLeaf x)

type Handler effs m h a r =
  (forall s. (SingI s) => h s -> Eff (s :& effs) m a) ->
  Eff effs m r

type HandlerNoArgs s effs m h a r =
  Eff (s :& effs) m a ->
  Eff effs m r

handleAny ::
  (MonadTrans t) =>
  h (Leaf t) ->
  (t (Eff effs m) a -> Eff effs m r) ->
  Handler effs m h a r
handleAny mkAny handler f = case f mkAny of
  MkEff (MkEff m) -> handler m
{-# INLINE handleAny #-}

handleAnyNoArgs ::
  (MonadTrans t) =>
  (t (Eff effs m) a -> Eff effs m r) ->
  HandlerNoArgs (Leaf t) effs m h a r
handleAnyNoArgs = coerce
{-# INLINE handleAnyNoArgs #-}

handleError :: Handler effs m (Error e) a (Either e a)
handleError = handleAny MkError Except.runExceptT
{-# INLINE handleError #-}

throw :: (err :> effs, SingI effs, Monad m) => Error e err -> e -> Eff effs m a
throw MkError e = embedT (Except.throwE e)
{-# INLINE throw #-}

throwNoArgs :: (Leaf (ExceptT e) :> effs, SingI effs, Monad m) => e -> Eff effs m a
throwNoArgs e = embedT (Except.throwE e)
{-# INLINE throwNoArgs #-}

handleState ::
  (SingI effs, Monad m) =>
  s ->
  Handler effs m (State s) a a
handleState s f = fmap fst (runState s f)
{-# INLINE handleState #-}

runStateNoArgs ::
  (SingI effs, Monad m) =>
  s ->
  HandlerNoArgs (Leaf (StateT s)) effs m (State s) a (a, s)
runStateNoArgs s = handleAnyNoArgs (flip State.runStateT s)
{-# INLINE runStateNoArgs #-}

handleStateNoArgs ::
  (SingI effs, Monad m) =>
  s ->
  HandlerNoArgs (Leaf (StateT s)) effs m (State s) a a
handleStateNoArgs s f = fmap fst (runStateNoArgs s f)
{-# INLINE handleStateNoArgs #-}

handleErrorNoArgs :: HandlerNoArgs (Leaf (ExceptT e)) effs m (Error e) a (Either e a)
handleErrorNoArgs = handleAnyNoArgs Except.runExceptT
{-# INLINE handleErrorNoArgs #-}

runState ::
  (SingI effs, Monad m) =>
  s ->
  Handler effs m (State s) a (a, s)
runState s = handleAny MkState (flip State.runStateT s)
{-# INLINE runState #-}

read ::
  (SingI effs, st :> effs, Monad m) => State s st -> Eff effs m s
read MkState = embedT State.get
{-# INLINE read #-}

readNoArgs ::
  (SingI effs, Leaf (StateT s) :> effs, Monad m) => Eff effs m s
readNoArgs = embedT State.get
{-# INLINE readNoArgs #-}

write :: (st :> effs, SingI effs, Monad m) => State s st -> s -> Eff effs m ()
write MkState s = embedT (State.put s)
{-# INLINE write #-}

writeNoArgs :: (Leaf (StateT s) :> effs, SingI effs, Monad m) => s -> Eff effs m ()
writeNoArgs s = embedT (State.put s)
{-# INLINE writeNoArgs #-}

modify ::
  (Monad m, SingI effs, st :> effs) => State s st -> (s -> s) -> Eff effs m ()
modify state f = do
  s <- read state
  write state $! f s
{-# INLINE modify #-}

examplePure :: (SingI effs, Monad m) => Eff effs m ()
examplePure = pure ()

exampleRead :: (SingI effs, Monad m) => Eff effs m ()
exampleRead =
  handleState () $ \st -> read st

exampleWrite :: (SingI effs, Monad m) => Eff effs m (Int, Int)
exampleWrite =
  handleState 0 $ \st -> do
    handleState 100 $ \st2 -> do
      modify st (+ 1)
      modify st2 (* 2)
      (,) <$> read st <*> read st2

exampleParity :: (SingI effs, Monad m) => Eff effs m (Int, Int)
exampleParity =
  handleState 0 $ \evens -> do
    handleState 0 $ \odds -> do
      for_ [1 :: Int .. 10] $ \i -> do
        ( if even i
            then modify odds
            else modify evens
          )
          (+ 1)

      e <- read evens
      o <- read odds

      pure (e, o)

example5 ::
  (st :> effs, err :> effs, SingI effs, Monad m) =>
  Error String err ->
  State Int st ->
  Eff effs m ()
example5 e s = do
  foo <- read s
  modify s (+ 1)
  _ <- throw e ("Hello " ++ show foo)
  modify s (+ 1)

example6 :: (err :> effs, SingI effs, Monad m) => Error String err -> Eff effs m ((), Int)
example6 = \e -> runState 10 (example5 e)

example6a :: (st :> effs, SingI effs, Monad m) => State Int st -> Eff effs m (Either String ())
example6a = \s -> handleError (\e -> example5 e s)

example7 :: (SingI effs, Monad m) => Eff effs m (Either String ((), Int))
example7 = handleError example6

example7a :: (SingI effs, Monad m) => Eff effs m (Either String (), Int)
example7a = runState 10 example6a

type EarlyReturn = Error

newtype MustReturnEarly = MustReturnEarly Void

returnedEarly :: MustReturnEarly -> a
returnedEarly (MustReturnEarly v) = absurd v
{-# INLINE returnedEarly #-}

withEarlyReturn ::
  (SingI effs, Monad m) =>
  ( forall err.
    (SingI err) =>
    EarlyReturn r err ->
    Eff (err :& effs) m MustReturnEarly
  ) ->
  Eff effs m r
withEarlyReturn f =
  fmap (either id returnedEarly) (handleError f)
{-# INLINE withEarlyReturn #-}

withEarlyReturnNoArgs ::
  (Monad m, SingI effs) =>
  HandlerNoArgs (Leaf (ExceptT e)) effs m (Error e) MustReturnEarly e
withEarlyReturnNoArgs f =
  fmap (either id returnedEarly) (handleErrorNoArgs f)
{-# INLINE withEarlyReturnNoArgs #-}

earlyReturn ::
  (err :> effs, SingI effs, Monad m) =>
  EarlyReturn r err ->
  r ->
  Eff effs m a
earlyReturn = throw
{-# INLINE earlyReturn #-}

myPure :: Bool
myPure = runEffPure (pure True)

myEarlyReturn :: Bool
myEarlyReturn =
  runEffPure (withEarlyReturnNoArgs (throwNoArgs True))

myState :: Int
myState = runEffPure $ handleStateNoArgs 0 $ do
  _ <- pure () :: Eff (Leaf (StateT Int) :& Empty) Identity ()
  s <- readNoArgs
  writeNoArgs $! (s + 1 :: Int)
  readNoArgs

myStateMTL :: Int
myStateMTL = runIdentity $ flip State.evalStateT 0 $ do
  s <- TransState.get
  TransState.put $! (s + 1 :: Int)
  TransState.get

mySum :: Int
mySum = runEffPure $ handleStateNoArgs 0 $ do
  _ <- pure () :: Eff (Leaf (StateT Int) :& Empty) Identity ()
  for_ [1 :: Int .. 10] $ \i -> do
    s <- readNoArgs
    writeNoArgs $! s + i
  readNoArgs

mySumMTL :: Int
mySumMTL = runIdentity $ flip State.evalStateT 0 $ do
  for_ [1 :: Int .. 10] $ \i -> do
    s <- TransState.get
    TransState.put $! s + i
  TransState.get

lookupEffects :: [a] -> Int -> Maybe a
xs `lookupEffects` i = runEffPure $
  withEarlyReturn $ \ret -> do
    handleState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (earlyReturn ret (Just a))
        write s (i' + 1)
    earlyReturn ret Nothing

lookupEffectsNoArgs ::
  forall effs m a r.
  (SingI effs, Monad m, Leaf (StateT Int) :> effs, 'Leaf (ExceptT (Maybe a)) :> effs) =>
  [a] ->
  Int ->
  Eff effs m r
xs `lookupEffectsNoArgs` i = do
  for_ xs $ \a -> do
    i' <- readNoArgs
    when (i == i') (throwNoArgs (Just a))
    writeNoArgs (i' + 1)
  throwNoArgs (Nothing :: Maybe a)

-- Even though this is as as concrete as you could want, it still
-- doesn't get specialized.
lookupEffectsNoArgs1 ::
  forall a.
  [a] ->
  Int ->
  Maybe a
xs `lookupEffectsNoArgs1` i = runEffPure $ do
  withEarlyReturnNoArgs $ do
    handleStateNoArgs 0 $ do
      pure () :: Eff (Leaf (StateT Int) :& (Leaf (ExceptT (Maybe a)) :& Empty)) Identity ()
      for_ xs $ \a -> do
        i' <- readNoArgs
        when (i == i') (throwNoArgs (Just a))
        writeNoArgs (i' + 1)
      throwNoArgs (Nothing :: Maybe a)

lookupEffectsInlined :: forall a. [a] -> Int -> Maybe a
xs `lookupEffectsInlined` i = runEffPure $
  withEarlyReturn $ \ret -> do
    fmap
      fst
      ( handleAny
          MkState
          (flip State.runStateT 0)
          ( \s -> do
              for_ xs $ \a -> do
                i' <- (\MkState -> effBranch (MkEff State.get)) s
                when (i == i') ((\MkError -> embed @(Leaf (ExceptT (Maybe a))) (MkEff (Except.throwE (Just a)))) ret)
                write s (i' + 1)
          )
      )
    earlyReturn ret Nothing

(!???) :: [a] -> Int -> Maybe a
xs !??? i = either id id $ do
  flip State.evalStateT 0 $ do
    for_ xs $ \a -> do
      i' <- State.get
      when (i == i') (lift (Left (Just a)))
      State.put (i' + 1)
  Left Nothing

lookupMTL :: [a] -> Int -> Maybe a
lookupMTL xs i = either id id $ runIdentity $ TransExcept.runExceptT $ do
  flip TransState.evalStateT 0 $ do
    for_ xs $ \a -> do
      i' <- TransState.get
      when (i == i') (lift (Except.throwE (Just a)))
      State.put (i' + 1)
  Except.throwE Nothing
