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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}

module RoseMTL where

import Control.Monad (when)
import Control.Monad.Morph (MFunctor, hoist)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.Except (ExceptT)
import qualified Control.Monad.Trans.Except as Except
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import Data.Foldable (for_)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (read)

data Rose a = Branch (Rose a) (Rose a) | Leaf a | Empty

data SRose i where
  SBranch :: (SingI i1, SingI i2) => SRose (Branch i1 i2)
  SLeaf :: (MonadTrans t, MFunctor t) => SRose (Leaf t)
  SEmpty :: SRose Empty

class SingI i where
  sing :: SRose i

instance (MonadTrans t, MFunctor t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

type (:&) = 'Branch

type Effect = (Type -> Type) -> Type -> Type

class (a :: Rose Effect) :> (b :: Rose Effect) where
  embed :: (Monad m) => Eff a m r -> Eff b m r

instance {-# INCOHERENT #-} e :> e where
  embed = id
  {-# INLINE embed #-}

instance (SingI x, SingI es, (e :> es)) => e :> (x :& es) where
  embed = MkEff . lift . embed
  {-# INLINE embed #-}

-- Do we want this?
-- instance {-# incoherent #-} (e :> es) => (e' :& e) :> (e' :> es)

-- This seems a bit wobbly
instance {-# INCOHERENT #-} (SingI e, SingI es) => e :> (e :& es) where
  embed = MkEff . hoist lift
  {-# INLINE embed #-}

newtype Eff es m a = MkEff (EffF es m a)

type family EffF (es :: Rose Effect) m where
  EffF Empty m = m
  EffF (Leaf t) m = t m
  EffF (Branch s1 s2) m = Eff s1 (Eff s2 m)

effLeaf :: t m a -> Eff (Leaf t) m a
effLeaf = MkEff
{-# INLINE effLeaf #-}

runEffPure :: Eff Empty Identity a -> a
runEffPure = \case
  MkEff ma -> runIdentity ma
{-# INLINE runEffPure #-}

instance (SingI es, Monad m) => Functor (Eff es m) where
  fmap f = case sing @es of
    SEmpty -> \(MkEff ma) -> MkEff (fmap f ma)
    SBranch -> \(MkEff ema) -> MkEff (fmap f ema)
    SLeaf -> \(MkEff tma) -> MkEff (fmap f tma)
  {-# INLINE fmap #-}

instance (SingI es, Monad m) => Applicative (Eff es m) where
  pure = case sing @es of
    SEmpty -> MkEff . pure
    SLeaf -> MkEff . lift . pure
    SBranch -> MkEff . lift . pure
  {-# INLINE pure #-}

  (<*>) = case sing @es of
    SEmpty -> \(MkEff f) (MkEff g) -> MkEff (f <*> g)
    SLeaf -> \(MkEff f) (MkEff g) -> MkEff (f <*> g)
    SBranch -> \(MkEff f) (MkEff g) -> MkEff (f <*> g)
  {-# INLINE (<*>) #-}

instance (SingI es, Monad m) => Monad (Eff es m) where
  (>>=) = case sing @es of
    SEmpty -> \(MkEff m) f -> MkEff $ do
      m' <- m
      case f m' of MkEff m'' -> m''
    SLeaf -> \(MkEff m) f -> MkEff $ do
      m' <- m
      case f m' of MkEff m'' -> m''
    SBranch -> \(MkEff m) f -> MkEff $ do
      m' <- m
      case f m' of MkEff m'' -> m''
  {-# INLINE (>>=) #-}

instance (SingI es) => MonadTrans (Eff es) where
  lift = case sing @es of
    SEmpty -> MkEff
    SLeaf -> MkEff . lift
    SBranch -> MkEff . lift . lift
  {-# INLINE lift #-}

instance (SingI es) => MFunctor (Eff es) where
  hoist f = case sing @es of
    SEmpty -> \(MkEff m) -> MkEff (f m)
    SLeaf -> \(MkEff m) -> MkEff (hoist f m)
    SBranch -> \(MkEff m) -> MkEff (hoist (hoist f) m)
  {-# INLINE hoist #-}

newtype Handle t where
  MkHandle ::
    ( forall m a effs.
      (Leaf t :> effs) =>
      (SingI effs) =>
      (Monad m) =>
      t m a ->
      Eff effs m a
    ) ->
    Handle t

data State s st where
  MkState :: Handle (StateT s) -> State s (Leaf (StateT s))

data Error e err where
  MkError :: Handle (ExceptT e) -> Error e (Leaf (ExceptT e))

handle ::
  (Leaf t :> effs, SingI effs, Monad m) => Handle t -> t m a -> Eff effs m a
handle (MkHandle r) = r

handleAny ::
  -- I don't know why tt isn't required to be t, but it seems to work!
  (MonadTrans tt, MFunctor tt) =>
  (Handle t -> h (Leaf tt)) ->
  (tt (Eff effs m) a -> Eff effs m r) ->
  (forall err. (SingI err) => h err -> Eff (err :& effs) m a) ->
  Eff effs m r
handleAny mkAny handler f = case f (mkAny (MkHandle (embed . effLeaf))) of
  MkEff (MkEff m) -> handler m
{-# INLINE handleAny #-}

handleError ::
  (forall err. (SingI err) => Error e err -> Eff (err :& effs) m a) ->
  Eff effs m (Either e a)
handleError = handleAny MkError Except.runExceptT
{-# INLINE handleError #-}

throw :: (err :> effs, SingI effs, Monad m) => Error e err -> e -> Eff effs m a
throw (MkError h) e = handle h (Except.throwE e)
{-# INLINE throw #-}

handleState ::
  (SingI effs, Monad m) =>
  s ->
  (forall st. (SingI st) => State s st -> Eff (st :& effs) m a) ->
  Eff effs m a
handleState s f = fmap fst (runState s f)
{-# INLINE handleState #-}

runState ::
  (SingI effs, Monad m) =>
  s ->
  (forall st. (SingI st) => State s st -> Eff (st :& effs) m a) ->
  Eff effs m (a, s)
runState s = handleAny MkState (flip State.runStateT s)
{-# INLINE runState #-}

read ::
  (SingI effs, st :> effs, Monad m) => State s st -> Eff effs m s
read (MkState h) = handle h State.get
{-# INLINE read #-}

write :: (st :> effs, SingI effs, Monad m) => State s st -> s -> Eff effs m ()
write (MkState h) s = handle h (State.put s)
{-# INLINE write #-}

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

earlyReturn ::
  (err :> effs, SingI effs, Monad m) =>
  EarlyReturn r err ->
  r ->
  Eff effs m a
earlyReturn = throw
{-# INLINE earlyReturn #-}

(!??) :: [a] -> Int -> Maybe a
xs !?? i = runEffPure $
  withEarlyReturn $ \ret -> do
    handleState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (earlyReturn ret (Just a))
        write s (i' + 1)
    earlyReturn ret Nothing

(!???) :: [a] -> Int -> Maybe a
xs !??? i = either id id $ do
  flip State.evalStateT 0 $ do
    for_ xs $ \a -> do
      i' <- State.get
      when (i == i') (lift (Left (Just a)))
      State.put (i' + 1)
  Left Nothing
