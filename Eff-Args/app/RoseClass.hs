{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}

module RoseClass where

import Control.Monad (join, when)
import Data.Data (Proxy (Proxy))
import Data.Foldable (for_)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Void (Void, absurd)
import GHC.Base (Proxy#)
import GHC.Exts (proxy#)
import GHC.IO.Unsafe (unsafePerformIO)
import Main (withScopedException_)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (drop, read, return)

data Rose a = Branch (Rose a) (Rose a)

type (:&) = 'Branch

data Effect

newtype Eff (es :: Rose Effect) a = Eff {unsafeUnEff :: IO a}
  deriving stock (Functor)
  deriving newtype (Applicative, Monad)

unsafeRemoveEff :: Eff (e :& es) a -> Eff es a
unsafeRemoveEff = Eff . unsafeUnEff

runEff :: (forall es. Eff es a) -> a
runEff = unsafePerformIO . unsafeUnEff

weakenEff :: t `In` t' -> Eff t r -> Eff t' r
weakenEff _ = Eff . unsafeUnEff

newtype Error e s = Error (forall a. e -> IO a)

newtype State s e = State (IORef s)

newtype Coroutine a b s = Coroutine (a -> IO b)

type Stream a s = Coroutine a () s

newtype In (a :: Rose k) (b :: Rose k) = In# (# #)

-- Hmm, cartesian category
--
-- Or do these as (# #) -> ...
eq :: (# #) -> a `In` a
eq (##) = In# (##)

fstI :: (# #) -> a `In` (a :& b)
fstI (##) = In# (##)

sndI :: (# #) -> a `In` (b :& a)
sndI (##) = In# (##)

cmp :: a `In` b -> b `In` c -> a `In` c
cmp (In# (##)) (In# (##)) = In# (##)

bimap :: a `In` b -> c `In` d -> (a :& c) `In` (b :& d)
bimap (In# (##)) (In# (##)) = In# (##)

assoc1 :: (# #) -> ((a :& b) :& c) `In` (a :& (b :& c))
assoc1 (##) = In# (##)

drop :: a `In` b -> a `In` (c :& b)
drop h = w2 (b h)

here :: a `In` b -> (a `In` (b :& c))
here h = w (b2 h)

w :: (a :& b) `In` c -> (a `In` c)
w = cmp (fstI (##))

w2 :: (b :& a) `In` c -> (a `In` c)
w2 = cmp (sndI (##))

b2 :: (a `In` b) -> ((a :& c) `In` (b :& c))
b2 h = bimap h (eq (##))

b :: (a `In` b) -> (c :& a) `In` (c :& b)
b = bimap (eq (##))

class (a :: Rose k) :> (b :: Rose k)

instance {-# INCOHERENT #-} e :> e

instance (e :> es) => e :> (x :& es)

-- Do we want this?
-- instance {-# incoherent #-} (e :> es) => (e' :& e) :> (e' :> es)

-- This seems a bit wobbly
instance {-# INCOHERENT #-} e :> (e :& es)

throw :: err :> effs => Error e err -> e -> Eff effs a
throw (Error throw_) e = Eff (throw_ e)

has :: forall a b. a :> b => a `In` b
has = In# (##)

data Dict c where
  Dict :: forall c. c => Dict c

-- Seems like it could be better
have :: forall a b. a `In` b -> Dict (a :> b)
have = unsafeCoerce (Dict @(a :> (a :& b)))

handleError ::
  (forall err. Error e err -> Eff (err :& effs) a) ->
  Eff effs (Either e a)
handleError f =
  Eff $ withScopedException_ (\throw_ -> unsafeUnEff (f (Error throw_)))

handleErrorX ::
  (forall err effs'. err :> effs' => Error e err -> Eff effs' a) ->
  Eff effs (Either e a)
handleErrorX = handleError

read :: st :> effs => State s st -> Eff effs s
read (State r) = Eff (readIORef r)

write :: st :> effs => State s st -> s -> Eff effs ()
write (State r) s = Eff (writeIORef r s)

modify :: st :> effs => State s st -> (s -> s) -> Eff effs ()
modify state f = do
  !s <- read state
  write state (f s)

handleState ::
  s ->
  (forall st. State s st -> Eff (st :& effs) a) ->
  Eff effs (a, s)
handleState s f = do
  state <- Eff (fmap State (newIORef s))
  unsafeRemoveEff $ do
    a <- f state
    s' <- read state
    pure (a, s')

yieldCoroutine :: eff :> effs => Coroutine a b eff -> a -> Eff effs b
yieldCoroutine (Coroutine f) a = Eff (f a)

yield :: eff :> effs => Stream a eff -> a -> Eff effs ()
yield = yieldCoroutine

handleCoroutine ::
  (a -> Eff effs b) ->
  (z -> Eff effs r) ->
  (forall eff. Coroutine a b eff -> Eff (eff :& effs) z) ->
  Eff effs r
handleCoroutine update finish f = do
  z <- forEach f update
  finish z

forEach ::
  (forall eff. Coroutine a b eff -> Eff (eff :& effs) z) ->
  (a -> Eff effs b) ->
  Eff effs z
forEach f h = unsafeRemoveEff (f (Coroutine (unsafeUnEff . h)))

forEachP ::
  (forall eff. Proxy eff -> Coroutine a b eff -> Eff (eff :& effs) z) ->
  (a -> Eff effs b) ->
  Eff effs z
forEachP f = forEach (f Proxy)

example :: err :> effs => Error String err -> Eff effs a
example = (\e -> throw e "My error")

example2 :: Eff effs (Either String a)
example2 = handleError example

example2X :: Eff effs (Either String a)
example2X = handleErrorX example

example3 :: Either String a
example3 = runEff example2

example5 ::
  (st :> effs, err :> effs) =>
  Error String err ->
  State Int st ->
  Eff effs ()
example5 e s = do
  foo <- read s
  modify s (+ 1)
  _ <- throw e ("Hello " ++ show foo)
  modify s (+ 1)

example6 :: err :> effs => Error String err -> Eff effs ((), Int)
example6 = \e -> handleState 10 (example5 e)

example6a :: st :> effs => State Int st -> Eff effs (Either String ())
example6a = \s -> handleError (\e -> example5 e s)

example7 :: Eff effs (Either String ((), Int))
example7 = handleError example6

example7a :: Eff effs (Either String (), Int)
example7a = handleState 10 example6a

simpleExampleNested ::
  Num s =>
  (err :> effs1, st :> effs2) =>
  Bool ->
  Error String err ->
  Eff effs1 (State s st -> Eff effs2 ())
simpleExampleNested cond e =
  if cond
    then throw e "Failed"
    else pure (\st -> do write st 100)

simpleExampleNested' ::
  Num s =>
  (st :> effs) =>
  Bool ->
  Either String (State s st -> Eff effs ())
simpleExampleNested' cond =
  runEff $ handleError $ \e -> simpleExampleNested cond e

bodyNested ::
  (err :> effs, st :> effs) =>
  Bool ->
  Error [Char] err ->
  State Int st ->
  Eff effs ((), Int)
bodyNested cond e st =
  if cond
    then throw e "Failed"
    else handleState 0 $ \st0 -> do
      s <- read st
      write st0 s

exampleNested ::
  (err :> effs, st :> effs, st :> effs0, st0 :> effs0) =>
  Bool ->
  Error String err ->
  State Int st ->
  Eff
    effs
    (State Int st0 -> Eff effs0 ())
exampleNested cond = \e st ->
  if cond
    then do
      write st 1
      throw e "Failed"
    else pure (\st0 -> do write st 2; modify st0 (+ 1))

exampleNested1 ::
  (err :> effs, st :> effs, st :> effs0, st0 :> effs0) =>
  Bool ->
  Error String err ->
  State Int st ->
  State Int st0 ->
  Eff effs (Eff effs0 ())
exampleNested1 cond = \e st st0 -> do
  r <- exampleNested cond e st
  pure (r st0)

exampleNested2 ::
  (err :> effs, st :> effs, st0 :> effs) =>
  Bool ->
  Error String err ->
  State Int st ->
  State Int st0 ->
  Eff effs ()
exampleNested2 cond = \e st st0 ->
  join (exampleNested1 cond e st st0)

exampleNestedRun :: Bool -> ((Either String (), Int), Int)
exampleNestedRun cond =
  runEff $
    handleState 1000 $ \st0 ->
      handleState 0 $ \st ->
        handleError $ \e ->
          exampleNested2 cond e st st0

-- This can't work because we have to work out how to find the subtree
-- relation for a variable of existential type.
--
--        handleErrorX $ \h e ->
--          exampleNested2 (h, _, _) cond e st st0
--
-- • Found hole: _ :: st1 :> effs'
--  Where: ‘effs'’ is a rigid type variable bound by
--           a type expected by the context:
--             forall (err :: Rose Effect) (effs' :: Rose Effect).
--             (err :> effs') -> Error String err -> Eff effs' ()
--           at /home/tom/Haskell/AD/Eff-Args/app/Rose.hs:(232,24)-(233,48)
--         ‘st1’ is a rigid type variable bound by
--           a type expected by the context:
--             forall (st1 :: Rose Effect).
--             State Int st1
--             -> Eff (st1 :& (st :& 'Branch '[])) (Either String ())
--           at /home/tom/Haskell/AD/Eff-Args/app/Rose.hs:(228,23)-(233,48)

handleError' ::
  (e -> r) ->
  (forall err. Error e err -> Eff (err :& effs) r) ->
  Eff effs r
handleError' h f = do
  r1 <- handleError f
  pure $ case r1 of
    Right r -> r
    Left l -> h l

type EarlyReturn = Error

newtype MustReturnEarly = MustReturnEarly Void

returnedEarly :: MustReturnEarly -> a
returnedEarly (MustReturnEarly v) = absurd v

withEarlyReturn ::
  (forall err. EarlyReturn r err -> Eff (err :& effs) MustReturnEarly) ->
  Eff effs r
withEarlyReturn f = handleError' id (fmap returnedEarly . f)

earlyReturn :: err :> effs => EarlyReturn r err -> r -> Eff effs a
earlyReturn = throw

evalState ::
  s ->
  (forall st. State s st -> Eff (st :& effs) a) ->
  Eff effs a
evalState s f = fmap fst (handleState s f)

(!??) :: [a] -> Int -> Maybe a
xs !?? i = runEff $
  withEarlyReturn $ \ret -> do
    evalState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (earlyReturn ret (Just a))
        write s (i' + 1)
    earlyReturn ret Nothing

data Compound e es where
  Compound ::
    Proxy# err ->
    Proxy# st ->
    Error e err ->
    State Int st ->
    Compound e (err :& st)

inComp :: forall a b c r. a :> b => b :> c => (a :> c => r) -> r
inComp k = case have (cmp (has @a @b) (has @b @c)) of Dict -> k

putC :: forall ss es e. ss :> es => Compound e ss -> Int -> Eff es ()
putC = \case Compound _ (_ :: Proxy# st) _ h -> inComp @st @ss @es (write h)

getC :: forall ss es e. ss :> es => Compound e ss -> Eff es Int
getC = \case Compound _ (_ :: Proxy# st) _ h -> inComp @st @ss @es (read h)

throwErrorC :: forall ss es e a. ss :> es => Compound e ss -> e -> Eff es a
throwErrorC = \case
  Compound (_ :: Proxy# err) _ h _ ->
    inComp @err @ss @es (throw h)

runC ::
  Int ->
  (forall ss. Compound e ss -> Eff (ss :& es) r) ->
  Eff es (Either e r, Int)
runC st f =
  evalState st $ \s -> do
    e <- handleError $ \e ->
      case have (assoc1 (##)) of
        Dict -> weakenEff (assoc1 (##)) (f (Compound proxy# proxy# e s))
    s' <- read s
    pure (e, s')

runC2 ::
  State Int st ->
  (forall ss. Compound e (ss :& st) -> Eff (ss :& es) r) ->
  Eff es (Either e r)
runC2 s f =
  handleError $ \e ->
    f (Compound proxy# proxy# e s)

runC' ::
  Int ->
  (forall ss. Compound r ss -> Eff (ss :& es) r) ->
  Eff es r
runC' st f = fmap fst $ do
  (e, s) <- runC st f
  pure (either id id e, s)

(!???) :: [a] -> Int -> Maybe a
xs !??? i = runEff $
  runC' 0 $ \c -> do
    for_ xs $ \a -> do
      i' <- getC c
      when (i == i') (throwErrorC c (Just a))
      putC c (i' + 1)
    pure Nothing

yieldToList ::
  (forall eff. Stream a eff -> Eff (eff :& effs) r) ->
  Eff effs ([a], r)
yieldToList f = do
  evalState [] $ \(s :: State lo st) -> do
    r <- forEach (weakenEff (b (drop (eq (##)))) . f) $ \i ->
      modify s (i :)
    as <- read s
    pure (reverse as, r)

exampleStream :: [Int]
exampleStream = fst $
  runEff $
    yieldToList $ \y' ->
      forEach (iter y') $ \n -> threeMore y' n
  where
    iter y' y = do
      yield y 10
      yield y 20
      yield y 30
      yield y' 666

threeMore :: eff :> effs => Stream Int eff -> Int -> Eff effs ()
threeMore y i = do
  yield y i
  yield y (i + 1)
  yield y (i + 2)

(!!??) :: [a] -> Int -> ([String], Maybe a)
xs !!?? i = runEff $
  yieldToList $ \y -> do
    withEarlyReturn $ \ret -> do
      evalState 0 $ \s -> do
        for_ xs $ \a -> do
          i' <- read s
          yield y ("At index " ++ show i')
          when (i == i') (earlyReturn ret (Just a))
          write s (i' + 1)
      earlyReturn ret Nothing
