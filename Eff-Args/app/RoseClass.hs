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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UnliftedNewtypes #-}

module RoseClass where

import Control.Monad (join, when)
import Data.Data (Proxy (Proxy))
import Data.Foldable (for_)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
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

runEff :: (forall es. Eff es a) -> a
runEff = unsafePerformIO . unsafeUnEff

weakenEff :: t `In` t' -> Eff t r -> Eff t' r
weakenEff _ = Eff . unsafeUnEff

newtype Error e s = Error (forall a. e -> IO a)

newtype State s e = State (IORef s)

newtype Yield a b s = Yield (a -> IO b)

newtype In (a :: Rose r) (b :: Rose r) = In# (# #)

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

data InLifted a b = InLifted (In a b)

class (a :: k) :> (b :: k)

-- Hmm, can type class members not have unlifted type?
-- Actually, probably don't need this
--  in_ :: InLifted a b

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
  forall effs e a.
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
handleState s f = Eff $ do
  state <- fmap State (newIORef s)
  unsafeUnEff $ do
    a <- f state
    s' <- read state
    pure (a, s')

yield :: eff :> effs => Yield a b eff -> a -> Eff effs b
yield (Yield f) a = Eff (f a)

handleYield ::
  (a -> Eff effs b) ->
  (z -> Eff effs r) ->
  (forall eff. Yield a b eff -> Eff (eff :& effs) z) ->
  Eff effs r
handleYield update finish f = do
  z <- forEach f update
  finish z

forEach ::
  (forall eff. Yield a b eff -> Eff (eff :& effs) z) ->
  (a -> Eff effs b) ->
  Eff effs z
forEach f h = Eff $ unsafeUnEff (f (Yield (unsafeUnEff . h)))

forEachP ::
  (forall eff. Proxy eff -> Yield a b eff -> Eff (eff :& effs) z) ->
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

evalState ::
  s ->
  (forall st. State s st -> Eff (st :& effs) a) ->
  Eff effs a
evalState s f = fmap fst (handleState s f)

(!??) :: [a] -> Int -> Maybe a
xs !?? i = runEff $
  handleError' Just $ \e -> do
    evalState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (throw e a)
        write s (i' + 1)
    pure Nothing

data Compound e es where
  Compound ::
    es ~ (err :& st) =>
    Error e err ->
    State Int st ->
    Compound e es

putC :: forall ss es e. ss :> es => Compound e ss -> Int -> Eff es ()
putC = \case
  Compound _ (h :: State Int st) ->
    let d = has :: ss `In` es
        d1 = sndI (##) :: st `In` ss
        d2 = cmp d1 d
     in case have d2 of Dict -> write h

getC :: forall ss es e. ss :> es => Compound e ss -> Eff es Int
getC = \case
  Compound _ (h :: State Int st) ->
    let d = has :: ss `In` es
        d1 = sndI (##) :: st `In` ss
        d2 = cmp d1 d
     in case have d2 of Dict -> read h

throwErrorC :: forall ss es e a. ss :> es => Compound e ss -> e -> Eff es a
throwErrorC = \case
  Compound (h :: Error e err) _->
    let d = has :: ss `In` es
        d1 = fstI (##) :: err `In` ss
        d2 = cmp d1 d
     in case have d2 of Dict -> throw h

runC ::
  forall e es r.
  Int ->
  (forall ss. Compound e ss -> Eff (ss :& es) r) ->
  Eff es (Either e r)
runC st f =
  evalState st $ \s ->
    handleError $ \e ->
      case have (assoc1 (# #)) of
        Dict -> weakenEff (assoc1 (# #)) (f (Compound e s))

runC2 ::
  State Int st ->
  (forall ss. Compound e (ss :& st) -> Eff (ss :& es) r) ->
  Eff es (Either e r)
runC2 s f =
  handleError $ \e ->
    f (Compound e s)

runC' ::
  Int ->
  (forall ss. Compound r ss -> Eff (ss :& es) r) ->
  Eff es r
runC' st f = fmap (either id id) (runC st f)

(!???) :: [a] -> Int -> Maybe a
xs !??? i = runEff $
  runC' 0 $ \c -> do
    for_ xs $ \a -> do
      i' <- getC c
      when (i == i') (throwErrorC c (Just a))
      putC c (i' + 1)
    pure Nothing

yieldToList ::
  forall effs a r.
  (forall eff. Yield a () eff -> Eff (eff :& effs) r) ->
  Eff effs ([a], r)
yieldToList f = do
  evalState [] $ \(s :: State lo st) -> do
    r <- forEach (weakenEff (b (drop (eq (# #)))) . f) $ \i ->
      modify s (i :)
    as <- read s
    pure (reverse as, r)

exampleYield :: [Int]
exampleYield = fst $
  runEff $
    yieldToList $
      \y' ->
        forEach
          ( \y -> do
              yield y 10
              yield y 20
              yield y 30
              yield y' 666
          )
          $ \n -> threeMore y' n

threeMore :: eff :> effs => Yield Int () eff -> Int -> Eff effs ()
threeMore y i = do
  yield y i
  yield y (i + 1)
  yield y (i + 2)

(!!??) :: [a] -> Int -> ([String], Maybe a)
xs !!?? i = runEff $
  yieldToList $ \y -> do
    handleError' Just $ \e -> do
      evalState 0 $ \s -> do
        for_ xs $ \a -> do
          i' <- read s
          yield y ("At index " ++ show i')
          when (i == i') (throw e a)
          write s (i' + 1)
      pure Nothing
