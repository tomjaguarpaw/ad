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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UnliftedNewtypes #-}

module Rose where

import Control.Monad (join, when)
import Data.Foldable (for_)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import GHC.IO.Unsafe (unsafePerformIO)
import Main (withScopedException_)
import Prelude hiding (drop, read, return)

data Rose a = Branch (Rose a) (Rose a)

type (:&) = 'Branch

data Effect

newtype Eff (es :: Rose Effect) a = Eff {unsafeUnEff :: IO a}
  deriving stock (Functor)
  deriving newtype (Applicative, Monad)

runEff :: (forall es. Eff es a) -> a
runEff = unsafePerformIO . unsafeUnEff

weakenEff :: t :> t' -> Eff t r -> Eff t' r
weakenEff _ = Eff . unsafeUnEff

newtype Error e s = Error (forall a. e -> IO a)

newtype State s e = State (IORef s)

newtype Yield a b s = Yield (a -> IO b)

-- Hmm, cartesian category
data (a :: Rose r) :> (b :: Rose r) where
  Eq :: a :> a
  Fst :: a :> (a :& b)
  Snd :: a :> (b :& a)
  Cmp :: a :> b -> b :> c -> a :> c
  Bimap :: a :> b -> c :> d -> (a :& c) :> (b :& d)
  Assoc1 :: ((a :& b) :& c) :> (a :& (b :& c))

drop :: a :> b -> a :> (c :& b)
drop = w2 . b

here :: a :> b -> a :> (b :& c)
here = w . b2

w :: (a :& b) :> c -> a :> c
w = Cmp Fst

w2 :: (b :& a) :> c -> a :> c
w2 = Cmp Snd

b2 :: (a :> b) -> (a :& c) :> (b :& c)
b2 = flip Bimap Eq

b :: (a :> b) -> (c :& a) :> (c :& b)
b = Bimap Eq

throw :: err :> effs -> Error e err -> e -> Eff effs a
throw _ (Error throw_) e = Eff (throw_ e)

handleError ::
  (forall err. Error e err -> Eff (err :& effs) a) ->
  Eff effs (Either e a)
handleError f =
  Eff $ withScopedException_ (\throw_ -> unsafeUnEff (f (Error throw_)))

handleErrorX ::
  (forall err effs'. err :> effs' -> Error e err -> Eff effs' a) ->
  Eff effs (Either e a)
handleErrorX f = handleError (f (here Eq))

read :: st :> effs -> State s st -> Eff effs s
read _ (State r) = Eff (readIORef r)

write :: st :> effs -> State s st -> s -> Eff effs ()
write _ (State r) s = Eff (writeIORef r s)

modify :: st :> effs -> State s st -> (s -> s) -> Eff effs ()
modify p state f = do
  s <- read p state
  write p state $! f s

handleState ::
  s ->
  (forall st. State s st -> Eff (st :& effs) a) ->
  Eff effs (a, s)
handleState s f = Eff $ do
  state <- fmap State (newIORef s)
  unsafeUnEff $ do
    a <- f state
    s' <- read (here Eq) state
    pure (a, s')

yield :: eff :> effs -> Yield a b eff -> a -> Eff effs b
yield _ (Yield f) a = Eff (f a)

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

example :: err :> effs -> Error String err -> Eff effs a
example = (\p e -> throw p e "My error")

example2 :: Eff effs (Either String a)
example2 = handleError (example (here Eq))

example2X :: Eff effs (Either String a)
example2X = handleErrorX example

example3 :: Either String a
example3 = runEff example2

example5 ::
  (st :> effs, err :> effs) ->
  Error String err ->
  State Int st ->
  Eff effs ()
example5 (pst, per) e s = do
  foo <- read pst s
  modify pst s (+ 1)
  _ <- throw per e ("Hello " ++ show foo)
  modify pst s (+ 1)

example6 :: err :> effs -> Error String err -> Eff effs ((), Int)
example6 p = \e -> handleState 10 (example5 (here Eq, drop p) e)

example6a :: st :> effs -> State Int st -> Eff effs (Either String ())
example6a p = \s -> handleError (\e -> example5 (drop p, here Eq) e s)

example7 :: Eff effs (Either String ((), Int))
example7 = handleError (example6 (here Eq))

example7a :: Eff effs (Either String (), Int)
example7a = handleState 10 (example6a (here Eq))

simpleExampleNested ::
  Num s =>
  (err :> effs1, st :> effs2) ->
  Bool ->
  Error String err ->
  Eff effs1 (State s st -> Eff effs2 ())
simpleExampleNested (per, pst) cond e =
  if cond
    then throw per e "Failed"
    else pure (\st -> do write pst st 100)

simpleExampleNested' ::
  Num s =>
  (st :> effs) ->
  Bool ->
  Either String (State s st -> Eff effs ())
simpleExampleNested' p cond =
  runEff $ handleError $ \e -> simpleExampleNested (here Eq, p) cond e

bodyNested ::
  (err :> effs, st :> effs) ->
  Bool ->
  Error [Char] err ->
  State Int st ->
  Eff effs ((), Int)
bodyNested (per, pst) cond e st =
  if cond
    then throw per e "Failed"
    else handleState 0 $ \st0 -> do
      s <- read (drop pst) st
      write (here Eq) st0 s

exampleNested ::
  (err :> effs, st :> effs, st :> effs0, st0 :> effs0) ->
  Bool ->
  Error String err ->
  State Int st ->
  Eff
    effs
    (State Int st0 -> Eff effs0 ())
exampleNested (per, pst, pst0, pst00) cond = \e st ->
  if cond
    then do
      write pst st 1
      throw per e "Failed"
    else pure (\st0 -> do write pst0 st 2; modify pst00 st0 (+ 1))

exampleNested1 ::
  (err :> effs, st :> effs, st :> effs0, st0 :> effs0) ->
  Bool ->
  Error String err ->
  State Int st ->
  State Int st0 ->
  Eff effs (Eff effs0 ())
exampleNested1 ps cond = \e st st0 -> do
  r <- exampleNested ps cond e st
  pure (r st0)

exampleNested2 ::
  (err :> effs, st :> effs, st0 :> effs) ->
  Bool ->
  Error String err ->
  State Int st ->
  State Int st0 ->
  Eff effs ()
exampleNested2 (per, pst, pst0) cond = \e st st0 ->
  join (exampleNested1 (per, pst, pst, pst0) cond e st st0)

exampleNestedRun :: Bool -> ((Either String (), Int), Int)
exampleNestedRun cond =
  runEff $
    handleState 1000 $ \st0 ->
      handleState 0 $ \st ->
        handleError $ \e ->
          exampleNested2 (here Eq, drop (here Eq), drop (drop (here Eq))) cond e st st0

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
        i' <- read (here Eq) s
        when (i == i') (throw (drop (here Eq)) e a)
        write (here Eq) s (i' + 1)
    pure Nothing

data Compound e es where
  Compound ::
    es ~ (err :& st) =>
    Error e err ->
    State Int st ->
    Compound e es

putC :: ss :> es -> Compound e ss -> Int -> Eff es ()
putC p = \case Compound _ h -> write (w2 p) h

getC :: ss :> es -> Compound e ss -> Eff es Int
getC p = \case Compound _ h -> read (w2 p) h

throwErrorC :: ss :> es -> Compound e ss -> e -> Eff es a
throwErrorC p = \case Compound h _ -> throw (w p) h

runC ::
  forall e es r.
  Int ->
  (forall ss. Compound e ss -> Eff (ss :& es) r) ->
  Eff es (Either e r)
runC st f =
  evalState st $ \s ->
    handleError $ \e ->
      weakenEff Assoc1 (f (Compound e s))

runC' ::
  Int ->
  (forall ss. Compound r ss -> Eff (ss :& es) r) ->
  Eff es r
runC' st f = fmap (either id id) (runC st f)

(!???) :: [a] -> Int -> Maybe a
xs !??? i = runEff $
  runC' 0 $ \c -> do
    for_ xs $ \a -> do
      i' <- getC (here Eq) c
      when (i == i') (throwErrorC (here Eq) c (Just a))
      putC (here Eq) c (i' + 1)
    pure Nothing

data Compound2 e es where
  Compound2 ::
    es ~ (er :& st) =>
    Error e er ->
    State Int st ->
    Compound2 e es

putC2 :: ss :> es -> Compound2 e ss -> Int -> Eff es ()
putC2 p = \case Compound2 _ h -> write (w2 p) h

runC2 ::
  State Int st ->
  (forall ss. Compound2 e (ss :& st) -> Eff (ss :& es) r) ->
  Eff es (Either e r)
runC2 s f =
  handleError $ \e ->
    f (Compound2 e s)

yieldToList ::
  (forall eff. Yield a () eff -> Eff (eff :& effs) r) ->
  Eff effs ([a], r)
yieldToList f = do
  evalState [] $ \s -> do
    r <- forEach (weakenEff (b (drop Eq)) . f) $ \i ->
      modify (here Eq) s (i :)
    as <- read (here Eq) s
    pure (reverse as, r)

exampleYield :: [Int]
exampleYield = fst $
  runEff $
    yieldToList $
      \y' ->
        forEach
          ( \y -> do
              yield (here Eq) y 10
              yield (here Eq) y 20
              yield (here Eq) y 30
              yield (drop (here Eq)) y' 666
          )
          $ \n -> threeMore (here Eq) y' n

threeMore :: eff :> effs -> Yield Int () eff -> Int -> Eff effs ()
threeMore h y i = do
  yield h y i
  yield h y (i + 1)
  yield h y (i + 2)

(!!??) :: [a] -> Int -> ([String], Maybe a)
xs !!?? i = runEff $
  yieldToList $ \y -> do
    handleError' Just $ \e -> do
      evalState 0 $ \s -> do
        for_ xs $ \a -> do
          i' <- read (here Eq) s
          yield (drop (drop (here Eq))) y ("At index " ++ show i')
          when (i == i') (throw (drop (here Eq)) e a)
          write (here Eq) s (i' + 1)
      pure Nothing
