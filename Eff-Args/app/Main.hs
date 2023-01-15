{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Control.Exception (Exception, throwIO, tryJust)
import Control.Monad (join, when)
import Data.Kind (Type)
import Data.Foldable (for_)
import Data.Proxy (Proxy (Proxy))
import Data.Reflection
import qualified Data.Unique
import Data.Void (Void)
import GHC.IO.Unsafe (unsafePerformIO)
import GHC.IORef (IORef, newIORef, readIORef, writeIORef)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (read)

newtype Eff (es :: [Type]) a = Eff {unsafeUnEff :: IO a}
  deriving stock (Functor)
  deriving newtype (Applicative, Monad)

runEff :: Eff '[] a -> a
runEff = unsafePerformIO . unsafeUnEff

removeEff :: (forall eff. Eff (eff : effs) a) -> Eff effs a
removeEff = Eff . unsafeUnEff

newtype Error e s = Error (forall a. e -> IO a)

newtype State s e = State (IORef s)

class (e :: Type) :> (es :: [Type])

instance {-# OVERLAPPING #-} e :> (e : es)

instance e :> es => e :> (x : es)

throw :: err :> effs => Error e err -> e -> Eff effs a
throw (Error throw_) e = Eff (throw_ e)

handleError ::
  (forall err. Error e err -> Eff (err : effs) a) ->
  Eff effs (Either e a)
handleError f =
  Eff $ withScopedException_ (\throw_ -> unsafeUnEff (f (Error throw_)))

handleError' ::
  (e -> r) ->
  (forall err. Error e err -> Eff (err : effs) r) ->
  Eff effs r
handleError' h f = do
  r1 <- handleError f
  pure $ case r1 of
    Right r -> r
    Left l -> h l

handleError'' ::
  (forall err. Error r err -> Eff (err : effs) r) ->
  Eff effs r
handleError'' = handleError' id

read :: st :> effs => State s st -> Eff effs s
read (State r) = Eff (readIORef r)

write :: st :> effs => State s st -> s -> Eff effs ()
write (State r) s = Eff (writeIORef r s)

modify :: st :> effs => State s st -> (s -> s) -> Eff effs ()
modify state f = do
  s <- read state
  write state (f s)

handleState ::
  s ->
  (forall st. State s st -> Eff (st : effs) a) ->
  Eff effs (a, s)
handleState s f = Eff $ do
  state <- fmap State (newIORef s)

  unsafeUnEff $ do
    a <- f state
    s' <- read state
    pure (a, s')

evalState ::
  s ->
  (forall st. State s st -> Eff (st : effs) a) ->
  Eff effs a
evalState s f = fmap fst (handleState s f)

evalStateT ::
  forall (t :: (Type -> Type) -> Type -> Type) s effs a.
  (forall m. Monad m => Monad (t m)) =>
  (forall m r. Monad m => m r -> t m r) ->
  (forall m n b. Monad m => (forall r. m r -> n r) -> t m b -> t n b) ->
  s ->
  (forall st. State s st -> t (Eff (st : effs)) a) ->
  t (Eff effs) a
evalStateT lift hoist s f = hoist Eff $ do
  state <- lift (fmap State (newIORef s))
  hoist unsafeUnEff (f state)

main :: IO ()
main = putStrLn "Hello, Haskell!"

example :: err :> effs => Error String err -> Eff effs a
example = (\e -> throw e "My error")

example2 :: Eff effs (Either String a)
example2 = handleError example

example3 :: Either String a
example3 = runEff example2

example4 :: Error String err -> Eff effs (Error String err)
example4 = pure

-- Couldn't match type ‘a’ with ‘Error String s’ because type variable
-- ‘s’ would escape its scope
-- exampleDoesn'tWork = handleError example4

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
  (err :> effs1, st :> effs2, Num s) =>
  Bool ->
  Error String err ->
  Eff effs1 (State s st -> Eff effs2 ())
simpleExampleNested cond e =
  if cond
    then throw e "Failed"
    else pure (\st -> do write st 100)

simpleExampleNested' ::
  (st :> effs, Num s) =>
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

-- Needs a type parameter that reflects the structure of the
-- computation so there's exactly one constructor to match on at each
-- stage
data Ravelled effs l l2 r where
  RavelEff :: Eff effs r -> Ravelled effs '[] '[] r
  RavelArg ::
    (forall eff. eff :> effs => f eff -> Ravelled effs l l2 r) ->
    Ravelled effs (f : l) l2 r
  RavelDict ::
    forall eff effs l l2 r.
    (eff :> effs => Ravelled effs l l2 r) ->
    Ravelled effs l (eff : l2) r

data ForallRavelled l l2 r where
  ForallRavelled :: (forall effs. Ravelled effs l l2 r) -> ForallRavelled l l2 r

data Dict c where
  Dict :: c => Dict c

exampleRavelled ::
  forall err st effs.
  (err :> effs, st :> effs) =>
  Bool ->
  Error String err ->
  State Int st ->
  Eff
    effs
    (ForallRavelled '[State Int] '[st] ())
exampleRavelled cond = \e st ->
  if cond
    then do
      write st 1
      throw e "Failed"
    else pure (ForallRavelled $ RavelDict @st $ RavelArg $ \st0 -> RavelEff (do write st 2; modify st0 (+ 1)))

exampleRavelledRun ::
  (err :> effs, st :> effs) =>
  Bool ->
  Error String err ->
  State Int st ->
  Eff effs ((), Int)
exampleRavelledRun cond e st = do
  r <- exampleRavelled cond e st
  handleState
    100
    ( \st0 ->
        case r of
          ForallRavelled r1 ->
            case r1 of
              RavelDict g ->
                case g of
                  RavelArg f ->
                    case f st0 of
                      RavelEff eff -> eff
    )

exampleRavelledRunAll :: Bool -> (Either String ((), Int), Int)
exampleRavelledRunAll cond =
  runEff $
    handleState 200 $ \st ->
      handleError $ \e ->
        exampleRavelledRun cond e st

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

data Tag s

class Has t s | s -> t where
  have :: forall s'. t s'

data Forall f where
  Forall :: {unForall :: forall a. f a} -> Forall f

instance Reifies s (Forall t) => Has t (Tag s) where
  have = unForall (reflect @s Proxy)

type HasError e s = Has (Error e) s

type HasState s = Has (State s)

throwE ::
  forall err e effs a.
  (Has (Error e) err, err :> effs) =>
  e ->
  Eff effs a
throwE = throw (have @(Error e) @err @err)

readS :: forall st s effs. st :> effs => Has (State s) st => Eff effs s
readS = read (have @(State s) @st @st)

writeS :: forall st s effs. (Has (State s) st, st :> effs) => s -> Eff effs ()
writeS = write (have @(State s) @st @st)

modifyS ::
  forall st s effs.
  (Has (State s) st, st :> effs) =>
  (s -> s) ->
  Eff effs ()
modifyS f = do
  s <- readS @st
  writeS @st (f s)

exampleS5 ::
  forall ex st ss.
  (st :> ss, ex :> ss, HasError String ex, HasState Int st) =>
  Eff ss ()
exampleS5 = do
  foo <- readS @st
  modifyS @st (+ 1)
  _ <- throwE @ex ("Hello " ++ show foo)
  modifyS @st (+ 1)

handleErrorE ::
  forall e effs a.
  (forall err. Has (Error e) err => Proxy err -> Eff (err : effs) a) ->
  Eff effs (Either e a)
handleErrorE f =
  handleError
    ( \(e :: Error e s') ->
        reify @(Forall (Error e))
          (forallError e)
          ( \(_ :: Proxy s) ->
              coerceEff (f @(Tag s) Proxy)
          )
    )
  where
    coerceEff = Eff . unsafeUnEff
    forallError e = Forall (let Error t = e in Error t)

handleStateS ::
  forall st a es.
  st ->
  (forall e. Has (State st) e => Proxy e -> Eff (e : es) a) ->
  Eff es (a, st)
handleStateS st f =
  handleState
    st
    ( \(s :: State st e) ->
        reify @(Forall (State st))
          (forallState s)
          ( \(_ :: Proxy s) ->
              coerceEff (f @(Tag s) Proxy)
          )
    )
  where
    coerceEff = Eff . unsafeUnEff
    forallState e = Forall (let State t = e in State t)

example6S ::
  forall st effs.
  (HasState Int st, st :> effs) =>
  Eff effs (Either String ())
example6S = handleErrorE (\(Proxy :: Proxy ex) -> exampleS5 @ex @st)

example7S :: Eff ss (Either String (), Int)
example7S = handleStateS 10 (\(Proxy :: Proxy st) -> example6S @st)

(!?) :: [a] -> Int -> Maybe a
xs !? i = runEff $
  handleError'' $ \e -> do
    evalState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (throw e (Just a))
        write s (i' + 1)
      throw e Nothing

(!??) :: [a] -> Int -> Maybe a
xs !?? i = runEff $
  handleError' Just $ \e -> do
    evalState 0 $ \s -> do
      for_ xs $ \a -> do
        i' <- read s
        when (i == i') (throw e a)
        write s (i' + 1)
    pure Nothing

-- withScopedException :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)

scopedExceptionExample :: IO (Either String (Either Int Void))
scopedExceptionExample = do
  withScopedException_ $ \throw1 ->
    withScopedException_ $ \throw2 ->
      if (1 :: Int) < 0
        then throw1 "Hello"
        else throw2 1234

-- ghci> scopedExceptionExample
-- Left "Hello"

data MyException where
  MyException :: e -> Data.Unique.Unique -> MyException

instance Show MyException where
  show _ = "<MyException>"

instance Exception MyException

withScopedException_ :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)
withScopedException_ f = do
  fresh <- Data.Unique.newUnique

  flip tryJust (f (\e -> throwIO (MyException e fresh))) $ \case
    MyException e tag ->
      -- unsafeCoerce is very unpleasant
      if tag == fresh then Just (unsafeCoerce e) else Nothing

data PromptTag a = PromptTag

newPromptTag :: IO (PromptTag a)
newPromptTag = undefined

prompt :: PromptTag a -> IO a -> IO a
prompt = undefined

control0 :: PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 = undefined

withScopedExceptionBad :: ((e -> IO (Either e r)) -> IO r) -> IO (Either e r)
withScopedExceptionBad body = do
  promptTag <- newPromptTag
  prompt promptTag $ do
    l <- control0 promptTag $ \myThrow -> do
      r <- body (myThrow . pure)
      pure (Right r)
    pure (Left l)

withScopedException :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)
withScopedException body = do
  promptTag <- newPromptTag
  prompt promptTag $ do
    r <- body (\e -> control0 promptTag (\_ -> pure (Left e)))
    pure (Right r)
