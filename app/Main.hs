{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Control.Exception (Exception, throw, throwIO, try, tryJust)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Reflection
import Data.Typeable (Typeable)
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

newtype ErrorT e = ErrorT e

instance Show (ErrorT e) where
  show = pure "<ErrorT e>"

instance Typeable e => Exception (ErrorT e)

data Error e s = Error

newtype State s e = State (IORef s)

class (e :: Type) :> (es :: [Type])

instance {-# OVERLAPPING #-} e :> (e : es)

instance e :> es => e :> (x : es)

raise :: (Typeable e, s :> ss) => Error e s -> e -> Eff ss a
raise Error e = Eff (throw (ErrorT e))

handleError ::
  Typeable e =>
  (forall s. Error e s -> Eff (s : ss) a) ->
  Eff ss (Either e a)
handleError f = Eff $ do
  flip fmap (try (unsafeUnEff (f Error))) $ \case
    Left (ErrorT e) -> Left e
    Right r -> Right r

read :: e :> es => State s e -> Eff es s
read (State r) = Eff (readIORef r)

write :: e :> es => State s e -> s -> Eff es ()
write (State r) s = Eff (writeIORef r s)

modify :: (e :> es) => State t e -> (t -> t) -> Eff es ()
modify state f = do
  s <- read state
  write state (f s)

handleState ::
  forall a s es.
  s ->
  (forall e. State s e -> Eff (e : es) a) ->
  Eff es (a, s)
handleState s f = Eff $ do
  r <- newIORef s
  let state = State r :: State s ()

  unsafeUnEff $ do
    a <- f state
    s' <- read state
    pure (a, s')

main :: IO ()
main = putStrLn "Hello, Haskell!"

example :: s :> ss => Error String s -> Eff ss a
example = (\e -> raise e "My error")

example2 :: Eff ss (Either String a)
example2 = handleError example

example3 :: Either String a
example3 = runEff example2

example4 :: Error String s -> Eff ss (Error String s)
example4 = pure

-- Couldn't match type ‘a’ with ‘Error String s’ because type variable
-- ‘s’ would escape its scope
-- exampleDoesn'tWork = handleError example4

example5 :: (e :> es, s :> es) => Error [Char] s -> State Int e -> Eff es ()
example5 e s = do
  foo <- read s
  modify s (+ 1)
  _ <- raise e ("Hello " ++ show foo)
  modify s (+ 1)

example6 :: e' :> es => Error String e' -> Eff es ((), Int)
example6 = \e -> handleState 10 (example5 e)

example6a :: st :> es => State Int st -> Eff es (Either [Char] ())
example6a = \s -> handleError (\e -> example5 e s)

example7 :: Eff es (Either String ((), Int))
example7 = handleError example6

example7a :: Eff es (Either String (), Int)
example7a = handleState 10 example6a

data TypeLevel s a

class HasError e s | s -> e where
  haveError :: Error e s

instance Reifies s (Error e s') => HasError e (TypeLevel s s') where
  haveError = let !Error = reflect @s Proxy in Error

class HasState s e | e -> s where
  haveState :: State s e

instance Reifies s (State s' e) => HasState s' (TypeLevel s e) where
  haveState =
    let State s = reflect @s @(State s' e) Proxy in State s

raiseE :: forall s e ss a. (Typeable e, HasError e s, s :> ss) => e -> Eff ss a
raiseE = raise (haveError @e @s)

readS :: forall s e ss. s :> ss => HasState e s => Eff ss e
readS = read (haveState @e @s)

writeS :: forall s e ss. (HasState e s, s :> ss) => e -> Eff ss ()
writeS = write (haveState @e @s)

modifyS :: forall e s ss. (HasState s e, e :> ss) => (s -> s) -> Eff ss ()
modifyS f = do
  s <- readS @e
  writeS @e (f s)

exampleS5 ::
  forall ex st ss.
  (st :> ss, ex :> ss, HasError String ex, HasState Int st) =>
  Eff ss ()
exampleS5 = do
  foo <- readS @st
  modifyS @st (+ 1)
  _ <- raiseE @ex ("Hello " ++ show foo)
  modifyS @st (+ 1)

handleErrorE ::
  forall e ss a.
  Typeable e =>
  (forall s. HasError e s => Proxy s -> Eff (s : ss) a) ->
  Eff ss (Either e a)
handleErrorE f =
  handleError
    ( \(e :: Error e s') ->
        reify @(Error e s')
          e
          ( \(_ :: Proxy s) ->
              coerceEff (f @(TypeLevel s s') (Proxy @_))
          )
    )
  where
    coerceEff = Eff . unsafeUnEff

handleStateS ::
  forall st a es.
  st ->
  (forall e. HasState st e => Proxy e -> Eff (e : es) a) ->
  Eff es (a, st)
handleStateS st f =
  handleState
    st
    ( \(s :: State st e) ->
        reify @(State st e)
          s
          ( \(_ :: Proxy s) ->
              coerceEff (f @(TypeLevel s e) (Proxy @_))
          )
    )
  where
    coerceEff = Eff . unsafeUnEff

example6S :: forall st ss. (HasState Int st, st :> ss) => Eff ss (Either String ())
example6S = handleErrorE (\(Proxy :: Proxy ex) -> exampleS5 @ex @st)

example7S :: Eff ss (Either String (), Int)
example7S = handleStateS 10 (\(Proxy :: Proxy st) -> example6S @st)

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
