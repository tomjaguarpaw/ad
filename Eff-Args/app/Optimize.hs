module Optimize where

import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, put)
import Data.Foldable (for_)
import Data.Void (absurd)
import RoseClass
  ( earlyReturn,
    evalState,
    read,
    runEff,
    withEarlyReturn,
    write,
  )
import Prelude hiding (read)

lookup1 :: [a] -> Int -> Maybe a
xs `lookup1` n
  | n < 0 = Nothing
  | otherwise =
    foldr
      ( \x r k -> case k of
          0 -> Just x
          _ -> r (k -1)
      )
      (const Nothing)
      xs
      n

-- This generates STG of
-- lookup2 = \r [eta_B2 eta_B1] Optimize.lookup1 eta_B2 eta_B1
lookup2 :: [a] -> Int -> Maybe a
xs `lookup2` n
  | n < 0 = Nothing
  | otherwise = case flip evalStateT n $ do
    for_ xs $ \a -> do
      n' <- get
      when (n' == 0) (lift (Left (Just a)))
      put (n' - 1)
    lift (Left Nothing) of
    Left l -> l
    Right r -> absurd r

-- This generate complex STG
lookup3 :: [a] -> Int -> Maybe a
xs `lookup3` n
  | n < 0 = Nothing
  | otherwise = RoseClass.runEff $
    RoseClass.withEarlyReturn $ \ret -> do
      RoseClass.evalState n $ \s -> do
        for_ xs $ \a -> do
          n' <- RoseClass.read s
          when (n' == 0) (RoseClass.earlyReturn ret (Just a))
          RoseClass.write s (n' + 1)
        RoseClass.earlyReturn ret Nothing
