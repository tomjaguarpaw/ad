-- cabal run tmp-strict -- +RTS -s

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

module Main where

import Strict

import Data.List (foldl')

import qualified Data.Map.Lazy as L
import qualified Data.Map.Strict as S

million :: Integer
million = 1000 * 1000

pairFoldBad :: (Integer, Integer)
pairFoldBad = foldl' f (0, 0) [1..million]
  where f (count, theSum) x = (count + 1, theSum + x)

pairFoldBangs :: (Integer, Integer)
pairFoldBangs = foldl' f (0, 0) [1..million]
  where f (!count, !theSum) x = (count + 1, theSum + x)

pairFoldSeq :: (Integer, Integer)
pairFoldSeq = foldl' f (0, 0) [1..million]
  where f (count, theSum) x = let count'  = count + 1
                                  theSum' = theSum + x
                              in count' `seq` theSum' `seq` (count', theSum')

pairFoldBangsAwkward :: (Integer, Integer)
pairFoldBangsAwkward = foldl' f (0, 0) [1..million]
  where f (count, theSum) x = let !count'  = count + 1
                                  !theSum' = theSum + x
                              in (count', theSum')

pairFoldBangsAwkward2 :: (Integer, Integer)
pairFoldBangsAwkward2 = foldl' f (0, 0) [1..million]
  where f (count, theSum) _ = ((,) $! count + 1) $! theSum

data StrictPair a b = StrictPair !a !b deriving Show

pairFoldStrictPair :: StrictPair Integer Integer
pairFoldStrictPair = foldl' f (StrictPair 0 0) [1..million]
  where f (StrictPair count theSum) x = StrictPair (count + 1) (theSum + x)

pairFoldStrict :: Strict (Integer, Integer)
pairFoldStrict = foldl' f (Strict (0, 0)) [1..million]
  where f (Strict (count, theSum)) x = strict (count + 1, theSum + x)

maybeFoldBad :: (Integer, Maybe Integer)
maybeFoldBad = foldl' f (0, Nothing) [1..million]
  where f (i, Nothing) x = (i + 1, Just x)
        f (i, Just j)  x = (i + 2, Just (j + x))

maybeFoldStillBad :: StrictPair Integer (Maybe Integer)
maybeFoldStillBad = foldl' f (StrictPair 0 Nothing) [1..million]
  where f (StrictPair i Nothing)  x = StrictPair (i + 1) (Just x)
        f (StrictPair i (Just j)) x = StrictPair (i + 2) (Just (j + x))

maybeFoldBangs :: (Integer, Maybe Integer)
maybeFoldBangs = foldl' f (0, Nothing) [1..million]
  where f (!i, Nothing) x = (i + 1, Just x)
        f (!i, Just !j) x = (i + 2, Just (j + x))

data StrictMaybe a = StrictNothing | StrictJust !a deriving Show

maybeFoldStrictMaybe :: StrictPair Integer (StrictMaybe Integer)
maybeFoldStrictMaybe = foldl' f (StrictPair 0 StrictNothing) [1..million]
  where f (StrictPair i StrictNothing)  x = StrictPair (i + 1) (StrictJust x)
        f (StrictPair i (StrictJust j)) x = StrictPair (i + 2) (StrictJust (j + x))

maybeFoldStrict :: Strict (Integer, Strict (Maybe Integer))
maybeFoldStrict = foldl' f (strict (0, strict Nothing)) [1..million]
  where f (Strict (i, Strict Nothing)) x  = strict (i + 1, strict $ Just x)
        f (Strict (i, Strict (Just j))) x = strict (i + 2, strict $ Just (j + x))

countParity :: [Integer] -> L.Map String Integer
countParity = foldl' inc (L.fromList [("even", 0), ("odd", 0)])
    where inc m n = if n `mod` 2 == 0
                    then L.adjust (+1) "even" m
                    else L.adjust (+1) "odd" m

countParityStrict :: [Integer] -> S.Map String Integer
countParityStrict = foldl' inc (S.fromList [("even", 0), ("odd", 0)])
    where inc m n = if n `mod` 2 == 0
                    then S.adjust (+1) "even" m
                    else S.adjust (+1) "odd" m

foo :: Strict (Int, Int) -> ()
foo (Strict (a, b)) = a `seq` b `seq` ()

bar :: Strict (Int, Int) -> ()
bar (unstrict->(a, b)) = a `seq` b `seq` ()

main :: IO ()
main = do
  print (countParityStrict [1..million])
  print (strict (1, 2))
  print (strict (Just 1))
  print (strict (Nothing :: Maybe Int))
--  print (strict (putStrLn "Hello"))
--  print (strict (1 :: Int))
--  print (strict ([] :: [Int]))
--  print (Strict (Strict (Nothing :: Maybe Int)))
  -- ^ emits custom type error
