-- cabal run tmp-strict -- +RTS -s

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wall #-}

module Main where

import Data.List (foldl')
import Unsafe.Coerce

import qualified Data.Map.Lazy as L
import qualified Data.Map.Strict as S

class Strictly a where
  data Strict a
  strict :: a -> Strict a
  unstrict :: Strict a -> a

instance Strictly (a, b) where
  data Strict (a, b) = StrictPair' !a !b deriving Show
  strict x = unsafeCoerce $ case x of
    (!_, !_) -> x
  unstrict (StrictPair' a b) = (a, b)

instance Strictly (Maybe a) where
  data Strict (Maybe a) = StrictNothing' | StrictJust' !a deriving Show
  strict x = unsafeCoerce $ case x of
    Nothing -> x
    Just !_ -> x
  unstrict = \case
    StrictJust' j  -> Just j
    StrictNothing' -> Nothing

pattern Strict x <- (unstrict->x)

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
  where f (count, theSum) x = ((,) $! count + 1) $! theSum


data StrictPair a b = StrictPair !a !b deriving Show

pairFoldStrictPair :: StrictPair Integer Integer
pairFoldStrictPair = foldl' f (StrictPair 0 0) [1..million]
  where f (StrictPair count theSum) x = StrictPair (count + 1) (theSum + x)

pairFoldStrict :: Strict (Integer, Integer)
pairFoldStrict = foldl' f (strict (0, 0)) [1..million]
  where f (unstrict->(count, theSum)) x = strict (count + 1, theSum + x)

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

main :: IO ()
main = print (countParityStrict [1..million])
