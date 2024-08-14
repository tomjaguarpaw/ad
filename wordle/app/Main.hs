{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Bluefin.EarlyReturn (EarlyReturn, returnEarly, withEarlyReturn)
import Bluefin.Eff (Eff, runEff, type (:&))
import Bluefin.IO (effIO)
import Bluefin.State (evalState, get, put)
import Control.Applicative (Const (Const), getConst)
import Control.Monad (forever)
import qualified Data.Foldable
import Data.List (minimumBy)
import qualified Data.Map.Strict as Data.Map
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import Data.Traversable (mapAccumL)
import Prelude hiding (Word, until)

until :: (forall e. EarlyReturn r e -> Eff (e :& es) ()) -> Eff es r
until body =
  withEarlyReturn $ \early ->
    forever $ body early

data Word a = Word a a a a a
  deriving (Functor, Foldable, Traversable, Show, Eq, Ord)

instance Applicative Word where
  pure x = Word x x x x x
  Word f1 f2 f3 f4 f5 <*> Word x1 x2 x3 x4 x5 =
    Word (f1 x1) (f2 x2) (f3 x3) (f4 x4) (f5 x5)

readWord :: [a] -> Maybe (Word a)
readWord = \case
  [a, b, c, d, e] -> Just (Word a b c d e)
  _ -> Nothing

showWord :: Word a -> [a]
showWord = Data.Foldable.toList

readResult :: String -> Maybe (Word Scored)
readResult = \case
  [a, b, c, d, e] -> traverse readScore (Word a b c d e)
  _ -> Nothing

showResult :: Word Scored -> String
showResult =
  showWord
    . fmap
      ( \case
          Green -> 'g'
          Yellow -> 'y'
          Grey -> ' '
      )

readScore :: Char -> Maybe Scored
readScore = \case
  'g' -> Just Green
  'y' -> Just Yellow
  'x' -> Just Grey
  _ -> Nothing

data Located a
  = CorrectLocation
  | NotCorrectLocation a
  deriving (Functor, Foldable, Traversable)

data Scored = Green | Yellow | Grey deriving (Show, Eq, Ord)

toList ::
  ((a -> Const [a] a) -> (s -> Const [a] s)) ->
  s ->
  [a]
toList f = getConst . f (Const . pure)

elemBy :: (a -> b -> Bool) -> b -> [a] -> Bool
elemBy (===) b = any (=== b)

removeBy :: (a -> b -> Bool) -> b -> [a] -> [a]
removeBy _ _ [] = []
removeBy (===) b (a : as) = case a === b of
  True -> as
  False -> a : removeBy (===) b as

score :: forall a b. (a -> b -> Bool) -> Word a -> Word b -> Word Scored
score (===) target candidate =
  let locatedWithTarget =
        ( \targetChar candidateChar ->
            if targetChar === candidateChar
              then CorrectLocation
              else NotCorrectLocation (targetChar, candidateChar)
        )
          <$> target
          <*> candidate

      located :: Word (Located b)
      located = (fmap . fmap) snd locatedWithTarget

      remaining =
        toList (traverse . traverse) $
          (fmap . fmap) fst locatedWithTarget
   in snd $
        mapAccumL
          ( \targets -> \case
              CorrectLocation -> (targets, Green)
              NotCorrectLocation a ->
                if elemBy (===) a targets
                  then (removeBy (===) a targets, Yellow)
                  else (targets, Grey)
          )
          remaining
          located

badness ::
  (a -> b -> Bool) ->
  [Word a] ->
  Word b ->
  (Int, Data.Map.Map (Word Scored) [Word a])
badness (===) possibles guess =
  let scoredPossibles = map (\possible -> (score (===) possible guess, [possible])) possibles

      groupedPossibles = Data.Map.fromListWith (++) scoredPossibles

      minMax = Data.Foldable.maximum (Data.Map.map length groupedPossibles)
   in (minMax, groupedPossibles)

leastBad ::
  (Ord a) =>
  (a -> b -> Bool) ->
  [Word b] ->
  [Word a] ->
  Either
    (Word a)
    (Word b, Data.Map.Map (Word Scored) [Word a])
leastBad (===) guesses possibles' =
  case possibles' of
    [] -> error "No possibles"
    [onlyPossible] -> Left onlyPossible
    possibles ->
      let foo = map (\guess -> (guess, badness (===) possibles guess)) guesses
          (bestGuess, (_, subsequentPossibles)) = minimumBy (comparing (fst . snd)) foo
       in Right (bestGuess, subsequentPossibles)

main :: IO ()
main = do
  let target_ = "boost"
      target = fromJust (readWord target_)

  wordsString <- readFile "/tmp/five"
  let words_ = case flip
        traverse
        (lines wordsString)
        ( \word -> case readWord word of
            Nothing -> Left word
            Just w -> Right w
        ) of
        Left word -> error word
        Right w -> w

  runEff $ \ioe ->
    evalState words_ $ \possibles -> do
      until $ \done -> do
        let leastBad_ = leastBad (==) words_
            score_ = score (==) target

        possibles_ <- get possibles

        let (bestGuess, subsequentPossibles) = case leastBad_ possibles_ of
              Right r -> r
              Left l -> (l, Data.Map.empty)

        effIO ioe (putStrLn (showWord bestGuess))

        {-
            result <- fix $ \tryAgain -> do
              (readResult <$> getLine) >>= \case
                Nothing -> do
                  putStrLn "Couldn't understand htat"
                  tryAgain
                Just r -> pure r
        -}

        let result = score_ bestGuess

        effIO ioe (putStrLn (showResult result))

        case result of
          Word Green Green Green Green Green -> returnEarly done ()
          _ -> do
            let nextPossibles = case Data.Map.lookup result subsequentPossibles of
                  Nothing -> error "Not found"
                  Just n -> n

            put possibles nextPossibles
