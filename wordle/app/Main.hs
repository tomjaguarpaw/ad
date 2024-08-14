{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Bluefin.EarlyReturn (EarlyReturn, returnEarly, withEarlyReturn)
import Bluefin.Eff (Eff, runEff, runPureEff, (:>), type (:&))
import Bluefin.IO (IOE, effIO)
import Bluefin.State (evalState, get, put)
import Control.Monad (forever)
import qualified Data.Foldable
import Data.List (minimumBy)
import qualified Data.Map.Strict as Data.Map
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import Data.Traversable (for)
import Data.Tuple.Optics (Field1 (_1))
import Optics.Core (toListOf, traversed, (%))
import Prelude hiding (Word, until)

until :: (forall e. EarlyReturn r e -> Eff (e :& es) ()) -> Eff es r
until body =
  withEarlyReturn $ \early ->
    forever $ body early

data Word a = Word !a !a !a !a !a
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

elemBy :: (a -> b -> Bool) -> b -> [a] -> Bool
elemBy (===) b = any (=== b)

removeBy :: (a -> b -> Bool) -> b -> [a] -> [a]
removeBy _ _ [] = []
removeBy (===) b (a : as) = case a === b of
  True -> as
  False -> a : removeBy (===) b as

score :: forall a b. (a -> b -> Bool) -> Word a -> Word b -> Word Scored
score (===) target candidate = runPureEff $ do
  let locatedWithTarget :: Word (Located (a, b))
      locatedWithTarget =
        ( \targetChar candidateChar ->
            if targetChar === candidateChar
              then CorrectLocation
              else NotCorrectLocation (targetChar, candidateChar)
        )
          <$> target
          <*> candidate

      located :: Word (Located b)
      located = (fmap . fmap) snd locatedWithTarget

      remaining :: [a]
      remaining = toListOf (traversed % traversed % _1) locatedWithTarget

  evalState remaining $ \targets' -> do
    for located $ \case
      CorrectLocation ->
        pure Green
      NotCorrectLocation a -> do
        -- FIXME: check why it still works even if I only get
        -- targets before the loop starts!
        targets <- get targets'
        if elemBy (===) a targets
          then do
            put targets' (removeBy (===) a targets)
            pure Yellow
          else pure Grey

groupBy ::
  (Ord k) =>
  (a -> k) ->
  [a] ->
  Data.Map.Map k [a]
groupBy k as =
  Data.Map.fromListWith (++) (map (\a -> (k a, [a])) as)

badness ::
  (a -> b -> Bool) ->
  [Word a] ->
  Word b ->
  (Int, Data.Map.Map (Word Scored) [Word a])
badness (===) possibles guess =
  let groupedPossibles = groupBy (\possible -> score (===) possible guess) possibles

      minMax = Data.Foldable.maximum (Data.Map.map length groupedPossibles)
   in (minMax, groupedPossibles)

leastBad ::
  forall a b.
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
      let foo :: [(Word b, (Int, Data.Map.Map (Word Scored) [Word a]))]
          foo = map (\guess -> (guess, badness (===) possibles guess)) guesses
          (bestGuess, (_, subsequentPossibles)) = minimumBy (comparing (fst . snd)) foo
       in Right (bestGuess, subsequentPossibles)

readFiveFile :: (e :> es) => IOE e -> Eff es [Word Char]
readFiveFile ioe = do
  wordsString <- effIO ioe (readFile "/tmp/five")
  let words_ = case for
        (lines wordsString)
        ( \word -> case readWord word of
            Nothing -> Left word
            Just w -> Right w
        ) of
        Left word -> error word
        Right w -> w
  pure words_

main :: IO ()
main = runEff $ \ioe -> do
  words_ <- readFiveFile ioe
  loopWords ioe words_ (scoreBoost ioe)

scoreBoost :: (e :> es) => IOE e -> Word Char -> Eff es (Word Scored)
scoreBoost ioe candidate = do
  let target_ = "boost"
      target = fromJust (readWord target_)
      score_ = score (==) target
  effIO ioe (putStrLn (showWord candidate))
  pure (score_ candidate)

readResultEff :: (e :> es) => IOE e -> Word Char -> Eff es (Word Scored)
readResultEff ioe candidate = until $ \gotResult -> do
  effIO ioe (putStrLn (showWord candidate))
  line <- effIO ioe getLine
  case readResult line of
    Nothing -> do
      effIO ioe (putStrLn "Couldn't understand that")
    Just r -> returnEarly gotResult r

loopWords ::
  (e :> es) =>
  IOE e ->
  [Word Char] ->
  (forall e1 e2. Word Char -> Eff (e1 :& e2 :& es) (Word Scored)) ->
  Eff es ()
loopWords ioe words_ score_ =
  evalState words_ $ \possibles -> do
    until $ \done -> do
      let leastBad_ = leastBad (==) words_

      possibles_ <- get possibles

      let (bestGuess, subsequentPossibles) = case leastBad_ possibles_ of
            Right r -> r
            Left l -> (l, Data.Map.empty)

      result <- score_ bestGuess

      effIO ioe (putStrLn (showResult result))

      case result of
        Word Green Green Green Green Green -> returnEarly done ()
        _ -> do
          let nextPossibles = case Data.Map.lookup result subsequentPossibles of
                Nothing -> error "Not found"
                Just n -> n

          put possibles nextPossibles
