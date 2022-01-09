{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Prelude hiding (Word)
import Control.Applicative (Const(Const), getConst)
import Data.Traversable (mapAccumL)

data Word a = Word a a a a a
  deriving (Functor, Foldable, Traversable, Show)

instance Applicative Word where
  pure x = Word x x x x x
  Word f1 f2 f3 f4 f5 <*> Word x1 x2 x3 x4 x5
    = Word (f1 x1) (f2 x2) (f3 x3) (f4 x4) (f5 x5)

data Located a = CorrectLocation
               | NotCorrectLocation a
               deriving (Functor, Foldable, Traversable)

data Scored = Green | Yellow | Grey deriving Show

toList :: ((a -> Const [a] a) -> (s -> Const [a] s))
          -> s -> [a]
toList f = getConst . f (Const . pure)

elemBy :: (a -> b -> Bool) -> b -> [a] -> Bool
elemBy (===) b = any (=== b)

removeBy :: (a -> b -> Bool) -> b -> [a] -> [a]
removeBy _ _ [] = []
removeBy (===) b (a:as) = case a === b of
  True -> as
  False -> a : removeBy (===) b as

score :: forall a b. (a -> b -> Bool) -> Word a -> Word b -> Word Scored
score (===) target candidate =
  let locatedWithTarget =
        (\targetChar candidateChar ->
            if targetChar === candidateChar
            then CorrectLocation
            else NotCorrectLocation (targetChar, candidateChar))
        <$> target <*> candidate

      located :: Word (Located b)
      located = (fmap . fmap) snd locatedWithTarget

      remaining = toList (traverse . traverse) $
                  (fmap . fmap) fst locatedWithTarget

  in snd $ mapAccumL (\targets -> \case
                         CorrectLocation -> (targets, Green)
                         NotCorrectLocation a ->
                           if elemBy (===) a targets
                           then (removeBy (===) a targets, Yellow)
                           else (targets, Grey)
                         ) remaining located

main :: IO ()
main = putStrLn "Hello, Haskell!"
