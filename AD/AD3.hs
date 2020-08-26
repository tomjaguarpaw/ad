{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

import qualified Data.Map.Strict as Map
import qualified Data.Maybe      as Maybe
import           Data.List       (foldl')
import           Data.Maybe      (fromJust)

type Coord = Int
type Map = Map.Map

-- An expression type that has labels e on subexpressions and labels v
-- on variables.
data E e v a = Var     (v, a)
             | Const   Double
             | Negate  (e, E e v a)
             | Sum     (e, E e v a) (e, E e v a)
             | Product (e, E e v a) (e, E e v a)
             | Exp     (e, E e v a)
             | Let     (e, E e v a) (e, E e v (Maybe a))
             deriving (Show, Functor)
 
instance Monad (E () ()) where
  return x = Var ((), x)
  m >>= f  = case m of
    Var (_, a)          -> f a
    Const d             -> Const d
    Negate (l, e)       -> Negate (l, e >>= f)
    Sum (l, e) (l', e') -> Sum (l, e >>= f)
                               (l', e' >>= f)
    Product (l, e) (l', e')
                        -> Product (l, e >>= f)
                                   (l', e' >>= f)
    Exp (l, e)          -> Exp (l, e >>= f)
    Let (l, e) (l', e') -> Let (l, e >>= f) (l', e' >>= (>>= f))

-- The vector type is implemented as a Map from coordinates to Double.
-- In this example, for concreteness, we will consider vectors of
-- length 1000.
type V a = Map.Map a Double

extend :: Ord a => Double -> V a -> V (Maybe a)
extend a = Map.insert Nothing a . Map.mapKeys Just

unextend :: Ord a => V (Maybe a) -> (V a, Double)
unextend v = ( Map.mapKeys fromJust (Map.delete Nothing v)
             , fromJust (Map.lookup Nothing v) )

-- The zero vector
zero :: V a
zero = Map.empty

-- Add two vectors
plus :: Ord a => V a -> V a -> V a
plus = Map.unionWith (+)

-- Multiply a vector by a scalar
times :: Ord a => Double -> V a -> V a
times a = Map.map (a *)

-- Negate a vector
negateV :: Ord a => V a -> V a
negateV = Map.map negate

-- The component of a vector in a given coordinate direction.  For
-- example, the "component along" 2 of (3,4,5,6,...) is 4.
componentAlong :: Ord a => a -> V a -> Double
componentAlong i v = Maybe.fromMaybe 0 (Map.lookup i v)

-- A vector which has one non-zero entry, value x in the i direction.
-- For example, "5 `inDirection` 3" is (0,0,5,0,...).
inDirection :: Ord a => Double -> a -> V a
inDirection x i = Map.fromList [(i, x)]

-- Add a quantity to the given component.  For example,
-- "plusComponent 2 10 (3,4,5,6,...)" is "(3,14,5,6,...)".
plusComponent :: Ord a => a -> Double -> V a -> V a
plusComponent = Map.insertWith (+)

eval :: Ord a => V a -> E e v a -> Double
eval v = ev where
  ev = \case
    Var (_, i)             -> componentAlong i v
    Const d                -> d
    Negate (_, e)          -> let ex = ev e
                              in  -ex
    Sum (_, e) (_, e')     -> let ex  = ev e
                                  ex' = ev e'
                              in  ex + ex'
    Product (_, e) (_, e') -> let ex  = ev e
                                  ex' = ev e'
                              in  ex * ex'
    Exp (_, e)             -> let ex = ev e
                              in  exp ex
    Let (_, e) (_, e')     -> let ex  = ev e
                                  ex' = eval (extend ex v) e'
                              in ex'

forwardMode :: Ord a => V a -> E e v a -> (Double, V a)
forwardMode v = ev where
  ev = \case
    Var (_, i)             -> (componentAlong i v, 1 `inDirection` i)
    Const d                -> (d, zero)
    Negate (_, e)          -> let (ex, ed) = ev e
                              in  (-ex, negateV ed)
    Sum (_, e) (_, e')     -> let (ex, ed)   = ev e
                                  (ex', ed') = ev e'
                              in  (ex + ex', ed `plus` ed')
    Product (_, e) (_, e') -> let (ex, ed)   = ev e
                                  (ex', ed') = ev e'
                              in  (ex * ex', (ex `times` ed')
                                               `plus`
                                             (ex' `times` ed))
    Exp (_, e)             -> let (ex, ed) = ev e
                              in  (exp ex, exp ex `times` ed)
    Let (_, e) (_, e')     -> let (ex, ed)   = ev e
                                  (ex', ed') = forwardMode (extend ex v) e'
                                  (ed'', edl) = unextend ed'
                              in (ex', ed'' `plus` (edl `times` ed))

-- We'll evaluate the partial derivatives of
--
-- f = X1 * (X2 + (X1 * 2))
--
-- at (X1, X2) = (3,4)
--
-- so we expect that
--
-- f = 30
--
-- f_X1 = X2 + 4 * X1 = 16
--
-- f_X2 = X1 = 3

-- X1 * (X2 + (X1 * 2))
--
-- becomes
--
-- [X1; 3] * [[X2; 4] + [[X1; 3] * [2; 2]; 6]; 10]
--
-- So indeed f = 30
evalDecorate :: Ord a => V a -> E e v a -> (Double, E Double v a)
evalDecorate v = ev where
  ev = \case
    Var (a, i)             -> (componentAlong i v, Var (a, i))
    Const d                -> (d, Const d)
    Negate (_, e)          -> let (x, d1) = ev e
                              in  (-x,    Negate (x, d1))
    Sum (_, e) (_, e')     -> let (x, d1) = ev e
                                  (y, d2) = ev e'
                              in  (x + y, Sum (x, d1) (y, d2))
    Product (_, e) (_, e') -> let (x, d1) = ev e
                                  (y, d2) = ev e'
                              in  (x * y, Product (x, d1) (y, d2))
    Exp (_, e)             -> let (x, d1) = ev e
                              in  (exp x, Exp (x, d1))
    Let (_, e) (_, e')     -> let (x, d1) = ev e
                                  (y, d2) = evalDecorate (extend x v) e'
                              in (y, Let (x, d1) (y, d2))
  
-- [X1; 3] * [[X2; 4] + [[X1; 3] * [2; 2]; 6]; 10]
--
-- becomes
--
-- [X1; 10] * ([X2; 3] + ([X1; 3 * 2] * 2))
--
-- (when the first argument is 1) which is
--
-- [X1; 10] * ([X2; 3] + ([X1; 6] * 2))
sensitivityDecorate :: Double -> E Double v a -> E () Double a
sensitivityDecorate = ev where
  ev s = \case
    Var (_, x)             -> Var     (s, x)
    Const d                -> Const   d
    Negate (_, e)          -> Negate  ((), ev (-s) e)
    Sum (_, e) (_, e')     -> Sum     ((), ev s e)
                                      ((), ev s e')
    Product (x, e) (y, e') -> Product ((), ev (s * y) e)
                                      ((), ev (s * x) e')
    Exp (x, e)             -> Exp     ((), ev (s * exp x) e)
    Let (x, e) (y, e')     -> Let     ((), ev s e)
                                      ((), sensitivityDecorate s e')

-- [X1; 10] * ([X2; 3] + ([X1; 6] * 2))
--
-- becomes
--
-- [X1; 10], [X2; 3], [X1; 6]
--
-- When we sum componentwise we get
--
-- X1: 16, X2: 3
--
-- as anticipated.
listOfVars :: Ord a => [(Double, a)] -> E () Double a -> [(Double, a)]
listOfVars = ev where
  ev l = \case
    Var t                  -> t : l
    Const _                -> l
    Negate (_, e)          -> l `ev` e
    Sum (_, e) (_, e')     -> l `ev` e `ev` e'
    Product (_, e) (_, e') -> l `ev` e `ev` e'
    Exp (_, e)             -> l `ev` e
    Let (_, e) (_, e')     ->
      let v = (foldr (\(a, d) e -> ((), Var (d, a)) `Sum` ((), e)) (Const 0)
               . Map.toList
               . foldl' (\d (s, x) -> plusComponent x s d) zero
               . listOfVars []) e
      in e' >>= (\case Nothing -> v
                       Just x  -> return x)                                   

reverseMode :: Ord a => V a -> E e v a -> V a
reverseMode v = foldl' (\d (s, x) -> plusComponent x s d) zero
                . listOfVars []
                . sensitivityDecorate 1
                . snd
                . evalDecorate v

square :: E () () a -> E () () a
square x = ((), x) `Product` ((), x)

manySquares :: E () () Coord
manySquares = iterate square x1 !! 17
  where x1 = (Var ((), 1))

squareLet :: E () () a -> E () () a
squareLet x = lety_ x (square_ y_)
-- "let y = x in square y"
  where square_ x = ((), square x)
        lety_ y   = Let ((), y) 
        y_        = (Var ((), Nothing))

manySquaresLet :: E () () Coord
manySquaresLet = iterate squareLet x1 !! 17
  where x1 = (Var ((), 1))

exampleSquaresEval =
  mapM_ (print
         . flip eval manySquares
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

exampleSquaresForward =
  mapM_ (print
         . componentAlong 1
         . snd
         . flip forwardMode manySquares
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

exampleSquaresReverse =
  mapM_ (print
         . componentAlong 1
         . flip reverseMode manySquares
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

exampleSquaresLetEval =
  mapM_ (print
         . flip eval manySquaresLet
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

exampleSquaresLetForward =
  mapM_ (print
         . componentAlong 1
         . snd
         . flip forwardMode manySquaresLet
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

exampleSquaresLetReverse =
  mapM_ (print
         . componentAlong 1
         . flip reverseMode manySquaresLet
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]
