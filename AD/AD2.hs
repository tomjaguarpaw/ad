{-# LANGUAGE LambdaCase #-}

import qualified Data.Map.Strict as Map
import qualified Data.Maybe      as Maybe
import           Data.List       (foldl')

type Coord = Int

-- An expression type that has labels e on subexpressions and labels v
-- on variables.
data E e v = Var     (v, Coord)
           | One
           | Zero
           | Negate  (e, E e v)
           | Sum     (e, E e v) (e, E e v)
           | Product (e, E e v) (e, E e v)
           | Exp     (e, E e v)
         deriving Show

-- The vector type is implemented as a Map from coordinates to Double.
-- In this example, for concreteness, we will consider vectors of
-- length 1000.
type V = Map.Map Coord Double

-- The zero vector
zero :: V
zero = Map.fromList (zip [1..1000] [0,0..])

-- Add two vectors
plus :: V -> V -> V
plus = Map.unionWith (+)

-- Multiply a vector by a scalar
times :: Double -> V -> V
times a = Map.map (a *)

-- Negate a vector
negateV :: V -> V
negateV = Map.map negate

-- The component of a vector in a given coordinate direction.  For
-- example, the "component along" 2 of (3,4,5,6,...) is 4.
componentAlong :: Coord -> V -> Double
componentAlong i v = Maybe.fromMaybe 0 (Map.lookup i v)

-- A vector which has one non-zero entry, value x in the i direction.
-- For example, "5 `inDirection` 3" is (0,0,5,0,...).
inDirection :: Double -> Coord -> V
inDirection x i = Map.fromList [(i, x)]

-- Add a quantity to the given component.  For example,
-- "plusComponent 2 10 (3,4,5,6,...)" is "(3,14,5,6,...)".
plusComponent :: Coord -> Double -> V -> V
plusComponent = Map.insertWith (+)

forwardMode :: V -> E e v -> (Double, V)
forwardMode v = ev where
  ev = \case
    Var (_, i)             -> (componentAlong i v, 1 `inDirection` i)
    One                    -> (1, zero)
    Zero                   -> (0, zero)
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
evalDecorate :: V -> E e v -> (Double, E Double v)
evalDecorate v = ev where
  ev = \case
    Var (a, i)             -> (componentAlong i v, Var (a, i))
    One                    -> (1, One)
    Zero                   -> (0, Zero)
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
  
-- [X1; 3] * [[X2; 4] + [[X1; 3] * [2; 2]; 6]; 10]
--
-- becomes
--
-- [X1; 10] * ([X2; 3] + ([X1; 3 * 2] * 2))
--
-- (when the first argument is 1) which is
--
-- [X1; 10] * ([X2; 3] + ([X1; 6] * 2))
sensitivityDecorate :: Double -> E Double v -> E () Double
sensitivityDecorate = ev where
  ev s = \case
    Var (_, x)             -> Var     (s, x)
    One                    -> One
    Zero                   -> Zero
    Negate (_, e)          -> Negate  ((), ev (-s) e)
    Sum (_, e) (_, e')     -> Sum     ((), ev s e)
                                      ((), ev s e')
    Product (x, e) (y, e') -> Product ((), ev (s * y) e)
                                      ((), ev (s * x) e')
    Exp (x, e)             -> Exp     ((), ev (s * exp x) e)

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
listOfVars :: [(v, Coord)] -> E e v -> [(v, Coord)]
listOfVars = ev where
  ev l = \case
    Var t                  -> t : l
    One                    -> l
    Zero                   -> l
    Negate (_, e)          -> l `ev` e
    Sum (_, e) (_, e')     -> l `ev` e `ev` e'
    Product (_, e) (_, e') -> l `ev` e `ev` e'
    Exp (_, e)             -> l `ev` e

reverseMode :: V -> E e v -> V
reverseMode v = foldl' (\d (s, x) -> plusComponent x s d) zero
                . listOfVars []
                . sensitivityDecorate 1
                . snd
                . evalDecorate v

f :: E () () -> E () ()
f x = exp_ (x_ `minus` one)
  where a `minus` b = a `Sum` ((), Negate b)
        one         = ((), One)
        x_          = ((), x)
        exp_ a      = Exp ((), a)
        
bigExpression :: E () ()
bigExpression = iterate f x1 !! 1000
  where x1 = (Var ((), 1))

square :: E () () -> E () ()
square x = ((), x) `Product` ((), x)

manySquares :: E () ()
manySquares = iterate square x1 !! 17
  where x1 = (Var ((), 1))

exampleForward =
  mapM_ (print
         . componentAlong 1
         . snd
         . flip forwardMode bigExpression
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

-- > exampleForward
-- 3.2478565715995278e-6
-- 1.0
-- 1.0100754777229357
--
-- -- That was slow

exampleReverse =
  mapM_ (print
         . componentAlong 1
         . (\x -> reverseMode x bigExpression)
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

-- > exampleReverse
-- 3.2478565715995362e-6
-- 1.0
-- 1.010075477722936
--
-- -- That was fast

reverseModeAllInOne :: V -> Double -> V -> E e v -> (Double, V)
reverseModeAllInOne v = ev where
  ev s d = \case
    Var (_, i)             -> (componentAlong i v, plusComponent i s d)
    One                    -> (1, d)
    Zero                   -> (0, d)
    Negate (_, e)          -> let (x, d1) = ev (-s) d e
                              in  (-x, d1)
    Sum (_, e) (_, e')     -> let (x, d1) = ev s d  e
                                  (y, d2) = ev s d1 e'
                              in  (x + y, d2)
    Product (_, e) (_, e') -> let (x, d1) = ev (s * y) d  e
                                  (y, d2) = ev (s * x) d1 e'
                              in  (x * y, d2)
    Exp (_, e)             -> let (x, d1) = ev (s * exp x) d e
                              in  (exp x, d1)

exampleReverseAllInOne =
  mapM_ (print
         . componentAlong 1
         . snd
         . (\x -> reverseModeAllInOne x 1 zero bigExpression)
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

-- > exampleReverseAllInOne
-- 3.2478565715995362e-6
-- 1.0
-- 1.010075477722936
-- 
-- -- That was fast

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
