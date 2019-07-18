{-# LANGUAGE LambdaCase #-}

import Control.Applicative ((<$>), (<*>), pure, Applicative, liftA, liftA2)

import qualified Control.Monad.Cont as C

data E = X | One | Zero | Negate E | Sum E E | Product E E | Exp E
       deriving Show

eval :: Double -> E -> Double
eval x = ev where
  ev = \case
    X            -> x
    One          -> 1
    Zero         -> 0
    Negate e     -> -ev e
    Sum e e'     -> ev e + ev e'
    Product e e' -> ev e * ev e'
    Exp e        -> exp (ev e)

diff :: E -> E
diff = \case
  X            -> One
  One          -> Zero
  Zero         -> Zero
  Negate e     -> Negate (diff e)
  Sum e e'     -> Sum (diff e) (diff e')
  Product e e' -> Product e (diff e') `Sum` Product (diff e) e'
  Exp e        -> Exp e `Product` diff e

diffEval :: Double -> E -> (Double, Double)
diffEval x = ev where
  ev = \case
    X            -> (x, 1)
    One          -> (1, 0)
    Zero         -> (0, 0)
    Negate e     -> let (ex, ed) = ev e
                    in (-ex, -ed)
    Sum e e'     -> let (ex, ed)   = ev e
                        (ex', ed') = ev e'
                    in (ex + ex', ed + ed')
    Product e e' -> let (ex, ed)   = ev e
                        (ex', ed') = ev e'
                    in (ex * ex', ex * ed' + ed * ex')
    Exp e        -> let (ex, ed) = ev e
                    in (exp ex, exp ex * ed)

diffEvalSlow :: Double -> E -> (Double, Double)
diffEvalSlow x = ev where
  ev = \case
    X            -> (x, 1)
    One          -> (1, 0)
    Zero         -> (0, 0)
    Negate e     -> let ex = fst (ev e)
                        ed = snd (ev e)
                    in (-ex, -ed)
    Sum e e'     -> let ex   = fst (ev e)
                        ed   = snd (ev e)
                        ex'  = fst (ev e')
                        ed'  = snd (ev e')
                    in (ex + ex', ed + ed')
    Product e e' -> let ex   = fst (ev e)
                        ed   = snd (ev e)
                        ex'  = fst (ev e')
                        ed'  = snd (ev e')
                    in (ex * ex', ex * ed' + ed * ex')
    Exp e        -> let ex = fst (ev e)
                        ed = snd (ev e)
                    in (exp ex, exp ex * ed)

reverseMode :: Double -> Double -> E -> (Double, Double)
reverseMode x = ev where
  ev s = \case
    X        -> (x, s)
    One      -> (1, 0)
    Zero     -> (0, 0)
    Negate e -> let (x, x') = ev (-s) e
                in (-x, x')
    Sum e e' -> let (x, x') = ev s e
                    (y, y') = ev s e'
                in (x + y, x' + y')
    Product e e' -> let (x, x') = ev (s * y) e
                        (y, y') = ev (s * x) e'
                    in (x * y, x' + y')
    Exp e        -> let (x, x') = ev (s * exp x) e
                    in (exp x, x')

reverseMode' :: Double -> E -> (Double, Double -> Double)
reverseMode' x = ev where
  ev = \case
    X        -> (x, id)
    One      -> (1, const 0)
    Zero     -> (0, const 0)
    Negate e -> let (x, x') = ev e
                in (-x, x' . negate)
    Sum e e' -> let (x, x') = ev e
                    (y, y') = ev e'
                in (x + y, \s -> x' s + y' s)
    Product e e' -> let (x, x') = ev e
                        (y, y') = ev e'
                    in (x * y, \s -> x' (s * y) + y' (s * x))
    Exp e        -> let (x, x') = ev e
                    in (exp x, \s -> x' (s * exp x))
{-
--reverseMode3 :: Double -> E -> (Double, Double -> Double)
reverseMode3 x = ev where
  ev = \case
    X        -> (x, undefined)
    One      -> (1, undefined)
    Zero     -> (0, undefined)
    Negate e -> let (x, x') = ev e
                in (-x, \f -> f (x', negate))
    Sum e e' -> let (x, x') = ev e
                    (y, y') = ev e'
                in (x + y, \f -> f (x', id) + f (y', id))
    Product e e' -> let (x, x') = ev e
                        (y, y') = ev e'
                    in (x * y, \f -> f (x', (* y)) + f (y', (* x)))
    Exp e        -> let (x, x') = ev e
                    in (exp x, \f -> f (x', (* exp x)))
-}
diffEval2 :: Double -> E -> (Double, Double)
diffEval2 x = ev where
  ev = let combine :: b -> (b -> r) -> r
           combine = flip ($)
       in \case
    X            -> (x, 1)
    One          -> (1, 0)
    Zero         -> (0, 0)
    Negate e     -> let (ex, ed) = ev e
                    in (-ex, combine ed negate)
    Sum e e'     -> let (ex, ed)   = ev e
                        (ex', ed') = ev e'
                    in (ex + ex', combine ed id + combine ed' id)
    Product e e' -> let (ex, ed)   = ev e
                        (ex', ed') = ev e'
                    in (ex * ex', combine ed' (* ex) + combine ed (* ex'))
    Exp e        -> let (ex, ed) = ev e
                    in (exp ex, combine ed (* exp ex))

reverseMode'' :: Applicative f => f Double -> Double -> E -> (Double, f Double)
reverseMode'' getX x = ev where
  ev = \case
    X        -> (x, getX)
    One      -> (1, pure 0)
    Zero     -> (0, pure 1)
    Negate e -> let (x, x') = ev e
                in (-x, negate <$> x')
    Sum e e' -> let (x, x') = ev e
                    (y, y') = ev e'
                in (x + y, (+) <$> x' <*> y')
    Product e e' -> let (x, x') = ev e
                        (y, y') = ev e'
                    in (x * y, (+) <$> ((*) <$> x' <*> pure y)
                                   <*> ((*) <$> pure x <*> y'))
    Exp e        -> let (x, x') = ev e
                    in (exp x, (exp x *) <$> x')


f :: E -> E
f x = Exp (x `minus` One)
  where a `minus` b = a `Sum` Negate b

smallExpression :: E
smallExpression = iterate f X !! 3

bigExpression :: E
bigExpression = iterate f X !! 1000


-- smallExpression

-- Exp (Sum (Exp (Sum (Exp (Sum X (Negate One))) (Negate One))) (Negate One))

-- diff smallExpression

-- Product (Exp (Sum (Exp (Sum (Exp (Sum X (Negate One))) (Negate One))) (Negate One))) (Sum (Product (Exp (Sum (Exp (Sum X (Negate One))) (Negate One))) (Sum (Product (Exp (Sum X (Negate One))) (Sum One (Negate Zero))) (Negate Zero))) (Negate Zero))

-- mapM_ (print . flip eval (diff smallExpression))    [0.0009, 1, 1.0001]

{-

0.12254834896191881
1.0
1.0003000600100016

-- mapM_ (print . flip eval (diff bigExpression))      [0.00009, 1, 1.00001]

3.2478565715995278e-6
1.0
1.0100754777229357

This is very slow

-- mapM_ (print . snd . flip diffEval smallExpression) [0.0009, 1, 1.0001]

0.12254834896191881
1.0
1.0003000600100016

-- mapM_ (print . snd . flip diffEval bigExpression)   [0.00009, 1, 1.00001]

3.2478565715995278e-6
1.0
1.0100754777229357

-- mapM_ (print . snd . (\x -> reverseMode x 1 bigExpression) [0.00009, 1, 1.00001]

-- mapM_ (print . (\x -> let (_, y) = reverseMode' x bigExpression in y 1)) [0.00009, 1, 1.00001]

-- mapM_ (print . (\x -> let (_, y) = reverseMode'' (const 1) x bigExpression in y 1)) [0.00009, 1, 1.00001]

-- ^^ (r ->)

-- 

-}
