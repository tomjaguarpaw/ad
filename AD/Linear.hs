{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

import qualified Data.Map                      as M
import qualified Streaming                     as S
import qualified Streaming.Prelude             as S
import qualified Control.Monad.State           as St

data Value = FloatV Float | TupleV [Value] deriving Show

data Function = Add | Mul | Sub | Div deriving Show

data Cmd = Call Var Function Var
         | Tuple Var [Var]
         | Untuple [Var] Var
         | Dup (Var, Var) Var
         | Lit Var Value

type Prog = [Cmd]

type Var = String

type Env = M.Map Var Value

call :: Function -> Value -> Maybe Value
call Add (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 + x2))
call Mul (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 * x2))
call Sub (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 - x2))
call Div (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 / x2))
call _   _                               = Nothing

-- Could do this directly with `WriterT a Maybe` I think.
-- A good example for typeclass dictionaries?
pop :: Ord k => k -> M.Map k v -> Maybe (v, M.Map k v)
pop k m = do
  let (mv, m') = M.alterF (\u -> (u, Nothing)) k m
  v <- mv
  pure (v, m')

note :: String -> Maybe a -> Either String a
note s = \case
  Nothing -> Left s
  Just a  -> pure a

eval :: Env -> Prog -> Either String Env
eval env []       = pure env
eval env (c : cs) = case c of
  Call v' f vv -> do
    (t, envWithoutv) <-
      note ("Could not pop " ++ show vv ++ " when calling") $ pop vv env
    vvv <- note ("Could not call " ++ show f) $ call f t
    eval (M.insert v' vvv envWithoutv) cs
  Tuple v' vs -> do
    let
      newVars = forWithState (S.each vs) env $ \(vv, env_) -> do
        (t, envWithoutV) <- S.lift
          (note ("Could not pop " ++ show vv ++ " when tupling") $ pop vv env_)
        S.yield t
        pure envWithoutV

    (ts S.:> ((), envFinal)) <- S.toList newVars

    eval (M.insert v' (TupleV ts) envFinal) cs
  Untuple{}      -> undefined
  Dup (v1, v2) v -> do
    (t, envWithoutV) <-
      note ("Could not pop " ++ show v ++ " when duping") $ pop v env
    let insertNew = M.insert v1 t . M.insert v2 t
    eval (insertNew envWithoutV) cs
  Lit v value -> eval (M.insert v value env) cs

example :: Prog
example = [Tuple "t" ["x", "y"], Call "z" Add "t", Dup ("z1", "z2") "z"]

awf :: Prog
awf =
  [ Lit "7" (FloatV 7)
  , Dup ("x1", "x2") "x"
  , Tuple "7x" ["7", "x1"]
  , Call "p" Mul "7x"
  , Dup ("p1", "p2") "p"
  , Lit "1" (FloatV 1)
  , Tuple "1/y" ["1", "y"]
  , Call "r" Div "1/y"
  , Tuple "px" ["p1", "x2"]
  , Call "p*x" Mul "px"
  , Lit "5" (FloatV 5)
  , Tuple "p*x5" ["p*x", "5"]
  , Call "q" Mul "p*x5"
  , Lit "2" (FloatV 2)
  , Tuple "2p" ["2", "p2"]
  , Call "2*p" Mul "2p"
  , Tuple "2*p_q" ["2*p", "q"]
  , Call "2*p*q" Mul "2*p_q"
  , Lit "3" (FloatV 3)
  , Tuple "3_r" ["3", "r"]
  , Call "3*r" Mul "3_r"
  , Tuple "2*p*q_3*r" ["2*p*q", "3*r"]
  , Call "v" Add "2*p*q_3*r"
  ]

awff :: Fractional a => a -> a -> a
awff x y =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

test :: IO ()
test = do
  print (eval (M.fromList [("x", FloatV 3), ("y", FloatV 4)]) example)
  print (eval (M.fromList [("x", FloatV 3), ("y", FloatV 4)]) awf)
  print (awff (3.0::Double) 4.0)

sexample :: Monad m => S.Stream (S.Of Integer) m ((), String)
sexample = forWithState (S.each [1 .. 10]) "" $ \(i, s) -> do
  S.yield i
  pure (s ++ show i ++ ",")

forWithState
  :: forall a f s m r
   . (Monad m, Functor f)
  => S.Stream (S.Of a) m r
  -> s
  -> ((a, s) -> S.Stream f m s)
  -> S.Stream f m (r, s)
forWithState stream initialState f = St.runStateT (switch inStateT)
                                                  initialState
 where
  inStateT :: S.Stream f (St.StateT s m) r
  inStateT = S.for (S.hoist S.lift stream) $ \a -> do
    s  <- St.lift St.get
    s' <- S.hoist S.lift (f (a, s))
    St.lift (St.put s')

switch
  :: ( Functor f
     , Monad m
     , Monad (t m)
     , St.MonadTrans t
     , Monad (t (S.Stream f m))
     , S.MFunctor t
     )
  => S.Stream f (t m) a
  -> t (S.Stream f m) a
switch s = S.destroy s yieldsT effectT pure

yieldsT
  :: (Functor f, Monad m, St.MonadTrans t, Monad (t (S.Stream f m)))
  => f (t (S.Stream f m) a)
  -> t (S.Stream f m) a
yieldsT = St.join . S.lift . S.yields

effectT
  :: (Monad (t (streamf m)), Monad m, St.MonadTrans streamf, S.MFunctor t)
  => t m (t (streamf m) a)
  -> t (streamf m) a
effectT = St.join . S.hoist S.lift
