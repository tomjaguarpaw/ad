```
import Data.These (These(This, That, These))

instance Strictly (These a b) where
  newtype Strict (These a b) = StrictThese (Data.Strict.These a b) deriving Show
  strict x = unsafeCoerce $ case x of
    This !_     -> x
    That !_     -> x
    These !_ !_ -> x
  matchStrict (StrictThese x) = case x of
    Data.Strict.This t    -> This t
    Data.Strict.That t    -> That t
    Data.Strict.These s t -> These s t
  unstrict = unsafeCoerce
```
