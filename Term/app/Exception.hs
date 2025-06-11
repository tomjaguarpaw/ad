{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Exception where

import Control.Exception (Exception, throwIO, tryJust)
import Data.Maybe (fromMaybe)
import Data.Typeable (Typeable, cast)
import Data.Unique qualified
import Prelude hiding (log)

data MyException where
  MyException :: (Typeable e) => e -> Data.Unique.Unique -> MyException

instance Show MyException where
  show _ = "<MyException>"

instance Exception MyException

-- This is similar to how effectful does it.  I don't like the
-- Typeable constraint.  Maybe we should use unsafeCoerce instead of
-- cast.
withScopedException ::
  (Typeable e) => ((forall a. e -> IO a) -> IO r) -> IO (Either e r)
withScopedException f = do
  fresh <- Data.Unique.newUnique

  flip tryJust (f (\e -> throwIO (MyException e fresh))) $ \case
    MyException e tag ->
      if tag == fresh
        then -- We should be able to successfully cast if the tags match
          Just (fromMaybe (error "Unexpected Typeable") (cast e))
        else Nothing

earlyReturn :: (Typeable r) => ((forall a. r -> IO a) -> IO r) -> IO r
earlyReturn h = fmap (either id id) (withScopedException h)
