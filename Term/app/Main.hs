{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Concurrent
import Control.Exception
import Data.ByteString
import Data.Char
import Data.Function (fix)
import GHC.IO.Device
import System.Exit
import System.IO
import System.Posix.IO
import qualified System.Posix.Pty as Pty
import System.Posix.Signals
import System.Posix.Terminal
import System.Process

main = do
  hSetEcho stdin False
  hSetBuffering stdin NoBuffering

  sz <- do
    Just stdInPty <- Pty.createPty 0
    Pty.ptyDimensions stdInPty

  (pty, _) <- Pty.spawnWithPty Nothing False "/bin/bash" [] sz

  _ <- flip (installHandler keyboardSignal) Nothing . Catch $ do
    Pty.writePty pty (pack [3])

  exit <- newEmptyMVar

  _ <- flip (installHandler sigCHLD) Nothing . Catch $ do
    putMVar exit ()

  let forkFinally' :: (Either SomeException () -> IO ()) -> IO () -> IO ThreadId
      forkFinally' = flip forkFinally

  let readPty = do
        try (Pty.readPty pty) >>= \case
          Left (e :: IOError) -> (myThreadId >>= killThread) >> error "Impossible!"
          Right bs -> pure bs

  forkIO $
    fix $ \again -> do
      bs <- hGet stdin 1
      Pty.writePty pty bs
      again

  forkIO $
    fix $ \again -> do
      bs <- readPty
      hPut stdout bs
      hFlush stdout
      again

  takeMVar exit
