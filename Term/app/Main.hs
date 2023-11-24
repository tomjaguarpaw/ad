{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Concurrent
import Control.Exception
import Data.ByteString
import Data.Function (fix)
import System.IO
import System.Posix.Pty qualified as Pty
import System.Posix.Signals

main :: IO ()
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

  let readPty = do
        try (Pty.readPty pty) >>= \case
          Left (_ :: IOError) -> (myThreadId >>= killThread) >> error "Impossible!"
          Right bs -> pure bs

  stdinMVar <- newEmptyMVar
  ptyMVar <- newEmptyMVar

  _ <- forkIO $
    fix $ \again -> do
      bs <- hGet stdin 1
      putMVar stdinMVar bs
      again

  _ <- forkIO $
    fix $ \again -> do
      bs <- readPty
      putMVar ptyMVar bs
      again

  _ <- forkIO $
    fix $ \again -> do
      bs <- takeMVar stdinMVar
      Pty.writePty pty bs
      again

  _ <- forkIO $
    fix $ \again -> do
      bs <- takeMVar ptyMVar
      hPut stdout bs
      hFlush stdout
      again

  takeMVar exit
