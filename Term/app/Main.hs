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

data In = PtyIn ByteString | StdIn ByteString

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

  inMVar <- newEmptyMVar

  _ <- forkIO $
    fix $ \again -> do
      bs <- hGet stdin 1
      putMVar inMVar (StdIn bs)
      again

  _ <- forkIO $
    fix $ \again -> do
      bs <- readPty
      putMVar inMVar (PtyIn bs)
      again

  _ <- forkIO $
    fix $ \again -> do
      takeMVar inMVar >>= \case
        StdIn bs -> Pty.writePty pty bs
        PtyIn bs -> do
          hPut stdout bs
          hFlush stdout

      again

  takeMVar exit
