{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Concurrent
import Control.Exception
import Data.ByteString
import Data.ByteString.Char8 qualified as C8
import Data.Function (fix)
import System.IO
import System.Posix (Fd)
import System.Posix.IO (stdInput)
import System.Posix.Pty qualified as Pty
import System.Posix.Signals
import Unsafe.Coerce (unsafeCoerce)

data In = PtyIn ByteString | StdIn ByteString

ptyToFd :: Pty.Pty -> Fd
ptyToFd = unsafeCoerce

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

  let readEither = do
        inMVar <- newEmptyMVar

        t1 <- forkIO $ do
          threadWaitRead stdInput
          putMVar inMVar True

        t2 <- forkIO $ do
          threadWaitRead (ptyToFd pty)
          putMVar inMVar False

        b <- readMVar inMVar

        killThread t1
        killThread t2

        case b of
          True -> StdIn <$> hGet stdin 1
          False -> PtyIn <$> readPty

  _ <- forkIO $
    fix $ \again -> do
      readEither >>= \case
        StdIn bs -> do
          Pty.writePty pty bs
          hPut stdout (C8.pack "\o33[6n")
          _ <- flip fix mempty $ \again' sofar -> do
            b <- hGet stdin 1
            if b == C8.pack "R"
              then
                let (x, Data.ByteString.drop 1 -> y) =
                      C8.break (== ';') (Data.ByteString.drop 1 sofar)
                 in pure (read (C8.unpack x) :: Int, read (C8.unpack y) :: Int)
              else again' (sofar <> b)
          pure ()
        PtyIn bs -> do
          hPut stdout bs
          hFlush stdout

      again

  takeMVar exit
