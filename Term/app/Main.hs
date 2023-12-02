{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Concurrent
import Control.Exception
import Control.Monad (when)
import Data.ByteString hiding (appendFile)
import Data.ByteString.Char8 qualified as C8
import Data.Function (fix)
import System.IO
import System.Posix (Fd, getProcessID)
import System.Posix.IO (stdInput)
import System.Posix.IO.ByteString (fdRead)
import System.Posix.Pty qualified as Pty
import System.Posix.Signals
import System.Posix.Terminal
import Unsafe.Coerce (unsafeCoerce)

data In = PtyIn ByteString | StdIn ByteString

ptyToFd :: Pty.Pty -> Fd
ptyToFd = unsafeCoerce

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering

  pid <- show <$> getProcessID

  oldTermSettings <- getTerminalAttributes stdInput
  -- We might want to copy the settings from abduco:
  --
  -- https://github.com/martanne/abduco/blob/8c32909a159aaa9484c82b71f05b7a73321eb491/client.c#L35C20-L56
  let newTermSettings =
        ( flip withoutMode ProcessInput
            . flip withoutMode ProcessOutput
            . flip withoutMode MapCRtoLF
            . flip withoutMode StartStopInput
            . flip withoutMode StartStopOutput
            . flip withoutMode EnableEcho
        )
          oldTermSettings
  -- Should probably reset this on exit
  setTerminalAttributes stdInput newTermSettings Immediately

  (cols, rows) <- do
    Just stdInPty <- Pty.createPty 0
    Pty.ptyDimensions stdInPty

  (pty, _) <- Pty.spawnWithPty Nothing False "/bin/bash" [] (cols, subtract 1 rows)

  _ <- flip (installHandler keyboardSignal) Nothing . Catch $ do
    -- Write Ctrl-C
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
          -- We shouldn't threadWaitRead on an Fd from a Handle
          -- because the Handle buffers some of the input so we wait
          -- even when there's buffered input available.
          threadWaitRead stdInput
          putMVar inMVar (StdIn <$> fdRead stdInput 1)

        t2 <- forkIO $ do
          threadWaitRead (ptyToFd pty)
          putMVar inMVar (PtyIn <$> readPty)

        action <- readMVar inMVar

        killThread t1
        killThread t2

        action

  _ <- forkIO $
    fix $ \again -> do
      readEither >>= \case
        StdIn bs -> do
          Pty.writePty pty bs
          appendFile "/tmp/log" ("StdIn " ++ pid ++ ": " ++ show bs ++ "\n")
        PtyIn bs -> do
          hPut stdout bs
          appendFile "/tmp/log" ("PtyIn " ++ pid ++ ": " ++ show bs ++ "\n")
          -- Ask for the position
          hPut stdout (C8.pack "\ESC[6n")
          appendFile "/tmp/log" ("Requesting position " ++ pid ++ "\n")
          hFlush stdout

          fix $ \again' -> do
            b <- hGet stdin 1
            when (b /= C8.pack "\ESC") $ do
              Pty.writePty pty b
              appendFile "/tmp/log" ("StdIn whilst searching ESC " ++ pid ++ ": " ++ show b ++ "\n")
              again'

          appendFile "/tmp/log" ("Found ESC " ++ pid ++ "\n")

          sofar <- flip fix mempty $ \again' sofar -> do
            b <- hGet stdin 1
            if b == C8.pack "R"
              then pure sofar
              else again' (sofar <> b)

          appendFile "/tmp/log" ("Handled ESC " ++ pid ++ " " ++ show (C8.unpack sofar) ++ "\n")

          -- Drop ;
          let (x, Data.ByteString.drop 1 -> y) =
                C8.break (== ';') (Data.ByteString.drop 1 sofar)

          let x' = read (C8.unpack x) :: Int
          let y' = read (C8.unpack y) :: Int
          -- Go to first column on last row
          hPut stdout (C8.pack ("\ESC[" <> show rows <> ";1H"))
          -- Clear line
          hPut stdout (C8.pack "\ESC[K")
          hPut stdout (C8.pack ("A status bar: " <> show sofar <> " I put: " <> show (C8.unpack bs)))
          -- Go back to where we were
          hPut stdout (C8.pack ("\ESC[" <> show x' <> ";" <> show y' <> "H"))

      again

  takeMVar exit
