{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Concurrent
import Control.Exception
import Control.Monad (when)
import Data.ByteString hiding (appendFile, elem, take)
import Data.ByteString.Char8 qualified as C8
import Data.Function (fix)
import Data.IORef (newIORef, readIORef, writeIORef)
import System.Environment
import System.Exit (exitWith)
import System.IO
import System.Posix (Fd, getProcessID)
import System.Posix.IO (stdInput)
import System.Posix.IO.ByteString (fdRead)
import System.Posix.Pty qualified as Pty
import System.Posix.Signals
import System.Posix.Signals.Exts (sigWINCH)
import System.Posix.Terminal
import System.Process (getProcessExitCode, getPid)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (log)

data In = PtyIn ByteString | StdIn ByteString | WinchIn

ptyToFd :: Pty.Pty -> Fd
ptyToFd = unsafeCoerce

main :: IO ()
main = do
  [bar, prog] <- getArgs

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

  theDims <- do
    Just stdInPty <- Pty.createPty 0
    dims <- Pty.ptyDimensions stdInPty
    newIORef dims

  (pty, childHandle) <- do
    (cols, rows) <- readIORef theDims
    Pty.spawnWithPty Nothing True "sh" ["-c", prog] (cols, subtract 1 rows)

  _ <- flip (installHandler sigINT) Nothing . Catch $ do
    -- Write Ctrl-C
    Pty.writePty pty (pack [3])

  exit <- newEmptyMVar

  _ <- flip (installHandler sigCHLD) Nothing . Catch $ do
    e <-
      getProcessExitCode childHandle >>= \case
        Nothing ->
          error "Impossible: should only happen when the process is still running"
        Just e -> pure e

    putMVar exit e

  winchMVar <- newEmptyMVar

  _ <- flip (installHandler sigWINCH) Nothing . Catch $ do
    _ <- tryPutMVar winchMVar ()
    pure ()

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

        t3 <- forkIO $ do
          readMVar winchMVar
          putMVar inMVar (WinchIn <$ takeMVar winchMVar)

        action <- readMVar inMVar

        killThread t1
        killThread t2
        killThread t3

        action

  let drawBar :: IO ()
      drawBar = do
        -- Ask for the position
        hPut stdout (C8.pack "\ESC[6n")
        log ("Requesting position " ++ pid ++ "\n")
        hFlush stdout

        fix $ \again' -> do
          b <- fdRead stdInput 1
          when (b /= C8.pack "\ESC") $ do
            Pty.writePty pty b
            log ("StdIn whilst searching ESC " ++ pid ++ ": " ++ show b ++ "\n")
            again'

        log ("Found ESC " ++ pid ++ "\n")

        sofar <- flip fix mempty $ \again' sofar -> do
          b <- fdRead stdInput 1
          if b == C8.pack "R"
            then pure sofar
            else again' (sofar <> b)

        log ("Handled ESC " ++ pid ++ " " ++ show (C8.unpack sofar) ++ "\n")

        -- Drop ;
        let (x, Data.ByteString.drop 1 -> y) =
              C8.break (== ';') (Data.ByteString.drop 1 sofar)

        let x' = read (C8.unpack x) :: Int
        let y' = read (C8.unpack y) :: Int
        (cols, rows) <- readIORef theDims
        -- Go to first column on last row
        hPut stdout (C8.pack ("\ESC[" <> show rows <> ";1H"))
        -- Clear line
        hPut stdout (C8.pack "\ESC[K")
        hPut stdout (C8.pack (take cols bar))
        -- Go back to where we were
        hPut stdout (C8.pack ("\ESC[" <> show x' <> ";" <> show y' <> "H"))

  _ <- forkIO $
    fix $ \again -> do
      readEither >>= \case
        WinchIn -> do
          Just stdInPty <- Pty.createPty 0
          dims@(cols, rows) <- Pty.ptyDimensions stdInPty
          writeIORef theDims dims
          Pty.resizePty pty (cols, rows - 1)
          getPid childHandle >>= \case
            -- I guess this only happens if there is a race condition
            -- between SIGWINCH and termination of the child process
            Nothing -> pure ()
            Just childPid -> signalProcess sigWINCH childPid
          log ("WinchIn " ++ pid ++ ": " ++ show dims ++ "\n")
        StdIn bs -> do
          Pty.writePty pty bs
          log ("StdIn " ++ pid ++ ": " ++ show bs ++ "\n")
        PtyIn bs -> do
          hPut stdout bs
          log (show bs ++ "\n")

          when (not ('\ESC' `elem` C8.unpack bs)) $
            drawBar

      again

  exitWith =<< takeMVar exit

log :: String -> IO ()
log = appendFile "/tmp/log"
