{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Concurrent
  ( MVar,
    forkIO,
    killThread,
    myThreadId,
    newEmptyMVar,
    putMVar,
    readMVar,
    takeMVar,
    threadWaitRead,
    tryPutMVar,
  )
import Control.Exception (try)
import Control.Monad (when)
import Data.ByteString (ByteString, drop, hPut)
import Data.ByteString.Char8 qualified as C8
import Data.Foldable (for_)
import Data.Function (fix)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Traversable (for)
import Foreign.C.Types (CSize)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitWith)
import System.IO
  ( BufferMode (NoBuffering),
    hFlush,
    hSetBuffering,
    stdin,
    stdout,
  )
import System.Posix (Fd, getProcessID)
import System.Posix.IO (stdInput)
import System.Posix.IO.ByteString (fdRead)
import System.Posix.Pty qualified as Pty
import System.Posix.Signals
  ( Handler (Catch),
    installHandler,
    sigCHLD,
    signalProcess,
  )
import System.Posix.Signals.Exts (sigWINCH)
import System.Posix.Terminal
  ( TerminalMode
      ( EnableEcho,
        KeyboardInterrupts,
        MapCRtoLF,
        ProcessInput,
        ProcessOutput,
        StartStopInput,
        StartStopOutput
      ),
    TerminalState (Immediately),
    getTerminalAttributes,
    setTerminalAttributes,
    withoutMode,
  )
import System.Process (getPid, getProcessExitCode)
import Text.Read (readMaybe)
import Prelude hiding (log)

data In = PtyIn ByteString | StdIn ByteString | WinchIn

data Selector a = MkSelector (IO ()) (IO a)
  deriving (Functor)

selectorFd :: CSize -> Fd -> Selector ByteString
selectorFd n fd =
  -- We shouldn't threadWaitRead on an Fd from a Handle
  -- because the Handle buffers some of the input so we wait
  -- even when there's buffered input available.
  MkSelector (threadWaitRead fd) (fdRead fd n)

selectorPty :: Pty.Pty -> Selector ByteString
selectorPty pty =
  MkSelector (Pty.threadWaitReadPty pty) (readPty pty)

selectorMVar :: MVar a -> Selector a
selectorMVar v =
  MkSelector (() <$ readMVar v) (takeMVar v)

readPty :: Pty.Pty -> IO ByteString
readPty pty = do
  try (Pty.readPty pty) >>= \case
    Left (_ :: IOError) -> (myThreadId >>= killThread) >> error "Impossible!"
    Right bs -> pure bs

select :: [Selector a] -> IO a
select selectors = do
  inMVar <- newEmptyMVar

  ts <- for selectors $ \(MkSelector wait act) -> forkIO $ do
    wait
    putMVar inMVar act

  act <- readMVar inMVar
  for_ ts killThread
  act

main :: IO ()
main = do
  (bar, prog) <-
    getArgs >>= \case
      [bar, prog] -> pure (bar, prog)
      _ -> do
        putStrLn "I need two arguments: the text to display and the program to run"
        exitFailure

  stdInPty <-
    Pty.createPty 0 >>= \case
      Nothing -> do
        putStrLn "Was not attached to terminal"
        exitFailure
      Just stdInPty -> pure stdInPty

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
            -- Disabling KeyboardInterrupts (ISIG) means that typing
            -- Ctrl-C, Ctrl-Z, and probably others, is not treated
            -- specially by the terminal.  It just sends that
            -- character to the child process.
            . flip withoutMode KeyboardInterrupts
        )
          oldTermSettings
  -- Should probably reset this on exit
  setTerminalAttributes stdInput newTermSettings Immediately

  theDims <- do
    dims <- Pty.ptyDimensions stdInPty
    newIORef dims

  (pty, childHandle) <- do
    (cols, rows) <- readIORef theDims
    Pty.spawnWithPty Nothing True "sh" ["-c", prog] (cols, subtract 1 rows)

  exit <- newEmptyMVar

  _ <- flip (installHandler sigCHLD) Nothing . Catch $ do
    e <-
      getProcessExitCode childHandle >>= \case
        Nothing ->
          error "Impossible: should only happen when the process is still running"
        Just e -> pure e

    putMVar exit e

  winchSelector <- do
    winchMVar <- newEmptyMVar
    _ <- flip (installHandler sigWINCH) Nothing . Catch $ do
      _ <- tryPutMVar winchMVar ()
      pure ()
    pure (selectorMVar winchMVar)

  let readEither = do
        select
          [ StdIn <$> selectorFd 1000 stdInput,
            PtyIn <$> selectorPty pty,
            WinchIn <$ winchSelector
          ]

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

        let mxy = do
              x' <- readMaybe (C8.unpack x) :: Maybe Int
              y' <- readMaybe (C8.unpack y) :: Maybe Int
              pure (x', y')

        (x', y') <- case mxy of
          Nothing -> error ("No read for " <> C8.unpack sofar)
          Just xy -> pure xy

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
