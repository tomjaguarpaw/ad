{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Arrow (Arrow (second))
import Control.Concurrent
  ( MVar,
    forkIO,
    newEmptyMVar,
    putMVar,
    takeMVar,
    threadDelay,
    tryPutMVar,
  )
import Control.Concurrent.Async qualified as Async
import Control.Concurrent.Chan (newChan, readChan, writeChan)
import Control.Exception (IOException, try)
import Control.Monad (forever, when)
import Data.ByteString (ByteString, drop, hPut)
import Data.ByteString.Char8 qualified as C8
import Data.Foldable (for_)
import Data.Function (fix)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.Void (absurd)
import Parse
  ( PtyParse,
    UpdateCursor (MkUpdateCursor),
    barLines,
    handleForever,
    ptyParses,
  )
import System.Environment (getArgs, getEnvironment)
import System.Exit (exitFailure, exitWith)
import System.IO
  ( BufferMode (NoBuffering),
    hSetBuffering,
    stdin,
    stdout,
  )
import System.Posix (getProcessID)
import System.Posix.IO (stdInput)
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
import System.Process.Typed
  ( ExitCode (ExitFailure, ExitSuccess),
    nullStream,
    proc,
    runProcess,
    setStderr,
    setStdin,
    setStdout,
  )
import Text.Read (readMaybe)
import Prelude hiding (log)

data In = PtyIn PtyParse | StdIn ByteString | WinchIn

readPty :: Pty.Pty -> IO (Either [Pty.PtyControlCode] ByteString)
readPty pty = do
  try (Pty.tryReadPty pty) >>= \case
    Left (_ :: IOError) -> forever $ do
      threadDelay (1000 * 1000 * 1000)
    Right bs -> pure bs

race :: IO a -> IO a -> IO a
race m1 m2 = fmap (either id id) (Async.race m1 m2)

main :: IO ()
main = do
  let terminfoName = "smy"
      terminfoFilename = "smy"

  warnIfTerminfoMissing terminfoName terminfoFilename
  warnIfHostTerminalUnsuitable

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
    env <- getEnvironment
    (cols, rows) <- readIORef theDims
    Pty.spawnWithPty
      (Just (insertAssocList "TERM" terminfoName env))
      True
      "sh"
      ["-c", prog]
      (cols, rows - barLines)

  (requestExit, exitWhenRequested) <- do
    exit <- newEmptyMVar
    pure (putMVar exit, exitWith =<< takeMVar exit)

  log <- makeLogger

  _ <- flip (installHandler sigCHLD) Nothing . Catch $ do
    e <-
      getProcessExitCode childHandle >>= \case
        Nothing -> do
          log "Impossible: should only happen when the process is still running"
          error "Impossible: should only happen when the process is still running"
        Just e -> pure e

    requestExit e

  winchMVar <- do
    winchMVar <- newEmptyMVar
    _ <- flip (installHandler sigWINCH) Nothing . Catch $ do
      _ <- tryPutMVar winchMVar ()
      pure ()
    pure winchMVar

  let readLoop :: (In -> IO ()) -> IO a
      readLoop yield' = do
        let sequentializeYield handler = do
              requesting <- newEmptyMVar
              pure $ \a -> do
                putMVar requesting ()
                b <- handler a
                takeMVar requesting
                pure b

        yield <- sequentializeYield yield'

        handleForever (C8.hGetSome stdin 1000) (yield . StdIn)
          `race` ptyParsesIncludingControlCode log (readPty pty) (yield . PtyIn)
          `race` mvarToLoop winchMVar (yield . const WinchIn)
          `race` fmap absurd exitWhenRequested

  let drawBar :: (Int, Int) -> (Int, Int) -> IO ()
      drawBar (cols, rows) (x, y) = do
        log ("Drawing bar and returning to " ++ show (x, y) ++ "\n")
        for_ [rows - barLines .. rows - 1] $ \l -> do
          putStdoutStr (cupXY0 (0, l))
          -- Clear line
          putStdoutStr "\ESC[K"
        -- Go to first column on first row of bar
        putStdoutStr (cupXY0 (0, rows - barLines))
        putStdoutStr (take cols bar)
        -- Go back to where we were
        putStdoutStr (cupXY0 (x, y))

  do
    pos <- do
      pos <- requestPositionXY0 pty log
      log ("pos: " ++ show pos ++ "\n")
      newIORef pos

    let scrollIfNeeded (cols, rows) wasWrapnext (oldx, oldy) thePos@(_, y) bs = do
          let virtualDims@(_, virtualRows) = (cols, rows - barLines)
          let scrollLinesNeeded = if y == virtualRows then 1 else 0 :: Int
          let returnTo =
                if wasWrapnext
                  then (0, oldy)
                  else (oldx, oldy - 1)
          when (scrollLinesNeeded > 0) $ do
            log
              ( "Overlap detected before "
                  ++ show bs
                  ++ ", going back to "
                  ++ show returnTo
                  ++ "/"
                  ++ show virtualDims
                  ++ "\n"
              )
            putStdoutStr
              ( cupXY0 (0, virtualRows)
                  ++ "\ESC[K"
                  ++ cupXY0 (0, rows - 1)
                  ++ "\n"
                  ++ cupXY0 returnTo
              )
          let dirty = scrollLinesNeeded > 0
          pure (second (subtract scrollLinesNeeded) thePos, dirty)

    do
      (x, y) <- readIORef pos
      (_, rows) <- readIORef theDims
      let virtualRows = rows - barLines
          scrollLinesNeeded = (y - virtualRows + 1) `max` 0
      log ("scrollLinesNeeded: " ++ show scrollLinesNeeded ++ "\n")
      when (scrollLinesNeeded > 0) $ do
        putStdoutStr
          ( cupXY0 (0, rows - 1)
              ++ replicate scrollLinesNeeded '\n'
              ++ cupXY0 (x, y - scrollLinesNeeded)
          )
        modifyIORef' pos (second (subtract scrollLinesNeeded))

    -- Like CURSOR_WRAPNEXT from st
    cursorWrapnext <- newIORef False

    let handlePtyF dims (bs, MkUpdateCursor updateCursor) = do
          oldWrapnext <- readIORef cursorWrapnext
          oldPos <- readIORef pos

          (nextWrapnext, newPos, dirty1) <- updateCursor log oldWrapnext dims oldPos

          writeIORef cursorWrapnext nextWrapnext

          (newerPos, dirty2) <- scrollIfNeeded dims oldWrapnext oldPos newPos bs
          writeIORef pos newerPos
          hPut stdout bs

          when (dirty1 || dirty2) (drawBar dims =<< readIORef pos)

    readLoop $ \case
      WinchIn -> do
        dims@(cols, rows) <- Pty.ptyDimensions stdInPty
        writeIORef theDims dims
        Pty.resizePty pty (cols, rows - barLines)
        getPid childHandle >>= \case
          -- I guess this only happens if there is a race condition
          -- between SIGWINCH and termination of the child process
          Nothing -> pure ()
          Just childPid -> signalProcess sigWINCH childPid
        log ("WinchIn: " ++ show dims ++ "\n")
      StdIn bs -> do
        Pty.writePty pty bs
        log ("StdIn: " ++ show bs ++ "\n")
      PtyIn move -> do
        dims <- readIORef theDims
        handlePtyF dims move

putStdoutStr :: String -> IO ()
putStdoutStr = hPut stdout . C8.pack

requestPosition :: Pty.Pty -> (String -> IO ()) -> IO (Int, Int)
requestPosition pty log = do
  -- Ask for the position
  putStdoutStr "\ESC[6n"

  log "Requesting position\n"

  fix $ \again' -> do
    b <- C8.hGet stdin 1
    when (b /= C8.pack "\ESC") $ do
      Pty.writePty pty b
      log ("StdIn whilst searching ESC: " ++ show b ++ "\n")
      again'

  log "Found ESC\n"

  sofar <- flip fix mempty $ \again' sofar -> do
    b <- C8.hGet stdin 1
    if b == C8.pack "R"
      then pure sofar
      else again' (sofar <> b)

  log ("Handled ESC: " ++ show (C8.unpack sofar) ++ "\n")

  -- Drop ;
  let (x, Data.ByteString.drop 1 -> y) =
        C8.break (== ';') (Data.ByteString.drop 1 sofar)

  let mxy = do
        x' <- readMaybe (C8.unpack x) :: Maybe Int
        y' <- readMaybe (C8.unpack y) :: Maybe Int
        pure (x', y')

  case mxy of
    Nothing -> do
      log ("No read for " <> show sofar)
      error ("No read for " <> show sofar)
    Just xy -> pure xy

requestPositionXY0 :: Pty.Pty -> (String -> IO ()) -> IO (Int, Int)
requestPositionXY0 pty log = do
  (y, x) <- requestPosition pty log
  pure (x - 1, y - 1)


mvarToLoop :: MVar a -> (a -> IO ()) -> IO r
mvarToLoop v = handleForever (takeMVar v)

warnIfTerminfoMissing :: String -> String -> IO ()
warnIfTerminfoMissing terminfoName terminfoFilename = do
  exitCode <-
    try
      $ runProcess
      $ setStdin nullStream
        . setStdout nullStream
        . setStderr nullStream
      $ proc "infocmp" [terminfoName]

  case exitCode of
    Left (_ :: IOException) -> do
      putStrLn
        ( unwords
            [ "Warning: I couldn't run tic so I couldn't determine",
              "whether you have a terminfo entry for ",
              terminfoName
            ]
        )
    Right ExitSuccess -> pure ()
    Right (ExitFailure {}) -> do
      putStrLn ("Warning: could not find terminfo entry for " ++ terminfoName)
      putStrLn "Terminal programs may not display correctly"
      putStrLn
        ( "You can install the terminfo entry by finding the "
            ++ terminfoFilename
            ++ " file in the repo and running \"tic "
            ++ terminfoFilename
            ++ "\""
        )

warnIfHostTerminalUnsuitable :: IO ()
warnIfHostTerminalUnsuitable = do
  env <- getEnvironment
  case lookup "TERM" env of
    Just "screen" -> pure ()
    _ ->
      putStrLn
        ( unwords
            [ "Warning: Currently, I only really",
              "work well with \"screen\" as my host"
            ]
        )

makeLogger :: IO (String -> IO ())
makeLogger = do
  pid <- show <$> getProcessID
  q <- newChan
  _ <- forkIO $ forever $ do
    s <- readChan q
    appendFile "/tmp/log" (pid ++ ": " ++ s)

  pure (writeChan q)

ptyParsesIncludingControlCode ::
  (String -> IO ()) ->
  IO (Either [Pty.PtyControlCode] ByteString) ->
  (PtyParse -> IO ()) ->
  IO a
ptyParsesIncludingControlCode log nextChunk yield =
  -- I don't know what we should do with PtyControlCodes
  consumeRights nextChunk $ \nextByteString -> do
    ptyParses log nextByteString yield

consumeRights ::
  IO (Either a b) ->
  (IO b -> IO r) ->
  IO r
consumeRights await k = do
  let go = do
        await >>= \case
          Left _ -> go
          Right r -> pure r

  k go

insertAssocList :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
insertAssocList k v [] = [(k, v)]
insertAssocList k v ((k', v') : kvs) =
  if k == k'
    then (k, v) : kvs
    else (k', v') : insertAssocList k v kvs

cupXY0 :: (Int, Int) -> String
cupXY0 (x, y) = "\ESC[" <> show (y + 1) <> ";" <> show (x + 1) <> "H"
