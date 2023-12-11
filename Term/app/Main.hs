{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Arrow (Arrow (second), first)
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
import Data.Char (isAlpha, isAscii)
import Data.Foldable (for_)
import Data.Function (fix)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
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

  let requestPosition :: IO (Int, Int)
      requestPosition = do
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

        case mxy of
          Nothing -> error ("No read for " <> C8.unpack sofar)
          Just xy -> pure xy

  let requestPositionXY0 = do
        (y, x) <- requestPosition
        pure (x - 1, y - 1)

  let drawBar :: IO ()
      drawBar = do
        (x', y') <- requestPosition

        (cols, rows) <- readIORef theDims
        -- Go to first column on last row
        hPut stdout (C8.pack ("\ESC[" <> show rows <> ";1H"))
        -- Clear line
        hPut stdout (C8.pack "\ESC[K")
        hPut stdout (C8.pack (take cols bar))
        -- Go back to where we were
        hPut stdout (C8.pack ("\ESC[" <> show x' <> ";" <> show y' <> "H"))

  _ <- forkIO $ do
    pos <- do
      pos <- requestPositionXY0
      log ("pos: " ++ show pos ++ "\n")
      newIORef pos

    -- Like CURSOR_WRAPNEXT from st
    cursorWrapnext <- newIORef False

    let handlePty bsIn = do
          (theLeftovers, seen) <- (fmap . first) C8.pack $ case C8.unpack bsIn of
            [] ->
              pure ("", 0)
            -- No idea what \SI is or why zsh outputs it
            '\SI' : rest -> do
              pure (rest, 1)
            '\r' : rest -> do
              modifyIORef' pos (first (const 0))
              writeIORef cursorWrapnext False
              pure (rest, 1)
            '\n' : rest -> do
              (_, rows) <- readIORef theDims
              modifyIORef' pos (second (\y -> (y + 1) `min` (rows - 1)))
              log "Newline\n"
              writeIORef cursorWrapnext False
              pure (rest, 1)
            '\a' : rest ->
              pure (rest, 1)
            '\b' : rest -> do
              (cols, rows) <- readIORef theDims
              modifyIORef'
                pos
                ( \(x, y) ->
                    let (yinc, x') = (x - 1) `divMod` cols
                     in (x', (y + yinc) `min` rows)
                )
              writeIORef cursorWrapnext False
              pure (rest, 1)
            '\ESC' : 'M' : rest -> do
              modifyIORef' pos (second (\y -> (y - 1) `max` 0))
              writeIORef cursorWrapnext False
              pure (rest, 2)
            '\ESC' : '>' : rest -> do
              pure (rest, 2)
            '\ESC' : '=' : rest -> do
              pure (rest, 2)
            -- Not sure how to parse sgr0 (or sgr) as a general CSI
            -- code.  What are we supposed to do with '\017'?
            '\ESC' : '[' : 'm' : '\017' : rest -> do
              pure (rest, 4)
            '\ESC' : '[' : csiAndRest -> do
              case break isValidCsiEnder csiAndRest of
                (_, "") -> error ("Missing CSI ender in " ++ show csiAndRest)
                -- In the general case we'll need to parse parameters
                (csi, verb : rest) -> do
                  case verb of
                    'H' -> writeIORef pos (0, 0)
                    -- I actually get numeric Cs, despite saying I
                    -- don't support them :(
                    'C' -> modifyIORef' pos (first (+ 1))
                    _ -> pure ()
                  writeIORef cursorWrapnext False
                  pure (rest, 2 + length csi + 1)
            _ : rest -> do
              (x, y) <- readIORef pos

              (x', y') <-
                readIORef cursorWrapnext >>= \case
                  True -> do
                    writeIORef cursorWrapnext False
                    pure (0, y + 1)
                  False -> do
                    (cols, _) <- readIORef theDims
                    x' <-
                      -- x > cols shouldn't happen. Check for it, and
                      -- at least warn?
                      if x >= cols - 1
                        then do
                          writeIORef cursorWrapnext True
                          pure x
                        else pure (x + 1)
                    pure (x', y)

              writeIORef pos (x', y')
              pure (rest, 1)

          let bs = C8.take seen bsIn

          when (C8.length bsIn /= seen + C8.length theLeftovers) $
            error (show (C8.length bsIn, seen, C8.length theLeftovers))

          hPut stdout bs
          dims@(_, rows) <- readIORef theDims
          thePos <- do
            (x, y0) <- readIORef pos
            y <- do
              log "Checking overlap: "
              if y0 == rows - 1
                then do
                  log ("detected, going back to " ++ show (y0 - 1) ++ "\n")
                  hPut stdout (C8.pack "\n\ESCM")
                  pure (y0 - 1)
                else do
                  log "not detected\n"
                  pure y0
            writeIORef pos (x, y)
            pure (x, y)

          log (show bs ++ " " ++ show thePos ++ " " ++ show dims ++ "\n")

          drawBar

          pure theLeftovers

    unhandledPty <- newIORef Nothing

    fix $ \again -> do
      readIORef unhandledPty >>= \case
        Nothing -> do
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
            PtyIn bs -> writeIORef unhandledPty (Just bs)
        Just bs -> do
          leftovers <- handlePty bs
          let mneleftovers =
                if C8.null leftovers
                  then Nothing
                  else Just leftovers
          writeIORef unhandledPty mneleftovers

      again

  exitWith =<< takeMVar exit

-- https://github.com/martanne/dvtm/blob/7bcf43f8dbd5c4a67ec573a1248114caa75fa3c2/vt.c#L619-L624
isValidCsiEnder :: Char -> Bool
isValidCsiEnder c =
  (isAscii c && isAlpha c) || (c == '@') || (c == '`')

log :: String -> IO ()
log = appendFile "/tmp/log"
