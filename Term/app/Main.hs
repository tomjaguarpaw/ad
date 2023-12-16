{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
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
import Control.Exception (IOException, try)
import Control.Monad (when)
import Data.Bits ((.&.))
import Data.ByteString (ByteString, drop, hPut)
import Data.ByteString.Char8 qualified as C8
import Data.ByteString.Internal (c2w)
import Data.Char (isAlpha, isAscii)
import Data.Foldable (for_)
import Data.Function (fix)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Traversable (for)
import Foreign.C.Types (CSize)
import System.Environment (getArgs, getEnvironment)
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

data In = PtyIn (Either [Pty.PtyControlCode] ByteString) | StdIn ByteString | WinchIn

data Selector a = MkSelector (IO ()) (IO a)
  deriving (Functor)

selectorFd :: CSize -> Fd -> Selector ByteString
selectorFd n fd =
  -- We shouldn't threadWaitRead on an Fd from a Handle
  -- because the Handle buffers some of the input so we wait
  -- even when there's buffered input available.
  MkSelector (threadWaitRead fd) (fdRead fd n)

selectorPty :: Pty.Pty -> Selector (Either [Pty.PtyControlCode] ByteString)
selectorPty pty =
  -- We should not use Pty.readPty after Pty.threadWaitReadPty because
  -- readPty discards control codes, and may therefore block even
  -- though using threadWaitRead means we don't expect it to.
  MkSelector (Pty.threadWaitReadPty pty) (readPty pty)

selectorMVar :: MVar a -> Selector a
selectorMVar v =
  MkSelector (() <$ readMVar v) (takeMVar v)

readPty :: Pty.Pty -> IO (Either [Pty.PtyControlCode] ByteString)
readPty pty = do
  try (Pty.tryReadPty pty) >>= \case
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
    env <- getEnvironment
    (cols, rows) <- readIORef theDims
    Pty.spawnWithPty
      (Just (("TERM", terminfoName) : env))
      True
      "sh"
      ["-c", prog]
      (cols, subtract 1 rows)

  exit <- newEmptyMVar

  _ <- flip (installHandler sigCHLD) Nothing . Catch $ do
    e <-
      getProcessExitCode childHandle >>= \case
        Nothing -> do
          log "Impossible: should only happen when the process is still running"
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
          Nothing -> do
            log ("No read for " <> show sofar)
            error ("No read for " <> show sofar)
          Just xy -> pure xy

  let requestPositionXY0 = do
        (y, x) <- requestPosition
        pure (x - 1, y - 1)

  let drawBar :: (Int, Int) -> IO ()
      drawBar (x@((+ 1) -> xp1), y@((+ 1) -> yp1)) = do
        log ("Drawing bar and returning to " ++ show (x, y) ++ "\n")
        (cols, rows) <- readIORef theDims
        -- Go to first column on last row
        hPut stdout (C8.pack ("\ESC[" <> show rows <> ";1H"))
        -- Clear line
        hPut stdout (C8.pack "\ESC[K")
        hPut stdout (C8.pack (take cols bar))
        -- Go back to where we were
        hPut stdout (C8.pack ("\ESC[" <> show yp1 <> ";" <> show xp1 <> "H"))

  _ <- forkIO $ do
    pos <- do
      pos <- requestPositionXY0
      log ("pos: " ++ show pos ++ "\n")
      newIORef pos

    let scrollIfNeeded wasWrapnext (oldxm1, oldym1) (markBarDirty :: IO ()) bs = do
          (_, rows) <- readIORef theDims
          (x, y0) <- readIORef pos
          when (y0 == rows - 1) $ do
            log ("Overlap detected before " ++ show bs ++ ", going back to " ++ show (y0 - 1) ++ "\n")
            hPut
              stdout
              ( C8.pack
                  ( "\ESC["
                      ++ show rows
                      ++ ";1H"
                      ++ "\ESC[K\n\ESCM\ESC["
                      ++ show (1 + if wasWrapnext then oldym1 else oldym1 - 1)
                      ++ ";"
                      ++ show (1 + if wasWrapnext then 0 else oldxm1)
                      ++ "H"
                  )
              )
            markBarDirty
            writeIORef pos (x, y0 - 1)

    do
      oldPos <- readIORef pos
      scrollIfNeeded False oldPos (pure ()) (C8.pack "Initial scroll")

    -- Like CURSOR_WRAPNEXT from st
    cursorWrapnext <- newIORef False

    let handlePty bsIn = do
          (markBarDirty, isBarDirty) <- do
            barDirty <- newIORef False
            pure (writeIORef barDirty True, readIORef barDirty)

          inWrapnext <- readIORef cursorWrapnext
          oldPos <- readIORef pos
          dims <- readIORef theDims
          ((mseen, nextWrapnext), newPos) <-
            parse markBarDirty inWrapnext dims oldPos (C8.unpack bsIn)

          writeIORef cursorWrapnext nextWrapnext
          writeIORef pos newPos

          case mseen of
            Nothing -> pure Nothing
            Just seen -> do
              let (bs, theLeftovers) = C8.splitAt seen bsIn

              scrollIfNeeded inWrapnext oldPos markBarDirty bs
              hPut stdout bs

              dirty <- isBarDirty
              when dirty (drawBar =<< readIORef pos)

              pure (Just theLeftovers)

    unhandledPty <- newIORef (Left mempty)

    fix $ \again -> do
      readIORef unhandledPty >>= \case
        Left neededmore -> do
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
            PtyIn (Right bs) -> do
              log ("PtyIn " ++ pid ++ ": " ++ show bs ++ "\n")
              writeIORef unhandledPty (Right (neededmore <> bs))
            PtyIn (Left {}) ->
              -- I don't know what we should do with PtyControlCodes
              pure ()
        Right bs -> do
          eleftovers <- handlePty bs
          thePos <- readIORef pos
          let mneleftovers =
                case eleftovers of
                  Just leftovers -> Right leftovers
                  Nothing -> Left bs
          case mneleftovers of
            Left {} -> log ("handlePty: pos " ++ show thePos ++ "\n")
            Right {} -> pure ()
          writeIORef unhandledPty mneleftovers

      again

  exitWith =<< takeMVar exit

warnIfTerminfoMissing :: String -> String -> IO ()
warnIfTerminfoMissing terminfoName terminfoFilename = do
  exitCode <-
    try
      $ runProcess
      $ setStdin nullStream
        . setStdout nullStream
        . setStderr nullStream
      $ proc "tic" [terminfoName]

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

parse ::
  IO () ->
  Bool ->
  (Int, Int) ->
  (Int, Int) ->
  String ->
  IO ((Maybe Int, Bool), (Int, Int))
parse markBarDirty inWrapnext (cols, rows) = parse'
  where
    parse' thePos =
      \case
        [] ->
          needMore
        -- No idea what \SI is or why zsh outputs it
        '\SI' : _ -> do
          noLocationChangeConsuming 1
        '\r' : _ -> do
          pure ((Just 1, False), first (const 0) thePos)
        '\n' : _ -> do
          log "Newline\n"
          pure ((Just 1, False), second (\y -> (y + 1) `min` (rows - 1)) thePos)
        '\a' : _ ->
          noLocationChangeConsuming 1
        '\b' : _ -> do
          let newPos =
                let (x, y) = thePos
                    (yinc, x') = (x - 1) `divMod` cols
                 in (x', (y + yinc) `min` rows)
          pure ((Just 1, False), newPos)
        '\ESC' : 'M' : _ -> do
          let newPos@(_, y) = second (\y' -> (y' - 1) `max` 0) thePos
          when (y == 0) markBarDirty
          pure ((Just 2, False), newPos)
        '\ESC' : '>' : _ -> do
          noLocationChangeConsuming 2
        '\ESC' : '=' : _ -> do
          noLocationChangeConsuming 2
        -- Not sure how to parse sgr0 (or sgr) as a general CSI
        -- code.  What are we supposed to do with '\017'?
        '\ESC' : '[' : 'm' : '\017' : _ -> do
          noLocationChangeConsuming 4
        '\ESC' : '[' : csiAndRest -> do
          case break isValidCsiEnder csiAndRest of
            (_, "") -> needMore
            -- In the general case we'll need to parse parameters
            (csi, verb : _) -> do
              newPos <- case verb of
                'H' -> case break (== ';') csi of
                  ("", "") -> pure (0, 0)
                  (_ : _, "") -> do
                    log "error: I guess this is just y"
                    error "I guess this is just y"
                  (yp1s, ';' : xp1s) -> do
                    xp1 <- case readMaybe xp1s of
                      Nothing -> do
                        log ("Could not read: " ++ show xp1s ++ "\n")
                        error ("Could not read: " ++ show xp1s)
                      Just j -> pure j
                    yp1 <- case readMaybe yp1s of
                      Nothing -> do
                        log ("Could not read: " ++ show yp1s ++ "\n")
                        error ("Could not read: " ++ show yp1s)
                      Just j -> pure j
                    pure (xp1 - 1, yp1 - 1)
                  (_, _ : _) -> do
                    log "Impossible.  Split must start with ;"
                    error "Impossible.  Split must start with ;"
                -- I actually get numeric Cs, despite saying I
                -- don't support them :(
                'J' -> do
                  markBarDirty
                  pure thePos
                'L' -> do
                  markBarDirty
                  pure thePos
                'A' -> do
                  let (negate -> dy)
                        | null csi = 1
                        | otherwise = read csi
                  pure (second (+ dy) thePos)
                'B' -> do
                  let dy
                        | null csi = 1
                        | otherwise = read csi
                  pure (second (+ dy) thePos)
                'C' -> do
                  let dx
                        | null csi = 1
                        | otherwise = read csi
                  pure (first (+ dx) thePos)
                'D' -> do
                  let mdx
                        | null csi = 1
                        | otherwise = read csi
                  pure (first (+ negate mdx) thePos)
                _ -> pure thePos
              pure ((Just (2 + length csi + 1), False), newPos)
        (c2w -> word) : rest
          | (word .&. 0b10000000) == 0b00000000 ->
              -- One byte (ASCII)
              singleDisplayableCharacter 1
          | (word .&. 0b11100000) == 0b11000000 ->
              -- Two byte
              case rest of
                _ : _ -> singleDisplayableCharacter 2
                _ -> needMore
          | (word .&. 0b11110000) == 0b11100000 ->
              -- Three byte
              case rest of
                _ : _ : _ -> singleDisplayableCharacter 3
                _ -> needMore
          | (word .&. 0b11111000) == 0b11110000 ->
              -- Four byte
              case rest of
                _ : _ : _ : _ -> singleDisplayableCharacter 4
                _ -> needMore
        c : _ -> do
          -- No idea what these mysterious entities are
          log ("Mysterious entity: " ++ show c ++ "\n")
          singleDisplayableCharacter 1
      where
        noLocationChangeConsuming n =
          pure ((Just n, inWrapnext), thePos)

        singleDisplayableCharacter n = do
          let (x, y) = thePos

          (newPos, nextWrapnext) <-
            case inWrapnext of
              True -> pure ((1, y + 1), False)
              False -> do
                -- x > cols shouldn't happen. Check for it, and
                -- at least warn?
                pure $
                  if x >= cols - 1
                    then ((x, y), True)
                    else ((x + 1, y), False)
          pure ((Just n, nextWrapnext), newPos)
        needMore = pure ((Nothing, inWrapnext), thePos)

-- https://github.com/martanne/dvtm/blob/7bcf43f8dbd5c4a67ec573a1248114caa75fa3c2/vt.c#L619-L624
isValidCsiEnder :: Char -> Bool
isValidCsiEnder c =
  (isAscii c && isAlpha c) || (c == '@') || (c == '`')

log :: String -> IO ()
log = appendFile "/tmp/log"
