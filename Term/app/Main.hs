{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
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
    takeMVar,
    tryPutMVar,
  )
import Control.Concurrent.Chan (newChan, readChan, writeChan)
import Control.Exception (IOException, try)
import Control.Monad (forever, when)
import Data.Bits ((.&.))
import Data.ByteString (ByteString, drop, hPut)
import Data.ByteString.Char8 qualified as C8
import Data.ByteString.Internal (c2w)
import Data.Char (isAlpha, isAscii)
import Data.Foldable (for_)
import Data.Function (fix)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
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

data In = PtyIn PtyParse | StdIn ByteString | WinchIn

type PtyParse = (ByteString, UpdateCursor)

type UpdateCursor =
  Bool ->
  (Int, Int) ->
  (Int, Int) ->
  IO (Bool, (Int, Int), Bool)

barLines :: Int
barLines = 3

readPty :: Pty.Pty -> IO (Either [Pty.PtyControlCode] ByteString)
readPty pty = do
  try (Pty.tryReadPty pty) >>= \case
    Left (_ :: IOError) -> (myThreadId >>= killThread) >> error "Impossible!"
    Right bs -> pure bs

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

  let readLoop yield' = sequentialize $ \sequentializer -> do
        yield <- sequentializer yield'

        pure
          [ handleForever (fdRead stdInput 1000) (yield . StdIn),
            ptyParses log pty (yield . PtyIn),
            mvarToLoop winchMVar (yield . const WinchIn)
          ]

  let putStdoutStr = hPut stdout . C8.pack

  let requestPosition :: IO (Int, Int)
      requestPosition = do
        -- Ask for the position
        putStdoutStr "\ESC[6n"

        log "Requesting position\n"

        fix $ \again' -> do
          b <- fdRead stdInput 1
          when (b /= C8.pack "\ESC") $ do
            Pty.writePty pty b
            log ("StdIn whilst searching ESC: " ++ show b ++ "\n")
            again'

        log "Found ESC\n"

        sofar <- flip fix mempty $ \again' sofar -> do
          b <- fdRead stdInput 1
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

  let requestPositionXY0 = do
        (y, x) <- requestPosition
        pure (x - 1, y - 1)

  let drawBar :: (Int, Int) -> IO ()
      drawBar (x, y) = do
        log ("Drawing bar and returning to " ++ show (x, y) ++ "\n")
        (cols, rows) <- readIORef theDims
        for_ [rows - barLines .. rows - 1] $ \l -> do
          putStdoutStr (cupXY0 (0, l))
          -- Clear line
          putStdoutStr "\ESC[K"
        -- Go to first column on first row of bar
        putStdoutStr (cupXY0 (0, rows - barLines))
        putStdoutStr (take cols bar)
        -- Go back to where we were
        putStdoutStr (cupXY0 (x, y))

  _ <- forkIO $ do
    pos <- do
      pos <- requestPositionXY0
      log ("pos: " ++ show pos ++ "\n")
      newIORef pos

    let scrollIfNeeded wasWrapnext (oldx, oldy) thePos@(_, y) bs = do
          (cols, rows) <- readIORef theDims
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

    let handlePtyF (bs, updateCursor) = do
          oldWrapnext <- readIORef cursorWrapnext
          oldPos <- readIORef pos
          dims <- readIORef theDims

          (nextWrapnext, newPos, dirty1) <- updateCursor oldWrapnext dims oldPos

          writeIORef cursorWrapnext nextWrapnext

          (newerPos, dirty2) <- scrollIfNeeded oldWrapnext oldPos newPos bs
          writeIORef pos newerPos
          hPut stdout bs

          when (dirty1 || dirty2) (drawBar =<< readIORef pos)

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
        handlePtyF move

  exitWhenRequested

handleForever :: IO a -> (a -> IO ()) -> IO r
handleForever act yield = forever (yield =<< act)

mvarToLoop :: MVar a -> (a -> IO ()) -> IO r
mvarToLoop v = handleForever (takeMVar v)

sequentialize ::
  ((forall a b. (a -> IO b) -> IO (a -> IO b)) -> IO [IO ()]) -> IO ()
sequentialize tasks = do
  requesting <- newEmptyMVar

  tasks' <- tasks $ \handler -> do
    av <- newEmptyMVar
    bv <- newEmptyMVar

    _ <- forkIO $ forever $ do
      a <- takeMVar av
      b <- handler a
      putMVar bv b
      takeMVar requesting

    pure $ \a -> do
      putMVar requesting ()
      putMVar av a
      takeMVar bv

  for_ tasks' forkIO

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

data PtyInput = NeedMore C8.ByteString | TryToParse C8.ByteString

ptyParses :: (String -> IO ()) -> Pty.Pty -> (PtyParse -> IO ()) -> IO a
ptyParses log pty yield = do
  unhandledPty <- newIORef (NeedMore mempty)

  forever $ do
    readIORef unhandledPty >>= \case
      NeedMore neededmore -> do
        readPty pty >>= \case
          Left {} ->
            -- I don't know what we should do with PtyControlCodes
            pure ()
          Right bs -> do
            log ("PtyIn: " ++ show bs ++ "\n")
            writeIORef unhandledPty (TryToParse (neededmore <> bs))
      TryToParse bsIn -> do
        parseBS log bsIn >>= \case
          Nothing -> do
            writeIORef unhandledPty (NeedMore bsIn)
          Just ((bs, theLeftovers), f) -> do
            yield (bs, f)
            writeIORef unhandledPty (TryToParse theLeftovers)

parseBS ::
  (String -> IO ()) ->
  ByteString ->
  IO (Maybe ((ByteString, ByteString), UpdateCursor))
parseBS log bsIn = do
  mResult <- parse log (C8.unpack bsIn)
  pure $ do
    (seen, f) <- mResult
    Just (C8.splitAt seen bsIn, f)

parse :: (String -> IO ()) -> String -> IO (Maybe (Int, UpdateCursor))
parse log = \case
  [] ->
    needMore
  -- This is "shift in", equivalent to '\017', and part of sgr0.
  --
  -- https://en.wikipedia.org/wiki/Shift_Out_and_Shift_In_characters
  '\SI' : _ -> do
    noLocationChangeConsuming 1
  '\r' : _ -> do
    pure (Just (1, \_ _ thePos -> pure (False, first (const 0) thePos, False)))
  '\n' : _ -> do
    pure (Just (1, \_ (_, rows) thePos -> pure (False, second (\y -> (y + 1) `min` (rows - barLines)) thePos, False)))
  '\a' : _ ->
    noLocationChangeConsuming 1
  '\b' : _ -> do
    pure
      ( Just
          ( 1,
            \_ (cols, rows) thePos ->
              let newPos =
                    let (x, y) = thePos
                        (yinc, x') = (x - 1) `divMod` cols
                     in (x', (y + yinc) `min` rows)
               in pure (False, newPos, False)
          )
      )
  '\ESC' : 'M' : _ -> do
    pure
      ( Just
          ( 2,
            \_ _ thePos ->
              let (_, oldy) = thePos
                  newPos = second (\y' -> (y' - 1) `max` 0) thePos
               in pure (False, newPos, oldy == 0)
          )
      )
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
        (updatePos, dirty) <- case verb of
          'H' -> case break (== ';') csi of
            ("", "") -> pure (const (0, 0), False)
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
              pure (const (xp1 - 1, yp1 - 1), False)
            (_, _ : _) -> do
              log "Impossible.  Split must start with ;"
              error "Impossible.  Split must start with ;"
          -- I actually get numeric Cs, despite saying I
          -- don't support them :(
          'J' -> do
            pure (id, True)
          'L' -> do
            pure (id, True)
          'A' -> do
            let (negate -> dy) = numberOr1IfMissing csi
            pure (second (+ dy), False)
          'B' -> do
            let dy = numberOr1IfMissing csi
            pure (second (+ dy), False)
          'C' -> do
            let dx = numberOr1IfMissing csi
            pure (first (+ dx), False)
          'D' -> do
            let (negate -> dx) = numberOr1IfMissing csi
            pure (first (+ dx), False)
          'G' -> do
            let x = read csi - 1
            pure (first (const x), False)
          'd' -> do
            let y = read csi - 1
            pure (second (const y), False)
          _ -> pure (id, False)
        pure
          ( Just
              ( 2 + length csi + 1,
                \inWrapnext _ thePos ->
                  let newPos = updatePos thePos
                   in pure
                        ( inWrapnext && (thePos == newPos),
                          newPos,
                          dirty
                        )
              )
          )
  '\ESC' : [] ->
    needMore
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
    numberOr1IfMissing csi
      | null csi = 1
      | otherwise = read csi

    noLocationChangeConsuming n =
      pure (Just (n, \inWrapnext _ thePos -> pure (inWrapnext, thePos, False)))

    singleDisplayableCharacter n =
      pure $
        Just
          ( n,
            \inWrapnext (cols, _) thePos -> do
              let (x, y) = thePos

              (newPos, nextWrapnext) <-
                case inWrapnext of
                  True -> pure ((1, y + 1), False)
                  False -> case x `compare` (cols - 1) of
                    GT -> do
                      log
                        ( "Warning: overflow: x: "
                            ++ show x
                            ++ " cols: "
                            ++ show cols
                        )
                      pure ((x, y), True)
                    EQ ->
                      pure ((x, y), True)
                    LT ->
                      pure ((x + 1, y), False)
              -- It's not completely clear whether we should mark the bar
              -- dirty here if we overwrite it, or only when we scroll.
              pure (nextWrapnext, newPos, False)
          )
    needMore = pure Nothing

insertAssocList :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
insertAssocList k v [] = [(k, v)]
insertAssocList k v ((k', v') : kvs) =
  if k == k'
    then (k, v) : kvs
    else (k', v') : insertAssocList k v kvs

-- https://github.com/martanne/dvtm/blob/7bcf43f8dbd5c4a67ec573a1248114caa75fa3c2/vt.c#L619-L624
isValidCsiEnder :: Char -> Bool
isValidCsiEnder c =
  (isAscii c && isAlpha c) || (c == '@') || (c == '`')

cupXY0 :: (Int, Int) -> String
cupXY0 (x, y) = "\ESC[" <> show (y + 1) <> ";" <> show (x + 1) <> "H"
