{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveFunctor #-}
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
    readMVar,
    takeMVar,
    threadWaitRead,
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

data In = PtyIn PtyParse | StdIn ByteString | WinchIn

type PtyParse = (ByteString, UpdateCursor)

type UpdateCursor =
  Bool ->
  (Int, Int) ->
  (Int, Int) ->
  IO (Bool, (Int, Int), Bool)

data Selector a = MkSelector (IO ()) (IO a)
  deriving (Functor)

barLines :: Int
barLines = 3

selectorFd :: CSize -> Fd -> Selector ByteString
selectorFd n fd =
  -- We shouldn't threadWaitRead on an Fd from a Handle
  -- because the Handle buffers some of the input so we wait
  -- even when there's buffered input available.
  MkSelector (threadWaitRead fd) (fdRead fd n)

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
      (Just (insertAssocList "TERM" terminfoName env))
      True
      "sh"
      ["-c", prog]
      (cols, rows - barLines)

  exit <- newEmptyMVar

  log <- do
    q <- newChan
    _ <- forkIO $ forever $ do
      s <- readChan q
      appendFile "/tmp/log" s

    pure (writeChan q)

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

  ptyInVar <- myPtyIn log pid pty

  let readEither = do
        select
          [ StdIn <$> selectorFd 1000 stdInput,
            PtyIn <$> selectorMVar ptyInVar,
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
        for_ [rows - barLines + 1 .. rows - 1 + 1] $ \l -> do
          hPut stdout (C8.pack ("\ESC[" <> show l <> ";1H"))
          -- Clear line
          hPut stdout (C8.pack "\ESC[K")
        -- Go to first column on first row of bar
        hPut stdout (C8.pack ("\ESC[" <> show (rows - barLines + 1) <> ";1H"))
        hPut stdout (C8.pack (take cols bar))
        -- Go back to where we were
        hPut stdout (C8.pack ("\ESC[" <> show yp1 <> ";" <> show xp1 <> "H"))

  _ <- forkIO $ do
    pos <- do
      pos <- requestPositionXY0
      log ("pos: " ++ show pos ++ "\n")
      newIORef pos

    let scrollIfNeeded wasWrapnext (oldxm1, oldym1) (markBarDirty :: IO ()) bs = do
          (cols, rows) <- readIORef theDims
          let virtualDims@(_, virtualRows) = (cols, rows - barLines)
          (_, y) <- readIORef pos
          let scrollLinesNeeded = if y == virtualRows then 1 else 0 :: Int
          when (scrollLinesNeeded > 0) $ do
            log ("Overlap detected before " ++ show bs ++ ", going back to " ++ show (y - 1) ++ "/" ++ show virtualDims ++ "\n")
            hPut
              stdout
              ( C8.pack
                  ( "\ESC["
                      ++ show (virtualRows + 1)
                      ++ ";1H"
                      ++ "\ESC[K"
                      ++ "\ESC["
                      ++ show (rows - 1 + 1)
                      ++ ";1H"
                      ++ "\n\ESCM\ESC["
                      ++ show (1 + if wasWrapnext then oldym1 else oldym1 - 1)
                      ++ ";"
                      ++ show (1 + if wasWrapnext then 0 else oldxm1)
                      ++ "H"
                  )
              )
            markBarDirty
            modifyIORef' pos (second (subtract scrollLinesNeeded))

    do
      (x, y) <- readIORef pos
      (_, rows) <- readIORef theDims
      let virtualRows = rows - barLines
          scrollLinesNeeded = (y - virtualRows + 1) `max` 0
      log ("scrollLinesNeeded: " ++ show scrollLinesNeeded ++ "\n")
      when (scrollLinesNeeded > 0) $ do
        hPut
          stdout
          ( C8.pack
              ( "\ESC["
                  ++ show (rows - 1 + 1)
                  ++ ";1H"
                  ++ replicate scrollLinesNeeded '\n'
                  ++ "\ESC["
                  ++ show (y - scrollLinesNeeded + 1)
                  ++ ";"
                  ++ show (x + 1)
                  ++ "H"
              )
          )
        modifyIORef' pos (second (subtract scrollLinesNeeded))

    -- Like CURSOR_WRAPNEXT from st
    cursorWrapnext <- newIORef False

    let handlePtyF (bs, updateCursor) = do
          (markBarDirty, isBarDirty) <- do
            barDirty <- newIORef False
            pure (writeIORef barDirty True, readIORef barDirty)

          inWrapnext <- readIORef cursorWrapnext
          oldPos <- readIORef pos
          dims <- readIORef theDims

          (nextWrapnext, newPos, dirty1) <- updateCursor inWrapnext dims oldPos

          writeIORef cursorWrapnext nextWrapnext
          writeIORef pos newPos

          scrollIfNeeded inWrapnext oldPos markBarDirty bs
          hPut stdout bs

          dirty2 <- isBarDirty
          when (dirty1 || dirty2) (drawBar =<< readIORef pos)

    forever $ do
      readEither >>= \case
        WinchIn -> do
          dims@(cols, rows) <- Pty.ptyDimensions stdInPty
          writeIORef theDims dims
          Pty.resizePty pty (cols, rows - barLines)
          getPid childHandle >>= \case
            -- I guess this only happens if there is a race condition
            -- between SIGWINCH and termination of the child process
            Nothing -> pure ()
            Just childPid -> signalProcess sigWINCH childPid
          log ("WinchIn " ++ pid ++ ": " ++ show dims ++ "\n")
        StdIn bs -> do
          Pty.writePty pty bs
          log ("StdIn " ++ pid ++ ": " ++ show bs ++ "\n")
        PtyIn move -> do
          handlePtyF move

  exitWith =<< takeMVar exit

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

forkLoopToMVar :: (forall r. (a -> IO ()) -> IO r) -> IO (MVar a)
forkLoopToMVar loop = do
  v <- newEmptyMVar
  _ <- forkIO (loop (putMVar v))
  pure v

myPtyIn :: (String -> IO ()) -> String -> Pty.Pty -> IO (MVar PtyParse)
myPtyIn log pid pty = forkLoopToMVar (myLoop log pid pty)

myLoop :: (String -> IO ()) -> String -> Pty.Pty -> (PtyParse -> IO ()) -> IO a
myLoop log pid pty yield = do
  unhandledPty <- newIORef (Left mempty)

  forever $ do
    readIORef unhandledPty >>= \case
      Left neededmore -> do
        readPty pty >>= \case
          Left {} ->
            -- I don't know what we should do with PtyControlCodes
            pure ()
          Right bs -> do
            log ("PtyIn " ++ pid ++ ": " ++ show bs ++ "\n")
            writeIORef unhandledPty (Right (neededmore <> bs))
      Right bsIn -> do
        withPtyIn'' log bsIn >>= \case
          Nothing -> do
            writeIORef unhandledPty (Left bsIn)
          Just ((bs, theLeftovers), f) -> do
            yield (bs, f)
            writeIORef unhandledPty (Right theLeftovers)

withPtyIn'' ::
  (String -> IO ()) ->
  ByteString ->
  IO (Maybe ((ByteString, ByteString), UpdateCursor))
withPtyIn'' log bsIn =
  parse log (C8.unpack bsIn) >>= \case
    Nothing -> pure Nothing
    Just (seen, f) -> pure (Just (C8.splitAt seen bsIn, f))

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
