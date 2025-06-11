{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Parse where

import Control.Arrow (Arrow (second), first)
import Control.Monad (forever)
import Data.Bits ((.&.))
import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as C8
import Data.ByteString.Internal (c2w)
import Data.Char (isAlpha, isAscii)
import Data.IORef (newIORef, readIORef, writeIORef)
import Exception (earlyReturn)
import Text.Read (readMaybe)
import Prelude hiding (log)

type PtyParse = (ByteString, UpdateCursor)

newtype UpdateCursor
  = MkUpdateCursor
      ( forall m.
        (Monad m) =>
        (String -> m ()) ->
        Bool ->
        (Int, Int) ->
        (Int, Int) ->
        m (Bool, (Int, Int), Bool)
      )

-- FIXME: parsing should not be coupled to barLines
barLines :: Int
barLines = 3

handleForever :: IO a -> (a -> IO ()) -> IO r
handleForever act yield = forever (yield =<< act)

ptyParses ::
  (String -> IO ()) ->
  IO ByteString ->
  (PtyParse -> IO ()) ->
  IO a
ptyParses log nextByteString yield = do
  unhandledPty <- newIORef mempty

  handleForever nextByteString $ \bs -> do
    log ("PtyIn: " ++ show bs ++ "\n")

    neededMore <- readIORef unhandledPty

    remainder <- parseUntilNeedMore log (neededMore <> bs) $ \ptyParse -> do
      yield ptyParse

    writeIORef unhandledPty remainder

parseUntilNeedMore ::
  (String -> IO ()) ->
  ByteString ->
  (PtyParse -> IO ()) ->
  IO ByteString
parseUntilNeedMore log bsInStart yield = do
  unhandledPty <- newIORef bsInStart

  earlyReturn $ \early -> forever $ do
    bsIn <- readIORef unhandledPty
    parseBS log bsIn >>= \case
      Nothing -> early bsIn
      Just (p, theLeftovers) -> do
        yield p
        writeIORef unhandledPty theLeftovers

parseBS ::
  (String -> IO ()) ->
  ByteString ->
  IO (Maybe ((ByteString, UpdateCursor), ByteString))
parseBS log bsIn = do
  mResult <- parse log (C8.unpack bsIn)
  pure $ do
    (seen, f) <- mResult
    let (bs, theLeftovers) = C8.splitAt seen bsIn
    Just ((bs, f), theLeftovers)

parse ::
  (Monad m) => (String -> m ()) -> String -> m (Maybe (Int, UpdateCursor))
parse log = \case
  [] ->
    needMore
  -- This is "shift in", equivalent to '\017', and part of sgr0.
  --
  -- https://en.wikipedia.org/wiki/Shift_Out_and_Shift_In_characters
  '\SI' : _ -> do
    noLocationChangeConsuming 1
  '\r' : _ -> do
    pure
      ( Just
          ( 1,
            MkUpdateCursor $ \_ _ _ thePos ->
              pure (False, first (const 0) thePos, False)
          )
      )
  '\n' : _ -> do
    pure
      ( Just
          ( 1,
            MkUpdateCursor $ \_ _ (_, rows) thePos ->
              pure
                ( False,
                  second (\y -> (y + 1) `min` (rows - barLines)) thePos,
                  False
                )
          )
      )
  '\a' : _ ->
    noLocationChangeConsuming 1
  '\b' : _ -> do
    pure
      ( Just
          ( 1,
            MkUpdateCursor $
              \_ _ (cols, rows) thePos ->
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
            MkUpdateCursor $
              \_ _ _ thePos ->
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
            let x = numberOr1IfMissing csi - 1
            pure (first (const x), False)
          'd' -> do
            let y = read csi - 1
            pure (second (const y), False)
          _ -> pure (id, False)
        pure
          ( Just
              ( 2 + length csi + 1,
                MkUpdateCursor $
                  \_ inWrapnext _ thePos ->
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
      pure
        ( Just
            ( n,
              MkUpdateCursor $ \_ inWrapnext _ thePos ->
                pure (inWrapnext, thePos, False)
            )
        )

    singleDisplayableCharacter n =
      pure $
        Just
          ( n,
            MkUpdateCursor $
              \log' inWrapnext (cols, _) thePos -> do
                let (x, y) = thePos

                (newPos, nextWrapnext) <-
                  case inWrapnext of
                    True -> pure ((1, y + 1), False)
                    False -> case x `compare` (cols - 1) of
                      GT -> do
                        log'
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

-- https://github.com/martanne/dvtm/blob/7bcf43f8dbd5c4a67ec573a1248114caa75fa3c2/vt.c#L619-L624
isValidCsiEnder :: Char -> Bool
isValidCsiEnder c =
  (isAscii c && isAlpha c) || (c == '@') || (c == '`')
