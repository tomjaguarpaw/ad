-- Following up on
--
-- https://mailman.haskell.org/archives/list/haskell-cafe@haskell.org/thread/MTUTVVTFZMQ6U5JNNTD46J3WXUY2QWBY/

{- cabal:
build-depends: conduit, base, bytestring, zip, cereal, bluefin>=0.5.1.0, containers, tar-conduit, bluefin-internal
-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RecordWildCards #-}

import Bluefin.Compound hiding (Handle)
import Bluefin.Compound qualified as Bf
import Bluefin.Consume
import Bluefin.DslBuilder
import Bluefin.DslBuilderEff
import Bluefin.Eff
import Bluefin.IO
import Bluefin.Internal qualified as BI
import Bluefin.Stream
import Codec.Archive.Zip hiding (getEntrySource)
import Codec.Archive.Zip qualified as Zip
import Codec.Archive.Zip.Internal
import Conduit hiding (await, yield)
import Conduit qualified as C
import Control.Monad
import Data.ByteString (ByteString)
import Data.ByteString qualified as B
import Data.Conduit.Combinators
import Data.Conduit.List
import Data.Conduit.List qualified as CB
import Data.Conduit.Tar (FileInfo)
import Data.Conduit.Tar qualified
import Data.Conduit.Tar qualified as CTar
import Data.IORef
import Data.Map qualified as M
import Data.Map qualified as Map
import Data.Serialize.Get
import Data.Traversable (for)
import System.IO

convertZipToTar ::
  (Zip.EntrySelector -> Zip.EntryDescription -> CTar.FileInfo) ->
  FilePath ->
  IO ()
convertZipToTar fileInfoFromZipEntry_ zipPath =
  Zip.withArchive zipPath $ do
    entries <- Map.toList <$> Zip.getEntries
    files <-
      for entries $ \(selector, descr) ->
        flip fmap (getEntrySource zipPath selector) $ \src ->
          dslBuilder $ \(Pair io y) -> do
            yield y (Left $ fileInfoFromZipEntry_ selector descr)
            forEach
              (\y' -> runDslBuilder (pair io y') src)
              (yield y . Right)
    C.liftIO $ runEff_ $ \io -> do
      forEach
        ( \yout ->
            streamConsume
              (\y -> runDslBuilder (pair io y) (sequence_ files))
              (\a -> tar io a yout)
        )
        (effIO io . B.hPut System.IO.stdout)

data Product h1 h2 e = Pair (h1 e) (h2 e)
  deriving (Generic)
  deriving (Bf.Handle) via OneWayCoercibleHandle (Product h1 h2)

pair ::
  (e1 <: es, e2 <: es, BI.Handle h1, BI.Handle h2) =>
  h1 e1 ->
  h2 e2 ->
  Product h1 h2 es
pair h1 h2 = Pair (mapHandle h1) (mapHandle h2)

instance
  (e <: es, BI.Handle h1, BI.Handle h2) =>
  OneWayCoercible (Product h1 h2 e) (Product h1 h2 es)
  where
  oneWayCoercibleImpl =
    withHandle @h1 $
      withHandle @h2 $
        gOneWayCoercible

getEntrySource ::
  FilePath ->
  -- | Selector that identifies archive entry
  EntrySelector ->
  ZipArchive (DslBuilder (Product IOE (Stream ByteString)) ())
getEntrySource path s =
  flip fmap (getEntrySourceYield path s) $ \bs -> do
    dslBuilder $ \(Pair io (BI.MkCoroutine y)) -> do
      effIO io (bs (BI.unsafeUnEff . y))

tar ::
  (e1 <: es, e2 <: es, e3 <: es) =>
  IOE e1 ->
  Consume (Either FileInfo ByteString) e2 ->
  Stream ByteString e3 ->
  Eff es ()
tar io (BI.MkCoroutine a) (BI.MkCoroutine y) =
  effIO io (tarYieldAwait (BI.unsafeUnEff (a ())) (BI.unsafeUnEff . y))

sourceEntryHandle ::
  (PrimMonad m, MonadThrow m, MonadResource m) =>
  -- | Path to archive that contains the entry
  Handle ->
  -- | Information needed to extract entry of interest
  EntryDescription ->
  -- | Should we stream uncompressed data?
  Bool ->
  -- | Source of uncompressed data
  ConduitT () ByteString m ()
sourceEntryHandle h EntryDescription {..} d = do
  liftIO seek
  source .| CB.isolate (fromIntegral edCompressedSize) .| decompress
  where
    source = sourceHandle h
    seek = do
      hSeek h AbsoluteSeek (fromIntegral edOffset)
      localHeader <- B.hGet h 30
      case runGet getLocalHeaderGap localHeader of
        Left msg ->
          -- TODO make better error handling
          error msg
        Right gap -> do
          hSeek h RelativeSeek gap
          return h
    decompress =
      if d
        then decompressingPipe edCompression
        else C.awaitForever C.yield

sourceEntryHandleYield ::
  -- | Path to archive that contains the entry
  Handle ->
  -- | Information needed to extract entry of interest
  EntryDescription ->
  -- | Should we stream uncompressed data?
  Bool ->
  -- | What to do with each element
  (ByteString -> IO ()) ->
  -- | Source of uncompressed data
  IO ()
sourceEntryHandleYield h ed d y =
  runConduitRes (sourceEntryHandle h ed d .| Data.Conduit.List.mapM_ (lift . y))

getEntrySourceYield ::
  -- | Selector that identifies archive entry
  FilePath ->
  EntrySelector ->
  ZipArchive ((ByteString -> IO ()) -> IO ())
getEntrySourceYield path s = do
  mdesc <- M.lookup s <$> getEntries
  case mdesc of
    Nothing -> throwM (EntryDoesNotExist path s)
    Just desc -> pure $ \y -> do
      withFile path ReadMode $ \h -> do
        sourceEntryHandleYield h desc True y

tarYieldAwait ::
  IO (Either FileInfo ByteString) ->
  (ByteString -> IO ()) ->
  IO ()
tarYieldAwait a y = do
  runConduit $
    do
      forever (liftIO a >>= C.yield)
      .| void Data.Conduit.Tar.tar
      .| Data.Conduit.List.mapM_ y
