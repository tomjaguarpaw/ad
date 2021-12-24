-- | An X11 Unix sockets proxy.  Proxies X11 data between your
-- currently running display, on display number @$DISPLAY@, and
-- display number 111 (hardcoded).

{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Network.Socket
    ( close,
      connect,
      accept,
      maxListenQueue,
      listen,
      bind,
      socket,
      SockAddr(SockAddrUnix),
      SocketType(Stream),
      Family(AF_UNIX),
      Socket )
import Network.Socket.ByteString ( recv, sendAll )
import Control.Concurrent (forkIO)
import Control.Exception (try)
import Control.Monad (forever)
import System.Environment (getEnv)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

-- | The type @IO a@ means that we will never terminate normally.
-- You'll have to Ctrl-C!
main :: IO a
main = do
  ':' : serverDisplayNumber <- getEnv "DISPLAY"

  -- I hope display number 111 wasn't already running!
  let proxyPath = "/tmp/.X11-unix/X111"

  -- Establish the named socket that we will listen on
  proxyListenSocket <- do
    proxyListenSocket <- socket AF_UNIX Stream 0
    bind proxyListenSocket (SockAddrUnix proxyPath)
    listen proxyListenSocket maxListenQueue
    pure proxyListenSocket

  let mkServerSocket = do
        write <- socket AF_UNIX Stream 0
        connect write (SockAddrUnix ("/tmp/.X11-unix/X" <> serverDisplayNumber))
        pure write

  runXProxyOn proxyListenSocket mkServerSocket

-- | Whenever we receive a connection on the proxy listen socket make
-- a new connection to the server and proxy data between them until
-- one side is closed.
runXProxyOn :: Socket
            -- ^ The proxy listen socket
            -> IO Socket
            -- ^ Make a new connection to the server
            -> IO a
runXProxyOn proxyListenSocket mkServerSocket = do
  forever $ do
    -- Wait for a connection on our proxy socket
    (proxySocket, _) <- accept proxyListenSocket

    -- When we receive a connection, fork off a thread
    forkIO $ do
      -- Set up the socket on which to communicate with the server
      serverSocket <- mkServerSocket

      -- How we close our sockets when we're done
      let closeThem = do
            close proxySocket
            close serverSocket

      -- Listens for data on @from :: Socket@ and then sends it to
      -- @to_ :: Socket@
      let proxyDataFromTo from to_ = do
            untilJust $ do
              recv' from 1024 >>= \case
                SocketClosed -> pure (Just ())
                ConnectionClosed -> pure (Just ())
                Read msg -> do
                  sendAll to_ msg
                  pure Nothing

            -- If the reading side was closed then we have no more use
            -- for either socket.
            closeThem

      _ <- forkIO $ proxyDataFromTo proxySocket serverSocket
      _ <- forkIO $ proxyDataFromTo serverSocket proxySocket

      pure ()

data ReadResult = SocketClosed | ConnectionClosed | Read ByteString

-- | Block the thread until we have something to read from the socket,
-- or the socket is closed.
recv' :: Socket
      -> Int
      -- ^ Read at most this many bytes
      -> IO ReadResult
recv' socket_ n = do
  try (recv socket_ n) >>= \case
    Left e -> let _ = e :: IOError
              in pure SocketClosed
    Right msg ->
      pure (if BS.null msg then ConnectionClosed else Read msg)

untilJust :: Monad m => m (Maybe b) -> m b
untilJust m = go
  where go = m >>= \case
          Nothing -> go
          Just a -> pure a
