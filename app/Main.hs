{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import Prelude hiding (read)

import Network.Socket
import Network.Socket.ByteString
import Data.Function (fix)
import System.Posix.IO.Select
import System.Posix.IO.Select.Types (Timeout (Never))
import System.Posix.Types (Fd(Fd))
import qualified Data.ByteString.Char8 as C
import Control.Concurrent (forkIO, threadDelay, threadWaitRead)


-- See https://stackoverflow.com/questions/29593116/simple-unix-domain-sockets-server
main :: IO ()
main = do
       read <- socket AF_UNIX Stream 0
       bind read (SockAddrUnix "/tmp/.X11-unix/X111")
       listen read maxListenQueue

       _FIXME_never_get_here <- fix (\acceptAgain -> do
         print "Waiting for new connection"
         (conn, _) <- accept read
         print "Got connection"
         _ <- forkIO $ do
           write <- socket AF_UNIX Stream 0
           connect write (SockAddrUnix "/tmp/.X11-unix/X1000")

           print "Opened new socket for writing"

           connFd <- Fd <$> unsafeFdSocket conn
           writeFd <- Fd <$> unsafeFdSocket write

           print connFd
           print writeFd

           _ <- forkIO $ fix (\readAgain -> do
             threadWaitRead connFd
             msg <- recv conn 1024
             if C.null msg then do
               close conn
               close write
             else do
               n <- send write msg
               print n
               readAgain)

           _ <- forkIO $ fix (\readAgain -> do
             threadWaitRead writeFd
             msg <- recv write 1024
             if C.null msg then do
               close conn
               close write
             else do
               n <- send conn msg
               print n
               readAgain)

           -- FIXME: need to close file descriptors
           pure ()

         acceptAgain)

       close read
