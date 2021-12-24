{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Prelude hiding (read)

import Network.Socket
import Network.Socket.ByteString
import Data.Function (fix)
import System.Posix.IO.Select
import System.Posix.IO.Select.Types (Timeout (Never))
import System.Posix.Types (Fd(Fd))
import qualified Data.ByteString.Char8 as C


-- See https://stackoverflow.com/questions/29593116/simple-unix-domain-sockets-server
main :: IO ()
main = withSocketsDo $ do
       read  <- socket AF_UNIX Stream 0
       bind read (SockAddrUnix "/tmp/.X11-unix/X111")
       listen read maxListenQueue

       write <- socket AF_UNIX Stream 0

       connect write (SockAddrUnix "/tmp/.X11-unix/X1000")

       (conn, _) <- accept read

       connFd <- Fd <$> unsafeFdSocket conn
       writeFd <- Fd <$> unsafeFdSocket write

       _ <- talk conn connFd write writeFd
       close conn
       close read
       close write

    where
      talk read readFd write writeFd = go
        where go = do fix (\again -> do
                              select' [readFd, writeFd] [] [] Never >>= \case
                                Nothing -> error "Got error when selecting"
                                Just (ready, _, _)
                                  | readFd `elem` ready -> do
                                      msg <- recv read 1024
                                      if C.null msg then
                                        pure ()
                                        else do
                                        n <- send write msg
                                        print n
                                        again
                                  | writeFd `elem` ready -> do
                                      msg <- recv write 1024
                                      if C.null msg then
                                        pure ()
                                        else do
                                        n' <- send read msg
                                        print n'
                                        again
                                  | otherwise -> again)
