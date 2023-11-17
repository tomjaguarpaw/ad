import Data.ByteString
import System.IO
import Data.Function (fix)
import System.Process
import System.Posix.IO
import System.Posix.Terminal
import Control.Concurrent

openPty = do
  (s, m) <- openPseudoTerminal
  (,) <$> fdToHandle m <*> fdToHandle s

main = do
  Prelude.putStrLn "Starting ..."
  hSetEcho stdin False
  hSetBuffering stdin NoBuffering

  (si, mi) <- openPty
  (so, mo) <- openPty
  (se, me) <- openPty

  hSetBuffering mi NoBuffering

  -- This won't work if I change "cat" to "dash"
  _ <-
    createProcess (proc "cat" []) { std_in = UseHandle si,
                                     std_out = UseHandle so,
                                     std_err = UseHandle se
                                   }

  forkIO $ fix $ \again -> do
    bs <- hGet me 1
    hPut stderr bs
    hFlush stderr
    again

  forkIO $ fix $ \again -> do
    bs <- hGet mo 1
    hPut stdout bs
    hFlush stdout
    again

  fix $ \again -> do
    bs <- hGet stdin 1
    hPut mi bs
    hFlush mi
    again
