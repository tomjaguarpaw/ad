import Data.ByteString
import System.IO
import Data.Function (fix)
import System.Process
import Control.Concurrent

main = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False

  (Just bin, Just bout, Nothing, _) <-
    createProcess (proc "cat" []) { std_in = CreatePipe, std_out = CreatePipe }

  forkIO $ fix $ \again -> do
    bs <- hGet stdin 1
    hPut bin bs
    hFlush bin
    again

  fix $ \again -> do
    bs <- hGet bout 1
    hPut stdout bs
    hFlush bin
    again
