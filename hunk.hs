{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

import Text.Parsec (string, many, satisfy, newline, parse, eof,
                    (<|>), Stream, ParsecT)
import Data.Algorithm.Diff (PolyDiff(Both, First, Second), getDiff)
import Control.Monad.Trans.Writer (tell, execWriter, Writer)
import qualified System.Exit
import qualified System.Environment

sepHead :: String
sepHead  = "<<<<<<< HEAD"

sepEq :: String
sepEq    = "======="

sepPatch :: String
sepPatch = ">>>>>>>"

eol :: Stream s m Char => ParsecT s u m ()
eol = string "\n" *> pure ()

parseHead :: Stream s m Char => ParsecT s u m ()
parseHead = do
  string sepHead
  eol

parseMerged :: Stream s m Char => ParsecT s u m ()
parseMerged = do
  string "|||||||"
  string " "
  string "merged common ancestors"
  eol

parseEquals :: Stream s m Char => ParsecT s u m ()
parseEquals = do
  string sepEq
  eol

parsePatch :: Stream s m Char => ParsecT s u m String
parsePatch = do
  string sepPatch
  string " "
  parseLine

parseLine :: Stream s m Char => ParsecT s u m String
parseLine = many (satisfy (/= '\n')) <* newline

data Hunk = Hunk {
    hunkTop :: [String]
  , hunkMid :: [String]
  , hunkBot :: [String]
  , patchName :: String
  }
  deriving Show

data FileElement = FileHunk Hunk
                 | FileLine String
                 deriving Show

parseBottomHunk :: Stream s m Char => ParsecT s u m ([String], String)
parseBottomHunk = do { p <- parsePatch
                     ; pure ([], p)
                     }
              <|> do { b <- parseLine
                     ; (bs, p) <- parseBottomHunk
                     ; pure (b:bs, p)
                     }

parseMiddleHunk :: Stream s m Char => ParsecT s u m ([String], [String], String)
parseMiddleHunk = do { parseEquals
                     ; (bs, p) <- parseBottomHunk
                     ; pure ([], bs, p)
                     }
              <|> do { m <- parseLine
                     ; (ms, bs, p) <- parseMiddleHunk
                     ; pure (m:ms, bs, p)
                     }

parseTopHunk :: Stream s m Char
             => ParsecT s u m ([String], [String], [String], String)
parseTopHunk = do { parseMerged
                  ; (ms, bs, p) <- parseMiddleHunk
                  ; pure ([], ms, bs, p)
                  }
           <|> do { t <- parseLine
                  ; (ts, ms, bs, p) <- parseTopHunk
                  ; pure (t:ts, ms, bs, p)
                  }

parseHunk :: Stream s m Char => ParsecT s u m FileElement
parseHunk = do { parseHead
               ; (ts, ms, bs, p) <- parseTopHunk
               ; pure (FileHunk (Hunk { hunkTop = ts
                                      , hunkMid = ms
                                      , hunkBot = bs
                                      , patchName = p
                                      }))
               }

parseHunkLine :: Stream s m Char => ParsecT s u m FileElement
parseHunkLine = FileLine <$> parseLine

parseDiff3File :: Stream s m Char => ParsecT s u m [FileElement]
parseDiff3File = do { -- It's really important that parseHunk is first
                      -- since it is more specific
                    ; h <- parseHunk <|> parseHunkLine
                    ; hs <- parseDiff3File
                    ; pure (h:hs)
                    }
             <|> (eof *> pure [])

showFileElement :: FileElement -> Iter String
showFileElement hunk = case hunk of
  FileLine hl -> yield hl
  FileHunk h -> do
    yield sepHead
    eachIn (hunkTop h)
    yield sepEq
    for (eachIn (getDiff (hunkMid h) (hunkBot h))) $ \diff -> do
      let diffLine = case diff of
            Both a _a -> ' ':a
            First a   -> '-':a
            Second a  -> '+':a
      yield diffLine
    yield (sepPatch ++ " " ++ patchName h)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  case args of
    [filename] -> mainWithFilename filename
    _ -> System.Exit.die "Expected exactly one argument, a filename"

mainWithFilename :: FilePath -> IO ()
mainWithFilename filename = do
  filecontents <- readFile filename

  hunks <- case parse parseDiff3File filename filecontents of
    Left errorMessage -> System.Exit.die (show errorMessage)
    Right hunks -> pure hunks

  let hunkLines = list (for (eachIn hunks) showFileElement)

  writeFile filename (unlines hunkLines)


-- Simple iterators
type Iter a = Writer [a] ()

yield :: a -> Iter a
yield = tell . pure

for :: Iter a -> (a -> Iter b) -> Iter b
for iter f = mapM_ f (execWriter iter)

eachIn :: [a] -> Iter a
eachIn = mapM_ yield

list :: Iter a -> [a]
list = execWriter
