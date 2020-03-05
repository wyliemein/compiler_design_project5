{-# LANGUAGE ScopedTypeVariables #-}

import Control.Exception  (catch)
import System.Environment (getArgs)
import System.IO          (stdout, stderr, hPutStrLn)
import System.Exit
import Language.Egg.Types
import Language.Egg.Parser
import Language.Egg.Normalizer

--------------------------------------------------------------------------------
main :: IO ()
main = runCompiler `catch` esHandle

esHandle :: [UserError] -> IO ()
esHandle es = renderErrors es >>= hPutStrLn stderr >> exitFailure

runCompiler :: IO ()
runCompiler = do
  f <- getSrcFile
  s <- readFile f
  let out = (pprint . anormal . parse f) s
  hPutStrLn stdout out
  exitSuccess

getSrcFile :: IO Text
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"
