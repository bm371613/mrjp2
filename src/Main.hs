import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Check
import Emit
import Parser.AbsLatte
import Parser.LexLatte
import Parser.ParLatte
import Parser.ErrM

err :: String -> IO a
err msg = do
    hPutStrLn stderr "ERROR"
    hPutStrLn stderr msg
    exitFailure

main :: IO ()
main = do
    args <- getArgs
    unless (not $ null args) $ err "Missing inputFileName argument."
    let inputFileName = head args
    input <- readFile inputFileName
    program <- case pProgram $ myLexer input of
        Bad e -> err e
        Ok tree -> return tree
    globals <- case checkProgramReturningGlobals program of
        Left e -> err e
        Right globals -> return globals
    emitProgramGivenGlobals program globals
    hPutStrLn stderr "OK"
