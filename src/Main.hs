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

main :: IO ()
main = do
    args <- getArgs
    unless (not $ null args) $ do
        hPutStrLn stderr "Missing inputFileName argument."
        exitFailure
    let inputFileName = head args
    input <- readFile inputFileName
    program <- case pProgram $ myLexer input of
        Bad e -> do
            hPutStrLn stderr e
            exitFailure
        Ok tree -> return tree
    globals <- case checkProgramReturningGlobals program of
        Left error -> do
            hPutStrLn stderr error
            exitFailure
        Right globals -> return globals
    emitProgramGivenGlobals program globals
