module StaticAnalysis where

import qualified DEA.DEA as DEA (State, Transition)
import qualified CFG.CFG (State, Transition)
import qualified StaticAnalysis.Residuals 
import qualified StaticAnalysis.PartialEvaluator 
import qualified StaticAnalysis.SCSemantics 

import EA.EA as EA
import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error

import Text.Parsec hiding (try)
import Text.Parsec.String
import Solidity
import CFG

type Filename = String

failWith :: IO a -> String -> IO a
io `failWith` e = io `catch` (const $ (fail e) :: IOError -> IO a)

ifNot :: Bool -> String -> IO ()
ifNot c e = if c then return () else fail e

parseIO :: Parseable a => Filename -> String -> IO a
parseIO filename = either (fail . (parseError ++) . show) return . parse parser ""
  where
    parseError = "Error during parsing of <"++filename++">\n"
    
main =
  do
    arguments <- getArgs
    ifNot (length arguments == 2)
      ("Usage: <input solidity file> <output solidity file>")
    let [inFile, outFile] = arguments
    inputText <- readFile inFile
      `failWith` ("Cannot read Solidity file <"++inFile++">")
    solidityCode <- parseIO inFile inputText
    let outCode = show (StaticAnalysis.SCSemantics.codeToSemantics solidityCode)
    writeFile outFile (outCode)
      `failWith` ("Cannot write to Solidity file <"++outFile++">")
    putStrLn ("Created contract-flow graph file <"++outFile++">")
  `catch` (putStrLn . ioeGetErrorString)