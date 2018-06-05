--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

module Main where

import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error

import Text.Parsec hiding (try)
import Text.Parsec.String
import Solidity
import CFG
import StaticAnalysis
import StaticAnalysis.Residuals
import EA.EA
import Parseable
import DEA

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
    ifNot (length arguments == 3)
      ("Usage: <input solidity file> <input dea file> <output dea file>")
    let [inSCFile, inDEAFile, outFile] = arguments
    inputText <- readFile inSCFile
      `failWith` ("Cannot read Solidity file <"++inSCFile++">")
    solidityCode <- parseIO inSCFile inputText
    inputDEA <- readFile inDEAFile
      `failWith` ("Cannot read DEA file <"++inDEAFile++">")
    dea <- parseIO inDEAFile inputDEA
    let outDEA = (performResidualAnalysisOnContractSpecification dea (fromCFG (contractCFG solidityCode) dea))
    writeFile outFile (display outDEA)
      `failWith` ("Cannot write to DEA file <"++outFile++">")
    putStrLn ("Created residual DEA file <"++outFile++">")
  `catch` (putStrLn . ioeGetErrorString)