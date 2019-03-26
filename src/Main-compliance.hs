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
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error

import Text.Parsec hiding (try)
import Text.Parsec.String
import Text.Parsec.Token
import Solidity
import CFG
import StaticAnalysis
import StaticAnalysis.Util
import StaticAnalysis.ComplianceChecking as ComplianceChecking
import StaticAnalysis.ICFG as ICFG
import StaticAnalysis.CallGraph as CallGraph
import Parseable
import DEA
import Numeric
import Numeric.Natural

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
  do  arguments <- getArgs
      ifNot (length arguments == 2)
        ("Usage: <number bigger than 0> <input solidity file> <input dea file>")
      let [inSCFile, inDEAFile] = arguments
      inputText <- readFile inSCFile
        `failWith` ("Cannot read Solidity file <"++inSCFile++">")
      solidityCode <- parseIO inSCFile inputText
      inputDEA <- readFile inDEAFile
        `failWith` ("Cannot read DEA file <"++inDEAFile++">")
      dea <- parseIO inDEAFile inputDEA
      let cg = icallgraph (ICFG.instrument (CFG.contractCFG solidityCode) dea)
      let compliant = ComplianceChecking.compliantWith (0) (ICFG.instrument (CFG.contractCFG solidityCode) dea) dea cg
      if compliant then putStrLn ("Smart contract is compliant with DEA!") else putStrLn ("Smart contract is not compliant with DEA!")
    `catch` (putStrLn . ioeGetErrorString)
