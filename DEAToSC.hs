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
import DEA.ParsingToSmartContract
import DEA.Parsing

type Filename = String

failWith :: IO a -> String -> IO a
io `failWith` e = io `catch` (const $ (fail e) :: IOError -> IO a)

ifNot :: Bool -> String -> IO ()
ifNot c e = if c then return () else fail e

parseIO :: Parseable a => Filename -> String -> IO a
parseIO filename = either (fail . (parseError ++) . show) return . parse parser ""
  where
    parseError = "Error during parsing of <"++filename++">\n"
    

parseDEA :: DEA -> DEA
parseDEA dea = dea

main =
  do
    arguments <- getArgs
    ifNot (length arguments == 2)
      ("Usage: <input dea file> <output solidity file>")
    let [inFile, outFile] = arguments
    inputText <- readFile inFile
      `failWith` ("Cannot read DEA file <"++inFile++">")
    contractSpecCode <- parseIO inFile inputText
    let outCode = toSmartContract contractSpecCode
    writeFile outFile (outCode)
      `failWith` ("Cannot write to Solidity file <"++outFile++">")
    putStrLn ("Created smart contract monitor rep <"++outFile++">")
  `catch` (putStrLn . ioeGetErrorString)