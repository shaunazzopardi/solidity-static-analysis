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

import System.Process
import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error

import Debug.Trace
import Data.List
import Text.Parsec hiding (try)
import Text.Parsec.String
import Text.Parsec.Token
import Solidity
import CFA
import SMT
import Parseable
import DEA
import ResidualAnalysis
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


--TODO need to add var declarations of DEA monitor
--TODO need to deal with the full DEA script not just the monitor part
--TODO typestate

main =
  do  arguments <- getArgs
      ifNot (length arguments == 6)
        ("Usage: <input solidity file> <input dea file> <output cfa files> <output acfa files> <output ams files> <output residual dea file>")
      let [inSCFile, inDEAFile, outFile, outACFAFile, outAMSFile, outDEAFile] = arguments
      inputText <- readFile inSCFile
        `failWith` ("Cannot read Solidity file <"++inSCFile++">")
      solidityCode <- parseIO inSCFile inputText
      inputDEAText <- readFile inDEAFile
        `failWith` ("Cannot read DEA file <"++inDEAFile++">")
      dea <- parseIO inDEAFile inputDEAText
      let outCFAs = (instrumentSC solidityCode dea)
      amss <- mapM (onlineConstructControlFlowABSFromCFA dea) outCFAs
      let cfaText = (foldr (++) "" (map display outCFAs))
          acfas = map (\cfa -> abstract cfa (getEventsFromDEA dea)) outCFAs
          acfaText = (foldr (++) "" (map display (acfas)))
          amssText = (foldr (++) "" (map display amss))
          residualDEA = reachibilityReduction $ bothResiduals amss dea
      writeFile outFile cfaText
        `failWith` ("Cannot write to CFA file <"++outFile++">")
      putStrLn ("Created residual CFA file <"++outFile++">")
      writeFile outACFAFile acfaText
        `failWith` ("Cannot write to ACFA file <"++outACFAFile++">")
      putStrLn ("Created residual ACFA file <"++outACFAFile++">")
      writeFile outAMSFile amssText
        `failWith` ("Cannot write to AMS file <"++outAMSFile++">")
      putStrLn ("Created residual AMS file <"++outAMSFile++">")
      writeFile outDEAFile (display residualDEA)
        `failWith` ("Cannot write to residual DEA file <"++outDEAFile++">")
      putStrLn ("Created residual DEA file <"++outDEAFile++">")
    `catch` (putStrLn . ioeGetErrorString)

z3Sat :: [Z3Construct] -> IO Bool
z3Sat [] = return True
z3Sat z3constructs =
     -- Create the process
  do writeFile "temp.txt" ((foldr (++) "" (map display z3constructs)) ++ "(check-sat)")
     (_pIn, pOut, pErr, handle) <- runInteractiveCommand "z3 -smt2 temp.txt"
     -- Wait for the process to finish and store its exit code
     exitCode <- waitForProcess handle
     -- Get the standard output.
     output   <- hGetContents pOut
     return (not $ isInfixOf "unsat" output)

z3SatDisjunctive :: [[Z3Construct]] -> IO Bool
z3SatDisjunctive [] = return False
z3SatDisjunctive (z3s:z3ss) = do sat <- z3Sat z3s
                                 if sat
                                    then return True
                                    else do satt <- z3SatDisjunctive z3ss
                                            return satt


z3SatCollective :: [Z3Construct] -> [AMSTransition [[Z3Construct]]] -> [AMSTransition [[Z3Construct]]] -> IO [AMSTransition [[Z3Construct]]]
z3SatCollective context _ [] = return []
z3SatCollective context allAmsts ((amst):amsts) = do let proofOblig = transitionProofObligation allAmsts amst
                                                     sat <- if (proofOblig == []) then return True else z3SatDisjunctive $ [(context ++ z3) | z3 <- proofOblig]
                                                     remaining <- z3SatCollective context allAmsts amsts
                                                     if sat
                                                       then return ([amst] ++ remaining)
                                                       else return remaining

onlineConstructControlFlowABSFromCFA :: DEA -> CFA -> IO (AMS [[Z3Construct]])
onlineConstructControlFlowABSFromCFA dea cfa = do onlineConstructControlFlowABS (abstract cfa (getEventsFromDEA dea)) dea

onlineConstructControlFlowABS :: AbstractCFA -> DEA -> IO (AMS [[Z3Construct]])
onlineConstructControlFlowABS acfa dea = onlineConstructABSGeneric (initConfigsSimpleDF, simpleDF) acfa dea

onlineConstructABSGeneric :: DFLEnv [[Z3Construct]] -> AbstractCFA -> DEA -> IO (AMS [[Z3Construct]])
onlineConstructABSGeneric (initConfigs, dataFlow) acfa dea = do (amsTrans, amsStates, _) <- onlineExhaustiveSteps dataFlow acfa dea ([],[],initConfigs acfa dea)
                                                                return AMS{
                                                                          cfaLabel = CFA.name $ cfa acfa,
                                                                          deaLabel = deaName dea,
                                                                          configs = amsStates,
                                                                          evolutions = amsTrans
                                                                      }

onlineExhaustiveSteps :: DataFlowLogic [[Z3Construct]] -> AbstractCFA -> DEA -> ([AMSTransition [[Z3Construct]]], [AMSConfig [[Z3Construct]]], [AMSConfig [[Z3Construct]]]) -> IO ([AMSTransition [[Z3Construct]]], [AMSConfig [[Z3Construct]]], [AMSConfig [[Z3Construct]]])
onlineExhaustiveSteps dataFlow acfa dea (ts,done,[]) = return (ts,done,[])
onlineExhaustiveSteps dataFlow acfa dea (ts,done,left) = do let potentialTransitions = (foldr (++) [] [step dataFlow c acfa dea | c <- left])
                                                            viableTransitions <- z3SatCollective (([Z3Sort s | s <- sortDecs $ cfa acfa]) ++ ([Z3Dec v | v <- varDecs $ cfa acfa])) potentialTransitions potentialTransitions
                                                            let newTrans = ts ++ viableTransitions
                                                                newDone = done ++ left
                                                                newLeft = [c | c <- (nextConfigs viableTransitions), not $ elem c newDone]
                                                            toReturn <- (onlineExhaustiveSteps dataFlow acfa dea (nub newTrans, nub newDone, nub newLeft))
                                                            return toReturn
