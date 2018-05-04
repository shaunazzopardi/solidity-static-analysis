-- Copyright 2017 Gordon J. Pace and Joshua Ellul
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

module DEA.ParsingToSmartContract where

import Data.List
import DEA.Parsing
import Solidity
import Solidity.Parsing
import DEA.DEA as DEA
import Data.Char as Char
import Text.Parsec hiding (try)
import Text.Parsec.String

transitionToCheck :: DEA -> Transition -> String
transitionToCheck dea (Transition _src _dst (GCL event Nothing Nothing)) = "if(_" ++ (daeName dea) ++ "State == " ++ "\"" ++ display _src ++ "\"" ++ ") _" ++ (daeName dea) ++ "State = " ++ display _dst ++ ";"
transitionToCheck dea (Transition _src _dst (GCL event (Just cond) Nothing)) = unlines $ 
                                                                              ["if(_" ++ (daeName dea) ++ "State == " ++ "\"" ++ display _src ++ "\"" 
                                                                                 ++ (if (display cond == "") then "" else ("\n&& " ++ display cond))
                                                                                 ++ (if (eventCondition event == "") then "" else ("\n&& " ++ eventCondition event))
                                                                                ,"){"
                                                                                , "_" ++ (daeName dea) ++ "State = " ++ "\"" ++ display _dst ++ "\";"
                                                                                , "}"]
transitionToCheck dea (Transition _src _dst (GCL event Nothing (Just action))) = unlines $ 
                                                                              ["if(_" ++ (daeName dea) ++ "State == " ++ "\"" ++ display _src ++ "\""
                                                                                 ++ (if (eventCondition event == "") then "" else ("\n&& " ++ eventCondition event))
                                                                                ,"){"
                                                                                , (display action)
                                                                                , "_" ++ (daeName dea) ++ "State = " ++ "\"" ++ display _dst ++ "\";"
                                                                                , "}"]
transitionToCheck dea (Transition _src _dst (GCL event (Just cond) (Just action))) = unlines $ 
                                                                              ["if(_" ++ (daeName dea) ++ "State == \"" ++ display _src ++ "\";"
                                                                                 ++ (if (display cond == "") then "" else ("\n&& " ++ display cond))
                                                                                 ++ (if (eventCondition event == "") then "" else ("\n&& " ++ eventCondition event))
                                                                                , "){"
                                                                                , display action
                                                                                , "_" ++ (daeName dea) ++ "State = \"" ++ display _dst ++ "\";"
                                                                                , "}"]

upperCaseFirstChar :: Identifier -> String
upperCaseFirstChar (Identifier []) = []
upperCaseFirstChar (Identifier (a:rest)) = ((Char.toUpper a):rest)

eventMethodLabel :: Event -> String
eventMethodLabel (UponEntry functionCall) = "uponEntry" ++ (upperCaseFirstChar (functionName functionCall))
eventMethodLabel (UponExit functionCall) = "uponExit" ++ (upperCaseFirstChar (functionName functionCall))
eventMethodLabel (VariableAssignment variableName _) = "changeIn" ++ (upperCaseFirstChar (variableName))

eventCondition :: Event -> String
eventCondition (VariableAssignment variableName (Just expr)) = display expr
eventCondition _ = ""



--TODO these need to be typed by comparing them to monitored smart contract
parameterListToString :: Maybe UntypedParameterList -> String
parameterListToString (Nothing) = ""
parameterListToString (Just (UntypedParameterList [])) = ""
parameterListToString (Just (UntypedParameterList ((Identifier id):[]))) = id
parameterListToString (Just (UntypedParameterList ((Identifier id):rest))) = id ++ ", " ++ (parameterListToString (Just (UntypedParameterList rest)))


variableListAssociatedWithEvent :: Event -> String
variableListAssociatedWithEvent (UponEntry functionCall) = parameterListToString (parametersPassed functionCall)
variableListAssociatedWithEvent (UponExit functionCall) = parameterListToString (parametersPassed functionCall)
variableListAssociatedWithEvent (VariableAssignment variableName _) = "pre" ++ (upperCaseFirstChar (variableName)) ++ ", post" ++ (upperCaseFirstChar (variableName))



getTransitionsOfAnEvent :: [Transition] -> Event -> [Transition]
getTransitionsOfAnEvent [] e = []
getTransitionsOfAnEvent (t:ts) e = let rest = (getTransitionsOfAnEvent ts e)
                                    in if (event (DEA.label t)) == e
                                        then (t : rest)
                                        else rest

createEventCheck :: DEA -> Event -> String
createEventCheck dea e = let trans = getTransitionsOfAnEvent (transitions dea) e
                             in unlines $
                                ["function " ++ eventMethodLabel e ++ "(" ++ variableListAssociatedWithEvent e ++ "){"
                                  , unlines $ (map (transitionToCheck dea) (trans))
                                  , "}"]



toMonitoringLogic :: DEA -> String
toMonitoringLogic dea = unlines $ 
                    ["string _" ++ (daeName dea) ++ "State = " ++ "\"" ++ unState (initialState dea) ++ "\"" ++ ";"
                     , unlines $ (map (createEventCheck dea) (getEventsFromDEA dea))
                     ];

toSmartContract :: ContractSpecification -> String
toSmartContract contractSpecification = let scName = upperCaseFirstChar (contractName contractSpecification)
                                          in unlines $
                                                ["contract " ++ scName ++ "{"
                                                , unlines $ (map (display) (declarations contractSpecification))
                                                , "function " ++ scName ++ "(){"
                                                ,  display (initialisation contractSpecification)
                                                , "}"
                                                , unlines $ (map (toMonitoringLogic) (daes contractSpecification)) 
                                                ,"}"]

toSmartContractWithError :: Either ParseError ContractSpecification -> String
toSmartContractWithError (Left error) = "error"
toSmartContractWithError (Right spec ) = (toSmartContract spec)