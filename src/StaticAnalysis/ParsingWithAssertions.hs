{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module StaticAnalysis.ParsingWithAssertions (module Parseable) where

import Control.Monad
import Text.Parsec hiding (State, label)
import Text.Parsec.String
import Text.Parsec.Number
import Data.Char hiding (DecimalNumber)
import Data.List
import Parseable

import Solidity.Solidity
import Solidity.Parsing
import CFG.Parsing
import DEA.Parsing
import CFG.CFG as CFG
import StaticAnalysis.CallGraph
import StaticAnalysis.SMTInstrumentation
import StaticAnalysis.ComplianceCheckingWithAssertions

import StaticAnalysis.ICFG

--Failure-safe choice
(<||>) :: Parser a -> Parser a -> Parser a
p <||> q =  try p <|> q


instance Parseable IEvent where
    parser =     do string "epsilon"
                    return Epsilon
            <||> do deaEvent <- parser
                    return (DEAEvent deaEvent)
    display (DEAEvent deaEvent) = (display deaEvent)
    display (Epsilon) = "epsilon"


instance Parseable ITransition where
    parser = do src <- parser
                spaces
                string "->"
                dst <- parser
                spaces
                char '['
                spaces
                string "label"
                spaces
                char '='
                spaces
                char '"'
                cond <- parser
                spaces
                string ">>"
                spaces
                event <- parser
                char '"'
                return (ITransition (src) (dst) (cond) (event))
    display (ITransition src dst cond event) = (display src) ++ " -> " ++ (display dst) ++ " [label = \"" ++ (display cond) ++ " >> " ++ (display event) ++ "\"];\n"

instance Parseable IFunctionCFG where
    parser = do string "digraph"
                spaces
                char '"'
                spaces
                signat <- parser
                char '"'
                spaces
                char '{'
                spaces
                string "initial"
                spaces
                string "->"
                spaces
                initialState <- parser
                spaces
                char ';'
                spaces
                endStates <- many (parser <* spaces <* string "->" <* spaces <* string "end" <* spaces <* char ';')
                transitionList <- many parser
                spaces
--                try string "labelloc=\"t\";"
--                string "label=\""
--                spaces
--                signat <- parser
--                spaces
--                string "\";"
--                spaces
                char '}'
                eof
                return IFunctionCFG{isignature = signat, itransitions = transitionList, istates = statesFromTransitions transitionList [], iinitial = initialState, iend = endStates}

    display cfg = "digraph \"" ++ display (isignature cfg) ++ "\"{\n" ++
                    foldr (++) "" (map display (itransitions cfg)) ++
                    foldr (++) "" (nub [display (ExpressionState label expr) ++ "[style=filled, color=gray]" ++ ";\n" | ITransition (ExpressionState label expr) _ _ _ <- (itransitions cfg)]) ++
                    foldr (++) "" (nub [display (ExpressionState label expr) ++ "[style=filled, color=gray]" ++ ";\n" | ITransition _ (ExpressionState label expr) _ _ <- (itransitions cfg)]) ++
                    foldr (++) "" (nub [display (FunctionCallState label expr) ++ "[style=filled, color=lightblue]" ++ ";\n" | ITransition _ (FunctionCallState label expr) _ _ <- (itransitions cfg), isOutsideFunctionCall expr]) ++
                    foldr (++) "" (nub [display (s) ++ "[style=filled, color=lightgreen]" ++ ";\n" | s <- (iend cfg)])
                    ++ "\n}\n"

isOutsideFunctionCall :: CFG.FunctionCall -> Bool
isOutsideFunctionCall (OutsideFunctionCall _ _ _) = True
isOutsideFunctionCall _ = False

instance Parseable ICFG where
    parser = do cfgList <- many parser
                return (ICFG cfgList)
    display (ICFG (cs)) = foldr (++) "" [display c | c <- cs]

statesFromTransitions :: [ITransition] -> [CFG.State] -> [CFG.State]
statesFromTransitions [] states = states
statesFromTransitions ((ITransition src dst _ _):ts) states =
                                let newStates = statesFromTransitions ts states
                                    withSource = if(elem src states)
                                                    then newStates
                                                    else newStates ++ [src]
                                    withDest = if(elem dst states)
                                                    then withSource
                                                    else withSource ++ [dst]
                                    in withDest



instance Parseable CallGraph where
    display (CallGraph must may) = "digraph {\n"
                    ++ foldr (++) "" ["\"" ++ (display (signature func)) ++ "\" -> \"" ++ (display (signature funcc)) ++ "\";\n"| (func, funcc) <- must]
                    ++ foldr (++) "" ["\"" ++ (display (signature funcc)) ++ "\" -> \"" ++ (display (signature funcc)) ++ "\" [style=dashed];\n"| (func, funcc) <- may]
                    ++ "\n}"

instance Parseable ICallGraph where
    display (ICallGraph must may) = "digraph {\n"
                    ++ foldr (++) "" ["\"" ++ (display (isignature func)) ++ "\" -> \"" ++ (display (isignature funcc)) ++ "\";\n"| (func, funcc) <- must]
                    ++ foldr (++) "" ["\"" ++ (display (isignature func)) ++ "\" -> \"" ++ (display (isignature funcc)) ++ "\" [style=dashed];\n"| (func, funcc) <- may]
                    ++ "\n}"


instance Parseable Config where
    display (s,q, ([],[])) = "\"" ++ (stripChars "\"" ("(" ++ (display s) ++ ", " ++ (display q) ++ ", " ++ "(assert true)" ++ ")")) ++ "\""
    display (s,q, (as,_)) = "\"" ++ (stripChars "\"" ("(" ++ (display s) ++ ", " ++ (display q) ++ ", " ++ (foldr (++) "" [(display z) | z <- as]) ++ ")")) ++ "\""


--from https://www.rosettacode.org/wiki/Strip_a_set_of_characters_from_a_string#Haskell
stripChars :: String -> String -> String
stripChars = filter . flip notElem

instance Parseable EventSeq where
    display [] = "<>"
    display (e:es) = "<" ++ (display e) ++ (foldr (++) "" [", " ++ display e | e <- es]) ++ ">"

instance Parseable SyncTransition where
    display (c, es, cc) = (display c) ++ " -> " ++ (display cc) ++ " [label = \"" ++ (display es) ++ "\"];\n"


instance Parseable SyncComp where
    display (SyncComp first configs evols transClosure) =
      "digraph \"syncComp\"{\n" ++
                    foldr (++) "" (map display evols)
                     ++  foldr (++) "" (nub [display (s,d,abs) ++ "[style=filled, color=lightblue]" ++ ";\n" | (s,d,abs) <- configs, s == ReturnState])
                     ++  foldr (++) "" (nub [display (s,d,abs) ++ "[style=filled, color=lightblue]" ++ ";\n" | (s,d,abs) <- configs, s == RevertState])
                     ++  foldr (++) "" (nub [display (s,d,abs) ++ "[style=filled, color=lightblue]" ++ ";\n" | (s,d,abs) <- configs, s == ThrowState])
                  ++ "\n}"
