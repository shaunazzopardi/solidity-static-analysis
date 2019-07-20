{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module CFA.CFA where

  import Data.List
  import qualified DEA.DEA as DEA
  import DEA.Parsing
  import SMT.SMTLib2
  import Data.List
  import Control.Monad hiding (guard)
  import Text.Parsec hiding (State, label)
  import Text.Parsec.String

  import Parseable

  data Event = Epsilon | DEAEvent DEA.Event deriving (Eq, Ord, Show)
---------
  instance Parseable Event where
    display Epsilon = ""
    display (DEAEvent ev) = display ev
    {-parser = do char 'ϵ'
                return Epsilon
        <||> do ev <- parser
                return DEAEvent ev-}
---------------
---------------
--  --the Z3Asserts here represent the value associated with the parameters of the called CFA
  --data Call = Call State CFA [Z3Assert] | DelegateCall State CFA [Z3Assert] | DynamicCall State [Z3Assert]

  --TODO need to model input parameters for more precise model checking
  data Call = Call State CFAReference | DelegateCall State | DynamicCall State deriving (Eq, Ord, Show)


  data State = State String deriving (Eq, Ord, Show)
--------
  instance Parseable State where
    display (State s) = s
  {-  parser = do s <- many alphaNum
                return State s-}
-----------------
-----------------
  type CFAReference = String
-----------------
-----------------
  type Z3Condition = [Z3Construct]
  type Z3Statement = [Z3Construct]

  data Transition =
    Transition {
        src, dst :: State,
        condition :: Z3Condition,
        stmt :: Z3Statement,
        event :: Event
  } deriving (Eq, Ord, Show)
--------
  instance Parseable Transition where
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
            --    cond <- parser TODO parse condition
                spaces
                string ">>"
                spaces
            --    act <- parser TODO parse action
                spaces
                string ">>"
                spaces
                event <- parser
                char '"'
                spaces
                char ']'
                spaces
                char ';'
                spaces
                return (Transition (src) (dst) [] [] (event))
    display (Transition src dst cond act event) = (display src) ++ " -> " ++ (display dst) ++ " [label = \"" ++ (foldr (++) "" $ map display cond) ++ " >> " ++ (foldr (++) "" $ map display act) ++ " >> " ++ (display event) ++ "\"];\n"
-----------------
-----------------

  data CFA = CFA{
      name :: String,
      sortDecs :: [SortDeclaration],
      varDecs :: [VarDeclaration],
      transitions :: [Transition],
      states :: [State],
      initial :: State,
      end :: [State],
      calls :: [Call]
  } deriving (Eq, Ord, Show)
--------
  instance Parseable CFA where
    parser = do string "digraph"
                spaces
                char '"'
                spaces
                cfaName <- many alphaNum
                char '"'
                spaces
                char '{'
                spaces
                transitionList <- many parser
                spaces
                calls <- many $ do state <- many alphaNum
                                   spaces
                                   char '['
                                   spaces
                                   manyTill alphaNum (string "label=\"")
                                   spaces
                                   string "call:"
                                   spaces
                                   cfaReference <- many alphaNum
                                   spaces
                                   string "\""
                                   spaces
                                   string "];"
                                   spaces
                                   return (Call (State state) cfaReference)
                           <||> do state <- many alphaNum
                                   spaces
                                   char '['
                                   spaces
                                   manyTill alphaNum (string "label=\"")
                                   spaces
                                   string "delegate call"
                                   spaces
                                   string "\""
                                   spaces
                                   string "];"
                                   spaces
                                   return (DelegateCall (State state))
                           <||> do state <- many alphaNum
                                   spaces
                                   char '['
                                   spaces
                                   manyTill alphaNum (string "label=\"")
                                   spaces
                                   string "dynamic call"
                                   spaces
                                   string "\""
                                   spaces
                                   string "];"
                                   spaces
                                   return (DynamicCall (State state))
                endStates <- many $ do state <- many alphaNum
                                       spaces
                                       char '['
                                       spaces
                                       manyTill alphaNum (string "];")
                                       spaces
                                       return (State state)
--                try string "labelloc=\"t\";"
--                string "label=\""
--                spaces
--                signat <- parser
--                spaces
--                string "\";"
                char '}'
                spaces
                case initState transitionList of
                    Nothing -> fail "no one initial state"
                    Just s -> return CFA{name = cfaName, sortDecs = [], varDecs = [], transitions = transitionList, states = [src t | t <- transitionList] ++ [dst t | t <- transitionList], initial = s, end = endStates}

    display cfa =   "z3SortDeclarations: " ++ foldr (++) "" (map display (sortDecs cfa)) ++ "\n" ++
                    "z3VarDeclarations: " ++ foldr (++) "" (map display (varDecs cfa)) ++ "\n\n" ++
                  "digraph \"" ++ display (name cfa) ++ "\"{\n" ++
                    foldr (++) "" (map display (transitions cfa)) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"call: " ++ name ++ "\"]" ++ ";\n" | (Call s name) <- calls cfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"delegate call\"]" ++ ";\n" | (DelegateCall s) <- calls cfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"dynamic call\"]" ++ ";\n" | (DynamicCall s) <- calls cfa]) ++
                    foldr (++) "" (nub [display (s) ++ "[style=filled, color=lightgreen]" ++ ";\n" | s <- (end cfa)])
                    ++ "\n}\n"
-----------------
-----------------
  instance Parseable [CFA] where
      parser = do cfas <- many parser
                  eof
                  return cfas


  initState :: [Transition] -> Maybe State
  initState (ts) = let states = [src t | t <- ts] ++ [dst t | t <- ts]
                       initStates = states \\ [s | s <- states, t <- ts, dst t == s]
                     in case initStates of
                          (s:_) -> Just s
                          _ -> Nothing

  emptyCFA :: CFA
  emptyCFA = CFA "" [] [] [] [State "0"] (State "0") [State "0"] []
