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
  {-  parser = do src <- parser
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
                act <- parser
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
                return (Transition (src) (dst) (cond) (act) (event))-}
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
{-    parser = do sortDecss <- many parser
                varDecss <- many parser
                string "digraph"
                spaces
                char '"'
                spaces
                cfaName <- many alphaNum
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
                return CFA{name = cfaName, sortDecs = sortDecss, varDecs = varDecss, transitions = transitionList, states = statesFromTransitions transitionList [], initial = initialState, end = endStates}-}

    display cfa =   foldr (++) "" (map display (sortDecs cfa)) ++
                    foldr (++) "" (map display (varDecs cfa)) ++ "\n\n" ++
                  "digraph \"" ++ display (name cfa) ++ "\"{\n" ++
                    foldr (++) "" (map display (transitions cfa)) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"call: " ++ name ++ "\"]" ++ ";\n" | (Call s name) <- calls cfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"delegate call\"]" ++ ";\n" | (DelegateCall s) <- calls cfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"dynamic call\"]" ++ ";\n" | (DynamicCall s) <- calls cfa]) ++
                    foldr (++) "" (nub [display (s) ++ "[style=filled, color=lightgreen]" ++ ";\n" | s <- (end cfa)])
                    ++ "\n}\n"
-----------------
-----------------

  emptyCFA :: CFA
  emptyCFA = CFA "" [] [] [] [State "0"] (State "0") [State "0"] []
