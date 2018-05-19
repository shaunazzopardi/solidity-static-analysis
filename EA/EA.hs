module EA.EA (cfgEventToDea, fromFunctionCFGs, Event(..), Transition(..), EA(..), State(..)) where

import qualified DEA.DEA as DEA
import qualified CFG.CFG as CFG
import qualified Solidity.Solidity as Solidity

data EA = EA{
            states :: [State],
            initial :: State,
            final :: [State],
            transitions :: [Transition]
        } deriving (Eq, Ord, Show)

data State = State { unState :: String} deriving (Eq, Ord, Show)

data Transition = Transition{
                    src :: State,
                    dst :: State,
                    event :: Event
                } deriving (Eq, Ord, Show)

data Event = Tau | DEAEvent DEA.Event deriving (Eq, Ord, Show)

--fromSC :: SC.SC -> SC.Blockhain -> EA
--fromSC sc blockhain = let public = SC.publicFunctions sc
--                          internal = SC.internalFunctions sc


cfgStateToString :: CFG.State -> Solidity.FunctionName ->  State
cfgStateToString (CFG.BasicState label) (Solidity.Identifier name) = State ("<<-" ++ label ++ "-" ++ name ++ "->>")
cfgStateToString (CFG.ThrowState) (Solidity.Identifier name) = State ("throw" ++ "-" ++ name)
cfgStateToString (CFG.RevertState) (Solidity.Identifier name) = State ("<<-" ++ "revert" ++ "-" ++ name++ "->>")
cfgStateToString (CFG.ReturnState) (Solidity.Identifier name) = State ("<<-" ++ "return" ++ "-" ++ name++ "->>")
cfgStateToString (CFG.FunctionCallState label _) (Solidity.Identifier name) = State ("<<-" ++ label ++ "-" ++ name++ "->>")


replicateTransitonForEvents :: Transition -> [Event] -> [Transition]
replicateTransitonForEvents _ [] = []
replicateTransitonForEvents (Transition src dst ev) (e:rest) = ((Transition src dst e): (replicateTransitonForEvents (Transition src dst ev) rest))


--TODO overloaded functions
cfgEventToDea :: CFG.Label -> [DEA.Event] -> [Event]
cfgEventToDea _ [] = [Tau]
cfgEventToDea (CFG.Exiting (CFG.FunctionCall name _)) ((DEA.UponExit (DEA.FunctionCall fName untypedParams)):_) = if(name == fName)
                                                                                                                        then [DEAEvent (DEA.UponExit (DEA.FunctionCall name untypedParams))]
                                                                                                                        else [Tau]
cfgEventToDea (CFG.Entering (CFG.FunctionCall name _)) ((DEA.UponEntry (DEA.FunctionCall fName untypedParams)):_) = if(name == fName)
                                                                                                                        then [DEAEvent (DEA.UponEntry (DEA.FunctionCall name untypedParams))]
                                                                                                                        else [Tau]
cfgEventToDea (CFG.LabelE expr) ((DEA.VariableAssignment varName maybeExpr):rest) = let otherMatches = cfgEventToDea (CFG.LabelE expr) rest
                                                                                                in if changesVariable varName expr
                                                                                                    then [DEAEvent (DEA.VariableAssignment varName maybeExpr)] ++ otherMatches
                                                                                                    else otherMatches

changesVariable :: Solidity.Identifier -> Solidity.Expression -> Bool
changesVariable (Solidity.Identifier varName) (Solidity.Unary "++" (Solidity.Literal (Solidity.PrimaryExpressionIdentifier (Solidity.Identifier varName2)))) = if(varName == varName2) 
                                                                                                                  then True
                                                                                                                  else False
changesVariable (Solidity.Identifier varName) (Solidity.Unary "--" (Solidity.Literal (Solidity.PrimaryExpressionIdentifier (Solidity.Identifier varName2)))) = if(varName == varName2) 
                                                                                                                  then True
                                                                                                                  else False
changesVariable (Solidity.Identifier varName) (Solidity.Unary "delete" (Solidity.Literal (Solidity.PrimaryExpressionIdentifier (Solidity.Identifier varName2)))) = if(varName == varName2) 
                                                                                                                        then True
                                                                                                                        else False
changesVariable (Solidity.Identifier varName) (Solidity.Binary op (Solidity.Literal (Solidity.PrimaryExpressionIdentifier (Solidity.Identifier varName2))) _) = 
                            if(op == "=" || op == "+=" || op == "|=" || op == "^=" || op == "-=" || op == "*=" || op == "%/" || op == "<<=" || op == ">>=" || op == "/=" ) 
                                then if(varName == varName2) 
                                       then True
                                       else False 
                                else False

changesVariable (Solidity.Identifier varName) _ = False

cfgTransitionToEA :: CFG.Transition -> CFG.FunctionCFG -> [DEA.Event] -> [Transition]

--We assume any outside function call can call any local function
cfgTransitionToEA (CFG.Transition src dst (CFG.Exiting (CFG.OutsideFunctionCall _ _ _))) cfg events =  let functionName = (CFG.functionName (CFG.signature cfg))
                                                                                                           extraState = State ((unState ((cfgStateToString src functionName))) ++ ">>" ++ (unState ((cfgStateToString dst functionName))))
                                                                                                           templateTransition = Transition extraState extraState Tau
                                                                                                           deaEvents = [DEAEvent ev | ev <- events]
                                                                                                        in   [Transition (cfgStateToString src functionName) 
                                                                                                                         extraState
                                                                                                                         Tau,
                                                                                                              Transition extraState
                                                                                                                         (cfgStateToString dst functionName) 
                                                                                                                         Tau]
                                                                                                                         ++ (replicateTransitonForEvents templateTransition deaEvents)
cfgTransitionToEA (CFG.Transition src dst event) cfg events = [Transition (cfgStateToString src (CFG.functionName (CFG.signature cfg)))
                                                                          (cfgStateToString dst (CFG.functionName (CFG.signature cfg)))
                                                                          ev | ev <- (cfgEventToDea event events)]




fromFunctionCFG :: CFG.FunctionCFG -> [DEA.Event] -> EA
fromFunctionCFG functionCFG events = EA{
                                        states = map (\x -> cfgStateToString x (CFG.functionName (CFG.signature functionCFG))) (CFG.states functionCFG) ,
                                        initial = cfgStateToString (CFG.initial functionCFG) (CFG.functionName (CFG.signature functionCFG)),
                                        final = (map (\x -> cfgStateToString x (CFG.functionName (CFG.signature functionCFG))) (CFG.end functionCFG)),
                                        transitions = foldr (++) [] (map (\x -> cfgTransitionToEA x functionCFG events) (CFG.transitions functionCFG))
                                    }



fromFunctionCFGs :: [CFG.FunctionCFG] -> [DEA.Event] -> EA
fromFunctionCFGs cfgs events =  let initialState = State "<-initial->"
                                    finalState = State "<-final->"
                                    eas = map (\x -> fromFunctionCFG x events) cfgs 
                                    easInitialStates = map (initial) eas
                                    initialTransitions = [Transition initialState eaInitialState Tau | eaInitialState <- easInitialStates]
                                    easFinalStates = foldr (++) [] (map (final) eas)
                                    finalTransitions = [Transition easFinalState finalState Tau | easFinalState <- easFinalStates]
                                    allTransitions = (foldr (++) [] (map (transitions) eas)) ++ initialTransitions ++ finalTransitions
                                  in EA{
                                            states = foldr (++) [] (map states eas),
                                            initial = initialState,
                                            final = [finalState],
                                            transitions = allTransitions
                                        }
