module StaticAnalysis.ICFG (ICFG(..), IFunctionCFG(..), IEvent(..), ITransition(..), instrument) where

  import Solidity.Solidity
  import Data.List
  import CFG.CFG as CFG
  import DEA.DEA as DEA

  data IEvent = Epsilon | DEAEvent Event deriving (Eq, Ord, Show)

  data ITransition =
    ITransition {
        isrc, idst :: CFG.State,
        icondition :: Condition,
        ievent :: IEvent
  } deriving (Eq, Ord, Show)

  --add possibility that control-flow is unknown
  data IFunctionCFG = IFunctionCFG{
      isignature :: FunctionSignature,
      itransitions :: [ITransition],
      istates :: [CFG.State],
      iinitial :: CFG.State,
      iend :: [CFG.State]
  } deriving (Eq, Ord, Show)

  data ICFG = ICFG [IFunctionCFG] deriving (Eq, Ord, Show)

  instrument :: CFG -> DEA -> ICFG
  instrument (CFG []) _ = ICFG []
  instrument (CFG cfgs) dea = ICFG (map (instrumentFunction dea) cfgs)


  instrumentFunction :: DEA -> FunctionCFG -> IFunctionCFG
  instrumentFunction dea cfg = let  events = getEventsFromDEA dea
                                    itransitions = [ITransition s d c Epsilon | CFG.Transition s d c <- CFG.transitions cfg, afterStateEvent cfg s events == Epsilon, beforeStateEvent cfg d events == Epsilon]
                                                  ++ [ITransition s d c (afterStateEvent cfg s events) | CFG.Transition s d c <- CFG.transitions cfg, afterStateEvent cfg s events /= Epsilon, beforeStateEvent cfg d events == Epsilon]
                                                 ++ [ITransition s d c (beforeStateEvent cfg d events) | CFG.Transition s d c <- CFG.transitions cfg, afterStateEvent cfg s events == Epsilon, beforeStateEvent cfg d events == Epsilon]
                                                  ++ (foldr (++) [] [[ITransition s newState c (afterStateEvent cfg s events), ITransition newState d c (beforeStateEvent cfg d events)] | CFG.Transition s d c <- CFG.transitions cfg, afterStateEvent cfg s events /= Epsilon, beforeStateEvent cfg d events/= Epsilon, let newState = BasicState ((CFG.label s) ++ "/" ++ (CFG.label d))])
                                in IFunctionCFG{
                                    isignature = CFG.signature cfg,
                                    itransitions = nub itransitions,
                                    istates = nub $ foldr (++) [] [[isrc t, idst t] | t <- itransitions],
                                    iinitial = CFG.initial cfg,
                                    iend = CFG.end cfg
                                }


  replicateTranstionForEvents :: CFG.Transition -> [IEvent] -> [ITransition]
  replicateTranstionForEvents _ [] = []
  replicateTranstionForEvents (CFG.Transition src dst c) (e:rest) = ((ITransition src dst c e): (replicateTranstionForEvents (CFG.Transition src dst c) rest))


  --TODO overloaded functions
  beforeStateEvent :: FunctionCFG -> CFG.State -> [Event] -> IEvent
  beforeStateEvent _ _ [] = Epsilon
  beforeStateEvent cfg s ((UponExit (DEA.FunctionCall fName untypedParams)): rest) = if((CFG.functionName (CFG.signature cfg)) == fName && elem s (CFG.end cfg))
                                                                                          then DEAEvent (UponExit (DEA.FunctionCall fName untypedParams))
                                                                                          else beforeStateEvent cfg s rest
  beforeStateEvent _ _ _ = Epsilon

  afterStateEvent :: FunctionCFG -> CFG.State -> [Event] -> IEvent
  afterStateEvent _ _ [] = Epsilon
  afterStateEvent cfg s ((UponEntry (DEA.FunctionCall fName untypedParams)): rest) = if((CFG.functionName (CFG.signature cfg)) == fName && s == (CFG.initial cfg))
                                                                                            then DEAEvent (UponEntry (DEA.FunctionCall fName untypedParams))
                                                                                            else afterStateEvent cfg s rest

  afterStateEvent cfg (ExpressionState l expr) ((VariableAssignment varName maybeExpr): rest) = if changesVariable varName expr
                                                                                                          then DEAEvent (VariableAssignment varName maybeExpr)
                                                                                                          else afterStateEvent cfg (ExpressionState l expr) rest

  afterStateEvent _ _ _ = Epsilon

  changesVariable :: Identifier -> Expression -> Bool
  changesVariable (Identifier varName) (Unary "++" (Literal (PrimaryExpressionIdentifier (Identifier varName2)))) = if(varName == varName2)
                                                                                                                    then True
                                                                                                                    else False
  changesVariable (Identifier varName) (Unary "--" (Literal (PrimaryExpressionIdentifier (Identifier varName2)))) = if(varName == varName2)
                                                                                                                    then True
                                                                                                                    else False
  changesVariable (Identifier varName) (Unary "delete" (Literal (PrimaryExpressionIdentifier (Identifier varName2)))) = if(varName == varName2)
                                                                                                                          then True
                                                                                                                          else False
  changesVariable (Identifier varName) (Binary op (Literal (PrimaryExpressionIdentifier (Identifier varName2))) _) =
                              if(op == "=" || op == "+=" || op == "|=" || op == "^=" || op == "-=" || op == "*=" || op == "%/" || op == "<<=" || op == ">>=" || op == "/=" )
                                  then if(varName == varName2)
                                         then True
                                         else False
                                  else False

  changesVariable (Identifier varName) _ = False

--------------------------------------------------------------
--------------------------------------------------------------

  iPrependStatementLabelsWith :: String -> IFunctionCFG -> IFunctionCFG
  iPrependStatementLabelsWith prefix functionCFG = IFunctionCFG{
                                                      isignature = isignature functionCFG,
                                                      itransitions = [(ITransition (iPrependStatementLabelWith prefix source) (iPrependStatementLabelWith prefix dest) c ev) | ITransition source dest c ev <- itransitions functionCFG],
                                                      istates = [iPrependStatementLabelWith prefix state | state <- istates functionCFG],
                                                      iinitial = iPrependStatementLabelWith prefix (iinitial functionCFG),
                                                      iend = [iPrependStatementLabelWith prefix state | state <- iend functionCFG]
                                              }
--------------------------------------------------------------
--------------------------------------------------------------

  iPrependStatementLabelWith :: String -> CFG.State -> CFG.State
  iPrependStatementLabelWith prefix (BasicState label) = BasicState (prefix ++ label)
  iPrependStatementLabelWith prefix (FunctionCallState label functionName) = FunctionCallState (prefix ++ label) functionName
  iPrependStatementLabelWith _ s = s


--  signatureToCall :: FunctionSignature -> CFG.FunctionCall
--  signatureToCall (FunctionSignature name _ (ParameterList []) _) = CFG.FunctionCall name Nothing
--  signatureToCall (FunctionSignature name _ params _) = CFG.FunctionCall name (Just $ typedParamsToUntyped params)

--  typedParamsToUntyped :: ParameterList -> UntypedParameterList
--  typedParamsToUntyped paramList = typedParamsToUntypedHelper paramList 0

--  typedParamsToUntypedHelper :: ParameterList -> Int -> UntypedParameterList
--  typedParamsToUntypedHelper (ParameterList ((Parameter typ (Just name)):ps)) no = let rest = fromUntypedParameterList $ typedParamsToUntypedHelper (ParameterList ps) no
--                                                                                                    in UntypedParameterList ([name] ++ rest)
--  typedParamsToUntypedHelper (ParameterList ((Parameter typ Nothing):ps)) no = let rest = fromUntypedParameterList $ typedParamsToUntypedHelper (ParameterList ps) (no + 1)
  --                                                                                                  in UntypedParameterList ([Identifier ("param" ++ (show no))] ++ rest)
--  typedParamsToUntypedHelper (ParameterList []) _ = UntypedParameterList []
