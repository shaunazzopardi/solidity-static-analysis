module CFA.CFGtoCFA where

    import Solidity.Solidity
    import Data.List
    import Debug.Trace
    import CFG.CFG as CFG
    import CFG.Parsing
    import DEA.DEA as DEA
    import SMT.SMTLib2
    import CFA.CFA as CFA
    import SMT.SolidityToSMTLib2

    instrumentSC :: SolidityCode -> DEA -> [CFA]
    instrumentSC (SolidityCode (SourceUnit [])) dea = []
    instrumentSC (SolidityCode (SourceUnit ((SourceUnit1_ContractDefinition cd):rest))) dea = instrument cd dea ++ (instrumentSC (SolidityCode (SourceUnit rest)) dea)
    instrumentSC (SolidityCode (SourceUnit (_:rest))) dea = (instrumentSC (SolidityCode (SourceUnit rest)) dea)

    instrument :: ContractDefinition -> DEA -> [CFA]
    instrument contractDefinition dea = let --(globalVarDecs, assertRels) = globalSCDecs contractDefinition
                                            cfgs = CFG.contractCFGFromContractDefinition contractDefinition
                                            functionCFAs = (map (instrumentFunction dea) cfgs)
                                            (globalVarDecs, initialisingAssertions) = contractDefinitionDecs contractDefinition
                                            scSortDecs = contractDefinitionSortDecs contractDefinition
                                            initialisingZ3Constructs = map (Z3Assert) (map (Assert) initialisingAssertions)
                                        --    mainCFA = CFA{
                                          --              CFA.name = unIdentifier $ definitionName contractDefinition,
                                            --            sortDecs = scSortDecs,
                                              --          varDecs = trace (foldr (++) "" (map display globalVarDecs)) globalVarDecs,
                                                --        CFA.transitions = [CFA.Transition (CFA.State "0") (CFA.State "1") [] initialisingZ3Constructs (Epsilon)]
                                                  --                      ++ [CFA.Transition (CFA.State "1") (CFA.State "2") [] [] (Epsilon)]
                                                    --                    ++ [CFA.Transition (CFA.State "2") (CFA.State "1") [] [] (Epsilon)]
                                                      --                  ++ [CFA.Transition (CFA.State "2") (CFA.State "3") [] [] (Epsilon)],
                                                        --CFA.states = [CFA.State "0", CFA.State "1", CFA.State "2", CFA.State "3"],
                                                        --CFA.initial = CFA.State "0",
                                                        --CFA.end = [CFA.State "3"],
                                                        --calls = [Call (CFA.State "2") (CFA.name f) | f <- functionCFAs]
                                              --        }
                                          in {-[mainCFA] ++-} [addSortDecs (addVarDecs f (globalVarDecs ++ functionSystemDecs)) scSortDecs | f <- functionCFAs]

    addVarDecs :: CFA -> [VarDeclaration] -> CFA
    addVarDecs cfa vars = CFA{
                            CFA.name = CFA.name cfa,
                            sortDecs = sortDecs cfa,
                            varDecs = vars ++ varDecs cfa,
                            CFA.transitions = CFA.transitions cfa,
                            CFA.states = CFA.states cfa,
                            CFA.initial = CFA.initial cfa,
                            CFA.end = CFA.end cfa,
                            calls = calls cfa
                          }

    addSortDecs :: CFA -> [SortDeclaration] -> CFA
    addSortDecs cfa sorts = CFA{
                            CFA.name = CFA.name cfa,
                            sortDecs = sorts ++ sortDecs cfa,
                            varDecs = varDecs cfa,
                            CFA.transitions = CFA.transitions cfa,
                            CFA.states = CFA.states cfa,
                            CFA.initial = CFA.initial cfa,
                            CFA.end = CFA.end cfa,
                            calls = calls cfa
                          }

    statementToZ3 :: CFG.State -> [Z3Construct]
    statementToZ3 (StatementState l stmt) = let (varDec, assertRels) = statementRel stmt
                                               in (map (Z3Dec) varDec) ++ (map (Z3Assert) (map (Assert) assertRels))
    statementToZ3 _ = []

    conditionToZ3 :: CFG.Condition -> [Z3Construct]
    conditionToZ3 (ConditionHolds expr) = case exprRel expr of
                                            Nothing -> []
                                            Just assert -> [Z3Assert $ Assert assert]

    conditionToZ3 (ConditionDoesNotHold expr) = case exprRel (Unary "!" expr) of
                                                  Nothing -> []
                                                  Just assert -> [Z3Assert $ Assert assert]
    conditionToZ3 (TT) = []
    conditionToZ3 (FF) = [falseAssert]

    eventUponEntry :: [DEA.Event] -> CFA -> CFA.Event
    eventUponEntry [] cfa = Epsilon
    eventUponEntry ((UponEntry (DEA.FunctionCall (Identifier fName) params)):evs) cfa = if fName == CFA.name cfa
                                                                                          then DEAEvent (UponEntry (DEA.FunctionCall (Identifier fName) params))
                                                                                          else eventUponEntry evs cfa
    eventUponEntry (_:evs) cfa = eventUponEntry evs cfa

    eventUponExit :: [DEA.Event] -> CFA -> CFA.Event
    eventUponExit [] cfa = Epsilon
    eventUponExit ((UponExit (DEA.FunctionCall (Identifier fName) params)):evs) cfa = if fName == CFA.name cfa
                                                                                        then DEAEvent (UponExit (DEA.FunctionCall (Identifier fName) params))
                                                                                        else eventUponExit evs cfa
    eventUponExit (_:evs) cfa = eventUponExit evs cfa

    addFunctionEntryEvent :: DEA -> CFA -> CFA
    addFunctionEntryEvent dea cfa = let entryEvent = eventUponEntry (getEventsFromDEA dea) cfa
                                      in if entryEvent == Epsilon
                                              then cfa
                                              else let prevInitState = CFA.initial cfa
                                                       newInitState = CFA.State "-1"
                                                       newTransition = CFA.Transition (CFA.State "-1") (prevInitState) [] [] entryEvent
                                                    in CFA{
                                                          CFA.name = CFA.name cfa,
                                                          sortDecs = sortDecs cfa,
                                                          varDecs = varDecs cfa,
                                                          CFA.transitions = [newTransition] ++ (CFA.transitions cfa),
                                                          CFA.states = [newInitState] ++ CFA.states cfa,
                                                          CFA.initial = newInitState,
                                                          CFA.end = CFA.end cfa,
                                                          calls = calls cfa
                                                        }

    addFunctionExitEvent :: DEA -> CFA -> CFA
    addFunctionExitEvent dea cfa = let exitEvent = eventUponExit (getEventsFromDEA dea) cfa
                                      in if exitEvent == Epsilon
                                              then cfa
                                              else let prevEndStates = CFA.end cfa
                                                       newEndState = CFA.State "-2"
                                                       newTransitions = [CFA.Transition (endSt) (CFA.State "-2") [] [] exitEvent | endSt <- CFA.end cfa]
                                                    in CFA{
                                                          CFA.name = CFA.name cfa,
                                                          sortDecs = sortDecs cfa,
                                                          varDecs = varDecs cfa,
                                                          CFA.transitions = newTransitions ++ (CFA.transitions cfa),
                                                          CFA.states = [newEndState] ++ CFA.states cfa,
                                                          CFA.initial = CFA.initial cfa,
                                                          CFA.end = [newEndState],
                                                          calls = calls cfa
                                                        }

    instrumentFunction :: DEA -> FunctionCFG -> CFA
    instrumentFunction dea cfg = let  events = (getEventsFromDEA dea)
                                      cfaTransitions = [CFA.Transition (cfgStateToState s) (cfgStateToState d) (conditionToZ3 c) (statementToZ3 d) (afterStateEvent cfg d events) | CFG.Transition s d c <- CFG.transitions cfg]
                                      cfa = CFA{
                                            CFA.name = unIdentifier $ CFG.functionName $ signature cfg,
                                            sortDecs = [],
                                            varDecs =((parameterListDec $ parameters $ signature cfg) ++ (parameterListDec $ returnParams $ signature cfg)),
                                            CFA.transitions = nub cfaTransitions,
                                            CFA.states = [cfgStateToState s | s <- CFG.states cfg],
                                            CFA.initial = cfgStateToState $ CFG.initial cfg,
                                            CFA.end = [cfgStateToState ReturnState],
                                            calls = callsInStates $ CFG.states cfg
                                  }
                                  in (addFunctionEntryEvent dea (addFunctionExitEvent dea cfa))

    cfgStateToState :: CFG.State -> CFA.State
    cfgStateToState (BasicState l) = CFA.State l
    cfgStateToState (StatementState l _) = CFA.State l
    cfgStateToState (ExpressionState l _) = CFA.State l
    cfgStateToState (ThrowState) = CFA.State "throw"
    cfgStateToState (RevertState) = CFA.State "revert"
    cfgStateToState (ReturnState) = CFA.State "return"
    cfgStateToState (FunctionCallState l _) = CFA.State l


    revertExecutionStates :: CFA -> [CFA.State]
    revertExecutionStates cfa = [cfgStateToState ThrowState, cfgStateToState RevertState]


    callsInStates :: [CFG.State] -> [Call]
    callsInStates [] = []
    callsInStates ((FunctionCallState l cfgCall):rest) = let  cfaState = (cfgStateToState (FunctionCallState l cfgCall))
                                                              call = case cfgCall of
                                                                        OutsideFunctionCall _ functionName _ -> if (unIdentifier functionName) == "delegateCall"
                                                                                                                  then DelegateCall (cfgStateToState (FunctionCallState l cfgCall))
                                                                                                                  else DynamicCall (cfgStateToState (FunctionCallState l cfgCall))
                                                                        CFG.FunctionCall functionName _ -> Call cfaState (unIdentifier functionName)
                                                             in [call] ++ (callsInStates rest)
    callsInStates (_:rest) = callsInStates rest

--    --TODO overloaded functions are not considered, instead for soundness we consider every function with the same name
--    matchCFAWithCFGFunctionCall :: [CFA] -> FunctionCall -> [CFA]
--    matchCFAWithCFGFunctionCall [] _ = Nothing
--    matchCFAWithCFGFunctionCall (cfa:cfas) (FunctionCall functionName _) = let rest = matchCFAWithCFGFunctionCall (cfas) (FunctionCall functionName Nothing)
--                                                                            in  if name cfa == unIdentifier functionName
--                                                                                  then [cfa] ++ rest
--                                                                                  else rest

    --replicateTranstionForEvents :: CFG.Transition -> [Event] -> [ITransition]
    --replicateTranstionForEvents _ [] = []
    --replicateTranstionForEvents (CFG.Transition src dst c) (e:rest) = ((ITransition src dst c e): (replicateTranstionForEvents (CFG.Transition src dst c) rest))


    --TODO overloaded functions
    beforeStateEvent :: FunctionCFG -> CFG.State -> [DEA.Event] -> CFA.Event
    beforeStateEvent _ _ [] = Epsilon
    beforeStateEvent cfg s ((UponExit (DEA.FunctionCall fName untypedParams)): rest) = if((CFG.functionName (CFG.signature cfg)) == fName && elem s (CFG.end cfg))
                                                                                                      then DEAEvent (UponExit (DEA.FunctionCall fName untypedParams))
                                                                                                      else beforeStateEvent cfg s rest
    beforeStateEvent _ _ _ = Epsilon

    afterStateEvent :: FunctionCFG -> CFG.State -> [DEA.Event] -> CFA.Event
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

--    prependStatementLabelsWith :: String -> IFunctionCFG -> IFunctionCFG
--    prependStatementLabelsWith prefix functionCFG = IFunctionCFG{
--                                                        isignature = isignature functionCFG,
--                                                        itransitions = [(ITransition (iPrependStatementLabelWith prefix source) (iPrependStatementLabelWith prefix dest) c ev) | ITransition source dest c ev <- itransitions functionCFG],
--                                                        istates = [iPrependStatementLabelWith prefix state | state <- istates functionCFG],
--                                                        iinitial = iPrependStatementLabelWith prefix (iinitial functionCFG),
--                                                        iend = [iPrependStatementLabelWith prefix state | state <- iend functionCFG]
--                                                }
  --------------------------------------------------------------
  --------------------------------------------------------------

--    iPrependStatementLabelWith :: String -> CFG.State -> CFG.State
--    iPrependStatementLabelWith prefix (BasicState label) = BasicState (prefix ++ label)
--    iPrependStatementLabelWith prefix (FunctionCallState label functionName) = FunctionCallState (prefix ++ label) functionName
--    iPrependStatementLabelWith _ s = s


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
