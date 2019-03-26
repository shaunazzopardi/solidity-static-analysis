module StaticAnalysis.Util (transitionDEAWithEvent, isDelegate, getFirstFunctionWithName, getFirstCFGFunctionWithName, transitionDEAWithEventWithGCL) where

  import qualified DEA.DEA as DEA
  import qualified CFG.CFG as CFG
  import qualified StaticAnalysis.ICFG as ICFG
  import Solidity.Solidity
  import Data.List
  import Debug.Trace

  transitionDEAWithEvent :: DEA.DEA -> DEA.State -> ICFG.IEvent -> [DEA.State]
  transitionDEAWithEvent _ deaState ICFG.Epsilon = [deaState]
  transitionDEAWithEvent  dea deaState (ICFG.DEAEvent deaEvent) = let transitionsAvailable = transitionsFromDEAState dea deaState
                                                                      matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, (DEA.event (DEA.label deaTransition)) == deaEvent]
                                                                      nextStates = [DEA.dst deaTransition | deaTransition <- matchingTransitions,
                                                                                                        Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "false")))
                                                                                                                          /= (DEA.guard (DEA.label deaTransition))]
                                                                                             ++ [deaState |  deaTransition <- matchingTransitions,
                                                                                                          Nothing /= (DEA.guard (DEA.label deaTransition)),
                                                                                                          Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "true")))
                                                                                                                              /= (DEA.guard (DEA.label deaTransition))]
                                                                      in if(matchingTransitions == [])
                                                                          then [deaState]
                                                                          else nextStates



  transitionDEAWithEventWithGCL :: DEA.DEA -> DEA.State -> ICFG.IEvent -> [(DEA.State, Maybe Expression, Maybe Statement)]
  transitionDEAWithEventWithGCL _ deaState ICFG.Epsilon = [(deaState, Nothing, Nothing)]
  transitionDEAWithEventWithGCL  dea deaState (ICFG.DEAEvent deaEvent) = let transitionsAvailable = transitionsFromDEAState dea deaState
                                                                             matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, (DEA.event (DEA.label deaTransition)) == deaEvent]
                                                                             nextStatesWithGCL = [(DEA.dst deaTransition, cond , (DEA.action (DEA.label deaTransition)))
                                                                                                                        | deaTransition <- matchingTransitions,
                                                                                                                      Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "false")))
                                                                                                                                        /= (DEA.guard (DEA.label deaTransition)),
                                                                                                                          let cond = (positiveConditionWithNegativeConditions (DEA.guard (DEA.label deaTransition)) [DEA.guard (DEA.label otherDEATrans) | otherDEATrans <- matchingTransitions, otherDEATrans /= deaTransition])]
                                                                                                           ++ [(deaState, positiveConditionWithNegativeConditions Nothing [DEA.guard (DEA.label otherDEATrans) | otherDEATrans <- matchingTransitions, otherDEATrans /= deaTransition], Nothing)
                                                                                                                        |  deaTransition <- matchingTransitions,
                                                                                                                            Nothing /= (DEA.guard (DEA.label deaTransition)),
                                                                                                                            Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "true")))
                                                                                                                                                /= (DEA.guard (DEA.label deaTransition))]
                                                                              in if(matchingTransitions == [])
                                                                                  then [(deaState, Nothing, Nothing)]
                                                                                  else nextStatesWithGCL


  positiveConditionWithNegativeConditions :: Maybe Expression -> [Maybe Expression] -> Maybe Expression
  positiveConditionWithNegativeConditions Nothing others = let negativeExprs = [e | Just e <- others]
                                                                  in if null negativeExprs
                                                                        then Nothing
                                                                        else negateAndExpr negativeExprs

  positiveConditionWithNegativeConditions (Just expr) others = let negativeExprs = [e | Just e <- others]
                                                                  in if null negativeExprs
                                                                        then Just expr
                                                                        else case negateAndExpr negativeExprs of
                                                                                        Nothing -> Just expr
                                                                                        Just exprr -> Just $ Binary "&&" expr exprr


  negateAndExpr :: [Expression] -> Maybe Expression
  negateAndExpr [] = Nothing
  negateAndExpr (e:es) = case negateAndExpr es of
                                Nothing -> Nothing
                                Just expr -> Just $ Binary "&&" (Unary "!" e) expr

--transitionDEAWithEventWithGCL :: DEA.DEA -> DEA.State -> ICFG.IEvent -> [(DEA.State, Maybe Expression, Maybe Statement)]
--transitionDEAWithEventWithGCL _ deaState ICFG.Epsilon = [deaState, Nothing, Nothing]
--transitionDEAWithEventWithGCL  dea deaState (ICFG.DEAEvent deaEvent) = let transitionsAvailable = transitionsFromDEAState dea deaState
  --                                                                         matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, (DEA.event (DEA.label deaTransition)) == deaEvent]
    --                                                                       nextStates = [DEA.dst deaTransition | deaTransition <- matchingTransitions,
      --                                                                                                        Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "false")))
        --                                                                                                                        /= (DEA.guard (DEA.label deaTransition))]
          --                                                                                         ++ [deaState |  deaTransition <- matchingTransitions,
            --                                                                                                    Nothing /= (DEA.guard (DEA.label deaTransition)),
              --                                                                                                  Just (Literal (PrimaryExpressionBooleanLiteral (BooleanLiteral "true")))
                --                                                                                                                    /= (DEA.guard (DEA.label deaTransition))]
                  --                                                          in [deaState] ++ [(dst t, guard (label t), action (label t)) | t <- matchingTransitions]



  transitionsFromDEAState :: DEA.DEA -> DEA.State -> [DEA.Transition]
  transitionsFromDEAState dea deaState = [transition | transition <- DEA.transitions dea, deaState == DEA.src transition]

  isDelegate :: CFG.State -> Bool
  isDelegate (CFG.FunctionCallState _ (CFG.OutsideFunctionCall _ (Identifier "delegatecall") _)) = True
  isDelegate _ = False

  isLocalCall :: CFG.State -> Bool
  isLocalCall (CFG.FunctionCallState _ (CFG.FunctionCall _ _)) = True
  isLocalCall _ = False

  isOutsideCall :: CFG.State -> Bool
  isOutsideCall (CFG.FunctionCallState _ (CFG.OutsideFunctionCall _ _ _)) = True
  isOutsideCall _ = False

  isCall :: CFG.State -> Bool
  isCall (CFG.FunctionCallState _ _) = True
  isCall _ = False

  getFirstFunctionWithName :: ICFG.ICFG -> Identifier -> Maybe ICFG.IFunctionCFG
  getFirstFunctionWithName (ICFG.ICFG []) _ = Nothing
  getFirstFunctionWithName (ICFG.ICFG (ifunc:ifuncs)) id = if id == CFG.functionName (ICFG.isignature ifunc)
                                                          then Just ifunc
                                                          else getFirstFunctionWithName (ICFG.ICFG ifuncs) id


  getFirstCFGFunctionWithName :: CFG.CFG -> Identifier -> Maybe CFG.FunctionCFG
  getFirstCFGFunctionWithName (CFG.CFG []) _ = Nothing
  getFirstCFGFunctionWithName (CFG.CFG (func:funcs)) id = if id == CFG.functionName (CFG.signature func)
                                                          then Just func
                                                          else getFirstCFGFunctionWithName (CFG.CFG funcs) id
