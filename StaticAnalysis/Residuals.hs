module StaticAnalysis.Residuals where

import qualified DEA.DEA as DEA
import qualified CFG as CFG
import Solidity.Solidity
import Data.List

reachibilityReduction :: DEA.DEA -> DEA.DEA
reachibilityReduction dea = let badAfterStates = [state | state <- DEA.allStates dea, badAfter dea state]
                                goodEntryPointStates = [state | state <- DEA.allStates dea, goodEntryPoint dea state]
                                usefulStates = badAfterStates ++ goodEntryPointStates
                                uselessStates = DEA.allStates dea \\ usefulStates
                                usefulTransitions = [transition | transition <- DEA.transitions dea, elem (DEA.src transition) usefulStates, elem (DEA.dst transition) usefulStates]
                                in DEA.DEA{
                                  DEA.daeName = DEA.daeName dea,
                                  DEA.allStates = usefulStates,
                                  DEA.initialStates = DEA.initialStates dea,
                                  DEA.transitions = usefulTransitions,
                                  DEA.badStates = (DEA.badStates dea \\ uselessStates),
                                  DEA.acceptanceStates = goodEntryPointStates
                                }

badAfter :: DEA.DEA -> DEA.State -> Bool
badAfter dea state = (pathBetween dea (head (DEA.initialStates dea)) state) && ((statesAfter dea [state]) \\ (DEA.badStates dea) /= [])

goodEntryPoint :: DEA.DEA -> DEA.State -> Bool
goodEntryPoint dea state = (pathBetween dea (head (DEA.initialStates dea)) state
                                && elem state (DEA.acceptanceStates dea))
                            || (not (badAfter dea state)
                                && [src | DEA.Transition src state _ <- DEA.transitions dea, badAfter dea state] /= [])

pathBetween :: DEA.DEA -> DEA.State -> DEA.State -> Bool
pathBetween dea q q' = elem q (statesAfter dea [q])

statesAfter :: DEA.DEA -> [DEA.State] -> [DEA.State]
statesAfter dea [] = []
statesAfter dea states = let afterOneStep = oneStep dea states
                             in if(afterOneStep \\ states /= [])
                                    then statesAfter dea afterOneStep
                                    else states

oneStep :: DEA.DEA -> [DEA.State] -> [DEA.State]
oneStep dea states = [dst | src <- states, DEA.Transition src dst _ <- DEA.transitions dea]

quickCheck :: DEA.DEA -> CFG.FunctionCFG -> DEA.DEA
quickCheck dea cfg = let reducedTransitions = [transition | transition <- DEA.transitions dea, [] /= getAllCFGTransitionsMatching (DEA.event (DEA.label transition)) (CFG.transitions cfg)]
                         naivelyReducedStates = (map (DEA.src) reducedTransitions) ++ (map (DEA.dst) reducedTransitions)
                         reducedInitialStates = [state | state <- naivelyReducedStates, state <- DEA.initialStates dea]
                         reducedBadStates = [state | state <- naivelyReducedStates, state <- DEA.badStates dea]
                         reducedAcceptanceStates = [state | state <- naivelyReducedStates, state <- DEA.acceptanceStates dea]
                         in DEA.DEA (DEA.daeName dea) naivelyReducedStates reducedInitialStates reducedTransitions reducedBadStates reducedAcceptanceStates 
                      
cfgSpecificSynchronousComposition :: DEA.DEA -> CFG.FunctionCFG -> CFG.FunctionCFG
cfgSpecificSynchronousComposition dea cfg = let initialTaggedStates = [(CFG.initial cfg, DEA.initialStates dea)]
                                                allTaggedStates = tagCFGStates dea cfg initialTaggedStates
                                                allUsedCFGStates = map (fst) allTaggedStates
                                                unusedCFGStates = CFG.states cfg \\ allUsedCFGStates
                                                usedTransitionsHere = usedCFGTransitions dea cfg allTaggedStates
                                                in if(notElem (CFG.initial cfg) unusedCFGStates)
                                                    then CFG.FunctionCFG{
                                                            CFG.signature = CFG.signature cfg,
                                                            CFG.transitions = [],
                                                            CFG.states = [CFG.BasicState "1"],
                                                            CFG.initial = CFG.BasicState "1",
                                                            CFG.end = [CFG.BasicState "1"]
                                                    }
                                                    else CFG.FunctionCFG{
                                                            CFG.signature = CFG.signature cfg,
                                                            CFG.transitions = usedTransitionsHere,
                                                            CFG.states = allUsedCFGStates,
                                                            CFG.initial = (CFG.initial cfg),
                                                            CFG.end = (CFG.end cfg) \\ unusedCFGStates
                                                         }
                         
                         
deaSpecificSynchronousComposition :: DEA.DEA -> CFG.FunctionCFG -> DEA.DEA
deaSpecificSynchronousComposition dea cfg = let initialTaggedStates = [(deaInitial, [CFG.initial cfg]) | deaInitial <- DEA.initialStates dea]
                                                allTaggedStates = tagDEAStates dea cfg initialTaggedStates
                                                allUsedDeaStates = map (fst) allTaggedStates
                                                unusedDeaStates = DEA.allStates dea \\ allUsedDeaStates
                                                usedTransitionsHere = usedDEATransitions dea cfg allTaggedStates
                                                in DEA.DEA{
                                                   DEA.daeName = DEA.daeName dea,
                                                   DEA.allStates = allUsedDeaStates,
                                                   DEA.initialStates = (DEA.initialStates dea) \\ unusedDeaStates,
                                                   DEA.transitions = usedTransitionsHere,
                                                   DEA.badStates = (DEA.badStates dea) \\ unusedDeaStates,
                                                   DEA.acceptanceStates = (DEA.acceptanceStates dea) \\ unusedDeaStates
                                                }


usedDEATransitions :: DEA.DEA -> CFG.FunctionCFG -> [(DEA.State, [CFG.State])] -> [DEA.Transition]
usedDEATransitions dea cfg taggedStates = [DEA.Transition deaStateSrc deaStateDst deaLabel | DEA.Transition deaStateSrc deaStateDst deaLabel <- DEA.transitions dea,
                                                    (deaStateSrc, cfgStatesSrc) <- taggedStates,
                                                    (deaStateDst, cfgStatesDst) <- taggedStates,
                                                    --deaStateSrc = src deaTransition,
                                                    --deaStateDst = dst deaTransition,
                                                    srcCfgState <- cfgStatesSrc,
                                                    dstCfgState <- cfgStatesDst,
                                                    --cfgTransition <- (transitions cfg),
                                                    CFG.Transition srcCfgState dstCfgState ev <- (CFG.transitions cfg),
                                                    propertyEventMatchesCFGEvent (DEA.event (deaLabel)) (ev)]


usedCFGTransitions :: DEA.DEA -> CFG.FunctionCFG -> [(CFG.State, [DEA.State])] -> [CFG.Transition]
usedCFGTransitions dea cfg taggedStates = [CFG.Transition cfgStateSrc cfgStateDst cfgLabel | CFG.Transition cfgStateSrc cfgStateDst cfgLabel <- CFG.transitions cfg,
                                                    (cfgStateSrc, deaStatesSrc) <- taggedStates,
                                                    (cfgStateDst, deaStatesDst) <- taggedStates,
                                                    --deaStateSrc = src deaTransition,
                                                    --deaStateDst = dst deaTransition,
                                                    srcDEAState <- deaStatesSrc,
                                                    dstDEAState <- deaStatesDst,
                                                    --cfgTransition <- (transitions cfg),
                                                    DEA.Transition srcDEAState dstDEAState ev <- (DEA.transitions dea),
                                                    propertyEventMatchesCFGEvent (DEA.event ev) (cfgLabel)]

                                     
tagDEAStates :: DEA.DEA -> CFG.FunctionCFG -> [(DEA.State, [CFG.State])] -> [(DEA.State, [CFG.State])]
tagDEAStates dea cfg [] = []
tagDEAStates dea cfg taggedDEAStates = let afterOneStepStates = [(deaState, [CFG.dst cfgTransition])
                                                                | (deaState1, cfgStates1) <- taggedDEAStates,
                                                                    deaTransition <- transitionsFromDEAState dea deaState1,
                                                                    cfgState1 <- cfgStates1,
                                                                    cfgTransition <- getAllCFGTransitionsMatching (DEA.event (DEA.label deaTransition)) (transitionsFromCFGState cfg cfgState1),--nextCFGTransitions, 
                                                                    deaState <- transitionDEAWithCFGTransition dea deaState1 cfgTransition]
                                        in let normalizedStates = unionOfTaggedDEAStates taggedDEAStates afterOneStepStates
                                                in if(normalizedStates /= taggedDEAStates)
                                                    then tagDEAStates dea cfg normalizedStates
                                                    else normalizedStates

                                     
tagCFGStates :: DEA.DEA -> CFG.FunctionCFG -> [(CFG.State, [DEA.State])] -> [(CFG.State, [DEA.State])]
tagCFGStates dea cfg [] = []
tagCFGStates dea cfg taggedCFGStates = let afterOneStepStates = [(cfgState, [DEA.dst deaTransition])
                                                                | (cfgState1, deaStates1) <- taggedCFGStates,
                                                                    cfgTransition <- transitionsFromCFGState cfg cfgState1,
                                                                    deaState1 <- deaStates1,
                                                                    deaTransition <- getAllDEATransitionsMatching (CFG.event cfgTransition) (transitionsFromDEAState dea deaState1),--nextCFGTransitions, 
                                                                    cfgState <- transitionCFGWithDEATransition cfg cfgState1 deaTransition]
                                        in let normalizedStates = unionOfTaggedCFGStates taggedCFGStates afterOneStepStates
                                                in if(normalizedStates /= taggedCFGStates)
                                                    then tagCFGStates dea cfg normalizedStates
                                                    else normalizedStates

transitionDEAWithCFGTransition :: DEA.DEA -> DEA.State -> CFG.Transition -> [DEA.State]
transitionDEAWithCFGTransition dea deaState cfgTransition = let transitionsAvailable = transitionsFromDEAState dea deaState  
                                                                matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, 
                                                                                                        propertyEventMatchesCFGEvent (DEA.event (DEA.label deaTransition)) (CFG.event cfgTransition)]
                                                                nextStates = [DEA.dst deaTransition | deaTransition <- matchingTransitions] ++ [deaState |          
                                                                                                    deaTransition <- matchingTransitions, 
                                                                                                    Nothing /= (DEA.guard (DEA.label deaTransition))]
                                                                in if(matchingTransitions == [])
                                                                    then [deaState]
                                                                    else nextStates
                                                                    

transitionCFGWithDEATransition :: CFG.FunctionCFG -> CFG.State -> DEA.Transition -> [CFG.State]
transitionCFGWithDEATransition cfg cfgState deaTransition = let transitionsAvailable = transitionsFromCFGState cfg cfgState  
                                                                matchingTransitions = [cfgTransition | cfgTransition <- transitionsAvailable, 
                                                                                                        propertyEventMatchesCFGEvent (DEA.event (DEA.label deaTransition)) (CFG.event cfgTransition)]
                                                                nextStates = [CFG.dst cfgTransition | cfgTransition <- matchingTransitions] 
                                                                            ++ [cfgState | cfgTransition <- matchingTransitions, 
                                                                                           Nothing /= (DEA.guard (DEA.label deaTransition))]
                                                                in if(matchingTransitions == [])
                                                                    then [cfgState]
                                                                    else nextStates
                                                                    
                                        
unionOfTaggedDEAStates :: [(DEA.State, [CFG.State])] -> [(DEA.State, [CFG.State])] -> [(DEA.State, [CFG.State])]
unionOfTaggedDEAStates states1 states2 = [(deaState, cfgStates1 ++ (cfgStates2 \\ cfgStates1)) | (deaState, cfgStates1) <- states1, (deaState, cfgStates2) <- states2] 
                                      ++ [(deaState, cfgStates) | (deaState, cfgStates) <- states1,  notElem deaState (map (fst) states2)]
                                      ++ [(deaState, cfgStates) | (deaState, cfgStates) <- states2,  notElem deaState (map (fst) states1)]

unionOfTaggedCFGStates :: [(CFG.State, [DEA.State])] -> [(CFG.State, [DEA.State])] -> [(CFG.State, [DEA.State])]
unionOfTaggedCFGStates states1 states2 = [(cfgState, deaStates1 ++ (deaStates2 \\ deaStates1)) | (cfgState, deaStates1) <- states1, (cfgState, deaStates2) <- states2] 
                                      ++ [(cfgState, deaStates) | (cfgState, deaStates) <- states1,  notElem cfgState (map (fst) states2)]
                                      ++ [(cfgState, deaStates) | (cfgState, deaStates) <- states2,  notElem cfgState (map (fst) states1)]
                                      


            
--transitionTogether :: DEA.DEA -> CFG.FunctionCFG -> DEA.State -> CFG.State -> (DEA.State, [CFG.State])
--transitionTogether dea cfg deaState cfgState = let deaTransitions = transitionsFromDEAState dea deaState
--                                                   cfgTransitions = transitionFromCFGState cfg cfgState
            
getAllCFGTransitionsMatching :: DEA.Event -> [CFG.Transition] -> [CFG.Transition]
getAllCFGTransitionsMatching deaEvent [] = []
getAllCFGTransitionsMatching deaEvent (t:ts) = if(propertyEventMatchesCFGEvent deaEvent (CFG.event t))
                                                then [t] ++ getAllCFGTransitionsMatching deaEvent ts
                                                else getAllCFGTransitionsMatching deaEvent ts
            
getAllDEATransitionsMatching :: CFG.Label -> [DEA.Transition] -> [DEA.Transition]
getAllDEATransitionsMatching cfgEvent [] = []
getAllDEATransitionsMatching cfgEvent (t:ts) = if(propertyEventMatchesCFGEvent (DEA.event (DEA.label t)) cfgEvent)
                                                then [t] ++ getAllDEATransitionsMatching cfgEvent ts
                                                else getAllDEATransitionsMatching cfgEvent ts

transitionsFromDEAState :: DEA.DEA -> DEA.State -> [DEA.Transition]
transitionsFromDEAState dea deaState = [transition | transition <- DEA.transitions dea, deaState == DEA.src transition]

transitionsFromCFGState :: CFG.FunctionCFG -> CFG.State -> [CFG.Transition]
transitionsFromCFGState cfg cfgState = [transition | transition <- CFG.transitions cfg, cfgState == CFG.src transition]

--DEA
--data Event
--  = DEA.UponEntry FunctionCall
--  | DEA.UponExit FunctionCall
--  | DEA.VariableAssignment VariableName (Maybe Expression)

--CFG
--data Label = Label Statement | CFG.LabelE Expression | ConditionHolds Expression | ConditionDoesNotHold Expression | Tau | ReturnLabel Expression | ReturnVoid deriving (Eq, Ord, Show)


propertyEventMatchesCFGEvent :: DEA.Event -> CFG.Label -> Bool
propertyEventMatchesCFGEvent  (DEA.UponEntry (DEA.FunctionCall name params)) (CFG.Entering (CFG.FunctionCall name2 _)) = if(name == name2)
                                                                                    then True
                                                                                    else False
propertyEventMatchesCFGEvent  (DEA.UponExit (DEA.FunctionCall name params)) (CFG.Exiting (CFG.FunctionCall name2 _)) = if(name == name2)
                                                                                    then True
                                                                                    else False
propertyEventMatchesCFGEvent  (DEA.VariableAssignment identifier Nothing) (CFG.LabelE expr) = changesVariable identifier expr 
propertyEventMatchesCFGEvent  (DEA.VariableAssignment identifier (Just expression)) (CFG.LabelE expr) = changesVariable identifier expr 
propertyEventMatchesCFGEvent _ _ = False


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