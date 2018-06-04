module StaticAnalysis.Residuals (transitionDEAWithCFGLabel, performResidualAnalysisOnContractSpecification) where

import qualified DEA.DEA as DEA
import qualified EA.EA as EA
import qualified CFG as CFG
import Solidity.Solidity
import Data.List


performResidualAnalysisOnContractSpecification :: DEA.ContractSpecification -> EA.EA -> DEA.ContractSpecification
performResidualAnalysisOnContractSpecification contract ea = let residuals = map (\x -> performResidualAnalysisOnDEA x ea) (DEA.daes contract) 
                                                               in DEA.ContractSpecification{
                                                                  DEA.contractName = DEA.contractName contract,
                                                                  DEA.declarations = DEA.declarations contract,
                                                                  DEA.initialisation = DEA.initialisation contract,
                                                                  DEA.satisfaction = DEA.satisfaction contract,
                                                                  DEA.reparation = DEA.reparation contract,
                                                                  DEA.daes = residuals
                                                             }


performResidualAnalysisOnDEA :: DEA.DEA -> EA.EA -> DEA.DEA
performResidualAnalysisOnDEA dea ea = let dea1 = reachibilityReduction $ quickCheck dea ea
                                          dea2 = reachibilityReduction $ deaSemiSynchronousComposition dea ea
                                        in dea2

toCombinedState :: DEA.State -> DEA.State -> DEA.State
toCombinedState s1 s2 = DEA.State ("(" ++ (DEA.unState s1) ++ "," ++ (DEA.unState s2) ++ ")")

syncComp :: DEA.DEA -> DEA.DEA -> DEA.DEA
syncComp dea1 dea2 = reachibilityReduction DEA.DEA{
                                                    DEA.daeName = (DEA.daeName dea1) ++ " || " ++ (DEA.daeName dea2),
                                                    DEA.allStates = [toCombinedState s1 s2 | s1 <- DEA.allStates dea1, s2 <- DEA.allStates dea2],
                                                    DEA.initialStates = [toCombinedState s1 s2 | s1 <- DEA.initialStates dea1, s2 <- DEA.initialStates dea2],
                                                    DEA.transitions = deasSyncTransitons dea1 dea2,
                                                    DEA.badStates = [toCombinedState s1 s2 | s1 <- DEA.badStates dea1, s2 <- DEA.badStates dea2],
                                                    DEA.acceptanceStates = [toCombinedState s1 s2 | s1 <- DEA.acceptanceStates dea1, s2 <- DEA.acceptanceStates dea2]
                                                  }

combineConditions :: Maybe Expression -> Maybe Expression -> Maybe Expression
combineConditions Nothing Nothing = Nothing
combineConditions Nothing c = c
combineConditions c Nothing = c
combineConditions (Just e1) (Just e2) = Just (Binary "&&" e1 e2) 
                                

combineActions :: Maybe Statement -> Maybe Statement -> Maybe Statement
combineActions Nothing Nothing = Nothing
combineActions Nothing s = s
combineActions s Nothing = s
combineActions (Just s1) (Just s2) = Just (BlockStatement (Block (s1:(s2:[]))))


deasSyncTransitons :: DEA.DEA -> DEA.DEA -> [DEA.Transition]
deasSyncTransitons dea1 dea2 = [DEA.Transition (toCombinedState q1 q2) (toCombinedState q1' q2') (DEA.GCL e (combineConditions c1 c2) (combineActions a1 a2))
                                                | (DEA.Transition q1 q1' (DEA.GCL e c1 a1)) <- DEA.transitions dea1,
                                                  (DEA.Transition q2 q2' (DEA.GCL e c2 a2)) <- DEA.transitions dea2]
                                       ++ [DEA.Transition (toCombinedState q1 q2) (toCombinedState q1' q2) (DEA.GCL e c1 a1)
                                                | (DEA.Transition q1 q1' (DEA.GCL e c1 a1)) <- DEA.transitions dea1,
                                                  q2 <- DEA.allStates dea2,
                                                  (usesEvent (DEA.transitions dea2) q2 e) /= True]
                                       ++ [DEA.Transition (toCombinedState q1 q2) (toCombinedState q1 q2') (DEA.GCL e c2 a2)
                                                | (DEA.Transition q2 q2' (DEA.GCL e c2 a2)) <- DEA.transitions dea2,
                                                  q1 <- DEA.allStates dea2,
                                                  (usesEvent (DEA.transitions dea1) q1 e) /= True]

usesEvent :: [DEA.Transition] -> DEA.State -> DEA.Event -> Bool
usesEvent [] _ _ = False
usesEvent ((DEA.Transition q _ (DEA.GCL e _ _)):rest) q' e' = (q == q' && e == e') || (usesEvent (rest) q e)

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

quickCheck :: DEA.DEA -> EA.EA -> DEA.DEA
quickCheck dea cfg = let reducedTransitions = [transition | transition <- DEA.transitions dea, [] /= getAllEATransitionsMatching (DEA.event (DEA.label transition)) (EA.transitions cfg)]
                         naivelyReducedStates = (map (DEA.src) reducedTransitions) ++ (map (DEA.dst) reducedTransitions)
                         reducedInitialStates = [state | state <- naivelyReducedStates, state <- DEA.initialStates dea]
                         reducedBadStates = [state | state <- naivelyReducedStates, state <- DEA.badStates dea]
                         reducedAcceptanceStates = [state | state <- naivelyReducedStates, state <- DEA.acceptanceStates dea]
                         in DEA.DEA (DEA.daeName dea) naivelyReducedStates reducedInitialStates reducedTransitions reducedBadStates reducedAcceptanceStates 
                   

--cfgSemiSynchronousComposition :: DEA.DEA -> EA -> EA
--cfgSemiSynchronousComposition dea cfg = let initialTaggedStates = [(EA.initial cfg, DEA.initialStates dea)]
--                                            allTaggedStates = tagCFGStates dea cfg initialTaggedStates
--                                            allUsedCFGStates = map (fst) allTaggedStates
--                                            unusedCFGStates = CFG.states cfg \\ allUsedCFGStates
--                                            usedTransitionsHere = usedCFGTransitions dea cfg allTaggedStates
--                                         in if(notElem (CFG.initial cfg) unusedCFGStates)
--                                                    then CFG.FunctionCFG{
--                                                            CFG.signature = CFG.signature cfg,
--                                                            CFG.transitions = [],
--                                                            CFG.states = [CFG.BasicState "1"],
--                                                            CFG.initial = CFG.BasicState "1",
--                                                            CFG.end = [CFG.BasicState "1"]
--                                                    }
--                                                    else CFG.FunctionCFG{
--                                                            CFG.signature = CFG.signature cfg,
--                                                            CFG.transitions = usedTransitionsHere,
--                                                            CFG.states = allUsedCFGStates,
--                                                            CFG.initial = (CFG.initial cfg),
--                                                            CFG.end = (CFG.end cfg) \\ unusedCFGStates
--                                                         }
                         
                           
deaSemiSynchronousComposition :: DEA.DEA -> EA.EA -> DEA.DEA
deaSemiSynchronousComposition dea cfg = let initialTaggedStates = [(deaInitial, [EA.initial cfg]) | deaInitial <- DEA.initialStates dea]
                                            allTaggedStates = tagDEAStates dea cfg initialTaggedStates
                                            allUsedDeaStates = map (fst) allTaggedStates
                                            unusedDeaStates = DEA.allStates dea \\ allUsedDeaStates
                                            usedTransitionsHere = usedDEATransitions dea cfg allTaggedStates
                                         in reachibilityReduction DEA.DEA{
                                                                     DEA.daeName = DEA.daeName dea,
                                                                     DEA.allStates = allUsedDeaStates,
                                                                     DEA.initialStates = (DEA.initialStates dea) \\ unusedDeaStates,
                                                                     DEA.transitions = usedTransitionsHere,
                                                                     DEA.badStates = (DEA.badStates dea) \\ unusedDeaStates,
                                                                     DEA.acceptanceStates = (DEA.acceptanceStates dea) \\ unusedDeaStates
                                                                  }


usedDEATransitions :: DEA.DEA -> EA.EA -> [(DEA.State, [EA.State])] -> [DEA.Transition]
usedDEATransitions dea cfg taggedStates = [DEA.Transition deaStateSrc deaStateDst deaLabel | DEA.Transition deaStateSrc deaStateDst deaLabel <- DEA.transitions dea,
                                                    (deaStateSrc, cfgStatesSrc) <- taggedStates,
                                                    (deaStateDst, cfgStatesDst) <- taggedStates,
                                                    --deaStateSrc = src deaTransition,
                                                    --deaStateDst = dst deaTransition,
                                                    srcCfgState <- cfgStatesSrc,
                                                    dstCfgState <- cfgStatesDst,
                                                    --cfgTransition <- (transitions cfg),
                                                    EA.Transition srcCfgState dstCfgState ev <- (EA.transitions cfg),
                                                    propertyEventMatchesEAEvent (DEA.event (deaLabel)) (ev)]


usedCFGTransitions :: DEA.DEA -> EA.EA -> [(EA.State, [DEA.State])] -> [EA.Transition]
usedCFGTransitions dea cfg taggedStates = [EA.Transition cfgStateSrc cfgStateDst cfgLabel | EA.Transition cfgStateSrc cfgStateDst cfgLabel <- EA.transitions cfg,
                                                    (cfgStateSrc, deaStatesSrc) <- taggedStates,
                                                    (cfgStateDst, deaStatesDst) <- taggedStates,
                                                    --deaStateSrc = src deaTransition,
                                                    --deaStateDst = dst deaTransition,
                                                    srcDEAState <- deaStatesSrc,
                                                    dstDEAState <- deaStatesDst,
                                                    --cfgTransition <- (transitions cfg),
                                                    DEA.Transition srcDEAState dstDEAState ev <- (DEA.transitions dea),
                                                    propertyEventMatchesEAEvent (DEA.event ev) (cfgLabel)]

                                     
tagDEAStates :: DEA.DEA -> EA.EA -> [(DEA.State, [EA.State])] -> [(DEA.State, [EA.State])]
tagDEAStates dea cfg [] = []
tagDEAStates dea cfg taggedDEAStates = let afterOneStepStates = [(deaState, [EA.dst cfgTransition])
                                                                | (deaState1, cfgStates1) <- taggedDEAStates,
                                                                    deaTransition <- transitionsFromDEAState dea deaState1,
                                                                    cfgState1 <- cfgStates1,
                                                                    cfgTransition <- getAllEATransitionsMatching (DEA.event (DEA.label deaTransition)) (transitionsFromEAState cfg cfgState1),--nextCFGTransitions, 
                                                                    deaState <- transitionDEAWithEATransition dea deaState1 cfgTransition]
                                        in let normalizedStates = unionOfTaggedDEAStates taggedDEAStates afterOneStepStates
                                                in if(normalizedStates /= taggedDEAStates)
                                                    then tagDEAStates dea cfg normalizedStates
                                                    else normalizedStates

                                     
tagEAStates :: DEA.DEA -> EA.EA -> [(EA.State, [DEA.State])] -> [(EA.State, [DEA.State])]
tagEAStates dea cfg [] = []
tagEAStates dea cfg taggedCFGStates = let afterOneStepStates = [(cfgState, [DEA.dst deaTransition])
                                                                | (cfgState1, deaStates1) <- taggedCFGStates,
                                                                    cfgTransition <- transitionsFromEAState cfg cfgState1,
                                                                    deaState1 <- deaStates1,
                                                                    deaTransition <- getAllDEATransitionsMatching (EA.event cfgTransition) (transitionsFromDEAState dea deaState1),--nextCFGTransitions, 
                                                                    cfgState <- transitionEAWithDEATransition cfg cfgState1 deaTransition]
                                        in let normalizedStates = unionOfTaggedEAStates taggedCFGStates afterOneStepStates
                                                in if(normalizedStates /= taggedCFGStates)
                                                    then tagEAStates dea cfg normalizedStates
                                                    else normalizedStates

transitionDEAWithEATransition :: DEA.DEA -> DEA.State -> EA.Transition -> [DEA.State]
transitionDEAWithEATransition dea deaState cfgTransition = let  transitionsAvailable = transitionsFromDEAState dea deaState  
                                                                matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, 
                                                                                                        propertyEventMatchesEAEvent (DEA.event (DEA.label deaTransition)) (EA.event cfgTransition)]
                                                                nextStates = [DEA.dst deaTransition | deaTransition <- matchingTransitions] ++ [deaState |          
                                                                                                    deaTransition <- matchingTransitions, 
                                                                                                    Nothing /= (DEA.guard (DEA.label deaTransition))]
                                                                in if(matchingTransitions == [])
                                                                    then [deaState]
                                                                    else nextStates

transitionDEAWithCFGLabel :: DEA.DEA -> DEA.State -> CFG.Label -> [DEA.State]
transitionDEAWithCFGLabel  dea deaState cfgLabel = let transitionsAvailable = transitionsFromDEAState dea deaState  
                                                       eaEvents = EA.cfgEventToDea cfgLabel [DEA.event (DEA.label trans) | trans <- DEA.transitions dea]
                                                       deaEvents = [ev | EA.DEAEvent ev <- eaEvents]
                                                       matchingTransitions = [deaTransition | deaTransition <- transitionsAvailable, elem (DEA.event (DEA.label deaTransition))  deaEvents]
                                                       nextStates = [DEA.dst deaTransition | deaTransition <- matchingTransitions] 
                                                                                       ++ [deaState |  deaTransition <- matchingTransitions, 
                                                                                                    Nothing /= (DEA.guard (DEA.label deaTransition))]
                                                                in if(matchingTransitions == [])
                                                                    then [deaState]
                                                                    else nextStates
                                                                    

transitionEAWithDEATransition :: EA.EA -> EA.State -> DEA.Transition -> [EA.State]
transitionEAWithDEATransition cfg cfgState deaTransition = let  transitionsAvailable = transitionsFromEAState cfg cfgState  
                                                                matchingTransitions = [cfgTransition | cfgTransition <- transitionsAvailable, 
                                                                                                        propertyEventMatchesEAEvent (DEA.event (DEA.label deaTransition)) (EA.event cfgTransition)]
                                                                nextStates = [EA.dst cfgTransition | cfgTransition <- matchingTransitions] 
                                                                            ++ [cfgState | cfgTransition <- matchingTransitions, 
                                                                                           Nothing /= (DEA.guard (DEA.label deaTransition))]
                                                                in if(matchingTransitions == [])
                                                                    then [cfgState]
                                                                    else nextStates
                                                                    
                                        
unionOfTaggedDEAStates :: [(DEA.State, [EA.State])] -> [(DEA.State, [EA.State])] -> [(DEA.State, [EA.State])]
unionOfTaggedDEAStates states1 states2 = [(deaState, cfgStates1 ++ (cfgStates2 \\ cfgStates1)) | (deaState, cfgStates1) <- states1, (deaState, cfgStates2) <- states2] 
                                      ++ [(deaState, cfgStates) | (deaState, cfgStates) <- states1,  notElem deaState (map (fst) states2)]
                                      ++ [(deaState, cfgStates) | (deaState, cfgStates) <- states2,  notElem deaState (map (fst) states1)]

unionOfTaggedEAStates :: [(EA.State, [DEA.State])] -> [(EA.State, [DEA.State])] -> [(EA.State, [DEA.State])]
unionOfTaggedEAStates states1 states2 = [(cfgState, deaStates1 ++ (deaStates2 \\ deaStates1)) | (cfgState, deaStates1) <- states1, (cfgState, deaStates2) <- states2] 
                                      ++ [(cfgState, deaStates) | (cfgState, deaStates) <- states1,  notElem cfgState (map (fst) states2)]
                                      ++ [(cfgState, deaStates) | (cfgState, deaStates) <- states2,  notElem cfgState (map (fst) states1)]
                                      


            
--transitionTogether :: DEA.DEA -> CFG.FunctionCFG -> DEA.State -> CFG.State -> (DEA.State, [CFG.State])
--transitionTogether dea cfg deaState cfgState = let deaTransitions = transitionsFromDEAState dea deaState
--                                                   cfgTransitions = transitionFromCFGState cfg cfgState
            
getAllEATransitionsMatching :: DEA.Event -> [EA.Transition] -> [EA.Transition]
getAllEATransitionsMatching deaEvent [] = []
getAllEATransitionsMatching deaEvent (t:ts) = let rest = getAllEATransitionsMatching deaEvent ts
                                                in case EA.event t of
                                                     EA.Tau -> rest
                                                     EA.DEAEvent deaEvent2 -> if deaEvent == deaEvent2
                                                                              then  [t] ++ rest
                                                                              else rest
            
getAllDEATransitionsMatching :: EA.Event -> [DEA.Transition] -> [DEA.Transition]
getAllDEATransitionsMatching eaEvent [] = []
getAllDEATransitionsMatching eaEvent (t:ts) = if propertyEventMatchesEAEvent (DEA.event (DEA.label t)) eaEvent
                                                            then [t] ++ getAllDEATransitionsMatching eaEvent ts
                                                            else getAllDEATransitionsMatching eaEvent ts

transitionsFromDEAState :: DEA.DEA -> DEA.State -> [DEA.Transition]
transitionsFromDEAState dea deaState = [transition | transition <- DEA.transitions dea, deaState == DEA.src transition]

transitionsFromEAState :: EA.EA -> EA.State -> [EA.Transition]
transitionsFromEAState ea eaState = [transition | transition <- EA.transitions ea, eaState == EA.src transition]

propertyEventMatchesEAEvent :: DEA.Event -> EA.Event -> Bool
propertyEventMatchesEAEvent deaEvent1 (EA.DEAEvent deaEvent2) = if deaEvent1 == deaEvent2
                                                                    then True
                                                                    else False
propertyEventMatchesEAEvent _ _ = False                                                                 