module ResidualAnalysis.DEAResiduals where

  import qualified DEA.DEA as DEA
  import qualified CFG.CFG as CFG
  import Solidity.Solidity
  import Data.List
  import Debug.Trace



  deaSyncComp :: DEA.DEA -> DEA.DEA -> DEA.DEA
  deaSyncComp dea1 dea2 =  DEA.DEA{
                                DEA.daeName = (DEA.daeName dea1) ++ " || " ++ (DEA.daeName dea2),
                                DEA.allStates = [toCombinedState s1 s2 | s1 <- DEA.allStates dea1, s2 <- DEA.allStates dea2],
                                DEA.initialStates = [toCombinedState s1 s2 | s1 <- DEA.initialStates dea1, s2 <- DEA.initialStates dea2],
                                DEA.transitions = deasSyncTransitons dea1 dea2,
                                DEA.badStates = [toCombinedState s1 s2 | s1 <- DEA.badStates dea1, s2 <- DEA.badStates dea2],
                                DEA.acceptanceStates = [toCombinedState s1 s2 | s1 <- DEA.acceptanceStates dea1, s2 <- DEA.acceptanceStates dea2]
                              }

  toCombinedState :: DEA.State -> DEA.State -> DEA.State
  toCombinedState s1 s2 = DEA.State ("(" ++ (DEA.unState s1) ++ "," ++ (DEA.unState s2) ++ ")")

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
                                  uselessStates = (DEA.allStates dea \\ usefulStates)
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
  badAfter dea state = (elem state (statesAfter dea (DEA.initialStates dea)))  && ([b | b <- (DEA.badStates dea), elem b (statesAfter dea [state])] /= [])

  goodEntryPoint :: DEA.DEA -> DEA.State -> Bool
  goodEntryPoint dea state = (elem state (statesAfter dea (DEA.initialStates dea)))
                                  && (elem state (DEA.acceptanceStates dea)
                                        || (not (badAfter dea state)
                                            && [DEA.src t | t <- DEA.transitions dea, badAfter dea (DEA.src t)] /= []))

  pathBetween :: DEA.DEA -> DEA.State -> DEA.State -> Bool
  pathBetween dea q qq = elem qq (statesAfter dea [q])

  statesAfter :: DEA.DEA -> [DEA.State] -> [DEA.State]
  statesAfter dea [] = []
  statesAfter dea states = let afterOneStep = nub $ ((oneStep dea states) ++ states)
                               in if(afterOneStep \\ states /= [])
                                      then statesAfter dea afterOneStep
                                      else afterOneStep

  oneStep :: DEA.DEA -> [DEA.State] -> [DEA.State]
  oneStep dea states = [DEA.dst t | s <- states, t <- DEA.transitions dea, DEA.src t == s]
