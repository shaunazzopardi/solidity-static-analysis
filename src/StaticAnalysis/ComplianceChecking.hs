
module StaticAnalysis.ComplianceChecking (SyncComp(..), Config, SyncTransition, EventSeq, compliantWith, testFunctionFlowAnalysis, exhaustiveSteps, oneStep) where

  import Data.List
  import CFG.CFG as CFG
  import StaticAnalysis.ICFG
  import DEA.DEA as DEA
  import StaticAnalysis.Util
  import StaticAnalysis.CallGraph
  import CFG.Parsing
  import Numeric.Natural
  import Debug.Trace

  --take out general flow to StaticAnalysis.hs, here leave compliance checking specific analysis

  type Config = (CFG.State, DEA.State)
  type EventSeq = [DEA.Event]
  type SyncTransition = (Config, EventSeq, Config)

  data SyncComp = SyncComp{
                    first :: [Config],
                    configurations :: [Config],
                    evolution :: [SyncTransition],
                    --this gives shortest transitive closure, i.e. loops aren't resolved infinitely but only once
                    transClosureFromFirst :: [(Config, EventSeq)]
                  }


  compliantWith :: Natural -> ICFG -> DEA -> ICallGraph -> Bool
  compliantWith level (ICFG ifuncs) dea cg = let deaStateAfterExec = exhaustiveFunctionExec level (ICFG ifuncs) dea ([], initialStates dea) cg
                                                 badStatesReached = [b | b <- deaStateAfterExec, b <- badStates dea]
                                            in null badStatesReached


  exhaustiveFunctionExec :: Natural -> ICFG -> DEA -> ([DEA.State], [DEA.State]) -> ICallGraph -> [DEA.State]
  exhaustiveFunctionExec level (ICFG ifuncs) dea (done, []) cg = done
  exhaustiveFunctionExec level (ICFG ifuncs) dea (done, todo) cg = let afterTodo = (oneFunctionExec level (ICFG ifuncs) dea todo cg)
                                                                       newDone = done ++ todo
                                                                       newTodo = afterTodo \\ newDone
                                                                    in exhaustiveFunctionExec level (ICFG ifuncs) dea (newDone, newTodo) cg

  oneFunctionExec :: Natural -> ICFG -> DEA -> [DEA.State] -> ICallGraph -> [DEA.State]
  oneFunctionExec level (ICFG ifuncs) dea deaStates cg =  [q | ifunc <- ifuncs,
                                                            let syncComp = functionFlowAnalysis level (ifunc, (ICFG ifuncs)) dea [(iinitial ifunc, deaState) | deaState <- initialStates dea] cg,
                                                            (s,q) <- configurations syncComp,
                                                            s <- iend ifunc]

  testFunctionFlowAnalysis :: Natural -> ICFG -> DEA -> [SyncComp]
  testFunctionFlowAnalysis level (ICFG (ifuncs)) dea = [exhaustiveSteps level (ifunc, (ICFG (ifuncs))) dea (first syncComp) syncComp (icallgraph (ICFG (ifuncs))) |
                                                                            ifunc <- ifuncs,
                                                                            let syncComp = SyncComp{
                                                                                  first = [(iinitial ifunc, deaState) | deaState <- initialStates dea],
                                                                                  configurations = [(iinitial ifunc, deaState) | deaState <- initialStates dea],
                                                                                  evolution = [],
                                                                                  transClosureFromFirst = [((iinitial ifunc, deaState), []) | deaState <- initialStates dea]
                                                                                }]


  functionFlowAnalysis :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> ICallGraph -> SyncComp
  functionFlowAnalysis level (ifunc, icfg) dea configs cg = let syncComp = SyncComp{
                                                                                  first = configs,
                                                                                  configurations = configs,
                                                                                  evolution = [],
                                                                                  transClosureFromFirst = [(c, []) | c <- configs]
                                                                                }
                                                                        in exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg


  exhaustiveSteps :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> SyncComp
  exhaustiveSteps level (ifunc, icfg) dea [] syncComp cg = syncComp
  exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg = let nextTransitions = oneStep level (ifunc, icfg) dea configs syncComp cg -- this should always be not in synccomp, since we are only exploring unexplored configs, see below
                                                                    nextConfigsReduced = nub ([cc | (c,e,cc) <- nextTransitions, notElem cc (configurations syncComp)])
                                                                    callStateConfigs = [(s,q) | (s,q) <- nextConfigsReduced, isFunctionCallState s]
                                                                    forcedCallStateTransitions =  [t | (s,q) <- callStateConfigs, t <- oneSyntacticStep (ifunc, icfg) dea (s,q)]
                                                                    forcedNextConfigs = nub ([cc | (c,e,cc) <- forcedCallStateTransitions, notElem cc (nextConfigsReduced ++ configurations syncComp)])
                                                                    updatedSyncComp = SyncComp{
                                                                                    first = first syncComp,
                                                                                    configurations = forcedNextConfigs ++ nextConfigsReduced ++ configurations syncComp,
                                                                                    evolution = nub (forcedCallStateTransitions ++ nextTransitions ++ evolution syncComp),
                                                                                    transClosureFromFirst = (transClosureFromFirst syncComp
                                                                                                                    ++ [(cc, ee ++ e) | (c,e,cc) <- (nextTransitions ++ forcedCallStateTransitions),
                                                                                                                                          (c, ee) <- transClosureFromFirst syncComp])
                                                                                  }
                                                            in (exhaustiveSteps level (ifunc, icfg) dea (forcedNextConfigs ++ nextConfigsReduced) updatedSyncComp cg)

  showStateLabel :: Config -> String
  showStateLabel (BasicState (l), State ll) = "(basic " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (StatementState (l) _, State ll) = "(state " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (ExpressionState (l) _, State ll) = "(expres " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (FunctionCallState (l) call, State ll) = "(function " ++ l ++ " , " ++ ll ++ ")\n" ++ (display call)
  showStateLabel (st, State l) = "(" ++ show st ++ ", " ++ l ++ ")"

 --returns the one-step transitions to add to the composition
  oneStep ::  Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> [(Config, EventSeq, Config)]
--  oneStep (ThrowState, _, _) _ _ _ a = ([], a)
  oneStep _ _ _ [] _ _ = []

  oneStep level (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState):configs) syncComp cg
                   = let prevState = (FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                       in newTransitions ++ oneStep level (ifunc, icfg) dea configs syncComp cg

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState):configs) syncComp cg =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                       in newTransitions ++ oneStep 0 (ifunc, icfg) dea configs syncComp cg


  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState):configs) syncComp cg =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState)
                         endDEAStateEventSeqPairs = [(deaState, eventSeq) | ifuncc <- ifuncs,
                                                        let callSyncComp = functionFlowAnalysis (level - 1) (ifunc, ICFG ifuncs) dea [(iinitial ifuncc, deaState)] cg,
                                                          let endStates = iend ifuncc,
                                                            endState <- endStates,
                                                            ((endState, deaState), eventSeq) <- transClosureFromFirst syncComp]
                         newTransitions = [(prevState, eventSeq, (fst prevState, newDEAState)) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                       in newTransitions ++ oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState):configs) syncComp cg =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState)
                         events = getEventsAssociatedWithIFunctionCFG ifunc icfg dea cg
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | e <- events, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                       in newTransitions ++ oneStep 0 (ifunc, icfg) dea configs syncComp cg

  --assuming functions have unique name
  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState):configs) syncComp cg =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState)
                         endDEAStateEventSeqPairs = [(deaState, eventSeq) | ifuncc <- ifuncs,
                                                        let callSyncComp = functionFlowAnalysis (level - 1) (ifunc, ICFG ifuncs) dea [(iinitial ifuncc, deaState)] cg,
                                                          let endStates = iend ifuncc,
                                                            endState <- endStates,
                                                            ((endState, deaState), eventSeq) <- transClosureFromFirst syncComp]
                         newTransitions = [(prevState, eventSeq, (fst prevState, newDEAState)) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                       in newTransitions ++ oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg




  oneStep level (ifunc, icfg) dea ((scState, deaState):configs) syncComp cg = ((oneSyntacticStep (ifunc, icfg) dea (scState, deaState)) ++ oneStep level (ifunc, icfg) dea configs syncComp cg)

  oneSyntacticStep :: (IFunctionCFG, ICFG) -> DEA -> Config -> [(Config, EventSeq, Config)]
  oneSyntacticStep (ifunc, icfg) dea (scState, deaState) = let outgoingTransitions = [t | t <- itransitions ifunc, isrc t == scState]
                                                               newTransitions = [((scState, deaState), toEventSeq (ievent t), (idst t, nextDEAState)) | t <- outgoingTransitions, nextDEAState <- transitionDEAWithEvent dea deaState (ievent t)]
                                                              in newTransitions

  -- OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))  deriving (Eq, Ord, Show)

--UTIL FUNCTIONS


  toEventSeq :: IEvent -> EventSeq
  toEventSeq Epsilon = []
  toEventSeq (DEAEvent ev) = [ev]

  delegate :: CFG.FunctionCall -> Bool
  delegate (OutsideFunctionCall _ (Identifier "delegatecall") _) = True
  delegate _ = False

  outsideCall :: CFG.FunctionCall -> Bool
  outsideCall (OutsideFunctionCall _ _ _) = True
  outsideCall _ = False


  getEventsAssociatedWithIFunctionCFG :: IFunctionCFG -> ICFG -> DEA -> ICallGraph -> [Event]
  getEventsAssociatedWithIFunctionCFG ifunc icfg dea callGraph = if eventuallyDelegates callGraph ifunc
                                                                    then [e | e <- getEventsFromDEA dea]
                                                                    else [e | ifunc <- getCalleesOf callGraph ifunc, t <- itransitions ifunc, e <- getEventsFromDEA dea, ievent t == DEAEvent e]
