
module StaticAnalysis.ComplianceChecking (SyncComp(..), Config, SyncTransition, EventSeq, Cache(..), compliantWith, testFunctionFlowAnalysis, exhaustiveSteps, oneStep, configsAfter, functionFlowAnalysis, getCachedResult) where

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
                  } deriving (Eq, Ord, Show)

  --if (f, n, c, cc) then when entering function f with nesting level n and config c then we may exit with cc
  data Cache = Cache{
                  summary :: [(IFunctionCFG, Natural, DEA.State, [(DEA.State, EventSeq)])]
            } deriving (Eq, Ord, Show)

  compliantWith :: Natural -> ICFG -> DEA -> ICallGraph -> Bool
  compliantWith level (ICFG ifuncs) dea cg = let (deaStateAfterExec, _) = exhaustiveFunctionExec level (ICFG ifuncs) dea ([], initialStates dea) cg (Cache [])
                                                 badStatesReached = [b | b <- intersect deaStateAfterExec (badStates dea)]
                                            in null badStatesReached


  exhaustiveFunctionExec :: Natural -> ICFG -> DEA -> ([DEA.State], [DEA.State]) -> ICallGraph -> Cache -> ([DEA.State], Cache)
  exhaustiveFunctionExec level (ICFG ifuncs) dea (done, []) cg cache = (done, cache)
  exhaustiveFunctionExec level (ICFG ifuncs) dea (done, todo) cg cache = let (afterTodo, newCache) = (oneFunctionExec level (ICFG ifuncs) dea todo cg cache)
                                                                             newDone = done ++ todo
                                                                             newTodo = afterTodo \\ newDone
                                                                            in exhaustiveFunctionExec level (ICFG ifuncs) dea (newDone, newTodo) cg newCache

  oneFunctionExec :: Natural -> ICFG -> DEA -> [DEA.State] -> ICallGraph -> Cache -> ([DEA.State], Cache)
  oneFunctionExec level (ICFG ifuncs) dea deaStates cg cache = oneFunctionExecWithCache level ifuncs (ICFG ifuncs) dea deaStates [] cg cache


  oneFunctionExecWithCache :: Natural -> [IFunctionCFG] -> ICFG -> DEA -> [DEA.State] -> [DEA.State] -> ICallGraph -> Cache -> ([DEA.State], Cache)
  oneFunctionExecWithCache level [] icfg dea initDeaStates finalDEAStates cg cache = (finalDEAStates, cache)
  oneFunctionExecWithCache level (ifunc:ifuncs) icfg dea initDeaStates finalDEAStates cg cache =  let (syncComp, newCache) = functionFlowAnalysis level (ifunc, (ICFG ifuncs)) dea [(iinitial ifunc, deaState) | deaState <- initialStates dea] cg cache
                                                                                                    in (finalDEAStates ++ [q | (s,q) <- configurations syncComp, elem s (iend ifunc)], newCache)

  testFunctionFlowAnalysis :: Natural -> ICFG -> DEA -> [SyncComp]
  testFunctionFlowAnalysis level (ICFG (ifuncs)) dea = let (syncComps, cache) = testFunctionFlowAnalysisWithCache level ifuncs  (ICFG (ifuncs)) dea (icallgraph (ICFG (ifuncs))) [] (Cache [])
                                                          in syncComps

  testFunctionFlowAnalysisWithCache :: Natural -> [IFunctionCFG] -> ICFG -> DEA -> ICallGraph -> [SyncComp] -> Cache -> ([SyncComp], Cache)
  testFunctionFlowAnalysisWithCache level ([]) (ICFG (ifuncs)) dea cg runningResult cache = (runningResult, cache)
  testFunctionFlowAnalysisWithCache level (ifunc:ifuncss) (ICFG (ifuncs)) dea cg runningResult cache = let syncComp = SyncComp{
                                                                                                                  first = [(iinitial ifunc, deaState) | deaState <- initialStates dea],
                                                                                                                  configurations = [(iinitial ifunc, deaState) | deaState <- initialStates dea],
                                                                                                                  evolution = [],
                                                                                                                  transClosureFromFirst = [((iinitial ifunc, deaState), []) | deaState <- initialStates dea]
                                                                                                                }
                                                                                                           (syncCompp, newCache) = exhaustiveSteps level (ifunc, (ICFG (ifuncs))) dea (first syncComp) syncComp cg cache
                                                                                                        in testFunctionFlowAnalysisWithCache level (ifuncss) (ICFG (ifuncs)) dea cg ([syncCompp] ++ runningResult) newCache
                                                                                                      --  in ([syncComps] ++ restSyncComps, newestCache)



  functionFlowAnalysis :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> ICallGraph -> Cache -> (SyncComp, Cache)
  functionFlowAnalysis level (ifunc, icfg) dea configs cg cache = let syncComp = SyncComp{
                                                                                  first = configs,
                                                                                  configurations = configs,
                                                                                  evolution = [],
                                                                                  transClosureFromFirst = [(c, []) | c <- configs]
                                                                                }
                                                                        in exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg cache


  exhaustiveSteps :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> Cache -> (SyncComp, Cache)
  exhaustiveSteps level (ifunc, icfg) dea [] syncComp cg cache = (syncComp, cache)
  exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg cache = let (nextTransitions, newCache) = oneStep level (ifunc, icfg) dea configs syncComp cg [] cache-- this should always be not in synccomp, since we are only exploring unexplored configs, see below
                                                                          nextConfigsReduced = (nub ([cc | (c,e,cc) <- nextTransitions, notElem cc (configurations syncComp)]))
                                                                          callStateConfigs = [(s,q) | (s,q) <- configs, isFunctionCallState s]
                                                                          forcedCallStateTransitions = [t | (s,q) <- callStateConfigs, t <- oneSyntacticStep (ifunc, icfg) dea (s,q)]
                                                                          forcedNextConfigs = nub ([cc | (c,e,cc) <- forcedCallStateTransitions, notElem cc (configurations syncComp)])
                                                                          updatedSyncComp = SyncComp{
                                                                                          first = first syncComp,
                                                                                          configurations = forcedNextConfigs ++ nextConfigsReduced ++ configurations syncComp,
                                                                                          evolution = nub (forcedCallStateTransitions ++ nextTransitions ++ evolution syncComp),
                                                                                          transClosureFromFirst = nub (transClosureFromFirst syncComp
                                                                                                                         ++ [(cc, ee ++ e) | (c,e,cc) <- (nextTransitions ++ forcedCallStateTransitions),
                                                                                                                                               (ccc, ee) <- transClosureFromFirst syncComp,
                                                                                                                                                c == ccc]
                                                                                                                          )
                                                                                        }
                                                                  in (exhaustiveSteps level (ifunc, icfg) dea (forcedNextConfigs ++ nextConfigsReduced) updatedSyncComp cg newCache)

  showStateLabel :: Config -> String
  showStateLabel (BasicState (l), State ll) = "(basic " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (StatementState (l) _, State ll) = "(state " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (ExpressionState (l) _, State ll) = "(expres " ++ l ++ ", " ++ ll ++ ")"
  showStateLabel (FunctionCallState (l) call, State ll) = "(function " ++ l ++ " , " ++ ll ++ ")\n" ++ (display call)
  showStateLabel (st, State l) = "(" ++ show st ++ ", " ++ l ++ ")"

 --returns the one-step transitions to add to the composition
  oneStep ::  Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> [(Config, EventSeq, Config)] -> Cache -> ([(Config, EventSeq, Config)], Cache)
--  oneStep (ThrowState, _, _) _ _ _ a = ([], a)
  oneStep _ _ _ [] _ _ runningResult cache = (runningResult, cache)

--  type Cache = [(IFunctionCFG, Natural, Config, Config)]

  oneStep level (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState):configs) syncComp cg runningResult cache
                   = let prevState = (FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                        in oneStep level (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "66" (newTransitions ++ transitions, newCache)

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                      in oneStep 0 (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                    --   in trace "77" (newTransitions ++ transitions, newCache)


  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState)
                         (endDEAStateEventSeqPairs, newCache) = (configsAfter (level - 1) ifuncs (ICFG ifuncs) dea deaState cg [] cache)--[(deaState, []) | ifuncc <- ifuncs,
                                                      --  let callSyncComp = (functionFlowAnalysis (level - 1) (ifuncc, ICFG ifuncs) dea [(iinitial ifuncc, deaState)] cg cache),
                                                        --    ((endState, deaState), es) <- transClosureFromFirst callSyncComp,
                                                          --    elem endState (iend ifuncc)]
                         newTransitions = [(prevState, eventSeq, (fst prevState, newDEAState)) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                       in oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg (newTransitions ++ runningResult) newCache
                      -- in trace "88" (newTransitions ++ transitions, newerCache)

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState)
                         events = getEventsAssociatedWithIFunctionCFG ifunc icfg dea cg
                         newTransitions = [(prevState, [e], (fst prevState, newDEAState)) | e <- events, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                       in oneStep 0 (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "99" (newTransitions ++ transitions, newCache)

  --assuming functions have unique name
  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState)
                         endDEAStateEventSeqPairs = [(deaState, eventSeq) | ifuncc <- ifuncs,
                                                        let callSyncComp = functionFlowAnalysis (level - 1) (ifunc, ICFG ifuncs) dea [(iinitial ifuncc, deaState)] cg,
                                                            ((endState, deaState), eventSeq) <- transClosureFromFirst syncComp,
                                                            elem endState (iend ifuncc)]
                         newTransitions = [(prevState, eventSeq, (fst prevState, newDEAState)) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                       in oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "1010" (newTransitions ++ transitions, newCache)



  --oneStep level (ifunc, icfg) dea ((scState, deaState):[]) syncComp cg cache = trace ("onestep empty" ++ (show (oneSyntacticStep (ifunc, icfg) dea (scState, deaState), cache))) (oneSyntacticStep (ifunc, icfg) dea (scState, deaState), cache)

  oneStep level (ifunc, icfg) dea ((scState, deaState):configs) syncComp cg runningResult cache = let syntacticSteps = (oneSyntacticStep (ifunc, icfg) dea (scState, deaState))
                                                                                                    in oneStep level (ifunc, icfg) dea configs syncComp cg (syntacticSteps ++ runningResult) cache
                                                                                  --    in  trace ("here3" ++ (show $ summary cache)) (syntacticSteps, cache)

  oneSyntacticStep :: (IFunctionCFG, ICFG) -> DEA -> Config -> [(Config, EventSeq, Config)]
  oneSyntacticStep (ifunc, icfg) dea (scState, deaState) = let outgoingTransitions = [t | t <- itransitions ifunc, isrc t == scState]
                                                               newTransitions = [((scState, deaState), toEventSeq (ievent t), (idst t, nextDEAState)) | t <- outgoingTransitions, nextDEAState <- transitionDEAWithEvent dea deaState (ievent t)]
                                                              in newTransitions

  --data Cache = Cache{
    --              summary :: [(IFunctionCFG, Natural, DEA.State, [(DEA.State, EventSeq)])]
      --      }

  configsAfter :: Natural -> [IFunctionCFG] -> ICFG -> DEA -> DEA.State -> ICallGraph -> [(DEA.State, EventSeq)] -> Cache -> ([(DEA.State, EventSeq)], Cache)
  configsAfter level [] (ICFG ifuncs) dea deaStates cg runningResult cache = (runningResult, cache)
  configsAfter level (ifunc:ifuncss) (ICFG ifuncs) dea deaState cg runningResult cache = let cachedResult = getCachedResult (summary cache) ifunc level deaState --[d | (f, n, startsAt, endsAt) <- (trace (show $ (summary cache)) summary cache), n >= level, startsAt == deaState, d <- endsAt, (case f of _ -> trace ("resolving function") f) == ifunc]
                                                                                           in if trace ("inconfigsafter__" ++ (show cachedResult)) $not $ null cachedResult
                                                                                                  then (cachedResult, cache)
                                                                                                  else let (callSyncComp, Cache deaSummary) = functionFlowAnalysis (level) (ifunc, ICFG ifuncs) dea [(iinitial ifunc, deaState)] cg cache
                                                                                                           endDEAStateEventSeq = [(d, es) | ((endState, d), es) <- transClosureFromFirst callSyncComp, elem endState (iend ifunc)]
                                                                                                           updatedCache = (Cache ([(ifunc, level, deaState, endDEAStateEventSeq)] ++ (deaSummary)))
                                                                                                        in (configsAfter level (ifuncss) (ICFG ifuncs) dea deaState cg endDEAStateEventSeq updatedCache)

  -- OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))  deriving (Eq, Ord, Show)

  getCachedResult :: [(IFunctionCFG, Natural, DEA.State, [(DEA.State, EventSeq)])] -> IFunctionCFG -> Natural -> DEA.State -> [(DEA.State, EventSeq)]
  getCachedResult [] f n d = []
  getCachedResult ((ff, nn, dd, des):rest) f n d = if nn >= n && dd == d && ff == f
                                                    then des
                                                    else getCachedResult rest f n d

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
