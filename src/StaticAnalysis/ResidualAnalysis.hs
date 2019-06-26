

module StaticAnalysis.ComplianceCheckingWithAssertions (SyncComp(..),
Config, SyncTransition, EventSeq, Cache(..),
SyncTransition(..), ProofObligation, ProofObligationMap(..),
compliantWith, testFunctionFlowAnalysis,
exhaustiveSteps, oneStep, oneSyntacticStep,
 configsAfter, functionFlowAnalysis,
 getCachedResult, getProofObligations, keepOnlySpecifiedTransitions) where

  import Data.List
  import Numeric.Natural
  import Debug.Trace

  import Solidity.Solidity
  import CFG.CFG as CFG
  import StaticAnalysis.ICFG
  import DEA.DEA as DEA
  import StaticAnalysis.Util
  import StaticAnalysis.CallGraph
  import CFG.Parsing
  import StaticAnalysis.SMTInstrumentation


  --TODO take out general flow to StaticAnalysis.hs, here leave compliance checking specific analysis
  type AbstractState = ([Z3Construct], SSAContext)
  emptyAbstractState = ([],[])


  type Config = (CFG.State, DEA.State, AbstractState)
  type EventSeq = [DEA.Event]
  type PreCondition = [Z3Construct]
  type ProofObligation = [Z3Construct]
  data SyncTransition = SyncTransition{
                                  csrc :: Config,
                                  evseq :: EventSeq,
                                  pre :: PreCondition,
                                  cdst :: Config
                              } deriving (Eq, Ord, Show)
  --data SyncTransition = SyncTransition{
    --                            csrc:: Config,
      --                          cevent :: EventSeq,
        --                    --    cabstractState :: AbstractState,
          --                      cdst :: Config
            --                } deriving (Eq, Ord, Show)

  data SyncComp = SyncComp{
                    functName :: FunctionSignature,
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


  compliantWith :: Natural -> ICFG -> DEA.ContractSpecification -> ICallGraph -> Bool
  compliantWith level icfg contractSpec cg = not $ elem False (map f (DEA.daes contractSpec))
                                                      where f dea = compliantWithDEA level icfg dea cg


  compliantWithDEA :: Natural -> ICFG -> DEA -> ICallGraph -> Bool
  compliantWithDEA level (ICFG ifuncs) dea cg = let (deaStateAfterExec, _) = exhaustiveFunctionExec level (ICFG ifuncs) dea ([], initialStates dea) cg (Cache [])
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
  oneFunctionExecWithCache level (ifunc:ifuncs) icfg dea initDeaStates finalDEAStates cg cache =  let (syncComp, newCache) = functionFlowAnalysis level (ifunc, (ICFG ifuncs)) dea [(iinitial ifunc, deaState, ([],[]){- TODO this can contain invariants of the program instead -}) | deaState <- initialStates dea] cg cache
                                                                                                    in (finalDEAStates ++ [q | (s,q, ass) <- configurations syncComp, elem s (iend ifunc)], newCache)

  testFunctionFlowAnalysis :: Natural -> ICFG -> SolidityCode -> DEA -> [SyncComp]
  testFunctionFlowAnalysis level (ICFG (ifuncs)) solidityCode dea = let (ssaContext, assertrules) = scDecs solidityCode
                                                                        ssaContextWithSystemVars = systemDecs ++ ssaContext
                                                                        (syncComps, cache) = testFunctionFlowAnalysisWithCache level ifuncs  (ICFG (ifuncs)) dea (icallgraph (ICFG (ifuncs))) ssaContextWithSystemVars [] (Cache [])
                                                                      in syncComps



  testFunctionFlowAnalysisWithCache :: Natural -> [IFunctionCFG] -> ICFG -> DEA -> ICallGraph -> SSAContext -> [SyncComp] -> Cache -> ([SyncComp], Cache)
  testFunctionFlowAnalysisWithCache level ([]) (ICFG (ifuncs)) dea cg ssaContext runningResult cache = (runningResult, cache)
  testFunctionFlowAnalysisWithCache level (ifunc:ifuncss) (ICFG (ifuncs)) dea cg ssaContext runningResult cache = let ifuncSSAContext = (parameterListDec [] ssaContext (parameters (isignature ifunc))) ++ (parameterListDec [] ssaContext (returnParams (isignature ifunc)))
                                                                                                                      newSSAContext = case trace ("ssacontext: " ++ show (ssaContext ++ ifuncSSAContext)) (ssaContext ++ ifuncSSAContext) of
                                                                                                                                                  _ -> ssaContext ++ ifuncSSAContext
                                                                                                                      --TODO we are starting initial configs at any state in the DEA, simulating the behaviour outside a method
                                                                                                                      initialConfigs = [(iinitial ifunc, deaState, ([], newSSAContext)) | deaState <- allStates dea]
                                                                                                                      syncComp = SyncComp{
                                                                                                                              functName = isignature ifunc,
                                                                                                                              first = initialConfigs,
                                                                                                                              configurations = initialConfigs,
                                                                                                                              evolution = [],
                                                                                                                              transClosureFromFirst = [((iinitial ifunc, deaState, ([], newSSAContext)), []) | deaState <- allStates dea]
                                                                                                                            }
                                                                                                                      (syncCompp, newCache) = exhaustiveSteps level (ifunc, (ICFG (ifuncs))) dea (first syncComp) syncComp cg cache
                                                                                                                    in testFunctionFlowAnalysisWithCache level (ifuncss) (ICFG (ifuncs)) dea cg ssaContext ([syncCompp] ++ runningResult) newCache
                                                                                                      --  in ([syncComps] ++ restSyncComps, newestCache)


--TODO add SSAContext logic
  functionFlowAnalysis :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> ICallGraph -> Cache -> (SyncComp, Cache)
  functionFlowAnalysis level (ifunc, icfg) dea configs cg cache = let syncComp = SyncComp{
                                                                                  functName = isignature ifunc,
                                                                                  first = configs,
                                                                                  configurations = configs,
                                                                                  evolution = [],
                                                                                  transClosureFromFirst = [(c, []) | c <- configs]
                                                                                }
                                                                        in exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg cache


  exhaustiveSteps :: Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> Cache -> (SyncComp, Cache)
  exhaustiveSteps level (ifunc, icfg) dea [] syncComp cg cache = (syncComp, cache)
  exhaustiveSteps level (ifunc, icfg) dea configs syncComp cg cache = let (nextTransitions, newCache) = oneStep level (ifunc, icfg) dea configs syncComp cg [] cache-- this should always be not in synccomp, since we are only exploring unexplored configs, see below
                                                                          nextConfigsReduced = (nub ([cc | SyncTransition c e _ cc <- nextTransitions, notElem cc (configurations syncComp)]))
                                                                          callStateConfigs = [(s,q, ass) | (s,q, ass) <- configs, isFunctionCallState s]
                                                                          forcedCallStateTransitions = [t | (s,q, ass) <- callStateConfigs, t <- oneSyntacticStep (ifunc, icfg) dea (s,q, ass)]
                                                                          forcedNextConfigs = nub ([cc | SyncTransition c e _ cc <- forcedCallStateTransitions, notElem cc (configurations syncComp)])
                                                                          updatedSyncComp = SyncComp{
                                                                                          functName = isignature ifunc,
                                                                                          first = first syncComp,
                                                                                          configurations = forcedNextConfigs ++ nextConfigsReduced ++ configurations syncComp,
                                                                                          evolution = nub (forcedCallStateTransitions ++ nextTransitions ++ evolution syncComp),
                                                                                          transClosureFromFirst = nub (transClosureFromFirst syncComp
                                                                                                                         ++ [(cc, ee ++ e) | SyncTransition c e _ cc <- (nextTransitions ++ forcedCallStateTransitions),
                                                                                                                                               (ccc, ee) <- transClosureFromFirst syncComp,
                                                                                                                                                c == ccc]
                                                                                                                          )
                                                                                        }
                                                                  in (exhaustiveSteps level (ifunc, icfg) dea (forcedNextConfigs ++ nextConfigsReduced) updatedSyncComp cg newCache)

  --showStateLabel :: Config -> String
  --showStateLabel (BasicState (l), State ll, ass) = "(basic " ++ l ++ ", " ++ ll ++ ")"
  --showStateLabel (StatementState (l) _, State ll, ass) = "(state " ++ l ++ ", " ++ ll ++ ")"
  --showStateLabel (ExpressionState (l) _, State ll, ass) = "(expres " ++ l ++ ", " ++ ll ++ ")"
  --showStateLabel (FunctionCallState (l) call, State ll, ass) = "(function " ++ l ++ " , " ++ ll ++ ")\n" ++ (display call)
  --showStateLabel (st, State l, ass) = "(" ++ show st ++ ", " ++ l ++ ", " ++ foldr (++) "" (map display ass) ++ ")"

 --returns the one-step transitions to add to the composition
  oneStep ::  Natural -> (IFunctionCFG, ICFG) -> DEA -> [Config] -> SyncComp -> ICallGraph -> [SyncTransition] -> Cache -> ([SyncTransition], Cache)
--  oneStep (ThrowState, _, _) _ _ _ a = ([], a)
  oneStep _ _ _ [] _ _ runningResult cache = (runningResult, cache)

--  type Cache = [(IFunctionCFG, Natural, Config, Config)]

  oneStep level (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState, ass):configs) syncComp cg runningResult cache
                   = let prevState = (FunctionCallState l (OutsideFunctionCall e (Identifier "delegatecall") p), deaState, ass)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [SyncTransition prevState [e] [] (fst3 prevState, newDEAState, ([],[])) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                        in oneStep level (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "66" (newTransitions ++ transitions, newCache)

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState, ass):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState, ass)
                         eventSeqs = [[e] | e <- getEventsFromDEA dea]
                         newTransitions = [SyncTransition prevState [e] [] (fst3 prevState, newDEAState, ([],[])) | [e] <- eventSeqs, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                      in oneStep 0 (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                    --   in trace "77" (newTransitions ++ transitions, newCache)


  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (OutsideFunctionCall e name p), deaState, ass):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (OutsideFunctionCall e name p), deaState, ass)
                         (endDEAStateEventSeqPairs, newCache) = (configsAfter (level - 1) ifuncs (ICFG ifuncs) dea deaState cg [] cache)--[(deaState, []) | ifuncc <- ifuncs,
                                                      --  let callSyncComp = (functionFlowAnalysis (level - 1) (ifuncc, ICFG ifuncs) dea [(iinitial ifuncc, deaState)] cg cache),
                                                        --    ((endState, deaState), es) <- transClosureFromFirst callSyncComp,
                                                          --    elem endState (iend ifuncc)]
                         newTransitions = [SyncTransition prevState eventSeq [] (fst3 prevState, newDEAState, ([],[])) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                       in oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg (newTransitions ++ runningResult) newCache
                      -- in trace "88" (newTransitions ++ transitions, newerCache)

  oneStep 0 (ifunc, icfg) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState, ass):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState, ass)
                         events = getEventsAssociatedWithIFunctionCFG ifunc icfg dea cg
                         newTransitions = [SyncTransition prevState [e] [] (fst3 prevState, newDEAState, ([],[])) | e <- events, newDEAState <- transitionDEAWithEvent dea deaState (DEAEvent e)]
                       in oneStep 0 (ifunc, icfg) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "99" (newTransitions ++ transitions, newCache)

  --assuming functions have unique name
  oneStep level (ifunc, ICFG ifuncs) dea ((FunctionCallState l (CFG.FunctionCall name params), deaState, ass):configs) syncComp cg runningResult cache =
                     let prevState = (FunctionCallState l (CFG.FunctionCall name params), deaState, ass)
                         maybeFunc = getFirstFunctionWithName (ICFG ifuncs) name
                      in case maybeFunc of
                                 Nothing -> oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg runningResult cache
                                 Just ifuncc -> let endDEAStateEventSeqPairs = [(deaState, eventSeq) |
                                                                let callSyncComp = functionFlowAnalysis (level - 1) (ifuncc, ICFG ifuncs) dea [(iinitial ifuncc, deaState, ([],[]) {- should be as?-})] cg,
                                                                        ((endState, deaState, _), eventSeq) <- transClosureFromFirst syncComp,
                                                                        elem endState (iend ifuncc)]
                                                    newTransitions = [SyncTransition prevState eventSeq [] (fst3 prevState, newDEAState, ([], [])) | (newDEAState, eventSeq) <- endDEAStateEventSeqPairs]
                                                  in oneStep level (ifunc, ICFG ifuncs) dea configs syncComp cg (newTransitions ++ runningResult) cache
                       --in trace "1010" (newTransitions ++ transitions, newCache)



  --oneStep level (ifunc, icfg) dea ((scState, deaState):[]) syncComp cg cache = trace ("onestep empty" ++ (show (oneSyntacticStep (ifunc, icfg) dea (scState, deaState), cache))) (oneSyntacticStep (ifunc, icfg) dea (scState, deaState), cache)

  oneStep level (ifunc, icfg) dea ((scState, deaState, ass):configs) syncComp cg runningResult cache = let syntacticSteps = (oneSyntacticStep (ifunc, icfg) dea (scState, deaState, ass))
                                                                                                    in oneStep level (ifunc, icfg) dea configs syncComp cg (syntacticSteps ++ runningResult) cache
                                                                                  --    in  trace ("here3" ++ (show $ summary cache)) (syntacticSteps, cache)

  oneSyntacticStep :: (IFunctionCFG, ICFG) -> DEA -> Config -> [SyncTransition]
  oneSyntacticStep (ifunc, icfg) dea (scState, deaState, (ass, ssa)) = let outgoingTransitions = [t | t <- itransitions ifunc, isrc t == scState]
                                                                           newTransitions =
                                                                                    [(SyncTransition (scState, deaState, (ass, ssa)) [] [] (idst t, deaState, updatedWithProgramTransiton))
                                                                                                                    | t <- outgoingTransitions, ievent t == Epsilon,
                                                                                                                      let updatedWithProgramTransiton = updateAbstractStateWithTransition (ass, ssa) t]
                                                                                    ++ [(SyncTransition (scState, deaState, (ass, ssa)) (toEventSeq (ievent t)) (condToZ3 cond ssa) (idst t, nextDEAState, addConditionsToAbstractState (condToZ3 cond ssa) (joinAbstractStates (actToZ3 act ssa) updatedWithProgramTransiton)))
                                                                                                          | t <- outgoingTransitions, ievent t /= Epsilon,
                                                                                                                let nextDEATransitions = [tt | tt <- DEA.transitions dea, (DEAEvent (DEA.event (DEA.label tt))) == (ievent t)],
                                                                                                                (nextDEAState, cond, act) <- transitionDEAWithEventWithGCL dea deaState (ievent t),
                                                                                                                --TODO define below function in Util
                                                                                                            --    (nextDEAState, guard, action) <- transitionDEAWithEventWithGCL dea deaState (ievent t),
                                                                                                                let updatedWithProgramTransiton = (updateAbstractStateWithTransition (ass, ssa) t)
                                                                                                                --TODO below
                                                                                                            --    let updatedwithDEATransiton = updateAbstractStateWithDEATransition updatedWithProgramTransiton (nextDEAState, guard, action)
                                                                                                                ]
                                                                 in newTransitions

  joinAbstractStates :: AbstractState -> AbstractState -> AbstractState
  joinAbstractStates (ass,ssa) (asss, sssa) = (ass ++ asss, nub (ssa ++ sssa))

  addConditionsToAbstractState :: [Z3Construct] -> AbstractState -> AbstractState
  addConditionsToAbstractState ass (asss, ssa) = (ass ++ asss, ssa)


  data ProofObligationMap = ProofObligationMap [(SyncTransition, ProofObligation)] deriving (Eq, Ord, Show)

  getProofObligations :: SyncComp -> ProofObligationMap
  getProofObligations syncComp = ProofObligationMap ([(t, conds) | t <- evolution syncComp,
                                                                  let conds = proofObligationOfTransition syncComp t,
                                                                  not $ null [ass | Z3Assert ass <- conds]]--, not (null (pre t))]
                                                          ++ [(t, [Z3Assert $ Assert $ Rel $ CBase $ BoolVal "true"]) | t <- evolution syncComp,
                                                                          let conds = proofObligationOfTransition syncComp t,
                                                                          null [ass | Z3Assert ass <- conds]])

  proofObligationOfTransition :: SyncComp -> SyncTransition -> ProofObligation
  proofObligationOfTransition syncComp (SyncTransition (_, _, (stateCond, stateSSA)) _ (preConds) _) = nub ([Z3Dec dec | dec <- varDecsFromSSAContext stateSSA]
                                                                                                    ++ stateCond ++ preConds)


  varDecsFromSSAContext :: SSAContext -> [VarDeclaration]
  varDecsFromSSAContext ssaContext = [Dec (s ++ (show n)) t | (Dec s t, nn) <- ssaContext, n <- [0..nn]]


  condToZ3 :: Maybe Expression -> SSAContext -> [Z3Construct]
  condToZ3 Nothing _ = []
  condToZ3 (Just expr) ssaContext = case exprRel [] ssaContext expr of
                                      (_, Nothing, _) ->  []
                                      (_, Just assertRel, _) -> [Z3Assert $ Assert assertRel]

  actToZ3 :: Maybe Statement -> SSAContext -> AbstractState
  actToZ3 Nothing _ = emptyAbstractState
  actToZ3 (Just stmt) ssaContext = case statementRel [] ssaContext stmt of
                                        (_, Nothing, _) -> emptyAbstractState
                                        (varDecs, Just assertRel, newSSAContext) -> ([Z3Assert $ Assert assertRel], newSSAContext)

--  oneSyntacticStepInductive :: IFunctionCFG -> DEA -> Config -> [DEA.Transition] -> [(Config, EventSeq, Config)]
--  oneSyntacticStepInductive ifunc dea (scState, deaState, ass) [] = let outgoingICFGTransitions = [t | t <- itransitions ifunc, isrc t == scState]
  --                                                                      outgoingDEATransitionsConds = [DEA.guard (DEA.label t) | t <- DEA.transitions dea, src t == deaState]
    --                                                                  in [((idst t, deaState, )) | t <- outgoingICFGTransitions, dt <- outgoingDEATransitions, let updatedAss = updateAbstractStateWithTransition ass t]

  --oneSyntacticStepInductive ifunc (scState, deaState, ass) (dt:rest) = let outgoingICFGTransitions = [t | t <- itransitions ifunc, isrc t == scState]
    --                                                                       outgoingDEATransitions = [(dState, DEA.guard (DEA.label t), DEA.action (DEA.label t))
      --                                                                                                      | t <- DEA.transitions dea, src t == deaState]



  --data Cache = Cache{
    --              summary :: [(IFunctionCFG, Natural, DEA.State, [(DEA.State, EventSeq)])]
      --      }

--Configs computed for transitive closure
  configsAfter :: Natural -> [IFunctionCFG] -> ICFG -> DEA -> DEA.State -> ICallGraph -> [(DEA.State, EventSeq)] -> Cache -> ([(DEA.State, EventSeq)], Cache)
  configsAfter level [] (ICFG ifuncs) dea deaStates cg runningResult cache = (runningResult, cache)
  configsAfter level (ifunc:ifuncss) (ICFG ifuncs) dea deaState cg runningResult cache = let cachedResult = getCachedResult (summary cache) ifunc level deaState --[d | (f, n, startsAt, endsAt) <- (trace (show $ (summary cache)) summary cache), n >= level, startsAt == deaState, d <- endsAt, (case f of _ -> trace ("resolving function") f) == ifunc]
                                                                                           in if not $ null cachedResult
                                                                                                  then (cachedResult, cache)
                                                                                                  --TODO ssaContext in abstract state below should contain the variable declarations associated with a smart contract and the function being called
                                                                                                  else let (callSyncComp, Cache deaSummary) = functionFlowAnalysis (level) (ifunc, ICFG ifuncs) dea [(iinitial ifunc, deaState, ([],[]))] cg cache
                                                                                                           endDEAStateEventSeq = [(d, es) | ((endState, d, ass), es) <- transClosureFromFirst callSyncComp, elem endState (iend ifunc)]
                                                                                                           updatedCache = (Cache ([(ifunc, level, deaState, endDEAStateEventSeq)] ++ (deaSummary)))
                                                                                                        in (configsAfter level (ifuncss) (ICFG ifuncs) dea deaState cg endDEAStateEventSeq updatedCache)

  -- OutsideFunctionCall Expression FunctionName (Maybe (Either NameValueList ExpressionList))  deriving (Eq, Ord, Show)

  getCachedResult :: [(IFunctionCFG, Natural, DEA.State, [(DEA.State, EventSeq)])] -> IFunctionCFG -> Natural -> DEA.State -> [(DEA.State, EventSeq)]
  getCachedResult [] f n d = []
  getCachedResult ((ff, nn, dd, des):rest) f n d = if nn >= n && dd == d && ff == f
                                                    then des
                                                    else getCachedResult rest f n d

--UTIL FUNCTIONS
  updateAbstractStateWithTransition :: AbstractState -> ITransition -> AbstractState

  updateAbstractStateWithTransition absState (ITransition (StatementState _ stmt) _ (ConditionHolds (expr)) _) = let withStmt = trace "conditiondoesholds" (updateAbstractStateWithStatement absState stmt)
                                                                                                                    in updateAbstractStateWithExpression withStmt expr


  updateAbstractStateWithTransition absState (ITransition (StatementState _ stmt) _ (ConditionDoesNotHold (expr)) _) = let withStmt = trace "conditiondoesnothold" (updateAbstractStateWithStatement absState stmt)
                                                                                                                            in updateAbstractStateWithExpression withStmt (Unary "!" expr)


  updateAbstractStateWithTransition absState (ITransition (StatementState _ stmt) _ FF _) = case absState of
                                                                                                _ -> absState
  updateAbstractStateWithTransition absState (ITransition (StatementState _ stmt) _ _ _) = case (updateAbstractStateWithStatement absState stmt) of
                                                                                                                      _ -> updateAbstractStateWithStatement absState stmt
  updateAbstractStateWithTransition absState (_) = absState

  --TODO
  updateAbstractStateWithDEATransition :: AbstractState -> (DEA.State, Maybe Expression, Maybe Statement) -> AbstractState

  updateAbstractStateWithDEATransition absState (deaState, Nothing, Nothing) = absState
  updateAbstractStateWithDEATransition absState (deaState, Just expr, Nothing) = absState
  updateAbstractStateWithDEATransition absState (deaState, Nothing, Just stmt) = absState
  updateAbstractStateWithDEATransition absState (deaState, Just expr, Just stmt) = absState


  updateAbstractStateWithState :: AbstractState -> CFG.State -> AbstractState
  updateAbstractStateWithState absState (StatementState _ stmt) = updateAbstractStateWithStatement absState stmt
  --updateAbstractStateWithState absState (BasicState _) = absState
  --updateAbstractStateWithState absState (ExpressionState _) = absState
  updateAbstractStateWithState absState (_) = absState

  updateAbstractStateWithStatement :: AbstractState -> Statement -> AbstractState
  updateAbstractStateWithStatement (z3Constructs, ssaContext) stmt = case statementRel [] ssaContext stmt of
                                                              (_, Nothing, newSSAContext) -> (z3Constructs, newSSAContext)
                                                              (_, Just assertRel, newSSAContext) ->  ([Z3Assert $ Assert assertRel] ++ z3Constructs, newSSAContext)
                                                              _ -> (z3Constructs, ssaContext)


  updateAbstractStateWithExpression :: AbstractState -> Expression -> AbstractState
  updateAbstractStateWithExpression (z3Constructs, ssaContext) expr = case exprRel [] ssaContext expr of --TODO no assertions being added because ssaContext is empty, it should have variable declarationsm, I think
                                                                                --  (_, Nothing, newSSAContext) -> trace ("updatewithexpr: Nothing " ++ (show expr) ++ "___" ++ (show ssaContext)) (z3Constructs, newSSAContext)
                                                                                  (_, Just assertRel, newSSAContext) -> trace ("updatewithexpr:  " ++ (show assertRel)) ([Z3Assert $ Assert assertRel] ++ z3Constructs, newSSAContext)
                                                                                  v -> (z3Constructs, ssaContext)

  fst3 :: (a,b,c) -> a
  fst3 (aa, _, _) = aa

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






  --extractProofObligations :: SyncComp -> [(SyncTransition, [Z3Construct])
  --extractProofObligations syncComp = [(t, toCheck) | (c,es,cond,act,_ cc) <- evolutions syncComp, t <- let toCheck = []]

  reduceForReachability :: SyncComp -> SyncComp
  reduceForReachability syncComp = let statesWithNoSource = [c | c <- configurations syncComp, not $ elem c (first syncComp), null [t | t <- evolution syncComp, csrc t == c]]
                                    in if null statesWithNoSource
                                        then syncComp
                                        else SyncComp{
                                                functName = functName syncComp,
                                                first = first syncComp,
                                                configurations = (configurations syncComp) \\ statesWithNoSource,
                                                evolution = [t | t <- evolution syncComp, not $ elem (csrc t) statesWithNoSource],
                                                --this gives shortest transitive closure, i.e. loops aren't resolved infinitely but only once
                                                transClosureFromFirst = [(c,e) | (c,e) <- transClosureFromFirst syncComp, not $ elem c statesWithNoSource]
                                              }

  keepOnlySpecifiedTransitions :: SyncComp -> [SyncTransition] -> SyncComp
  keepOnlySpecifiedTransitions syncComp toKeep = reduceForReachability SyncComp{
                                                                        functName = functName syncComp,
                                                                        first = first syncComp,
                                                                        configurations = configurations syncComp,
                                                                        evolution = intersect toKeep (evolution syncComp),
                                                                        --this gives shortest transitive closure, i.e. loops aren't resolved infinitely but only once
                                                                        transClosureFromFirst = transClosureFromFirst syncComp
                                                                      }
