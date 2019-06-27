module ResidualAnalysis.AbstractCFA where

  import Data.List
  import Numeric.Natural
  import Debug.Trace

  import Solidity.Solidity
  import CFA.CFA as CFA
  import CFA.CFGtoCFA
  import DEA.DEA as DEA
  import SMT.SMTLib2


  data AbstractTransition = AbstractTransition{
                                asrc, adst :: CFA.State,
                                aevent :: CFA.Event
                            } deriving (Eq, Ord, Show)

  instance Parseable AbstractTransition where
  {-  parser = do src <- parser
                spaces
                string "->"
                dst <- parser
                spaces
                char '['
                spaces
                string "label"
                spaces
                char '='
                spaces
                char '"'
                cond <- parser
                spaces
                string ">>"
                spaces
                act <- parser
                spaces
                string ">>"
                spaces
                event <- parser
                char '"'
                spaces
                char ']'
                spaces
                char ';'
                spaces
                return (Transition (src) (dst) (cond) (act) (event))-}
    display (AbstractTransition asrc adst aevent) = (display asrc) ++ " -> " ++ (display adst) ++ " [style=dashed,label = \"" ++ (display aevent) ++ "\"];\n"

  type StateInvariant = [Z3Construct]
  type VariableAbstraction = [(CFA.State, StateInvariant)]

  data AbstractCFA = AbstractCFA{
                        cfa :: CFA,
                        abstractTransitions :: [AbstractTransition],
                        variableAbstraction :: VariableAbstraction
                    } deriving (Eq, Ord, Show)

  instance Parseable AbstractCFA where
    display acfa =  foldr (++) "" (map display (sortDecs $ cfa acfa)) ++
                    foldr (++) "" (map display (varDecs $ cfa acfa)) ++ "\n\n" ++
                  "digraph \"" ++ display (CFA.name $ cfa acfa) ++ "\"{\n" ++
                    foldr (++) "" (map display (CFA.transitions $ cfa acfa)) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"call: " ++ name ++ "\"]" ++ ";\n" | (Call s name) <- calls $ cfa acfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"delegate call\"]" ++ ";\n" | (DelegateCall s) <- calls $ cfa acfa]) ++
                    foldr (++) "" (nub [display s ++ "[style=filled, color=gray, label=\"dynamic call\"]" ++ ";\n" | (DynamicCall s) <- calls $ cfa acfa]) ++
                    foldr (++) "" (nub [display (s) ++ "[style=filled, color=lightgreen]" ++ ";\n" | s <- (CFA.end $ cfa acfa)]) ++
                    foldr (++) "" (map (display) (abstractTransitions acfa)) ++
                    foldr (++) "" [display s ++ "[label=\"" ++ (foldr (++) "" (map display si)) ++ "\"];\n" | (s,si) <- variableAbstraction acfa]
                    ++ "\n}\n"


---------------------------------------------------------------------------------
--TODO we should be abstracting outside behaviour through an abstract initial state, an abstract end state, and an abstract call state (and tag those by invariants of the program)
  abstract :: CFA -> [DEA.Event] -> AbstractCFA
  abstract cfa events = AbstractCFA cfa (abstractOutsideBehaviour cfa events) (abstractDF cfa)
---------------------------
---Control-flow abstraction
---------------------------
  abstractOutsideBehaviour :: CFA -> [DEA.Event] -> [AbstractTransition]
  abstractOutsideBehaviour cfa events = [AbstractTransition endState endState (DEAEvent e) | e <- events, endState <- CFA.end cfa]
                                                  ++ [AbstractTransition (CFA.initial cfa) (initial cfa) (DEAEvent e) | e <- events]
                                                  ++ [AbstractTransition c c (DEAEvent e) | e <- events, c <- callStatesOf (calls cfa)]
-----------------------------------------------------------------
  callStatesOf :: [Call] -> [CFA.State]
  callStatesOf [] = []
  callStatesOf ((Call st _):rest) = [st] ++ callStatesOf rest
  callStatesOf ((DelegateCall st):rest) = [st] ++ callStatesOf rest
  callStatesOf ((DynamicCall st):rest) = [st] ++ callStatesOf rest
-----------------------------------------------------------------------
-----------------------------------------------------------------------
---------------------------
---Data-flow abstraction
---------------------------
  abstractDF :: CFA -> VariableAbstraction
  abstractDF cfa = let (varAbs, _) = abstractForwardDFExhaustiveSteps cfa ([(CFA.initial cfa, [])], [CFA.initial cfa])
                    in optimiseVA $ propagateBackwardsRevertConditions cfa varAbs

  abstractForwardDFExhaustiveSteps :: CFA -> (VariableAbstraction, [CFA.State]) -> (VariableAbstraction, [CFA.State])
  abstractForwardDFExhaustiveSteps cfa (va, []) = (va, [])
  abstractForwardDFExhaustiveSteps cfa (va, states) = let nextTuples = [abstractForwardDFStep cfa s va | s <- states]
                                                          nextVA = nub $ va ++ (foldr (++) [] [va | (va, _) <- nextTuples])
                                                          nextStates = nub $ [s | (_, sss) <- nextTuples, s <- sss]
                                                        in abstractForwardDFExhaustiveSteps cfa (nextVA, nextStates)

  --perform this until variableAbstraction is not updated
  abstractForwardDFStep :: CFA -> CFA.State -> VariableAbstraction -> (VariableAbstraction, [CFA.State])
  abstractForwardDFStep cfa s va = let outTrans = (outgoingCFATransitions s cfa)
                                       reachedStates = [CFA.dst t | t <- outTrans]
                                       callStatesAbs = [(CFA.dst t,[]) | t <- outTrans, (elem (CFA.dst t) (callStatesOf $ calls cfa)) || (elem (CFA.dst t) (CFA.end cfa))]
                                       nonCallStatesAbs = [(CFA.dst t, updateVA si (condition t) (stmt t)) | t <- outTrans, si <- (vabsOf va s), not (elem (CFA.dst t) (callStatesOf $ calls cfa)) && not (elem (CFA.dst t) (CFA.end cfa))]
                                     in (va ++ callStatesAbs ++ nonCallStatesAbs, reachedStates)

  updateVA :: StateInvariant -> Z3Condition -> Z3Statement -> StateInvariant
  updateVA invars cond stmt = let invarBeforeStatementExec = invars ++ cond
                                  newInvars = [invar | invar <- invarBeforeStatementExec, not $ affectedByDisjunctive invar stmt] ++ stmt
                                in newInvars

  optimiseVA :: VariableAbstraction -> VariableAbstraction
  optimiseVA va = (nub [(s,v) | (s,v) <- va, not $ elem (s,[]) va]) ++ (nub [(s,[]) | (s,v) <- va, elem (s,[]) va])

--------------
--This propagates backwards conditions that lead to a revert or throw state
--This can be done safely since we are only propgating to states that cannot have incoming transitions that affect the condition
--and since we know that at runtime such states cannot be reached in a recorded execution, by definition
--TODO need to propagte conditions about local variables to before call states
-----
  propagateBackwardsRevertConditions :: CFA -> VariableAbstraction -> VariableAbstraction
  propagateBackwardsRevertConditions cfa va = let revertingTuples = [(CFA.src t, map negatez3 (CFA.condition t)) | s <- revertExecutionStates cfa, t <- incomingCFATransitions s cfa]
                                                  (va', _) = propagateBackwardsRevertConditionsExhaustive cfa (va, revertingTuples)
                                                in nub va'

  propagateBackwardsRevertConditionsExhaustive :: CFA -> (VariableAbstraction, [(CFA.State, [Z3Construct])]) -> (VariableAbstraction,[(CFA.State, [Z3Construct])])
  propagateBackwardsRevertConditionsExhaustive cfa (va, []) = (va, [])
  propagateBackwardsRevertConditionsExhaustive cfa (va, tuples) = let (va', nextTuples) = propagateBackwardsRevertConditionsStepInSequence cfa (va, nub tuples) []
     --[propagateBackwardsRevertConditionsStep cfa (va, (s,cond)) | (s,cond) <- tuples)]
                                                                    in if nextTuples == []
                                                                        then (va', [])
                                                                        else propagateBackwardsRevertConditionsExhaustive cfa (va', nub nextTuples)


  propagateBackwardsRevertConditionsStepInSequence :: CFA -> (VariableAbstraction, [(CFA.State, [Z3Construct])]) -> [(CFA.State, [Z3Construct])] -> (VariableAbstraction,[(CFA.State, [Z3Construct])])

  propagateBackwardsRevertConditionsStepInSequence cfa (va, []) nextTuples = (va, nextTuples)
  propagateBackwardsRevertConditionsStepInSequence cfa (va, ((s, cond):rest)) nextTuples = let (va',next) = propagateBackwardsRevertConditionsStep cfa (va, (s, cond))
                                                                                               remaining = propagateBackwardsRevertConditionsStepInSequence cfa (va', rest) (nextTuples ++ next)
                                                                                              in remaining


  propagateBackwardsRevertConditionsStep :: CFA -> (VariableAbstraction, (CFA.State, [Z3Construct])) -> (VariableAbstraction, [(CFA.State, [Z3Construct])])
  propagateBackwardsRevertConditionsStep cfa (va, (s, cond)) = if elem s (callStatesOf $ calls cfa)
                                                                then (va, []) --TODO optimise, since if cond is about a local variable we can propagate
                                                                else let inTrans = (incomingCFATransitions s cfa)
                                                                         reachedStates = [(CFA.src t, cond) | t <- inTrans,  not $ elem (CFA.src t) (callStatesOf $ calls cfa)]
                                                                         affectingTransitions = [t | t <- inTrans, not $ elem s (callStatesOf $ calls cfa), affectedByDisjunctiveCollective cond (stmt t)]
                                                                      in if ([] == affectingTransitions)
                                                                          then let vaWithoutSInvariants = [(ss,v) | (ss,v) <- va, ss /= s]
                                                                                   updatedSInvariants = [(s,v ++ cond) | (ss,v) <- va, ss == s]
                                                                                 in (vaWithoutSInvariants ++ updatedSInvariants, reachedStates)
                                                                          else (va, []) --TODO is this what should be done here?

---------------------------
--Util functions
--------------------------

  vabsOf :: VariableAbstraction -> CFA.State -> [StateInvariant]
  vabsOf [] _ = []
  vabsOf ((ss,invar):vabs) s = if ss == s
                                then (invar:(vabsOf vabs s))
                                else vabsOf vabs s

  outgoingCFATransitions :: CFA.State -> CFA -> [CFA.Transition]
  outgoingCFATransitions s cfa = [t | t <- (CFA.transitions cfa), s == CFA.src t]

  incomingCFATransitions :: CFA.State -> CFA -> [CFA.Transition]
  incomingCFATransitions s cfa = [t | t <- (CFA.transitions cfa), s == CFA.dst t]

  outgoingAbstractTransitions :: CFA.State -> AbstractCFA -> [AbstractTransition]
  outgoingAbstractTransitions s acfa = [t | t <- (abstractTransitions acfa), s == asrc t]

--check that RHS variables of second parameter are not used in the first
  -- affectedBy :: Assert -> Assert -> Bool
  -- affectedBy (AssertRel ass1) (AssertRel (Assign genRel1 genRel2)) = intersect (varsOf ass1) (varsOf genRell) /= []
  -- affectedBy _ _ = false


  affectedBy :: Z3Construct -> Z3Construct -> Bool
  affectedBy (Z3Assert (Assert (ass1))) (Z3Assert (Assert ((Assign genRel1 genRel2)))) = let result = intersect (varsOf ass1) (varsOf genRel1) /= []
                                                                                            in result
  affectedBy _ _ = False

  affectedByDisjunctive :: Z3Construct -> [Z3Construct] -> Bool
  affectedByDisjunctive z3 [] = False
  affectedByDisjunctive z3 (z31:z3s) = affectedBy z3 z31 || affectedByDisjunctive z3 z3s

  affectedByDisjunctiveCollective :: [Z3Construct] -> [Z3Construct] -> Bool
  affectedByDisjunctiveCollective z3 [] = False
  affectedByDisjunctiveCollective (z31:z3s1) z3s = affectedByDisjunctive z31 z3s || affectedByDisjunctiveCollective z3s1 z3s

  affectedByCFA :: Z3Construct -> CFA -> Bool
  affectedByCFA ass cfa = [t | t <- CFA.transitions cfa, z3Cons <- (stmt t), affectedBy ass z3Cons] /= []
