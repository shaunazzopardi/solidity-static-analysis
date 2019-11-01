{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses  #-}

module ResidualAnalysis.IntraProceduralAbstractMonitoredSystem where

  import Data.List
  import Numeric.Natural
  import Debug.Trace

  import Solidity.Solidity hiding (from)
  import ResidualAnalysis.AbstractCFA
  import CFA.CFA as CFA
  import DEA.DEA as DEA hiding (from)
  import SMT.SMTLib2
  import SMT.SolidityToSMTLib2
  import Parseable

  --This module provides to functionality to create an abstraction of the runtime monitored system

  --The abstraction of a program state at runtime, with *a* representing the type of data abstraction chosen.
  --[[Z3Construct]] is one choice for *a*, representing the disjunction of conjunction of Z3construct 
  type AMSConfig a = (CFA.State, DEA.State, a)

  instance Parseable [[Z3Construct]] where
      display [] = ""
      display ([]:[[]]) = ""
      display (va:[]) = (foldr (++) "" (map display va))
      display (va:vabs) = (foldr (++) "" (map display va)) ++ " OR " ++ display vabs

  instance Parseable a => Parseable (AMSConfig a) where
    display (s,q,a) = "(" ++ display s ++ ", " ++ display q ++ ", " ++  display a ++ ")"


  data AMSTransition a = AMSTransition{
                          from :: AMSConfig a,
                          cfaTrans :: (Maybe CFA.Transition),
                          deaTrans :: (Maybe DEA.Transition),
                          to :: AMSConfig a
                        } deriving (Eq, Ord, Show)

  instance Parseable a => Parseable (AMSTransition a) where
    display (AMSTransition fromConf cfaTrans deaTrans toConf) = let cfaTransString = case cfaTrans of
                                                                                        Nothing -> "#"
                                                                                        Just trans -> (foldr (++) "" $ map display (condition trans)) ++ " >> " ++ (foldr (++) "" $ map display (stmt trans)) ++ " >> " ++ (display (CFA.event trans))
                                                                    deaTransString = case deaTrans of
                                                                                    Nothing -> "#"
                                                                                    Just trans -> display $ label trans
                                                                 in "\"" ++ display fromConf ++ "\"" ++ " -> " ++ "\"" ++ display toConf ++ "\"" ++ " [label = \"" ++ (display cfaTransString) ++ " || " ++ (display deaTransString) ++ "\"];\n"

  transitionProofObligation :: [AMSTransition [[Z3Construct]]] -> AMSTransition [[Z3Construct]] -> [[Z3Construct]]
  transitionProofObligation _ (AMSTransition (s,q,va) Nothing (Just deaTrans) to) = let deaCond = guard $ label deaTrans
                                                                                    in case deaCond of
                                                                                            Nothing -> []
                                                                                            Just expr -> case exprRel expr of
                                                                                                            Just assert -> [v ++ [Z3Assert $ Assert $ assert] | v <- va]
                                                                                                            Nothing -> []
  transitionProofObligation _ (AMSTransition (s,q,va) (Just cfaTrans) (Just deaTrans) to) = let deaCond = guard $ label deaTrans
                                                                                            in case deaCond of
                                                                                                    Nothing -> []
                                                                                                    Just expr -> let updatedVA = [updateVA v (condition cfaTrans) (stmt cfaTrans) | v <- va]
                                                                                                                  in case exprRel expr of
                                                                                                                          Just assert -> [v ++ [Z3Assert $ Assert $ assert] | v <- updatedVA]
                                                                                                                          Nothing -> []
  transitionProofObligation amsts (AMSTransition (s,q,va) (Just st) Nothing to) = let alternativeDEATransitions = [deaTrans amst | amst <- amsts, from amst == (s,q,va), cfaTrans amst == Just st, deaTrans amst /= Nothing]
                                                                                      deaConds = [guard $ label qt | Just qt <- alternativeDEATransitions, (guard $ label qt) /= Nothing]
                                                                                      justifiedDeaConditions = [exprRel cond | Just cond <- deaConds]
                                                                                      justifiedDeajustifiedDeaAssertions = [ass | Just ass <- justifiedDeaConditions]
                                                                                          in case justifiedDeajustifiedDeaAssertions of
                                                                                                [] -> []
                                                                                                _ -> let updatedVA = [updateVA v (condition st) (stmt st) | v <- va]
                                                                                                         disjunction = disjunctz3 justifiedDeajustifiedDeaAssertions
                                                                                                      in case disjunction of
                                                                                                            Nothing -> []
                                                                                                            Just ass -> [v ++ [negatez3 (Z3Assert $ Assert ass)] | v <- updatedVA]
  transitionProofObligation _ _ = []

  data AMS a = AMS{
                cfaLabel :: String,
                deaLabel :: String,
                configs :: [AMSConfig a],
                evolutions :: [AMSTransition a]
              } deriving (Eq, Ord, Show)

  instance Parseable a => Parseable (AMS a) where
    display (AMS cfaLabel deaLabel configs evols) =  "digraph \"" ++ (display cfaLabel ++ " || " ++ display deaLabel) ++ "\"{\n" ++
                                                foldr (++) "" (map display (evols)) ++
                                                "\n}\n"

  type DataFlowLogic a =  AbstractCFA -> DEA -> AMSConfig a -> (Either CFA.Transition AbstractTransition) -> (Maybe DEA.Transition) -> AMSConfig a
  type DFL a = DataFlowLogic a

  type InitConfigsDFL a = AbstractCFA -> DEA -> [AMSConfig a]

  type DFLEnv a = (InitConfigsDFL a, DFL a)

  initConfigsnoDF :: InitConfigsDFL [[Z3Construct]]
  --TODO associate variable state in variable abstraction
  initConfigsnoDF acfa dea = [(CFA.initial $ cfa acfa, initt, []) | initt <- initialStates dea]

  noDF :: DataFlowLogic a
  noDF _ _ (s,q,vabs) (Left t) Nothing = if s == CFA.src t
                                              then (CFA.dst t, q, vabs)
                                              else (s,q,vabs)
  noDF _ _ (s,q,vabs) (Left t) (Just dt) = if s == CFA.src t && DEA.src dt == q
                                                then (CFA.dst t, DEA.dst dt, vabs)
                                                else (s,q,vabs)
  noDF _ _ (s,q,vabs) (Right ast) Nothing = if s == asrc ast
                                                    then (adst ast, q, vabs)
                                                    else (s,q,vabs)
  noDF _ _ (s,q,vabs) (Right ast) (Just dt) = if s == asrc ast && DEA.src dt == q
                                                      then (adst ast, DEA.dst dt, vabs)
                                                      else (s,q,vabs)

  initConfigsSimpleDF :: InitConfigsDFL [[Z3Construct]]
  --TODO associate variable state in variable abstraction
  initConfigsSimpleDF acfa dea = [(CFA.initial $ cfa acfa, initt, []) | initt <- initialStates dea]

  simpleDF :: DataFlowLogic [[Z3Construct]]
  simpleDF acfa dea (s,q,vabs) (Left t) Nothing = if s == CFA.src t
                                                    then (CFA.dst t, q, vabsOf (variableAbstraction acfa) s)
                                                    else (s,q,vabs)
  simpleDF acfa dea (s,q,vabs) (Left t) (Just dt) = if s == CFA.src t && DEA.src dt == q
                                                then (CFA.dst t, DEA.dst dt, vabsOf (variableAbstraction acfa) s)
                                                else (s,q,vabs)
  simpleDF acfa dea (s,q,vabs) (Right ast) Nothing = if s == asrc ast
                                                    then (adst ast, q, vabsOf (variableAbstraction acfa) s)
                                                    else (s,q,vabs)
  simpleDF acfa dea (s,q,vabs) (Right ast) (Just dt) = if s == asrc ast && DEA.src dt == q
                                                      then (adst ast, DEA.dst dt, vabsOf (variableAbstraction acfa) s)
                                                      else (s,q,vabs)


---create DF logic with dynamic SSA

  constructControlFlowABS :: AbstractCFA -> DEA -> AMS [[Z3Construct]]
  constructControlFlowABS acfa dea = constructABSGeneric (initConfigsnoDF, noDF) acfa dea

  constructABSGeneric ::  (Eq a) => DFLEnv a -> AbstractCFA -> DEA -> AMS a
  constructABSGeneric (initConfigs, dataFlow) acfa dea = let (amsTrans, amsStates, _) = exhaustiveSteps dataFlow acfa dea ([],[],initConfigs acfa dea)
                                                                                      in AMS{
                                                                                            cfaLabel = CFA.name $ cfa acfa,
                                                                                            deaLabel = deaName dea,
                                                                                            configs = amsStates,
                                                                                            evolutions = amsTrans
                                                                                          }

  exhaustiveSteps :: (Eq a) => DataFlowLogic a -> AbstractCFA -> DEA -> ([AMSTransition a], [AMSConfig a], [AMSConfig a]) -> ([AMSTransition a], [AMSConfig a], [AMSConfig a])
  exhaustiveSteps dataFlow acfa dea (ts,done,[]) = (ts,done,[])
  exhaustiveSteps dataFlow acfa dea (ts,done,left) = let newTrans = ts ++ (foldr (++) [] [step dataFlow c acfa dea | c <- left])
                                                         newDone = done ++ left
                                                         newLeft = (nextConfigs newTrans) \\ newDone
                                                      in exhaustiveSteps dataFlow acfa dea (newTrans, newDone, newLeft)

  nextConfigs :: [AMSTransition a] -> [AMSConfig a]
  nextConfigs [] = []
  nextConfigs (t:ts) = [to t] ++ (nextConfigs ts)

  step :: DataFlowLogic a -> AMSConfig a -> AbstractCFA -> DEA -> [AMSTransition a]
  step dataFlow (s,q,vs) acfa dea = let outgoingCFATrans = outgoingCFATransitions s (cfa acfa)
                                        outgoingAbstractTrans = outgoingAbstractTransitions s acfa
                                        outgoingDEATrans = outgoingDEATransitions q dea
                                        newAMSTransitions = (foldr (++) [] [matchConcreteTransition dataFlow acfa dea (s,q,vs) t outgoingDEATrans | t <- outgoingCFATrans])
                                                       ++ (foldr (++) [] [matchAbstractTransition dataFlow acfa dea (s,q,vs) t outgoingDEATrans | t <- outgoingAbstractTrans])
                                   in newAMSTransitions



  outgoingDEATransitions :: DEA.State -> DEA.DEA -> [DEA.Transition]
  outgoingDEATransitions s dea = [t | t <- (DEA.transitions dea), s == DEA.src t]

  addStatesAndTransitions :: AMS a -> [AMSConfig a] -> [AMSTransition a] -> AMS a
  addStatesAndTransitions ams cs ts = AMS{
                                          cfaLabel = cfaLabel ams,
                                          deaLabel = deaLabel ams,
                                          configs = cs ++ (configs ams),
                                          evolutions = ts ++ (evolutions ams)
                                        }

  matchConcreteTransition :: DataFlowLogic a -> AbstractCFA -> DEA -> AMSConfig a -> CFA.Transition -> [DEA.Transition] -> [AMSTransition a]
  matchConcreteTransition dataFlow acfa dea (s,q,vs) st [] = if s == CFA.src st
                                                            then let destConfig = (dataFlow acfa dea (s,q,vs) (Left st) Nothing)
                                                                  in [AMSTransition (s,q,vs) (Just st) Nothing destConfig]
                                                            else []
  matchConcreteTransition dataFlow acfa dea (s,q,vs) st (qt:qts) = let rest = matchConcreteTransition dataFlow acfa dea (s,q,vs) st qts
                                                            in if s == CFA.src st && q == DEA.src qt && sameEvent st qt
                                                              then let destConfig = (dataFlow acfa dea (s,q,vs) (Left st) (Just qt))
                                                                       newTransition = AMSTransition (s,q,vs) (Just st) (Just qt) destConfig
                                                                    in if guard (label qt) == Nothing
                                                                      then [newTransition]
                                                                      else rest ++ [newTransition]
                                                              else rest

  matchAbstractTransition :: DataFlowLogic a -> AbstractCFA -> DEA -> AMSConfig a -> AbstractTransition -> [DEA.Transition] -> [AMSTransition a]
  matchAbstractTransition dataFlow acfa dea (s,q,vs) ast [] = if s == asrc ast
                                                    then let destConfig = (dataFlow acfa dea (s,q,vs) (Right ast) Nothing)
                                                          in [AMSTransition (s,q,vs) Nothing Nothing destConfig]
                                                    else []
  matchAbstractTransition dataFlow acfa dea (s,q,vs) ast (qt:qts) = let rest = matchAbstractTransition dataFlow acfa dea (s,q,vs) ast qts
                                                          in if (s == asrc ast) && (q == DEA.src qt) && (sameEventAbstract ast qt)
                                                              then let destConfig = (dataFlow acfa dea (s,q,vs) (Right ast) (Just qt))
                                                                       newTransition = AMSTransition (s,q,vs) Nothing (Just qt) destConfig
                                                                    in if guard (label qt) == Nothing
                                                                      then [newTransition]
                                                                      else rest ++ [newTransition]
                                                              else rest


  sameEvent :: CFA.Transition -> DEA.Transition -> Bool
  sameEvent (CFA.Transition src dst cond act ev) (DEA.Transition dsrc ddst (GCL evv maybeCond maybeAct)) = ev == (DEAEvent evv)

  sameEventAbstract :: AbstractTransition -> DEA.Transition -> Bool
  sameEventAbstract (AbstractTransition asrc adst ev) (DEA.Transition dsrc ddst (GCL evv maybeCond maybeAct)) = ev == (DEAEvent evv)

--TODO remove transitions to states that cannot reach a bad state
--  pruneAMS ::
