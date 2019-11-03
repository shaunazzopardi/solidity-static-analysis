module ResidualAnalysis.ResidualAnalysis where

  import Solidity.Solidity
  import ResidualAnalysis.AbstractCFA
  import ResidualAnalysis.IntraAMS as AMS
  import DEA.DEA as DEA
  import CFA.CFA as CFA
  import SMT.SMTLib2
  import Data.List
  import Debug.Trace

  bothResiduals :: (Eq a) => [AMS a] -> DEA -> DEA
  bothResiduals amss dea = guardResidual amss $ intraproceduralResidual amss dea

  intraproceduralResidual :: [AMS a] -> DEA -> DEA
  intraproceduralResidual amss dea = subDEA dea (nub $ justifyList $ intraproceduralResidual' amss)

  intraproceduralResidual' :: [AMS a] -> [Maybe DEA.Transition]
  intraproceduralResidual' [] = []
  intraproceduralResidual' (ams:amss) = [deaTrans ev | ev <- evolutions ams, (cfaTrans ev) /= Nothing] ++ (intraproceduralResidual' amss)

  justifyList :: [Maybe a] -> [a]
  justifyList [] = []
  justifyList (Nothing:rest) = justifyList rest
  justifyList ((Just thing):rest) = [thing] ++ justifyList rest

  subDEA :: DEA -> [DEA.Transition] -> DEA
  subDEA dea trans = DEA{
                    deaName = deaName dea,
                    allStates = nub ([DEA.src t | t <- DEA.transitions dea] ++ [DEA.dst t | t <- DEA.transitions dea]),
                    initialStates = initialStates dea,
                    DEA.transitions = nub [t | t <- trans, elem t (DEA.transitions dea)],
                    badStates = badStates dea,
                    acceptanceStates = acceptanceStates dea
              }

  guardResidual :: (Eq a) => [AMS a] -> DEA -> DEA
  guardResidual amss dea =  DEA{
                              deaName = deaName dea,
                              allStates = allStates dea,
                              initialStates = initialStates dea,
                              DEA.transitions = guardResidual' amss (DEA.transitions dea),
                              badStates = badStates dea,
                              acceptanceStates = acceptanceStates dea
                            }

  guardResidual' :: (Eq a) => [AMS a] -> [DEA.Transition] -> [DEA.Transition]
  guardResidual' [] _ = []
  guardResidual' _ [] = []
  guardResidual' amss (qt:qts) = let rest = guardResidual' amss qts
                                  in if guardAlwaysTrue amss qt
                                        then [DEA.Transition (DEA.src qt) (DEA.dst qt) (GCL (DEA.event $ label qt) Nothing (DEA.action $ label qt))] ++ rest
                                        else [qt] ++ rest

  guardAlwaysTrue:: (Eq a) => [AMS a] -> DEA.Transition -> Bool
  -- guardAlwaysTrue [] _ = False
  guardAlwaysTrue (ams:[]) qt = (guardAlwaysTrue' ams qt)
  guardAlwaysTrue (ams:amss) qt = (guardAlwaysTrue' ams qt) && (guardAlwaysTrue amss qt)

  guardAlwaysTrue' :: (Eq a) => AMS a -> DEA.Transition -> Bool
  guardAlwaysTrue' ams qt = let matches = [ev | ev <- evolutions ams, deaTrans ev == Just qt, (cfaTrans ev) /= Nothing]
                                statesFromWhichQTIsNotTheOnlyPossibility = [(AMS.from ev, (outgoingAMSTransitions ams (AMS.from ev) (DEA.event $ label qt))) | ev <- matches, (length (outgoingAMSTransitions ams (AMS.from ev) (DEA.event $ label qt))) > 1]
                            in (statesFromWhichQTIsNotTheOnlyPossibility == [])

  outgoingAMSTransitions :: (Eq a) => AMS a -> AMSConfig a -> DEA.Event -> [AMSTransition a]
  outgoingAMSTransitions ams c event = [ev | ev <- evolutions ams, AMS.from ev == c, usesEvent ev event]

  usesEvent :: AMSTransition a -> DEA.Event -> Bool
  usesEvent ev deaEvent = case cfaTrans ev of
                          Nothing -> False
                          Just trans -> CFA.event trans == DEAEvent deaEvent
