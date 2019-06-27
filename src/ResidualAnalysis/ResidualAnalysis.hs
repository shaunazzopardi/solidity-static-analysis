module ResidualAnalysis.ResidualAnalysis where

  import Solidity.Solidity
  import ResidualAnalysis.AbstractCFA
  import ResidualAnalysis.IntraProceduralAbstractMonitoredSystem as AMS
  import DEA.DEA as DEA
  import CFA.CFA as CFA
  import SMT.SMTLib2
  import Data.List
  import Debug.Trace

  bothResiduals :: [AMS] -> DEA -> DEA
  bothResiduals amss dea = guardResidual amss $ intraproceduralResidual amss dea

  intraproceduralResidual :: [AMS] -> DEA -> DEA
  intraproceduralResidual amss dea = subDEA dea (nub $ justifyList $ intraproceduralResidual' amss)

  intraproceduralResidual' :: [AMS] -> [Maybe DEA.Transition]
  intraproceduralResidual' [] = []
  intraproceduralResidual' (ams:amss) = [deaTrans ev | ev <- evolutions ams, (cfaTrans ev) /= Nothing] ++ (intraproceduralResidual' amss)

  justifyList :: [Maybe a] -> [a]
  justifyList [] = []
  justifyList (Nothing:rest) = justifyList rest
  justifyList ((Just thing):rest) = [thing] ++ justifyList rest

  subDEA :: DEA -> [DEA.Transition] -> DEA
  subDEA dea trans = DEA{
                    daeName = daeName dea,
                    allStates = nub ([DEA.src t | t <- DEA.transitions dea] ++ [DEA.dst t | t <- DEA.transitions dea]),
                    initialStates = initialStates dea,
                    DEA.transitions = nub [t | t <- trans, elem t (DEA.transitions dea)],
                    badStates = badStates dea,
                    acceptanceStates = acceptanceStates dea
              }

  guardResidual :: [AMS] -> DEA -> DEA
  guardResidual amss dea =  DEA{
                              daeName = daeName dea,
                              allStates = allStates dea,
                              initialStates = initialStates dea,
                              DEA.transitions = guardResidual' amss (DEA.transitions dea),
                              badStates = badStates dea,
                              acceptanceStates = acceptanceStates dea
                            }

  guardResidual' :: [AMS] -> [DEA.Transition] -> [DEA.Transition]
  guardResidual' [] _ = []
  guardResidual' _ [] = []
  guardResidual' amss (qt:qts) = let rest = guardResidual' amss qts
                                  in if guardAlwaysTrue amss qt
                                        then [DEA.Transition (DEA.src qt) (DEA.dst qt) (GCL (DEA.event $ label qt) Nothing (DEA.action $ label qt))] ++ rest
                                        else [qt] ++ rest

  guardAlwaysTrue:: [AMS] -> DEA.Transition -> Bool
  -- guardAlwaysTrue [] _ = False
  guardAlwaysTrue (ams:[]) qt = (guardAlwaysTrue' ams qt)
  guardAlwaysTrue (ams:amss) qt = (guardAlwaysTrue' ams qt) && (guardAlwaysTrue amss qt)

  guardAlwaysTrue' :: AMS -> DEA.Transition -> Bool
  guardAlwaysTrue' ams qt = let matches = [ev | ev <- evolutions ams, deaTrans ev == Just qt, (cfaTrans ev) /= Nothing]
                                statesFromWhichQTIsNotTheOnlyPossibility = [(AMS.from ev, (outgoingAMSTransitions ams (AMS.from ev) (DEA.event $ label qt))) | ev <- matches, (length (outgoingAMSTransitions ams (AMS.from ev) (DEA.event $ label qt))) > 1]
                            in (statesFromWhichQTIsNotTheOnlyPossibility == [])

  outgoingAMSTransitions :: AMS -> AMSConfig -> DEA.Event -> [AMSTransition]
  outgoingAMSTransitions ams c event = [ev | ev <- evolutions ams, AMS.from ev == c, usesEvent ev event]

  usesEvent :: AMSTransition -> DEA.Event -> Bool
  usesEvent ev deaEvent = case cfaTrans ev of
                          Nothing -> False
                          Just trans -> CFA.event trans == DEAEvent deaEvent
