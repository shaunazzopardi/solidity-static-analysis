module StaticAnalysis.CallGraph where

  import Solidity.Solidity
  import Data.List
  import CFG.CFG as CFG
  import StaticAnalysis.ICFG as ICFG
  import DEA.DEA as DEA
  import StaticAnalysis.Util as Util

  --add possibility that control-flow is unknown
  data CallGraph = CallGraph{
      mustCalls :: [(CFG.FunctionCFG, CFG.FunctionCFG)],
      mayCalls :: [(CFG.FunctionCFG, CFG.FunctionCFG)]
  } deriving (Eq, Ord, Show)

  data ICallGraph = ICallGraph{
      iMustCalls :: [(ICFG.IFunctionCFG, ICFG.IFunctionCFG)],
      iMayCalls :: [(ICFG.IFunctionCFG, ICFG.IFunctionCFG)]
  } deriving (Eq, Ord, Show)

  callgraph :: CFG.CFG -> CallGraph
  callgraph (CFG.CFG []) = CallGraph [] []
  callgraph (CFG.CFG funcs) = CallGraph [(func, funcc) | func <- funcs, funcc <- funcs, s <- (states func), funcc <- mustCall s (CFG.CFG funcs)] [(func, funcc) | func <- funcs, funcc <- funcs, s <- (states func), funcc <- mayCall s (CFG.CFG funcs)]


  mustCall :: CFG.State -> CFG.CFG -> [CFG.FunctionCFG]
  mustCall (CFG.FunctionCallState _ _) (CFG []) = []
  mustCall (CFG.FunctionCallState _ (CFG.OutsideFunctionCall _ _ _)) (CFG.CFG cfgs) = []
  mustCall (CFG.FunctionCallState _ (CFG.FunctionCall (Identifier "call") _)) (CFG.CFG cfgs) = []
  mustCall (CFG.FunctionCallState _ (CFG.FunctionCall name _)) cfg = maybeToList $ getFirstCFGFunctionWithName cfg name
  mustCall _ _ = []

  mayCall :: CFG.State -> CFG.CFG -> [CFG.FunctionCFG]
  mayCall (CFG.FunctionCallState _ _) (CFG []) = []
  mayCall (CFG.FunctionCallState _ (CFG.OutsideFunctionCall _ _ _)) (CFG.CFG cfgs) = cfgs
  mayCall (CFG.FunctionCallState _ (CFG.FunctionCall (Identifier "call") _)) (CFG.CFG cfgs) = cfgs
  mayCall _ _ = []

  icallgraph :: ICFG.ICFG -> ICallGraph
  icallgraph (ICFG.ICFG []) = ICallGraph [] []
  icallgraph (ICFG.ICFG funcs) = let must = (nub [(func, funcc) | func <- funcs, funcc <- funcs, s <- (ICFG.istates func), funcc <- iMustCall s (ICFG.ICFG funcs)])
                                     may = (nub [(func, funcc) | func <- funcs, funcc <- funcs, s <- (ICFG.istates func), funcc <- iMayCall s (ICFG.ICFG funcs)])
                                  in ICallGraph must may




  iMustCall :: CFG.State -> ICFG.ICFG -> [ICFG.IFunctionCFG]
  iMustCall (CFG.FunctionCallState _ (CFG.FunctionCall name _)) icfg = let called = maybeToList $ Util.getFirstFunctionWithName icfg name
                                                                          in called
  iMustCall _ _ = []

  iMayCall :: CFG.State -> ICFG.ICFG -> [ICFG.IFunctionCFG]
  iMayCall (CFG.FunctionCallState _ (CFG.OutsideFunctionCall _ _ _)) (ICFG.ICFG icfgs) = icfgs
  --iMayCall (CFG.FunctionCallState _ (CFG.FunctionCall (Identifier "call") _)) (ICFG.ICFG icfgs) = icfgs
  iMayCall _ _ = []


  maybeToList :: Maybe a -> [a]
  maybeToList Nothing = []
  maybeToList (Just x) = [x]

  getCalleesOf :: ICallGraph -> ICFG.IFunctionCFG -> [ICFG.IFunctionCFG]
  getCalleesOf icg ifunc = multipleStepsCallee icg (oneStepCallee icg ifunc)

  multipleStepsCallee :: ICallGraph -> [ICFG.IFunctionCFG] -> [ICFG.IFunctionCFG]
  multipleStepsCallee icg prev = let oneFurtherStep = nub (foldr (++) prev [oneStepCallee icg ifuncc | ifuncc <- prev])
                                    in if oneFurtherStep \\ prev == []
                                          then oneFurtherStep
                                          else multipleStepsCallee icg oneFurtherStep

  oneStepCallee :: ICallGraph -> ICFG.IFunctionCFG -> [ICFG.IFunctionCFG]
  oneStepCallee icg ifunc = [ifuncc | (ifunc, ifuncc) <- ((iMayCalls icg) ++ (iMustCalls icg))]

  eventuallyDelegates :: ICallGraph -> ICFG.IFunctionCFG -> Bool
  eventuallyDelegates icg ifunc = let allCallees = getCalleesOf icg ifunc
                                      delCalls = [s | ifunc <- allCallees, s <- istates ifunc, Util.isDelegate s]
                                    in if delCalls /= []
                                          then True
                                          else False
