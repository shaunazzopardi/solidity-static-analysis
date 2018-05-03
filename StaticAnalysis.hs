module StaticAnalysis where

import qualified DEA.DEA as DEA (State, Transition)
import qualified CFG.CFG (State, Transition)
import qualified StaticAnalysis.Residuals 
import qualified StaticAnalysis.PartialEvaluator 
import qualified StaticAnalysis.SCSemantics 
