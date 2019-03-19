module StaticAnalysis where


import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error

import Text.Parsec hiding (try)
import Text.Parsec.String
import Solidity
--import EA.EA
import qualified DEA.DEA as DEA
import qualified CFG.CFG as CFG
import qualified StaticAnalysis.ICFG as ICFG
import qualified StaticAnalysis.CallGraph
import qualified StaticAnalysis.Parsing
import qualified StaticAnalysis.ComplianceChecking as ComplianceChecking
--import StaticAnalysis.Residuals
--import StaticAnalysis.SCSemantics
