# solidity-static-analysis
WIP Static analysis for Solidity, based on https://github.com/shaunazzopardi/solidity-cfg-builder and https://github.com/gordonpace/contractlarva.

Tools
---

Over-approximation based Static Analysis (α)
-----------

Using a control-flow graph representation of a Solidity smart contract we attempt to prove properties (as symbolic automata, namely [Dynamic Event Automata or DEAs](https://github.com/gordonpace/contractlarva)) of smart contracts statically. This is constructed by considering every possible configuration of function calls. See ./StaticAnalysis/SCSemantics.hs

Residual/Quotient Analysis (α)
-----------

The previous static analysis may fail, therefore we are developing methods to reduce from a property parts that can be proved safe using residual analysis, leaving a residual that we still have to prove against the smart contract. See ./StaticAnalysis/Residuals.hs

Features:

1. This contains utilities to perform a reachability reduction of a DEA (limited to DEAs with only bad states).
2. Synchronous compositions of a DEA with a control-flow graph
3. Residuals of a DEA against a control-flow graph
4. (WIP) Residual of a DEA against a DEA (i.e. can be used to reduce the first DEA with what the second DEA ensures, so that we can just monitor the residual and the second DEA).

Monitoring Smart Contracts (α)
-----------
(Not static analysis, will be moved out of here at some point)

https://github.com/gordonpace/contractlarva monitors smart contracts for properties as symbolic automata by instrumenting smart contract with business logic of the properties. Here we are working on a tool to move this logic to its own smart contract, with the monitored smart contract calling this monitor upon a given event. See ./DEAToSC.hs and ./DEA/ParsingToSmartContract.hs

Current limitations: 

1. Instrumentation in original smart contract must be done manually (i.e. <i>call</i>s or <i>delegatecall</i>s to the respective event trigger method in the monitor smart contract).
2. Event trigger methods in the monitor smart contract have untyped parameters that need to be manually typed.

Partial Evaluator (experimental)
-----------

I am also currently attempting to develop a partial evaluation approach to Solidity smart contracts, which could be used to strengthen the current static analysis that ignores variable state.
