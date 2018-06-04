# solidity-static-analysis
WIP Static analysis for Solidity, based on https://github.com/shaunazzopardi/solidity-cfg-builder and https://github.com/gordonpace/contractlarva.


## Static Analysis with Residual/Quotient Analysis

Using a control-flow graph representation of a Solidity smart contract we attempt to prove properties (as symbolic automata, namely [Dynamic Event Automata or DEAs](https://github.com/gordonpace/contractlarva)) of smart contracts statically: by over-approximating the control-flow of a Solidity smart contract (see [solidity-cfg-builder](https://github.com/shaunazzopardi/solidity-cfg-builder), and ./EA/EA.hs) we synchronously compose with the DEAs. If the synchronous composotion is empty then the smart contract cannot violate the DEA.

The previous static analysis may fail, therefore we reduce from a DEA the parts that have been proven safe leaving a residual that we still have to prove against the smart contract. The smart contract can then be monitored with this residual DEA, e.g. by [instrumenting the smart contract with the DEA logic](https://github.com/gordonpace/contractlarva), or as a [separate smart contract](https://github.com/shaunazzopardi/ethereuem-runtime-verification/).

Limitations:
-----------------
1. Currently only limited to DEA with only bad states.

## Building the tool

Requirements: [GHC](https://www.haskell.org/ghc/) (e.g. install the full [Haskell Platform](https://www.haskell.org/platform/))

Compilation: Run the following command in the src folder:

> ghc -o solidity-static-analysis Main.hs

## Tool usage:

For correct results always make sure that the Solidity code compiles with a Solidity compiler.

To use the tool pass the location of the smart contract solidity file, the DEA property file, and the preferred location of the output to the executable, e.g. execute:

> "./solidity-static-analysis" &lt;solidity-code.sol&gt; &lt;property.dea&gt; &lt;residual.dea&gt;

## License
This project is licensed under the terms of the [Apache 2.0 license](LICENSE).
