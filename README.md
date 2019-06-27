# Static Analysis with Residual/Quotient Analysis

WIP Static analysis for verification of Solidity smart contracts, based on https://github.com/shaunazzopardi/solidity-cfg-builder and https://github.com/gordonpace/contractlarva.


We use a control-flow graph representation of a Solidity smart contract in an attempt to prove properties of smart contracts statically by over-approximating the control-flow of a Solidity smart contract (based on [solidity-cfg-builder](https://github.com/shaunazzopardi/solidity-cfg-builder), and its variable state. 

This is partially based on work presented in the proceedings of [PrePost 2017](http://staff.um.edu.mt/afra1/prepost17/), in the [EPCTS series](http://eptcs.web.cse.unsw.edu.au/content.cgi?PrePost17), and available on [arXiv](https://arxiv.org/abs/1708.07230).


## Description of Analysis

1. Each smart contract function is represented as a *control-flow automaton* (CFA) with transitions tagged with a triple containing: (i) a condition on the program variable state; (ii) a statement which transforms the program variable state; and (iii) a property event activated upon the statement's execution.

2. Each such automaton is augmented with abstract transitions (tagged only by a property event) that allows for any event to occur while at an initial, call, or end state of the program. This is used as the basis of intraprocedural analysis. Each such automaton over-approximates all the executions of the smart contract that call the corresponding function. This automaton is called an *abstract control-flow automaton* (ACFA).

3. A simple assertion propagation algorithm propagates assertions about the program variable state (implied by conditions and statements) through the explicit states of a CFA until statements that can affect the assertion is encountered. This is sound.

4. A property is represented as a [*dynamic event automaton* (DEA)](https://github.com/gordonpace/contractlarva) that uses transitions tagged with a triple of: (i) an event; (ii) a guard on the property variable state; and (iii) an action on the property variable state. 

4. An ACFA with a variable abstraction is composed with DEA, producing an *abstract monitored system* (AMS) with transitions tagged with pairs of CFA and DEA transitions, or with one of the positions containing the # symbol. When # is used instead of a CFA transition it signals the match of an abstract transition, while when instead of a DEA transition it signals no DEA transition match.

5. Then, an AMS is created for each function of the program against the given DEA.

6. An SMT solver, [z3](https://github.com/Z3Prover/z3), is called on-the-fly during construction of the AMS to determine whether it is possible for the given transition\s to activate at that point time in a real run. Given a CFA-DEA transition pair, we check that the DEA guard can hold true on the variable abstraction of the source state updated with the condition and statement of the CFA transition. While given a CFA-# pair we check that the variable abstraction of the source state updated with the condition and statement of the CFA transition is not inconsistent with the negation of the disjunction of the guards of the DEA transitions possibly activated at this point (note the DEA transitions outgoing from the same DEA state are assured to have mutually exclusive guards).

7. Each AMS is analysed to identify CFA-DEA transition pairs, extracting the DEA transitions used in this way, ignoring matches of DEA transitions with the # placeholder. The union of these DEA transitions produces a residual of the original DEA. This can sometimes be further reduced through syntatic analysis of the residual DEA.

8. Moreover, from the AMSs we can identify when a DEA transition's guard can be removed (i.e. changed to *true*), i.e. whenever it can be used in the AMS it is always used.

9. If the residual produced has no transitions then the property has been proven.



## Limitations

1. We are not dealing function modifiers, and smart contract inheritance (inline everything to enable analysis);
2. DEA script not fully supported. A file only containing the "DEA ...." part of the script should be included;
3. Reaching a call state removes every known assertion about the program state;
4. v0.4.* Solidity code.

## Requirements

1. (Required) [GHC](https://www.haskell.org/ghc/) (to compile);
2. (Required) [z3](https://github.com/Z3Prover/z3) (to prove assertions about the smart contract);
3. (Optional) [graphviz](https://www.graphviz.org/) (to visualise CFAs, ACFAs, and AMSs).

## Building the tool

Compilation: Run the following command in the src folder:

> ghc -make Main-online-smt.hs

## Tool usage:

For correct results always make sure that the Solidity code compiles with a Solidity compiler.

To use the tool pass the location of the smart contract solidity file, the DEA property file, and the preferred location of the output to the executable, e.g. execute:

> "./Main-online-smt" &lt;solidity-code.sol&gt; &lt;property.dea&gt; &lt;cfa.txt&gt; &lt;acfa.txt&gt; &lt;ams.txt&gt; &lt;residual.dea&gt;

## License
This project is licensed under the terms of the [Apache 2.0 license](LICENSE).
