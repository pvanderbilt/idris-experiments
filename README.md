# idris-experiments
Experiments with the Idris dependently-typed programming language.

# Contents

* `project/`: Experiments about proving various things (most July 2018)
    * `BaseOps`: Some core types for booleans as propositions and
       type refinement, including `IsTrue`.
    * `ListOps`: Reimplementation of basic list operations using
      boolean expressions, instead of propositions.
	  Also, experimented with using preconditions and `absurd` to handle invalid cases.
     * `EqAx`: Adding axioms to the `Eq` interface and
	  extending `Eq` for cases where it is equivalent to `Id`,
	  with proof for  some types.
    * `Fact`: A type `Fact` that allows asserting arbitrary things.
