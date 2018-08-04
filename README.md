# idris-experiments
Experiments with [Idris](http://idris-lang.org/), a dependently-typed programming language.

Most of this was in response to discussions at the [SF Types, Theorems and Programming
Languages Meetup](https://www.meetup.com/SF-Types-Theorems-and-Programming-Languages/),
mostly in 2018.

## Contents

* `projects/`: Experiments about proving various things (most recent first):
    * `Mod2`: Made a start at proving that `mod n` forms a group.
	I'm stuck at proving any non-trivial axiom.  (Aug 2018)
    * `Mod1`:  Some previous attempts at `mod n`, where I represented it by `(k : Nat ** LT k n)`
	and `(k : Nat ** IsTrue(k<n))`.
    * `Category`: Defined category theory in Idris. (July 2018)
    * `Fact`: Defined a type `Fact` that allows asserting arbitrary things.
    * `EqAx`: Defined an `EqAx` interface which adds axioms to the `Eq` interface.
    	 Also defined an interface that extends `Eq` for cases where it is equivalent to `Id`.
    	 Includes proofs for  some types.
    * `ListOps`: Reimplemented basic list operations using
      boolean expressions instead of propositions.
	  Also, experimented with using preconditions and `absurd` to handle invalid cases.
    * `BaseOps`: Defined some core types for booleans as propositions and
       type refinement, including `IsTrue`.

