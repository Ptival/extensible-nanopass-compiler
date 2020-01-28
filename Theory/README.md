# Where to start?

`Functor` describes what a functor is, and what laws it must obey.  While I
initially wanted to reuse the `Functor` definition from `coq-ext-lib`, universe
polymorphism started becoming a problem, so I just reimplemented my own `Set ->
Set` functors.

`Algebra` defines the types of algebras we will need: simple algebras, Mendler
algebras, and mixin algebras.  It also defines folds and wrap / unwrap
operations for the simpler algebras.

`SubFunctor` defines a notion of embedded functors `SubFunctor`, and carves out
among those the well-behaved ones, `WellFormedSubFunctor`.

`Sum1` defines a lifted algebraic sum for functors.

`UniversalProperty` defines the universal property for simple folds and Mendler
folds.  The property is split in two parts: the direct direction is simply a
lemma that holds for all algebras by definition, while the reverse direction is
a type class to be satisfied by each implementation of a fold.

`ProgramAlgebra` characterizes those algebras we will use for programming.
Those are essentially `MixinAlgebra`s, with some added well-formedness
properties, defined in `WellFormedProgramAlgebra`.

`ProofAlgebra` characterizes those algebras we will use for proving.  Those are
simple algebras, in that they are computationally-irrelevant, but they always
have a codomain of the form `{ e : Fix F | P e }`, such that the `e` being
returned is "equal" to the original (it computes the same way).  This is
captured in `WellFormedProofAlgebra`.
