# Where to start?

## Theory

The `Theory` folder contains all the theory needed to build extensible
languages.

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

## Features

This directory contains unique language features to be combined.  Some of those
features may be used to create source languages, target languages, or both.

## Passes

This directory contains compiler passes.  A compiler pass is given by a
`WellFormedProgramAlgebra` from its source language features to its target
language features.  They support a "small footprint" style of specification
where only the features needed but be declared.  The typeclass mechanism will
lift the compiler pass into any pair of source/target languages that are
supersets of the wanted features.

For instance, `RemoveUnaryIfs` contains a program algebra that compiles away
unary if constructs into binary if constructs, with a `unit` in the else
branch.  This is currently done in an untyped fashion.

Ideally, but not implemented yet, it would come with a `WellFormedProofAlgebra`
guaranteeing that the transformation is semantics-preserving w.r.t. an
evaluation semantics for the language features.
