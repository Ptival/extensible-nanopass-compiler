# Where to start?

A compiler pass is given by a `WellFormedProgramAlgebra` from its source
language features to its target language features.  They support a "small
footprint" style of specification where only the features needed but be
declared.  The typeclass mechanism will lift the compiler pass into any pair of
source/target languages that are supersets of the wanted features.

For instance, `RemoveUnaryIfs` contains a program algebra that compiles away
unary if constructs into binary if constructs, with a `unit` in the else branch.
This is currently done in an untyped fashion.

Ideally, but not implemented yet, it would come with a `WellFormedProofAlgebra`
guaranteeing that the transformation is semantics-preserving w.r.t. an
evaluation semantics for the language features.
