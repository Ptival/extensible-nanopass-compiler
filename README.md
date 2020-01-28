# What is this?

TODO

# Notes

Throughout the code base, we try to have a consistent use of abbreviations.
Here are most of those abbreviations and their meaning:

- `T` will stand for an extensible functor of types,
- `E` will stand for an extensible functor of expressions,
- `V` will stand for an extensible functor of values (the results of evaluation,
  often a subset of expressions),
- `B` will stand for an extensible functor of binders (really, variables, but
  the letter `V` was already used, so `B` it is...),
- `R` will stand for a recursive occurrence of any functor: many definitions of
  a concrete functor must recursively call their extension, `R` is how they do
  so, in an open-recursion style,
- `UP` stands for the universal property of folds, as described in the
  Meta-Theory à la Carte paper, in the direct direction,
- `UP'` stands for the universal property of folds, as described in the
  Meta-Theory à la Carte paper, in the reverse direction,
- the subscript `__F` is used to indicate that a function returns a raw fixed
  point of its extension functor, rather than the usual existential package of
  said value with its reverse universal property proof.

# Where to start?

## [Theory](./Theory)

Contains all the theory needed to build extensible languages, their static and
dynamic semantics, the statement of soundness of those semantics, etc.

## [Syntax](./Syntax)

Contains the definition of extensible type and term language features to be
combined.  Features can be used as part of the source or target language of a
program transformation, or even both.

## [Semantics](./Semantics)

Contains many extensible, static and dynamic semantics for the language features
defined in [Syntax](./Syntax).

## [Passes](./Passes)

Contains extensible compiler passes.  Those define transformations from a given
subset of input features to a given subset of output features.
