From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     ProofAlgebra
     UniversalProperty
.

(** [TypeFix] is just an alias for [WellFormedValue], but it makes it so that
    code that depends on wrapping types can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition TypeFix
           T `{Functor T}
  := WellFormedValue T.
