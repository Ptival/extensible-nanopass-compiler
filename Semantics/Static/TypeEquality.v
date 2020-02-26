From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     Types
.

Definition TypeEqualityResult
           T `{Functor T}
  := TypeFix T -> bool.

Variant ForTypeEquality := .

Definition typeEquality
           {T} `{Functor T}
           {TypeEquality__T : forall R, ProgramAlgebra ForTypeEquality
                                                T R (TypeEqualityResult T)}
  : Fix T -> TypeEqualityResult T
  := mendlerFold (fun _ => programAlgebra).
