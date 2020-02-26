From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     Types
.

Definition TypeOfResult
           T `{Functor T}
  := option (TypeFix T).

Variant ForTypeOf := .

Definition typeOf
           {E T}
           `{Functor E} `{Functor T}
           {TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
  : Fix E -> TypeOfResult T
  := mendlerFold (fun _ => programAlgebra).
