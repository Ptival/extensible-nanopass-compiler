From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Semantics.Static Require Import
     TypeOf
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     SubFunctor
     Types
.

Local Open Scope SubFunctor.

Section Bool.

  Context
    {T}
    `{Functor T}
    `{! T supports BoolType}
  .

  Definition typeOf__Bool
    : forall R, MixinAlgebra Bool R (TypeOfResult T)
    := fun _ rec '(MkBool _) => Some boolType'.

  Global Instance TypeOf__Bool
    : forall {R}, ProgramAlgebra ForTypeOf Bool R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__Bool _ |}.

  Global Instance WellFormedMendlerProgramAlgebra__TypeOf__Bool
    : WellFormedMendlerProgramAlgebra (fun R => TypeOf__Bool).
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End Bool.
