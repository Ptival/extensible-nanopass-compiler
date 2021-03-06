From ExtensibleCompiler.Syntax Require Import
     Terms.If1
     Terms.If2
     Terms.Unit
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor.

Definition removeUnaryIfs__If1
           {V}
           `{Functor V}
           `{! V supports If2}
           `{! V supports Unit}
  : forall T, MixinAlgebra If1 T (WellFormedValue V)
  := fun _ rec '(MkIf1 condition thenBranch) =>
       if2 (rec condition) (rec thenBranch) unit.

Definition removeUnaryIfs__Other
           {L V}
           `{Functor L} `{Functor V}
           `{! V supports L}
  : forall T, MixinAlgebra L T (WellFormedValue V)
  := fun _ rec v => injectUP' (fmap rec v).

Variant ForRemoveUnaryIfs := .

Global Instance Algebra__RemoveUnaryIfsIf1
       {V} `{Functor V}
       `{! V supports Unit}
       `{! V supports If2}
  : forall {T}, ProgramAlgebra ForRemoveUnaryIfs If1 T (WellFormedValue V)
  := fun T => {| programAlgebra := removeUnaryIfs__If1 _ |}.

Global Instance Algebra__RemoveUnaryIfsOther
       {L V}
       `{Functor L} `{Functor V}
       `{! V supports L}
  : forall {T}, ProgramAlgebra ForRemoveUnaryIfs L T (WellFormedValue V)
  := fun T => {| programAlgebra := removeUnaryIfs__Other _ |}.

Definition removeUnaryIfs
           {L V}
           `{Functor L} `{Functor V}
           {removeUnaryIfs__L : forall T, ProgramAlgebra ForRemoveUnaryIfs L T (WellFormedValue V)}
  : Fix L -> WellFormedValue V
  := mendlerFold (fun _ => programAlgebra).
