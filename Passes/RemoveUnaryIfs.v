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

Local Open Scope SubFunctor_scope.

Definition
  removeUnaryIfs__If1
  {V} `{FunctorLaws V}
  `{! V supports If2}
  `{! V supports Unit}
  : forall {T}, MixinAlgebra If1 T (WellFormedValue V)
  := fun _ rec '(MkIf1 condition thenBranch) =>
       if2 (rec condition) (rec thenBranch) unit.

Definition
  removeUnaryIfs__Other
  {L V} `{FunctorLaws L} `{FunctorLaws V}
  `{! V supports L}
  : forall {T}, MixinAlgebra L T (WellFormedValue V)
  := fun _ rec v => inject (fmap rec v).

Variant ForRemoveUnaryIfs := .

Global Instance Algebra__RemoveUnaryIfsIf1
  {V} `{FunctorLaws V}
  `{! V supports Unit}
  `{! V supports If2}
  : forall {T}, ProgramAlgebra ForRemoveUnaryIfs If1 T (WellFormedValue V)
| 0
  := fun T => {| programAlgebra := removeUnaryIfs__If1; |}.

Global Instance Algebra__RemoveUnaryIfsOther
  {L V} `{FunctorLaws L} `{FunctorLaws V}
  `{! V supports L}
  : forall {T}, ProgramAlgebra ForRemoveUnaryIfs L T (WellFormedValue V)
| 1
  := fun T => {| programAlgebra := removeUnaryIfs__Other; |}.

Definition removeUnaryIfs
           {L V}
           `{FunctorLaws L} `{FunctorLaws V}
           {removeUnaryIfs__L : forall T, ProgramAlgebra ForRemoveUnaryIfs L T (WellFormedValue V)}
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ _ (removeUnaryIfs__L _)).
