From ExtensibleCompiler.Theory Require Import Functor.

Definition Algebra (F : Set -> Set) (A : Set)
  := F A -> A.

Definition MixinAlgebra (T : Set) (F : Set -> Set) (A : Set) : Set
  := (T -> A) -> F T -> A.

Definition MendlerAlgebra (F : Set -> Set) (A : Set) : Set
  := forall (R : Set), MixinAlgebra R F A.

Definition Fix (F : Set -> Set) : Set
  := forall (A : Set), MendlerAlgebra F A -> A.

Definition
  mendlerFold
  {F : Set -> Set} {A : Set} (f : MendlerAlgebra F A)
  : Fix F -> A
  := fun e => e A f.

Definition
  fold
  {F : Set -> Set} {F_Functor : Functor F} {A : Set} (f : Algebra F A)
  : Fix F -> A
  := mendlerFold (fun r rec fa => f (fmap rec fa)).

Definition
  wrapFix
  {F} (unwrapped : F (Fix F))
  : Fix F
  := fun A f
     => f _ (mendlerFold f) unwrapped.

Definition
  unwrapFix
  {F : Set -> Set} {F_Functor : Functor F}
  : Fix F -> F (Fix F)
  := fold (fmap wrapFix).
