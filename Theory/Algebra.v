From ExtensibleCompiler.Theory Require Import
     Functor
     Sum1
.

(** A classic F-algebra *)
Definition Algebra (F : Set -> Set) (A : Set)
  := F A -> A.

(**
[MixinAlgebra]s generalize F-algebras in two ways:

- like [MendlerAlgebra]s, it delays recursion by providing an operator of type
  [T -> A] to explicitly indicate recursive calls in the algebra,

- whereas [MendlerAlgebra]s quantify the type of recursive occurrences
  universally, [MixinAlgebra]s exposes the actual type.
 *)
Definition MixinAlgebra (F : Set -> Set) (T : Set) (A : Set) : Set
  := (T -> A) -> F T -> A.

(**
[MendlerAlgebra]s are like [MixinAlgebra]s, but do not expose the type of
recursive occurrences.
 *)
Definition MendlerAlgebra (F : Set -> Set) (A : Set) : Set
  := forall (R : Set), MixinAlgebra F R A.

(**
A fixed-point operator compatible with Coq's type system.  It is defined as the
set of all folds of [MendlerAlgebra]s for [F].
 *)
Definition Fix (F : Set -> Set) : Set
  := forall (A : Set), MendlerAlgebra F A -> A.

(**
Every [MendlerAlgebra] gives rise to a fold, simply by running it.
 *)
Definition mendlerFold
  {F : Set -> Set} {A : Set} (f : MendlerAlgebra F A)
  : Fix F -> A
  := fun e => e A f.

(**
Every F-[Algebra] also gives rise to a fold, that we can implement as a
[mendlerFold].
 *)
Definition
  fold
  {F : Set -> Set} {F_Functor : Functor F} {A : Set} (f : Algebra F A)
  : Fix F -> A
  := mendlerFold (fun r rec fa => f (fmap rec fa)).

(**
[wrapF] allows wrapping a functor value [F (Fix F)] into [Fix F].  In general,
we'll use a more generic wrapper for [F (Fix E)] where [E supports F].
 *)
Definition
  wrapF
  {F} (unwrapped : F (Fix F))
  : Fix F
  := fun A f
     => f _ (mendlerFold f) unwrapped.

(**
[unwrapF] allows unwrapping a value [Fix F] into [F (Fix F)].  In practice,
we'll use a more generic unwrapper intop [option (F (Fix E))].
 *)
Definition
  unwrapF
  {F : Set -> Set} {F_Functor : Functor F}
  : Fix F -> F (Fix F)
  := fold (fmap wrapF).
