Definition id {A : Type} (a : A) : A := a.
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (a : A) : C := g (f a).

(*
Sadly, we cannot use ext-lib's FunctorLaws because we're in [Set].  We import it
for using [id] and [compose].
 *)

Class Functor (F : Set -> Set) : Set :=
  {
    fmap : forall {A B : Set} (f : A -> B), F A -> F B;

    fmapId :
      forall (A : Set) (a : F A),
        fmap id a = a;

    fmapFusion :
      forall (A B C : Set)
        (f : A -> B)
        (g : B -> C)
        (a : F A),
        fmap g (fmap f a) = fmap (compose g f) a;

  }.
