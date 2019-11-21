From ExtLib Require Import Programming.Extras.

(* Sadly, we cannot use ext-lib's FunctorLaws because we're at Set. *)

Class Functor (F : Set -> Set) : Set :=
  {
    fmap : forall {A B : Set} (f : A -> B), F A -> F B;
  }.

Class FunctorLaws {F} `{Functor F}
  :=
    {

      fmapId
      : forall (A : Set) (a : F A),
          fmap id a = a;

      fmapFusion
      : forall (A B C : Set)
          (f : A -> B)
          (g : B -> C)
          (a : F A),
        fmap g (fmap f a) = fmap (compose g f) a;

    }.
