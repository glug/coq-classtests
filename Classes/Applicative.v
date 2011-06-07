(** * Applicative -- Applicative Functor Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Classes.Functor.
Require Import Classes.Pointed.

(** * The Applicative Functor Class **)

Class Applicative {F : Type -> Type} {FUNCTOR : Functor F} (POINTED : Pointed FUNCTOR) :=
    {   fapp : forall {a b : Type}, F (a -> b) -> F a -> F b
    ;   fmap_lift : forall {a b : Type} (g : a -> b) (x : F a),
                      fmap g x = fapp (pure g) x
    }.

Notation "f <*> x" := (fapp f x) (at level 42).



(* ************************************************************************ *)



(* option, function, sum, prod, list *)


