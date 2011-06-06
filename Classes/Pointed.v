(* Pointed -- Pointed Functor Type Class *)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Classes.Functor.

(** * The Pointed Functor Class **)

Class Pointed {F : Type -> Type} (FUNCTOR : Functor F) :=
    {   pure : forall {a : Type}, a -> F a
    ;   fmap : forall {a b : Type} (f : a -> b), F a -> F b
             := @fmap F FUNCTOR
(** free theorem: this cannot be false
[[
    ;   pointed_fmap : forall {a b : Type} (g : a -> b) (x : a),
                          fmap g (pure x) = pure (g x)
]]
**)
    }.

(** * Base Instances **)

(** ** option is a pointed functor **)

Instance optionPointed : Pointed optionFunctor :=
    {   pure := Some
    }.

(** ** functions from a fixed type are pointed functors **)

Instance funPointed : forall e, Pointed (funFunctor e) :=
    {   pure := fun _ v => fun _ => v
    }.

(** ** list is a pointed functor **)

Instance listPointed : Pointed listFunctor :=
    {   pure := fun _ x => (cons x nil)
    }.

(** * Usage Example
[[
 Definition foo {F FUN} (P : @Pointed F FUN) := fmap (plus 1) (pure 3).
 Eval compute in foo listPointed.

 -> [4]
]]
**)

(* sum l/r, prod l/r do not work yet... FIXME *)

