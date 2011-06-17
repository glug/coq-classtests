(** * Pointed -- Pointed Functor Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Classes.Cat.
Require Import Classes.Monoid.
Require Import Classes.Functor.

(** * The Pointed Functor Class **)

Class Pointed (F : Type -> Type) {FUNCTOR : Functor F} :=
    {   pure : forall {a : Type}, a -> F a
(** free theorem: this cannot be false
[[
    ;   pointed_fmap : forall {a b : Type} (g : a -> b) (x : a),
                          fmap g (pure x) = pure (g x)
]]
**)
    }.

(** * Base Instances **)

(** ** option is a pointed functor **)

Instance optionPointed : Pointed option :=
    {   pure := Some
    }.

(** ** functions from a fixed type are pointed functors **)

Instance funPointed : forall e, Pointed (FUN e) :=
    {   pure := fun _ v => fun _ => v
    }.

(** ** list is a pointed functor **)

Instance listPointed : Pointed list :=
    {   pure := fun _ x => (cons x nil)
    }.

(** * Usage Example
[[
 Definition foo (F : Type -> Type)  {FF : Functor F} {P : Pointed F} := (plus 1) <$> (pure 3).
 Eval compute in foo list. (* -> [4] *)
 Eval compute in foo (FUN bool). (* -> fun (_ : bool) -> 4 *)
]]
**)

Instance sumLeftPointed : forall {R}, Pointed (fun L => sum L R) :=
    {   pure := (fun L => @inl L R)
    }.

Instance sumRightPointed : forall {L}, Pointed (sum L) :=
    {   pure := @inr L
    }.

Instance prodLeftPointed : forall {R} {M : Monoid R}, Pointed (fun L => prod L R) :=
    {   pure := fun _ x => (x, mempty)
    }.

Instance prodRightPointed : forall {L} {M : Monoid L}, Pointed (prod L) :=
    {   pure := fun _ x => (mempty, x)
    }.
