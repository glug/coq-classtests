(** * Base -- Base Definitions and Notations **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Logic.FunctionalExtensionality.

(** * Functional Helpers **)

(** ** Argument swapping **)

Definition flip {a b c : Type} (f : a -> b -> c) :=
  fun x y => f y x.

(** ** Function Composition **)

Definition compose {a b c : Type} (g : b -> c) (f : a -> b) : a -> c :=
    fun x => g (f x).

Notation "g ∘ f" := (compose g f) (at level 70).
Notation "g ∘" := (compose g) (at level 70).
Notation "∘ f" := (flip compose f) (at level 70).

(** ** Constant Function **)

Definition const {a b : Type} (v : b) :=
    fun (_:a) => v.







Class Eq (A : Type) :=
    {   eq  : A -> A -> bool
    }.

Class NEq (A : Type) :=
    {   neq : A -> A -> bool
    }.

Instance Eq_NEq : forall {A} (E : Eq A), NEq A :=
    {   neq := (negb ∘) ∘ eq
    }.

Instance NEq_Eq : forall {A} (E : NEq A), Eq A :=
    {   eq := (negb ∘) ∘ neq
    }.

Require Import Bool.

Instance BLN : NEq (list bool) :=
    { }.
  intros xs ys.
    induction xs; destruct ys.
      exact false.
      exact true.
      exact true.
      remember (eqb a b) as c.
      destruct c.
        apply IHxs.
        exact true.
Defined.

Instance BLE : Eq (list bool) := NEq_Eq BLN.


