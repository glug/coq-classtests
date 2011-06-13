(** * Base -- Base Definitions and Notations **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Export Coq.Logic.FunctionalExtensionality.

(** ** argument swapper **)

Definition flip {a b c : Type} (f : a -> b -> c) :=
  fun x y => f y x.

Notation "f $ x" := (f x) (at level 0, only parsing).
Notation "f $" := (f) (at level 0, only parsing).
Notation "$ x" := (fun f => f x) (at level 0, only parsing).

(** * Category Class **)

Class Cat (cat : Type -> Type -> Type) :=
    {   identity : forall a, cat a a
        (* explicit type parameter, otherwise @ unhides class params :-/ *)
    ;   compose : forall {a b c}, cat b c -> cat a b -> cat a c
    ;   cat_id_l : forall {a b} (p : cat a b),
          compose (@identity b) p = p
    ;   cat_id_r : forall {a b} (p : cat a b),
          compose p (@identity a) = p
    ;   cat_compose_assoc : forall {a b c d}
            (p : cat a b) (q : cat b c) (r : cat c d),
          compose (compose r q) p = compose r (compose q p)
    }.

(* this one is technically wrong but easier to type on Linux:
   compose ^ .  --> ·
   (is a mid-dot, not a dot operator or function composition symbol)
*)
Notation "g · f" := (compose g f) (at level 70, only parsing).
Notation "g ·" := (compose g) (at level 70, only parsing).
Notation "· f" := (flip compose f) (at level 70, only parsing).

(* this one is correct but harder to type *)

Notation "g ∘" := (compose g) (at level 70).
Notation "∘ f" := (flip compose f) (at level 70).
Notation "g ∘ f" := (compose g f) (at level 70).

(** * Base Instances **)

(** ** functions form a category **)

Definition FUN := (fun a b => a -> b).

Instance funCat : Cat FUN :=
    {   identity := fun _ x => x
    ;   compose := fun _ _ _ g f x => g (f x)
    }.
Proof.
  intros; extensionality x; reflexivity.
  intros; extensionality x; reflexivity.
  reflexivity.
Defined.
