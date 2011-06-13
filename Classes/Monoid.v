(* Monoid -- Monoid Class *)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Require Import Classes.Cat.

(** * Monoid Class **)

Class Monoid (A : Type) :=
    {   e   : A
    ;   add : A -> A -> A
    ;   monoid_e_l : forall a, add e a = a
    ;   monoid_e_r : forall a, add a e = a
    ;   monoid_assoc : forall a b c, add a (add b c) = add (add a b) c
    }.

(** * Some Instances **)

Instance natPlusMonoid : Monoid nat :=
    { e   := 0
    ; add := plus
    }.
Proof.
  apply plus_O_n.
  intros; rewrite <- plus_n_O; reflexivity.
  apply plus_assoc.
Defined.

Instance natMultMonoid : Monoid nat :=
    { e   := 1
    ; add := mult
    }.
Proof.
  apply mult_1_l.
  apply mult_1_r.
  apply mult_assoc.
Defined.

Instance listConcMonoid : forall {a}, Monoid (list a) :=
    { e   := nil
    ; add := @app a
    }.
Proof.
  apply app_nil_l.
  apply app_nil_r.
  apply app_assoc.
Defined.







