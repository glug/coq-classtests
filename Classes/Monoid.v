(* Monoid -- Monoid Class *)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Require Import Classes.Cat.

(** * Monoid Class **)

Class Monoid (A : Type) :=
    {   mempty  : A
    ;   mappend : A -> A -> A
    ;   monoid_e_l : forall a, mappend mempty a = a
    ;   monoid_e_r : forall a, mappend a mempty = a
    ;   monoid_assoc : forall a b c,
                mappend a (mappend b c) = mappend (mappend a b) c
    }.

Definition monoid_concat {a : Type} {M : Monoid a} : list a -> a :=
  fold_right mappend mempty.

(** * Some Instances **)

Instance natPlusMonoid : Monoid nat :=
    {   mempty  := 0
    ;   mappend := plus
    }.
Proof.
  apply plus_O_n.
  intros; rewrite <- plus_n_O; reflexivity.
  apply plus_assoc.
Defined.

Instance natMultMonoid : Monoid nat :=
    {   mempty  := 1
    ;   mappend := mult
    }.
Proof.
  apply mult_1_l.
  apply mult_1_r.
  apply mult_assoc.
Defined.

Instance listAppMonoid : forall {a}, Monoid (list a) :=
    {   mempty  := nil
    ;   mappend := @app a
    }.
Proof.
  apply app_nil_l.
  apply app_nil_r.
  apply app_assoc.
Defined.

Instance endoMonoid : forall {a}, Monoid (FUN a a) :=
    {   mempty  := identity a
    ;   mappend := compose
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

(** * Derived Instances **)

Instance funMonoid : forall {e a} {M : Monoid a}, Monoid (FUN e a) :=
    {   mempty  := fun _ => mempty
    ;   mappend := fun g h =>
                      fun x => mappend (g x) (h x)
    }.
Proof.
  simpl; intros; extensionality x; rewrite monoid_e_l; reflexivity.
  simpl; intros; extensionality x; rewrite monoid_e_r; reflexivity.
  simpl; intros; extensionality x; rewrite monoid_assoc; reflexivity.
Defined.




