(** * Alternative -- Monoidal Functor Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Monoid.
Require Import Classes.Functor.
Require Import Classes.Pointed.
Require Import Classes.Applicative.

(** * The Alternative Class **)

Class Alternative (F : Type -> Type) {FUNCTOR : Functor F}
                {POINTED : Pointed F} {APPLICATIVE : Applicative F} :=
    {   aempty : forall {a}, F a
    ;   aplus  : forall {a}, F a -> F a -> F a
    (** these are the monoid laws -- how can we state that the defs above
        should form a monoid without copypasting the definitions? **)
    ;   alternative_e_l : forall {T} (a : F T), aplus aempty a = a
    ;   alternative_e_r : forall {T} (a : F T), aplus a aempty = a
    ;   alternative_assoc : forall {T} (a b c : F T),
                aplus a (aplus b c) = aplus (aplus a b) c
    }.

(** ** common functions for monads **)

Notation "x <|> y" := (aplus x y) (at level 42).

(** * base instances **)

Instance optionAlternative : Alternative option :=
    {   aempty := fun _ => None
    ;   aplus  := fun _ x y =>
                    match x with
                    | Some v => Some v
                    | None   => y
                    end
    }.
Proof.
  reflexivity.
  intros; destruct a; reflexivity.
  intros; destruct a; reflexivity.
Defined.

