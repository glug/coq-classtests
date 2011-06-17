(** * Monad -- Monoidal Monad Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Monoid.
Require Import Classes.Functor.
Require Import Classes.Pointed.
Require Import Classes.Applicative.
Require Import Classes.Monad.

(** * The Monad Class **)

Class MonadPlus (F : Type -> Type) {FUNCTOR : Functor F} {POINTED : Pointed F}
        {APPLICATIVE : Applicative F} {MONAD : Monad F} :=
    {   mzero : forall {a}, F a
    ;   mplus  : forall {a}, F a -> F a -> F a
    (** these are the monoid laws -- how can we state that the defs above
        should form a monoid without copypasting the definitions? **)
    ;   mplus_e_l : forall {T} (a : F T), mplus mzero a = a
    ;   mplus_e_r : forall {T} (a : F T), mplus a mzero = a
    ;   mplus_assoc : forall {T} (a b c : F T),
                mplus a (mplus b c) = mplus (mplus a b) c
    ;   mzero_bind_l : forall {a b} {f : a -> F b}, bind  mzero f = mzero
    ;   mzero_bind_r : forall {a} {f : F a}, bind_ f mzero = @mzero a
    }.

(** * base instances **)

Instance listMPlus : MonadPlus list :=
    {   mzero := fun _ => nil
    ;   mplus := app
    }.
Proof.
  reflexivity.
  intros; rewrite app_nil_r; reflexivity.
  intros; rewrite app_assoc; reflexivity.
  reflexivity.
  induction 0; try reflexivity; simpl in *; assumption.
Defined.

Instance optionMPlus : MonadPlus option :=
    {   mzero := fun _ => None
    ;   mplus := fun _ mx my =>
                    match mx with
                    | None => my
                    | Some x => Some x
                    end
    }.
Proof.
  reflexivity.
  destruct 0; reflexivity.
  intros T a; destruct a; reflexivity.
  reflexivity.
  destruct 0; reflexivity.
Defined.

