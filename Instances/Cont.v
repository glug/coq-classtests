(** * Cont -- Continuations **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Functor.
Require Import Classes.Pointed.
Require Import Classes.Applicative.
Require Import Classes.Monad.

(** * Continuation monad **)

Definition Cont (r a : Type) := (a -> r) -> r.

Instance contFunctor : forall {r}, Functor (Cont r) :=
    {   fmap := fun _ _ f cx cont =>
                  cx (fun x => cont (f x))
    }.
Proof.
  reflexivity.
  reflexivity.
Defined.

Instance contPointed : forall {r}, Pointed (Cont r) :=
    {   pure := fun _ x cont => (cont x)
    }.

Instance contApplicative : forall {r}, Applicative (Cont r) :=
    {   fapp := fun _ _ cf cx cont =>
                  cf (fun f =>
                    cx (fun x =>
                      cont (f x)))
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Instance contMonad : forall {r}, Monad (Cont r) :=
    {   join := fun _ ccx cont => ccx (fun cx => cx cont )
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

