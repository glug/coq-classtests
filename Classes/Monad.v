(** * Monad -- Monad Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Functor.
Require Import Classes.Pointed.
Require Import Classes.Applicative.

(** * The Monad Class **)

Class Monad (F : Type -> Type) {FUNCTOR : Functor F}
                {POINTED : Pointed F} {APPLICATIVE : Applicative F} :=
    {   join : forall {a : Type}, F (F a) -> F a
    ;   monad_id_l : forall {a}, join · pure = identity (F a)
    ;   monad_id_r : forall {a}, join · (fmap pure) = identity (F a)
    ;   monad_assoc : forall {a}, (join · join : F (F (F a)) -> F a) = (join · (fmap join))
    }.

(** ** common functions for monads **)

Definition bind {F : Type -> Type} {FF : Functor F} {PF : Pointed F} {AF : Applicative F} {MF : Monad F}
  {a b : Type} (x : F a) (f : a -> F b) : F b :=
    join (f <$> x).

Notation "x >>= f" := (bind x f) (at level 40).

Definition bind_ {F} {a b} {FF : Functor F} {PF : Pointed F} {AF : Applicative F} {MF : Monad F}
  (x : F a) (y : F b) := x >>= (fun _ => y).

Notation "x >> y" := (bind_ x y) (at level 40).

Definition mcompose {F : Type -> Type} {FF : Functor F} {PF : Pointed F} {AF : Applicative F} {MF : Monad F} {a b c : Type} :=
  fun (g : a -> F b) (h : b -> F c) =>
    join · (fmap h) · join · (fmap g).

Notation "f >=> g" := (mcompose f g) (at level 40).

(** * base instances **)

Instance optionMonad : Monad option :=
    {   join := fun _ mmx =>
                  match mmx with
                  | None => None
                  | Some mx => mx
                  end
    }.
Proof.
  reflexivity.
  intros; extensionality x; destruct x; reflexivity.
  intros; extensionality x; repeat destruct x as [x|]; reflexivity.
Defined.

Instance funMonad : forall e, Monad (FUN e) :=
    {   join := fun _ mmx x => (mmx x) x
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Fixpoint concat {a : Type} (xss : list (list a)) : list a :=
  match xss with
  | nil        => nil
  | xs :: xss' => app xs (concat xss')
  end.

Instance listMonad : Monad list :=
    {   join := fun t => concat
    }.
Proof.
  intros; extensionality xs; simpl; apply app_nil_r.
  intros; extensionality xs; simpl; induction xs as [| x xs]; simpl;
    f_equal; assumption.
  intros; extensionality xss; simpl; induction xss as [| xs xss]; simpl.
    reflexivity.
    rewrite <- IHxss; clear IHxss. induction xs as [| x xs]; simpl.
      reflexivity.
      rewrite IHxs; rewrite app_assoc; reflexivity.
Defined.

(* Continuation monad *)

Definition Cont (r a : Type) := (a -> r) -> r.

Instance contFunctor : forall {r}, Functor (Cont r) :=
    {   fmap := fun _ _ f m =>
                  fun c => m (fun x => c (f x))
    }.
Proof.
  reflexivity.
  reflexivity.
Defined.

Instance contPointed : forall {r}, Pointed (Cont r) :=
    {   pure := fun _ x => ($ x)
    }.

(* halp! *)
Program Instance contApplicative : forall {r}, Applicative (Cont r) :=
    {   fapp := fun _ _ mf mx => _
    }.
Next Obligation.
  intros.
  refine (fun c => _).
  refine (_ (fun x => x c)).
  refine (fun d => mf _).
  refine (fun x => _).
  apply d.
  refine (_ x).
  refine (fun f g => _).
  refine (_ (fun x => g x)).
  refine (fun h => mx _).
  refine (fun x => h (f x)).
Defined.
Solve Obligations using reflexivity.

Instance contMonad : forall {r}, Monad (Cont r) :=
    {   join := fun _ m c => m (fun x => x c)
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.


(* TODO sum, prod *)
