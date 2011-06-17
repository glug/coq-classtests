(** * Monad -- Monad Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Monoid.
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

Instance sumLeftMonad : forall {R}, Monad (fun L => sum L R) :=
    {   join := fun _ mmx =>
                  match mmx with
                  | inl mx => mx
                  | inr v  => inr v
                  end
    }.
Proof.
  intros; extensionality x; reflexivity.
  intros; extensionality x; destruct x; reflexivity.
  intros; extensionality x; destruct x; reflexivity.
Defined.

Instance sumRightMonad : forall {L}, Monad (sum L) :=
    {   join := fun _ mmx =>
                  match mmx with
                  | inr mx => mx
                  | inl v  => inl v
                  end
    }.
Proof.
  intros; extensionality x; reflexivity.
  intros; extensionality x; destruct x; reflexivity.
  intros; extensionality x; destruct x; reflexivity.
Defined.

Instance prodLeftMonad : forall {R} {M : Monoid R}, Monad (fun L => prod L R) :=
    {   join := fun _ mmx =>
                  match mmx with
                  | (mx, r) =>
                    match mx with
                    | (x, r2) => (x, mappend r r2)
                    end
                  end
    }.
Proof.
  intros; extensionality x; destruct x; simpl; rewrite monoid_e_l; reflexivity.
  intros; extensionality x; destruct x; simpl; rewrite monoid_e_r; reflexivity.
  intros; extensionality x; destruct x; simpl; repeat destruct p; simpl;
    rewrite monoid_assoc; reflexivity.
Defined.

Instance prodRightMonad : forall {L} {M : Monoid L}, Monad (prod L) :=
    {   join := fun _ mmx =>
                  match mmx with
                  | (l, mx) =>
                    match mx with
                    | (l2, x) => (mappend l l2, x)
                    end
                  end
    }.
Proof.
  intros; extensionality x; destruct x; simpl; rewrite monoid_e_l; reflexivity.
  intros; extensionality x; destruct x; simpl; rewrite monoid_e_r; reflexivity.
  intros; extensionality x; destruct x; simpl; repeat destruct p; simpl;
    rewrite monoid_assoc; reflexivity.
Defined.

