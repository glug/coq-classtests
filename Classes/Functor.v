(* Functor -- Functor Type Class  *)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

(** * The Functor Class **)

Class Functor (F : Type -> Type) :=
    {   fmap : forall {a b : Type} (f : a -> b), F a -> F b
    ;   fmap_id   : forall {a : Type} (v : F a), fmap (@id a) v = (@id (F a)) v
    ;   fmap_lift : forall {a b c : Type} (h : b -> c) (g : a -> b) (v : F a),
                      fmap h (fmap g v) = fmap (fun x => h (g x)) v
    }.

(** * Base Instances **)

(** ** option is a functor **)

Instance optionFunctor : Functor option :=
    {   fmap := fun _ _ f x =>
                  match x with
                  | Some v => Some (f v)
                  | None   => None
                  end
    }.
Proof.
  destruct 0; reflexivity.
  destruct 0; reflexivity.
Defined.

(** ** sum is a functor in the left or right component **)

Instance sumLeftFunctor : forall b, Functor (fun a => sum a b) :=
    {   fmap := fun _ _ f x =>
                  match x with
                  | inl v => inl (f v)
                  | inr v => inr v
                  end
    }.
Proof.
  destruct 0; reflexivity.
  destruct 0; reflexivity.
Defined.

Instance sumRightFunctor : forall a, Functor (sum a) :=
    {   fmap := fun _ _ f x =>
                  match x with
                  | inl v => inl v
                  | inr v => inr (f v)
                  end
    }.
Proof.
  destruct 0; reflexivity.
  destruct 0; reflexivity.
Defined.

(** ** prod is a functor in the left or right component **)

Instance prodLeftFunctor : forall b, Functor (fun a => a * b)%type :=
    {   fmap := fun _ _ f x =>
                  match x with
                  | (l,r) => (f l, r)
                  end
    }.
Proof.
  destruct 0; reflexivity.
  destruct 0; reflexivity.
Defined.

Instance prodRightFunctor : forall a, Functor (prod a) :=
    {   fmap := fun _ _ f x =>
                  match x with
                  | (l,r) => (l, f r)
                  end
    }.
Proof.
  destruct 0; reflexivity.
  destruct 0; reflexivity.
Defined.

(** ** functions from a fixed type are a functor **)

Instance funFunctor : forall e, Functor (fun a => e -> a) :=
    {   fmap := fun _ _ f g => fun x => f (g x)
    }.
Proof.
  intros; reflexivity.
  intros; reflexivity.
Defined.

(** ** list is a functor **)

Instance listFunctor : Functor list :=
    {   fmap := List.map
    }.
Proof.
  induction 0 as [| x xs IHxs]; simpl;
    try rewrite IHxs;
    reflexivity.
  induction 0 as [| x xs IHxs]; simpl;
    f_equal;
    try rewrite <- IHxs;
    reflexivity.
Defined.

