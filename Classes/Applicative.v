(** * Applicative -- Applicative Functor Type Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Lists.List.

Require Import Classes.Cat.
Require Import Classes.Functor.
Require Import Classes.Pointed.

(** * The Applicative Functor Class **)

Class Applicative (F : Type -> Type) {FUNCTOR : Functor F} {POINTED : Pointed F} :=
    {   fapp : forall {a b : Type}, F (a -> b) -> F a -> F b
    ;   fapp_id : forall {a : Type} (x : F a),
                    fapp (pure (identity (cat := FUN) a)) x = x
    ;   fapp_hom : forall {a b : Type} (f : a -> b) (x : a),
                    fapp (pure f) (pure x) = pure (f x)
    ;   fapp_compose : forall {a b c : Type} (u : F (b -> c)) (v : F (a -> b)) (w : F a),
                        (fapp (fapp (fapp (pure compose) u) v) w) =
                        fapp u (fapp v w)
    ;   fapp_lift : forall {a b : Type} (g : a -> b) (x : F a),
                      fapp (pure g) x = fmap g x
    }.

Notation "f <*> x" := (fapp f x) (at level 42).



(* ************************************************************************ *)

(** * Base Instances **)

(** ** option is an applicative functor **)

Instance optionApplicative : Applicative option :=
    {   fapp := fun _ _ Ff Fx =>
                  match Ff with
                  | Some f =>
                    match Fx with
                    | Some x => Some (f x)
                    | None   => None
                    end
                  | None   => None
                  end
    }.
Proof.
  simpl; destruct 0; reflexivity.
  reflexivity.
  simpl; intros; destruct u; destruct v; destruct w; reflexivity.
  reflexivity.
Defined.

(** ** lists are applicative **)

Fixpoint fapp_list {a b : Type} (fs0 : list (a -> b)) xs :=
  match fs0 with
  | nil => nil
  | (cons f fs) => app (fmap f xs) (fapp_list fs xs)
  end.

Instance listApplicative : Applicative list :=
    {   fapp := fun _ _ fs xs => fapp_list fs xs
    }.
Proof.
  simpl; intros; rewrite app_nil_r; apply map_id.
  reflexivity.
  (* #3 *)
  admit.
  (* #4 *)
  simpl; intros; rewrite app_nil_r; reflexivity. 
Defined.

Instance funApplicative : forall e, Applicative (FUN e) :=
    {   fapp := fun _ _ f g x => f x (g x)
    }.
Proof.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(* TODO sum, prod need monoid *)


