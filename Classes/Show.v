(** * Show -- Generic String conversion Class **)
(* vim: set tw=78 ts=2 et syn=coq fdm=marker fmr={{{,}}} : *)

Require Import Coq.Arith.Arith.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Coq.Lists.List.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

Require Import Omega.
Require Import NPeano.
Require Import Recdef.

Require Import Classes.Cat.

(** * The Show Class **)

Definition showS := string -> string.

Class Show (T : Type) :=
    {   showsPrec : nat -> T -> showS
    }.

Definition shows {T : Type} {S : Show T} (x : T) := showsPrec 0 x.

Definition show {T : Type} {S : Show T} (x : T) := shows x ""%string.

(** * helper functions **)

Definition showChar : ascii -> showS :=
  String.

Definition showString : string -> showS :=
  append.

Definition showParen (p : bool) (s : showS) : showS :=
  if p
    then showChar "(" · s · showChar ")"
    else s.

(** * Base Instances **)

(* with this, show behaves similar to extraction *)
Instance ShowPropDefault : forall {a : Prop}, Show a :=
    {   showsPrec := fun _ _ => showChar "_"
    }.

Instance ShowBool : Show bool :=
    {   showsPrec := fun _ b =>
                      match b with
                      | true  => showString "true"
                      | false => showString "false"
                      end
    }.

Instance ShowUnit : Show unit :=
    {   showsPrec := fun _ _ => showString "tt"
    }.

Definition digit_of_nat n := ascii_of_nat (n + 48).

Function string_of_nat_aux n acc {measure (fun x => x) n} :=
  match n with
    | 0 => acc
    | _ => string_of_nat_aux (n / 10) (String (digit_of_nat (n mod 10)) acc)
  end.
Proof.
  intros. apply Nat.div_lt; auto with arith.
Defined.

Definition string_of_nat n :=
  match n with
    | 0 => "0"%string
    | _ => string_of_nat_aux n EmptyString
  end.

Instance ShowNat : Show nat :=
    {   showsPrec := fun _ n => showString (string_of_nat n)
    }.

Instance ShowOption : forall {a} {S : Show a}, Show (option a) :=
    {   showsPrec := fun n s =>
                      match s with
                      | Some v => (showParen $ leb 100 n) $
                                    showString "Some " · showsPrec 101 v
                      | None   => showString "None"
                      end
    }.

Instance ShowSum : forall {a b} {SA : Show a} {SB : Show b}, Show (sum a b) :=
    {   showsPrec := fun n s =>
                      match s with
                      | inl l => (showParen $ leb 100 n) $
                                  showString "inl " · showsPrec 101 l
                      | inr r => (showParen $ leb 100 n) $
                                  showString "inr " · showsPrec 101 r
                      end
    }.

Instance ShowProd : forall {a b} {SA : Show a} {SB : Show b}, Show (a * b) :=
    {   showsPrec := fun _ s =>
                      match s with
                      | (l,r) => (showParen true) $
                                    showsPrec 0 l · showString ", " · showsPrec 0 r
                      end
    }.

Fixpoint showList_ {a} {SA : Show a} (xs : list a) : showS :=
  match xs with
  | nil      => id
  | x :: xs' => showString ", " · showsPrec 0 x · showList_ xs'
  end.

Instance ShowList : forall {a} {SA : Show a}, Show (list a) :=
    {   showsPrec := fun _ xs0 =>
                      match xs0 with
                      | nil     => showString "[ ]"
                      | x :: xs => showChar "[" · showsPrec 0 x · showList_ xs · showChar "]"
                      end
    }.

Definition showHex (x : bool*bool*bool*bool) : showS :=
  let N := fun (x:bool) => match x with | true => 1 | false => 0 end in
  match x with
  | (x1,x2,x3,x4) =>
    let n := (2*(2*(2*N(x1)+N(x2))+N(x3))+N(x4)) in
    if leb n 10
      then showChar (ascii_of_nat (n+48))
      else showChar (ascii_of_nat (n+87))
  end.

Definition quoteCChar_hex (a : ascii) : showS :=
  match a with
  | Ascii a1 a2 a3 a4 b1 b2 b3 b4 =>
    showString "\x" · showHex (b4,b3,b2,b1) · showHex (a4,a3,a2,a1)
  end.

Definition quoteCChar (a : ascii) : showS :=
  let n := nat_of_ascii a in
  match n with
  |  8 => showString "\b"
  |  9 => showString "\t"
  | 10 => showString "\n"
  | 12 => showString "\f"
  | 13 => showString "\r"
  | 92 => showString "\\"
  | _  =>
    if orb (leb n 31) (leb 127 n)
      then quoteCChar_hex a
      else showChar a
  end.

Definition quoteCAscii (a : ascii) : showS :=
  if ascii_dec "'" a
    then showString "'\''"
    else showChar "'" · quoteCChar a · showChar "'".

Fixpoint quoteCString_inner (s0 : string) : showS :=
  match s0 with
  | EmptyString => id
  | String c s  =>
    if ascii_dec """" c
      then showString "\""" · quoteCString_inner s
      else quoteCChar c · quoteCString_inner s
  end.

Definition quoteCString (s : string) : showS :=
  showChar """" · quoteCString_inner s · showChar """".

Instance AsciiShow : Show ascii :=
    {    showsPrec := fun _ c => quoteCAscii c
    }.

Instance StringShow : Show string :=
    {   showsPrec := fun _ s => quoteCString s
    }.

Instance ShowSigT : forall {A} {P : A -> Type} {SA : Show A} {SP : forall a, Show (P a)}, Show (@sigT A P) :=
    {   showsPrec := fun _ s =>
                      match s with
                      | existT x P => showString "existT " ·
                                       showsPrec 101 x ·
                                       showChar " " ·
                                       showsPrec 101 P
                      end
    }.

Instance ShowSigT2 : forall {A} {P Q : A -> Type} {SA : Show A} {SP : forall a, Show (P a)} {SQ : forall a, Show (Q a)}, Show (@sigT2 A P Q) :=
    {   showsPrec := fun _ s =>
                      match s with
                      | existT2 x P Q => showString "existT2" ·
                                          showsPrec 101 x ·
                                          showChar " " ·
                                          showsPrec 101 P ·
                                          showChar " " ·
                                          showsPrec 101 Q
                      end
    }.

Instance ShowComparison : Show comparison :=
    {   showsPrec := fun _ c =>
                      match c with
                      | Eq => showString "Eq"
                      | Lt => showString "Lt"
                      | Gt => showString "Gt"
                      end
    }.

(* missing: identity (reflexive equality on Type), shadowed by Classes.Cat *)

(* prop-infected, will have holes *)

Instance ShowSig : forall {A} {P : A -> Prop} {SA : Show A} {SP : forall a, Show (P a)}, Show (@sig A P) :=
    {   showsPrec := fun _ s =>
                      match s with
                      | exist x P => showString "{" ·
                                       showsPrec 0 x ·
                                     showString " | " ·
                                       showsPrec 0 P ·
                                     showString "}"
                      end
    }.

Instance ShowSig2 : forall {A} {P Q : A -> Prop} {SA : Show A} {SP : forall a, Show (P a)} {SQ : forall a, Show (Q a)}, Show (@sig2 A P Q) :=
    {   showsPrec := fun _ s =>
                      match s with
                      | exist2 x P Q => showString "{" ·
                                          showsPrec 0 x ·
                                        showString " | " ·
                                          showsPrec 0 P ·
                                        showString " & " ·
                                          showsPrec 0 Q ·
                                        showString "}"
                      end
    }.

Instance ShowSumbool : forall {a b : Prop} {SA : Show a} {SB : Show b}, Show (sumbool a b) :=
    {   showsPrec := fun n s =>
                      match s with
                      | left l => (showParen $ leb 100 n) $
                                    showString "left " · showsPrec 101 l
                      | right r => (showParen $ leb 100 n) $
                                    showString "right " · showsPrec 101 r
                      end
    }.

Instance ShowSumor : forall {a : Type} {b : Prop} {SA : Show a} {SB : Show b}, Show (sumor a b) :=
    {   showsPrec := fun n s =>
                      match s with
                      | inleft l => (showParen $ leb 100 n) $
                                    showString "inleft " · showsPrec 101 l
                      | inright r => (showParen $ leb 100 n) $
                                    showString "inright " · showsPrec 101 r
                      end
    }.
