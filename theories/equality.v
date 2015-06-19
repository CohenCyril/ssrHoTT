(*------------------------------------------------------------------------------
 In this file, we define Equality and its basic properties.
------------------------------------------------------------------------------*)

Require Import init datatypes.

Load "options".


(** Eq type *)
Inductive Eq (A : Type) (a : A) : A -> Type := Eq_refl : Eq a a.
Scheme Eq_rect := Induction for Eq Sort Type.
Hint Resolve Eq_refl: core.
Arguments Eq {A} _ _ .
Arguments Eq_refl {A a} , [A] a , A a.
Arguments Eq_rect [A] x P Prefl y exy : rename.

Delimit Scope Eq_scope with Eq.
Notation "x = y :> A" := (@Eq A x y)%Eq : Eq_scope.
Notation "x = y" := (x = y :>_)%Eq : Eq_scope.
Notation "x <> y  :> T" := (~ x = y :>T)%Eq : Eq_scope.
Notation "x <> y" := (x <> y :>_)%Eq : Eq_scope.

Open Scope Eq_scope.

(** Another way of interpreting booleans as propositions *)

(* Definition is_true b := b = true. *)

(** Polymorphic lists and some operations *)

Inductive List (A : Type) : Type :=
 | nil : List A
 | cons : A -> List A -> List A.
Scheme List_rect := Induction for List Sort Type.
Arguments nil [A].

Infix "::" := cons (at level 60, right associativity) : List_scope.
Delimit Scope List_scope with List.
Bind Scope List_scope with List.


Section Eq_is_a_congruence.

Variables (A B : Type) (x y z : A).

Definition Eq_sym (p : Eq x y) : y = x := match p with Eq_refl => Eq_refl end.

Definition Eq_trans (p1 : Eq x y) : y = z ->  x = z :=
  match p1 with Eq_refl => fun p => p end.

Definition Eq_congr1 (f : A -> B) (p : x = y) : f x = f y :=
 match p with Eq_refl => Eq_refl end.


(* Lemma not_Eq_sym : ~ (Eq x y) -> ~ (Eq y x). *)
(* Proof. *)
(* red; intros H H'; apply H; destruct H'; trivial. *)
(* Qed. *)

End Eq_is_a_congruence.

Lemma Eq_congr2 (A B C : Type) (f : A -> B -> C)
 (x1 y1 : A) (x2 y2 : B) (p1 : x1 = y1) (p2 : x2 = y2) :  f x1 x2 = f y1 y2.
Proof.
destruct p1; destruct p2; reflexivity.
Qed.


Definition Eq_ind_r :
  forall (A : Type) (a : A) (P : A -> Prop), P a -> forall y : A, Eq y a -> P y.
 intros A x P H y H0; case Eq_sym with (1 := H0); trivial.
Defined.

Definition Eq_rec_r :
  forall (A : Type) (a : A) (P : A -> Set), P a -> forall y : A, y = a -> P y.
 intros A x P H y H0; case Eq_sym with (1 := H0); trivial.
Defined.

Definition Eq_rect_r :
  forall (A : Type) (a : A) (P : A -> Type), P a -> forall y : A, y = a -> P y.
 intros A x P H y H0; case Eq_sym with (1 := H0); trivial.
Defined.

Hint Immediate Eq_sym (* not_Eq_sym*): core v62.
