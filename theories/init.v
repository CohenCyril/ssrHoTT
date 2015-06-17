Set Implicit Arguments.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Local Unset Elimination Schemes.

(** These are the notations whose level and associativity are imposed by Coq *)

(** Notations for propositional connectives *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "x ^ y" (at level 30, right associativity).

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )" (at level 0).

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level than "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).

Delimit Scope type_scope with type.
Delimit Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.

(** ML Tactic Notations *)

Declare ML Module "coretactics".
Declare ML Module "extratactics".
Declare ML Module "eauto".
Declare ML Module "g_class".
Declare ML Module "g_eqdecide".
Declare ML Module "g_rewrite".
Declare ML Module "tauto".


(* Logic *)
Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

Inductive Unit : Type := tt : Unit.
Scheme Unit_rect := Induction for Unit Sort Type.
Hint Resolve tt : core.

Inductive Empty : Type :=.
Scheme Empty_rect := Induction for Empty Sort Type.

Definition Not (A : Type) : Type := A -> Empty.
Notation "~ x" := (Not x) : type_scope.
Hint Unfold Not : core.

(* Datatypes *)
Inductive Option (A : Type) : Type :=
  | Some : A -> Option A
  | None : Option A.
Scheme Option_rect := Induction for Option Sort Type.
Arguments None [A].

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive Sum (A B : Type) : Type :=
  | inl : A -> Sum A B
  | inr : B -> Sum A B.
Scheme Sum_rect := Induction for Sum Sort Type.
Notation "x + y" := (Sum x y) : type_scope.
Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* Notation "A \/ B" := (A + B)%type (only parsing) : type_scope. *)
(* Notation or := sum (only parsing). *)

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

(* Record prod (A B : Type) := pair { fst : A ; snd : B }. *)

(* Scheme prod_rect := Induction for prod Sort Type. *)

(* Arguments pair {A B} _ _. *)
(* Arguments fst {A B} _ / . *)
(* Arguments snd {A B} _ / . *)

(* Add Printing Let prod. *)

(* Notation "x * y" := (prod x y) : type_scope. *)
(* Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope. *)
(* Notation "A /\ B" := (prod A B) (only parsing) : type_scope. *)
(* Notation and := prod (only parsing). *)
(* Notation conj := pair (only parsing). *)

(* Hint Resolve pair inl inr : core. *)

(* Definition prod_curry (A B C : Type) (f : A -> B -> C) *)
(*   (p : prod A B) : C := f (fst p) (snd p). *)

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

(* Definition iff (A B : Type) := prod (A -> B) (B -> A). *)

(* Notation "A <-> B" := (iff A B) : type_scope. *)

(* Natural numbers. *)
Inductive Nat : Type := O : Nat | S : Nat -> Nat.
Scheme Nat_rect := Induction for Nat Sort Type.


(* It would be nice not to need this, but the tactic [induction] requires it when the target is in [Set], and the above definition of [nat] puts it in [Set]. *)
(* Scheme nat_rec := Induction for nat Sort Set. *)

Delimit Scope Nat_scope with Nat.
Bind Scope Nat_scope with Nat.
Arguments S _%Nat.
Arguments S _.

Declare ML Module "ssrhott_nat_syntax_plugin".

(* Open Scope Nat_scope. *)

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
