(*------------------------------------------------------------------------------
 In this file, we define basic datatypes and their associated notations.
------------------------------------------------------------------------------*)

Require Import init.

Load "options".

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


(** Polymorphic lists and some operations *)

Inductive List (A : Type) : Type :=
 | nil : List A
 | cons : A -> List A -> List A.
Scheme List_rect := Induction for List Sort Type.
Arguments nil [A].

Infix "::" := cons (at level 60, right associativity) : List_scope.
Delimit Scope List_scope with List.
Bind Scope List_scope with List.
