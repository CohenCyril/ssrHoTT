(* -*- coq-prog-args: ("-emacs" "-top" "SsrHoTT.nat") -*- *)

(*------------------------------------------------------------------------------
 In this file, we define type Nat and install a parser/printer for type Nat.
------------------------------------------------------------------------------*)

Require Import init equality.

Load "options".

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

Check 0%Nat.