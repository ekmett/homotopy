Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Export Homotopy.Category.
Require Export Homotopy.Sigma.

Set Automatic Introduction.
Set Implicit Arguments.
Set Shrink Obligations.
Set Universe Polymorphism.

(** H-Levels *)

(* h-levels 0..2 *)
Definition is_contractible (A : Type) := {x : A & ∀ y : A, y ~ x}.
Definition is_prop (A : Type) := ∀ (x y : A), is_contractible (x ~ y).
Definition is_set (A : Type)  := ∀ (x y : A), is_prop (x ~ y).

Program Fixpoint is_level (n: nat) (A: Type) : Type :=
  match n with
  | O => is_contractible A
  | S n => ∀ (x y: A), is_level n (paths x y)
  end.

Program Fixpoint n_path (n : nat) (A: Type) : Type :=
  match n with
  | O => ∀ (x y : A), x ~ y
  | S n => ∀ (x y : A), n_path n (paths x y)
  end.

Definition contractible := sigT is_contractible.
Definition prop := sigT is_prop.
Definition set := sigT is_set.
Definition level (n: nat) := sigT (is_level n).

Definition contractible_Type (p : contractible) := p.1.
Coercion contractible_Type : contractible >-> Sortclass.

Definition prop_Type (p : prop) := p.1.
Coercion prop_Type : prop >-> Sortclass.

Definition set_Type (p : set) := p.1.
Coercion set_Type : set >-> Sortclass.

Definition level_Type {n} (p : level n) := p.1.
Coercion level_Type : level >-> Sortclass.

Class is_category1 (C : category) :=
  is_category1_prop : ∀ {x y : C}, is_set (x ~> y).

Class is_thin (C : category) :=
  is_thin_prop : ∀ {x y : C}, is_prop (x ~> y).

Class is_strict (C : category) :=
  is_strict_prop : is_set C.
