(************************************************************************)
(* Copyright 2014 Edward Kmett                                          *)
(* BSD3                                                                 *)
(************************************************************************)

(* requires coq trunk newer than August 14th, 2014 *)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Program.Tactics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Specif.


Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
(* Set Primitive Projections. *)
Set Shrink Obligations.
Set Universe Polymorphism.
Generalizable All Variables.

Reserved Notation "x ~> y" (at level 90, right associativity).
Reserved Notation "x ⇒ y" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).
Reserved Notation "1".
Reserved Notation "x ~{ C }~> y" (at level 90, right associativity).

Delimit Scope category_scope with category.
Delimit Scope hom_scope with hom.
Delimit Scope path_scope with path.
Delimit Scope based_path_scope with based_path.

Local Open Scope hom_scope.

(** (based) paths *)

Inductive based_paths {A} (a: A) : A → Type :=
  refl' : based_paths a a.

Inductive paths {A} : A → A → Type :=
  refl : ∀ (a: A), paths a a.

Bind Scope path_scope with based_paths.
Bind Scope path_scope with paths.

Arguments refl' {A a}, [A] a.
Arguments refl {A a}, [A] a.
Hint Resolve @refl @refl'.

Notation "x ~ y" := (paths x y) (at level 70).
Notation "x ~{ A }~ y" := (@paths A x y) (at level 69).

Ltac path_induction :=
  intros; repeat progress (
     match goal with
     | [ p : @paths _ _ _ |- _ ] => destruct p
     | [ p : @based_paths _ _ _ |- _ ] => destruct p
     | _ => idtac
     end
  ).

Local Obligation Tactic := autounfold; program_simpl; path_induction; auto.

(* an (∞,1)-category / category up to coherent homotopy *)

Class is_category {ob : Type} (hom : ob → ob → Type) :=
{ id               : ∀ {x : ob}, hom x x where "x ~> y" := (hom x y)
; compose          : ∀ {x y z : ob}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) ~ (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h ~ f ∘ (g ∘ h)
; right_id         : ∀ {x y : ob} (f : x ~> y), f ∘ @id x ~ f
; left_id          : ∀ {x y : ob} (f : x ~> y), @id y ∘ f ~ f
; id_id            : ∀ {x : ob}, @id x ∘ @id x ~ @id x
}.

Arguments compose [ob hom !C x y z] f g : rename.
Arguments compose_assoc [ob hom !C w x y z] f g h : rename.
Arguments compose_assoc_op [ob hom !C w x y z] f g h : rename.
Arguments id [ob hom !C x] : rename.
Arguments right_id [ob hom !C x y] f : rename.
Arguments left_id [ob hom !C x y] f : rename.
Arguments id_id [ob hom !C x] : rename.

Bind Scope category_scope with is_category.

Record category :=
{ ob  :> Type
; hom : ob → ob → Type where "x ~> y" := (hom x y)
; category_is_category :> @is_category ob hom
}.

Arguments hom [!C] x y : rename.

Existing Instance category_is_category.

Bind Scope category_scope with category.
Bind Scope hom_scope with hom.

Create HintDb category discriminated.
Create HintDb hom discriminated.


Infix "~>" := hom.
Infix "~{ C }~>" := (hom (C := C)) (at level 90, right associativity).
Infix "∘" := compose : morphism_scope.

Hint Resolve compose_assoc compose_assoc_op left_id right_id id_id.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

Notation "1" := (id) : morphism_scope.
Notation "1" := (refl) : path_scope.
Notation "1" := (refl') : based_path_scope.

Open Scope morphism_scope.
Open Scope category_scope.

Class is_groupoid {ob : Type} (hom : ob → ob → Type) :=
{ is_groupoid_is_category :> is_category hom where "x ~> y" := (hom x y)
; inverse : ∀ {x y : ob}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y : ob} (f : x ~> y), inverse (inverse f) ~ f
; inverse_left_inverse : ∀ {x y : ob} (f : x ~> y), inverse f ∘ f ~ id
; inverse_right_inverse : ∀ {x y : ob} (f : x ~> y), f ∘ inverse f ~ id
}.

Record groupoid :=
{ groupoid_category :> @category
; groupoid_is_groupoid : is_groupoid (hom (C := groupoid_category))
}.

Notation "! p" := (inverse p) (at level 50) : hom_scope.

Arguments inverse               [ob hom !C] x y f%hom : rename.
Arguments inverse_inverse       [ob hom !C] x y f%hom : rename.
Arguments inverse_left_inverse  [ob hom !C] x y f%hom : rename.
Arguments inverse_right_inverse [ob hom !C] x y f%hom : rename.

Hint Resolve inverse_inverse inverse_left_inverse inverse_right_inverse.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : hom.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : path.

(** types *)

Definition types (x y : Type) := x -> y.
Hint Unfold types.
Program Instance types_is_category : is_category types.
(* Definition Types : category := {| hom := types |}. *)

Definition sets (x y : Set) := x -> y.
Hint Unfold sets.
Program Instance sets_is_category : is_category sets.
(* Definition Sets : category := {| hom := sets |}. *)

Definition fun_compose := compose (hom:=types).
Infix "∘" := fun_compose : type_scope.

(** Paths *)

Program Instance paths_is_category {A} : is_category (@paths A).
Program Instance paths_is_groupoid {A} : is_groupoid (@paths A).
Existing Instance paths_is_groupoid.
Hint Resolve paths_is_groupoid.

Definition path_compose {A} := compose (hom:=@paths A).
Definition path_inverse {A} := inverse (hom:=@paths A).

Infix "∘" := path_compose : path_scope.
Notation "! p" := (path_inverse p) (at level 50) : path_scope.

(* based paths *)

Program Instance based_paths_is_category A : is_category (@based_paths A).
Program Instance based_paths_is_groupoid A : is_groupoid (@based_paths A).

Definition based_path_compose {A} := compose (hom:=@based_paths A).
Definition based_path_inverse {A} := inverse (hom:=@based_paths A).

Infix "∘" := based_path_compose : based_path_scope.
Notation "! p" := (based_path_inverse p) (at level 50) : based_path_scope.

Section unique_id.
  Variable C : category.
  Implicit Types x y : C.

  Lemma unique_id (id0 id1 : ∀ x, x ~> x)
    (id1_left  : ∀ x y (f : x ~> y), f ~ id1 y ∘ f)
    (id0_right : ∀ x y (f : x ~> y), f ∘ id0 x ~ f)
    : ∀ x, id0 x ~ id1 x.
  Proof.
    intro.
    specialize (id1_left x x (id0 x)).
    specialize (id0_right x x (id1 x)).
    apply (compose id0_right id1_left).
  Defined.


  Definition as_left_id {x y} (f : x ~> y) (i : y ~> y) (H : i ~ id) : i ∘ f ~ f.
  Proof.
    inversion H.
    subst.
    apply left_id.
  Defined.


  Definition as_right_id {x y} (f : x ~> y) (i : x ~> x) (H: i ~ id) : f ∘ i ~ f.
  Proof.
    inversion H.
    subst.
    apply right_id.
  Defined.

End unique_id.

Arguments unique_id [!C] f i H%hom id1_left id0_right : rename.
Arguments as_left_id [!C] x y f i H%hom : rename.
Arguments as_right_id [!C] x y f i H%hom : rename.

Record functor (C: category) (D: category) :=
{ fobj :> C → D
; map : ∀ {x y : C}, (x ~> y) → (fobj x ~> fobj y)
; map_id : ∀ {x : C}, map (id (x := x)) = id
; map_compose : ∀ {x y z : C} (f : y ~> z) (g : x ~> y),
   map f ∘ map g = map (f ∘ g)
}.

(* Opposite notions *)

Section Op.
  Variable ob : Type.
  Variable hom : ob -> ob -> Type.

  Definition op (x: ob) (y: ob) : Type := hom y x.

  Hint Unfold op.

  Program Instance op_is_category { C : is_category hom } : is_category op :=
  { id := @id _ _ C
  ; compose := λ _ _ _ f g, compose (C := C) g f
  }.

  Program Instance op_is_groupoid { C : is_groupoid hom } : is_groupoid op :=
  { is_groupoid_is_category := op_is_category
  ; inverse := λ x y, @inverse _ _ C y x
  }.

End Op.

Hint Unfold op.

Arguments op_is_category [ob] hom [C].
Arguments op_is_groupoid [ob] hom [C].

(* Probably the first novel development in this file *)
Program Definition ap `(f : A -> B) : functor (paths A) (paths B).

Program Definition transportF {A : Type} (P: A -> Type) := Build_Functor (Paths A) Sets_Category P _ _ _.

Program Definition transport {A : Type} (B : A -> Type) {x y : A} : (x = y) -> B x -> B y.
Proof.
  path_induction.
  destruct H.
  apply X.
Defined.

Program Definition apd {A : Type} {B : A -> Type} {x y : A} (f: ∀ (a: A), B a) (p: x = y) :
  transport B p (f x) = f y := _.

Program Definition optransportF `(P: A -> Type) := Build_Functor (Op_Category (Paths A)) Sets_Category P _ _ _.

Program Definition optransport {A : Type} (B : A -> Type) {x y : A} : (x = y) -> B y -> B x.
Proof.
  path_induction.
  destruct H.
  apply X.
Defined.

Program Definition coe := Build_Functor (Paths Type) Sets_Category _ _ _ _.

Program Definition opcoe := Build_Functor (Op_Category (Paths Type)) Sets_Category _ _ _ _.

Program Definition based {A} := Build_Functor (Paths A) (BasedPaths A) _ _ _ _.

Program Definition debased {A} := Build_Functor (BasedPaths A) (Paths A) _ _ _ _.

(* h-levels 0..2 *)
Definition is_contractible (A : Type) := {x : A & ∀ y : A, y = x}.
Definition is_prop (A : Type) := ∀ (x y : A), x = y.
Definition is_set (A : Type) := ∀ (x y : A), is_prop (x = y).

Program Fixpoint is_level (n: nat) (A: Type) : Type :=
  match n with
  | O => is_contractible A
  | S n => ∀ (x y: A), is_level n (@paths A x y)
  end.

Program Fixpoint n_path (n : nat) (A: Type) : Type :=
  match n with
  | O => ∀ (x y : A), x = y
  | S n => ∀ (x y : A), n_path n (@paths A x y)
  end.

Definition contractible := { A : Type & is_contractible A }.
Definition prop := { A : Type & is_prop A }.
Definition set := { A : Type & is_set A }.
Definition level (n: nat) := {A : Type & is_level n A }.

(* TODO: Hedberg's theorem showing types with decidable equalities are sets *)

Program Definition path_over `(B: A -> Type) `(p : x = y) (u : B x) (v : B y):= u = v.

(* Paulin-Mohring J / based path induction *)
Program Definition J
  {A : Type}  (M : A) (C : ∀ (y : A), (based_paths M y) -> Type)
  (H : C M refl') (N : A) (P : based_paths M N) : C N P.
Proof. path_induction. auto. Defined.

(* TODO: replace these with a comma category ? *)
Definition fiber `(f : A -> B) (y : B) := { x : A & f x = y }.

Ltac contract_fiber y p :=
  match goal with
  | [ |- contractible (@fiber _ _ ?f ?x) ] =>
    eexists (existT (fun z => f z = x) y p);
      let z := fresh "z" in
      let q := fresh "q" in
        intros [z q]
  end.

(*
Higher Inductive circle : Type
  := base : circle
   | loop : base = base.
*)

Module Export circle.

  Private Inductive circle : Type := | base : circle.
  Axiom loop : base = base.

  (* dependent elimination *)
  Program Definition circle_ind (B: circle -> Type) (b : B base) (l : transport B loop b = b) (x : circle) : B x.
  Proof.
    destruct x.
    apply b.
  Defined.

  (* non-dependent elimination *)
  Program Definition circle_rect (B : Type) (b : B) (l : b = b) : circle -> B.
  Proof.
   intros.
   destruct H.
   apply b.
  Defined.

End circle.










(* a category is an (∞,1)-category, where the hom-sets are actual sets. *)
Class Category1 :=
{ category1_category :> Category
; hom_set : ∀ {x y}, is_set (x ~> y)
}.

Coercion category1_category : Category1 >-> Category.

Class ThinCategory :=
{ thincategory_category1 :> Category1
; hom_prop : ∀ {x y}, is_prop (x ~> y)
}.

Coercion thincategory_category1 : ThinCategory >-> Category1.

Class StrictCategory :=
{ strictcategory_category1 :> Category1
; ob_set : ∀ x, is_set x
}.

Coercion strictcategory_category1 : StrictCategory >-> Category1.