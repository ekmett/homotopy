(* requires coq trunk newer than August 14th, 2014 *)

Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Module Export Main.

Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
(* Set Primitive Projections. *)
Set Shrink Obligations.
Set Universe Polymorphism.
Generalizable All Variables.

Reserved Notation "x ~> y" (at level 90, right associativity).
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

Arguments compose [ob hom !C x y z] f%hom g%hom : rename.
Arguments compose_assoc [ob hom !C w x y z] f%hom g%hom h%hom : rename.
Arguments compose_assoc_op [ob hom !C w x y z] f%hom g%hom h%hom : rename.
Arguments id [ob hom !C x] : rename.
Arguments right_id [ob hom !C x y] f%hom : rename.
Arguments left_id [ob hom !C x y] f%hom : rename.
Arguments id_id [ob hom !C x] : rename.

Bind Scope category_scope with is_category.

Record category :=
{ ob  :> Type
; hom :> ob → ob → Type where "x ~> y" := (hom x y)
; category_is_category :> @is_category ob hom
}.

Arguments hom [!C] x y : rename.

Existing Instance category_is_category.

Bind Scope category_scope with category.
Bind Scope hom_scope with hom.

Create HintDb category discriminated.
Create HintDb hom discriminated.

Infix "~>" := hom.
Infix "~{ C }~>" := (hom C) (at level 90, right associativity).
Infix "∘" := compose : hom_scope.

Hint Resolve compose_assoc compose_assoc_op left_id right_id id_id.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

Notation "1" := (id) : hom_scope.
Notation "1" := (refl) : path_scope.
Notation "1" := (refl') : based_path_scope.

Open Scope hom_scope.
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

Arguments inverse               [ob hom !C x y] f%hom : rename.
Arguments inverse_inverse       [ob hom !C x y] f%hom : rename.
Arguments inverse_left_inverse  [ob hom !C x y] f%hom : rename.
Arguments inverse_right_inverse [ob hom !C x y] f%hom : rename.

Hint Resolve inverse_inverse inverse_left_inverse inverse_right_inverse.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : hom.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : path.

(** types *)

Definition types (x y : Type) : Type := x -> y.
Hint Unfold types.
Program Instance types_is_category : is_category types.
Definition Types : category := {| hom := types |}.

Definition sets (x y : Set) := x -> y.
Hint Unfold sets.
Program Instance sets_is_category : is_category sets.
Definition Sets : category := {| hom := sets |}.

Definition fun_compose := compose (hom:=types).
Infix "∘" := fun_compose : type_scope.

(** Paths *)

Program Instance paths_is_category {A} : is_category (@paths A).
Program Instance paths_is_groupoid {A} : is_groupoid (@paths A).

Definition path_compose {A} := compose (hom:=@paths A).
Definition path_inverse {A} := inverse (hom:=@paths A).

Definition Paths A : category := {| hom := @paths A |}.

Infix "∘" := path_compose : path_scope.
Notation "! p" := (path_inverse p) (at level 50) : path_scope.

(* based paths *)

Program Instance based_paths_is_category A : is_category (@based_paths A).
Program Instance based_paths_is_groupoid A : is_groupoid (@based_paths A).

Definition BasedPaths A : category := {| hom := @paths A |}.

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
    intro x.
    specialize (id1_left x x (id0 x)).
    specialize (id0_right x x (id1 x)).
    apply (compose id0_right id1_left).
  Defined.

(*
  (* TODO: avoid inversion? *)
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
*)
End unique_id.

Arguments unique_id [!C] f i H%hom id1_left id0_right : rename.
(*
Arguments as_left_id [!C x y] f i H%hom : rename.
Arguments as_right_id [!C x y] f i H%hom : rename.
*)

Record functor (C: category) (D: category) :=
{ fobj :> C → D
; map : ∀ {x y : C}, (x ~> y) → fobj x ~> fobj y
; map_id : ∀ {x : C}, map (id (x := x)) ~ id
; map_compose : ∀ {x y z : C} (f : y ~> z) (g : x ~> y),
   map f ∘ map g ~ map (f ∘ g)
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

Definition Op (C : category) : category := 
{| ob := C
 ; hom := op (@hom C)
 ; category_is_category := op_is_category (@hom C)
 |}.

(* Probably the first novel development in this file *)
Program Definition ap `(f : A -> B) := Build_functor (Paths A) (Paths B) _ _ _ _.

Program Definition transportF {A : Type} (P: A -> Type) := Build_functor (Paths A) Types _ _ _ _.

Program Definition transport {A : Type} (B : A -> Type) {x y : A} (H : x ~ y) : B x -> B y := _.

Program Definition apd {A : Type} {B : A -> Type} {x y : A} (f: ∀ (a: A), B a) (p: x ~ y) :
  transport B p (f x) ~ f y := _.

Program Definition optransportF `(P: A -> Type) := Build_functor (Op (Paths A)) Types _ _ _ _.

Program Definition optransport {A : Type} (B : A -> Type) {x y : A} : (x ~ y) -> B y -> B x := _.

Program Definition coe := Build_functor (Paths Type) Types _ _ _ _.

(*
Program Definition gopf `(f : functor C D) { C' : is_groupoid C } := Build_functor (Op C) D f _ _ _.
Next Obligation.
  assert (L := inverse).
  assert (C'' := @op_is_groupoid C _ C').
  *)


(*
Program Definition opcoe := Build_functor (Op (Paths Type)) Types _ _ _ _.
Next Obligation.
  unfold opcoe_obligation_1.
  destruct X.
  apply id.
Defined.
Next Obligation.
  intros.
  unfold op.
  unfold types_is_category_obligation_2.
  unfold opcoe_obligation_2.
Defined.
*) 

Program Definition based {A} := Build_functor (Paths A) (BasedPaths A) _ _ _ _.
Program Definition debased {A} := Build_functor (BasedPaths A) (Paths A) _ _ _ _.

(* h-levels 0..2 *)
Definition is_contractible (A : Type) := {x : A & ∀ y : A, y ~ x}.
Definition is_prop (A : Type) := ∀ (x y : A), x ~ y.
Definition is_set (A : Type) := ∀ (x y : A), is_prop (x ~ y).

(*
Definition is_prop_implies_is_set (A : Type) (p : is_prop A): is_set A.
Proof.
*)

Program Fixpoint is_level (n: nat) (A: Type) : Type :=
  match n with
  | O => is_contractible A
  | S n => ∀ (x y: A), is_level n (paths x y)
  end.

Program Fixpoint n_path (n : nat) (A: Type) : Type :=
  match n with
  | O => ∀ (x y : A), x = y
  | S n => ∀ (x y : A), n_path n (paths x y)
  end.

Definition contractible := { A : Type & is_contractible A }.
Definition prop := { A : Type & is_prop A }.
Definition set := { A : Type & is_set A }.
Definition level (n: nat) := {A : Type & is_level n A }.

Definition contractible_Type (p : contractible) := projT1 p.
Coercion contractible_Type : contractible >-> Sortclass.

Definition prop_Type (p : prop) := projT1 p.
Coercion prop_Type : prop >-> Sortclass.

Definition set_Type (p : set) := projT1 p.
Coercion set_Type : set >-> Sortclass.

(* Definition sigT_Type {A: Type} {P: A → Type} (p : @sigT A P) := projT1 p. *)

(* TODO: Hedberg's theorem showing types with decidable equalities are sets *)

Program Definition path_over `(B: A -> Type) `(p : x ~ y) (u : B x) (v : B y):= u ~ v.

(* Paulin-Mohring J / based path induction *)
Program Definition J
  {A : Type}  (M : A) (C : ∀ (y : A), (based_paths M y) -> Type)
  (H : C M refl') (N : A) (P : based_paths M N) : C N P := _.

(* TODO: replace these with a comma category ? *)
Definition fiber `(f : A -> B) (y : B) := { x : A & f x ~ y }.

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
  Axiom loop : base ~ base.

  (* dependent elimination *)
  Program Definition circle_ind (B: circle -> Type) (b : B base) (l : transport B loop b ~ b) (x : circle) : B x.
  Proof.
    destruct x.
    apply b.
  Defined.

  (* non-dependent elimination *)
  Program Definition circle_rect (B : Type) (b : B) (l : b ~ b) : circle -> B.
  Proof.
   intros.
   destruct H.
   apply b.
  Defined.

End circle.

(* a 1-category is an (∞,1)-category, where the hom-sets are actual sets. *)
Class is_category1 (C : category) := 
{ is_category1_prop : ∀ {x y : C}, is_set (x ~> y)
}.

Class is_thin (C : category) := 
{ is_thin_prop : ∀ {x y : C}, is_prop (x ~> y)
}.

Class is_strict (C : category) := 
{ is_strict_prop : is_set C
}.

(*
Program Definition thin_is_category1 {C : category} (thin : is_thin C):  is_category1 C.
Proof. Admitted.

Coercion thin_is_category1  : is_thin >-> is_category1.
*)

End Main.

