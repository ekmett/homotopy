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
Delimit Scope ob_scope with ob.
Delimit Scope hom_scope with hom.
Delimit Scope path_scope with path.

Local Open Scope hom_scope.

(** paths *)

Inductive paths {A} (a: A) : A → Type :=
  refl : paths a a.

Bind Scope path_scope with paths.

Arguments refl {A a}, [A] a.
Hint Resolve @refl.

Notation "x = y" := (paths x y) (at level 70).
Notation "x ={ A }= y" := (@paths A x y) (at level 69).

Ltac path_induction :=
  intros; repeat progress (
     match goal with
     | [ p : @paths _ _ _ |- _ ] => destruct p
     | _ => idtac
     end
  ); auto.

Local Obligation Tactic := program_simpl; path_induction.

(* An (∞, 1)-category / category up to coherent homotopy *)
Class Category :=
{ ob               :> Type
; hom              : ob → ob → Type where "x ~> y" := (hom x y)
; compose          : ∀ {x y z : ob}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) = (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h = f ∘ (g ∘ h)
; id               : ∀ {x : ob}, x ~> x
; right_id         : ∀ {x y : ob} (f : x ~> y), f ∘ @id x = f
; left_id          : ∀ {x y : ob} (f : x ~> y), @id y ∘ f = f
; id_id            : ∀ {x : ob}, @id x ∘ @id x = @id x
}.

Coercion ob : Category >-> Sortclass.

Bind Scope category_scope with Category.
Bind Scope ob_scope with ob.
Bind Scope hom_scope with hom.

Tactic Notation "evia" open_constr(y) :=
  match goal with |- ?R ?x ?z => refine (@compose _ R _ x y z _ _) end.
  
Tactic Notation "evia" := evia _.

Create HintDb category discriminated.
Create HintDb hom discriminated.

Arguments ob C%category : rename.
Arguments hom !C%category x y : rename.
Arguments compose [!C%category x%ob y%ob z%ob] f%hom g%hom : rename.
Arguments id [!C%category] x%ob : rename.
Arguments right_id [!C%category] x%ob y%ob f%hom : rename.
Arguments left_id [!C%category] x%ob y%ob f%hom : rename.
Arguments id_id [!C%category] x%ob : rename.

Hint Resolve compose_assoc compose_assoc_op : category morphism.
Hint Resolve left_id right_id id_id : category hom.
Hint Rewrite left_id right_id id_id : category.
Hint Rewrite left_id right_id id_id : hom.

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90, right associativity) : category_scope.
Infix "∘" := compose : hom_scope.

Notation "1" := (id _) : hom_scope.
Notation "1" := (refl) : path_scope.

Open Scope category_scope.

(* ∞-groupoid *)
Class Groupoid :=
{ groupoid_category :> Category
; inverse : ∀ {x y}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y} (f : x ~> y), inverse (inverse f) = f
; inverse_left_inverse : ∀ {x y} (f : x ~> y), inverse f ∘ f = id x 
; inverse_right_inverse : ∀ {x y} (f : x ~> y), f ∘ inverse f = id y 
}.

Coercion groupoid_category : Groupoid >-> Category. 

Notation "! p" := (inverse p) (at level 50) : hom_scope.

Arguments inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_left_inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_right_inverse [!C%category] x%ob y%ob f%hom : rename.

Hint Resolve @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category hom path.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : hom.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : path.

(** Sets *)

Program Instance Sets_Category : Category :=
{ ob      := Type
; hom     := λ x y, x → y
; compose := λ _ _ _ f g x, f (g x)
}.

Definition fun_compose := @compose Sets_Category.
Infix "∘" := fun_compose : type_scope.

(** Paths *)

Program Instance Paths_Category {A} : Category :=
{ ob := A
; hom := @paths A
}.

Program Instance Paths_Groupoid {A} : Groupoid :=
{ groupoid_category := @Paths_Category A
}.
 
Definition Paths A := @Paths_Groupoid A.
Definition path_compose {A} := @compose (@Paths_Category A).
Definition path_inverse {A} := @inverse (@Paths_Groupoid A).

Infix "∘" := path_compose : path_scope.
Notation "! p" := (path_inverse p) (at level 50) : path_scope.
 
Lemma unique_id {C : Category} (id0 id1 : ∀ {x : C}, x ~> x)
  (id1_left  : ∀ (x y : C) (f : x ~> y), @id1 y ∘ f = f)
  (id0_right : ∀ (x y : C) (f : x ~> y), f ∘ @id0 x = f) 
  : ∀ x, @id0 x = @id1 x.
Proof.
  intro.
  etransitivity; [ symmetry; apply id1_left | apply id0_right ].
Qed.

Definition as_left_id { C : Category } {x y : C} (f : x ~> y) (i : y ~> y) (H : i = @id C y) : i ∘ f = f.
Proof.
  rewrite -> H.
  path_induction.
  apply left_id.
Defined.

Arguments as_left_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

Definition as_right_id { C : Category } {x y : C} (f : x ~> y) (i : x ~> x) (H: i = @id C x) : f ∘ i = f.
Proof.    
  rewrite -> H.
  path_induction.
  apply right_id.
Defined.

Arguments as_right_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

Record Functor (C: Category) (D: Category) :=
{ fobj :> C → D
; map : ∀ {x y : C}, (x ~> y) → (fobj x ~> fobj y)
; map_id : ∀ {x : C}, map (@id C x) = @id D (fobj x)
; map_compose : ∀ {x y z : C} (f : y ~> z) (g : x ~> y),
   map f ∘ map g = map (f ∘ g)
}.

(* Opposite notions *)

Program Instance Op_Category (C : Category) : Category :=
{ ob := C
; hom := λ x y, @hom C y x
; compose := λ x y z f g, @compose C z y x g f
; id := @id C
}.
Next Obligation. apply compose_assoc_op. Defined.
Next Obligation. apply compose_assoc. Defined.
Next Obligation. apply left_id. Defined.
Next Obligation. apply right_id. Defined.
Next Obligation. apply id_id. Defined.

Program Instance Op_Groupoid (C : Groupoid) : Groupoid :=
{ groupoid_category := Op_Category C
; inverse := λ x y, @inverse C y x
}.
Next Obligation. apply inverse_inverse. Defined.
Next Obligation. apply inverse_right_inverse. Defined.
Next Obligation. apply inverse_left_inverse. Defined.

(* Probably the first novel development in this file *)
Program Definition ap `(f : A -> B) := Build_Functor (Paths A) (Paths B) _ _ _ _.

Program Definition transport `(P: A -> Type) := Build_Functor (Paths A) Sets_Category P _ _ _. 

Program Definition optransport `(P: A -> Type) := Build_Functor (Op_Category (Paths A)) Sets_Category P _ _ _.

Program Definition coe := Build_Functor (Paths Type) Sets_Category _ _ _ _.

Program Definition opcoe := Build_Functor (Op_Category (Paths Type)) Sets_Category _ _ _ _.
(* h-levels 0..2 *)
Definition contractible (A : Type) := {x : A & ∀ y : A, y = x}.
Definition prop (A : Type) := ∀ (x y : A), x = y.
Definition set (A : Type) := ∀ (x y : A), prop (x = y).

Program Definition path_over `(B: A -> Type) `(p : x = y) (u : B x) (v : B y):= u = v.

(* Paulin-Mohring J *)
Program Definition J 
  {A : Type}  (M : A) (C : ∀ (y : A), (paths M y) -> Type)
  (H : C M refl) (N : A) (P : paths M N) : C N P.
Proof. path_induction. Defined.

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

(* a category is an (∞,1)-category, where the hom-sets are actual sets. *)
Class Category1 :=
{ category1_category :> Category
; hom_set : ∀ {x y}, set (x ~> y)
}.

Coercion category1_category : Category1 >-> Category. 

Class ThinCategory :=
{ thincategory_category1 :> Category1
; hom_prop : ∀ {x y}, prop (x ~> y)
}.

Coercion thincategory_category1 : ThinCategory >-> Category1. 

Class StrictCategory :=
{ strictcategory_category1 :> Category1
; ob_set : ∀ x, set x
}.

Coercion strictcategory_category1 : StrictCategory >-> Category1.