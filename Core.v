(* requires coq trunk newer than August 14th, 2014 *)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Program.Tactics.

Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
Set Primitive Projections.
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

Inductive paths {A} : A → A → Type :=
  refl : ∀ (a: A), paths a a.

Bind Scope path_scope with paths.

Arguments refl {A a}, [A] a.
Hint Resolve @refl.

Notation "x = y" := (paths x y) (at level 70).
Notation "x ={ A }= y" := (@paths A x y) (at level 70).

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
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@compose _ R _ x y z _ _).

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

Hint Resolve @compose_assoc @compose_assoc_op : category morphism.
Hint Resolve @left_id @right_id @id_id : category hom.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90, right associativity) : category_scope.
Infix "∘" := compose : hom_scope.

Notation "1" := id : hom_scope.
Notation "1" := refl : path_scope.

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

(*
Definition as_left_id { C : Category } {x y : C} (f: x ~> y) i (H: i = 1) : i ∘ f = f.
Proof.
  rewrite -> H.
  path_induction.
  apply left_id.
Defined.

Arguments as_left_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

Definition as_right_id { C : Category } {x y : C} (f : x ~> y) i (H: i = 1) : f ∘ i = f.
Proof.    
  rewrite -> H.
  path_induction.
  apply right_id.
Defined.

Arguments as_right_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.
*)

(* Prefunctor *)

Record Functor :=
{ dom : Category
; cod : Category
; fobj :> dom → cod
; map : ∀ {x y : dom}, (x ~> y) → (fobj x ~> fobj y)
; map_id : ∀ {x : dom}, map (@id dom x) = @id cod (fobj x)
; map_compose : ∀ {x y z : dom} (f : y ~> z) (g : x ~> y),
   map f ∘ map g = map (f ∘ g)
}.

Program Definition ap {A B} (f : A -> B) : Functor := Build_Functor (Paths A) (Paths B) f _ _ _.

Program Definition transport {A} {P: A -> Type} : Functor := Build_Functor (Paths A) Sets_Category P _ _ _.


Definition contractible A := {x : A & ∀ y : A, y = x}.
Definition fiber {A B} (f : A -> B) (y : B) := { x : A & f x = y }.

Ltac contract_fiber y p :=
  match goal with
  | [ |- contractible (@fiber _ _ ?f ?x) ] =>
    eexists (existT (fun z => f z = x) y p);
      let z := fresh "z" in
      let q := fresh "q" in 
        intros [z q] 
  end.

(*
Theorem map_naturality A (f : A → A) (p : ∀ x, f x = x) (x y : A) (q : x = y) : 
  (p y ∘ map_path f q = q ∘ p x) % path.
*)

Definition isProp (A : Type) := ∀ (x y : A), x = y.
Definition isSet (A : Type) := ∀ (x y : A) (p q : x = y), p = q.

(* a category is an (∞,1)-category, where the hom-sets are actual sets.

*)
Class Category1 :=
{ category1_category :> Category
; hom_set : ∀ {x y}, isSet (x ~> y)
}.

Coercion category1_category : Category1 >-> Category. 

Class ThinCategory :=
{ thincategory_category1 :> Category1
; hom_prop : ∀ {x y}, isProp (x ~> y)
}.

Coercion thincategory_category1 : ThinCategory >-> Category1. 

Class StrictCategory :=
{ strictcategory_category1 :> Category1
; ob_set : ∀ x, isSet x
}.

Coercion strictcategory_category1 : StrictCategory >-> Category1.

(* Opposite notions *)

Program Instance Op_Category (C : Category) : Category :=
{ ob := C
; hom := λ x y, @hom C y x
; compose := λ x y z f g, @compose C z y x g f
; id := @id C
}.
Next Obligation. apply (@compose_assoc_op C). Defined.
Next Obligation. apply (@compose_assoc C). Defined.
Next Obligation. apply (@left_id C). Defined.
Next Obligation. apply (@right_id C). Defined.
Next Obligation. apply (@id_id C). Defined.

Program Instance Op_Groupoid (C : Groupoid) : Groupoid :=
{ groupoid_category := Op_Category C
; inverse := λ x y, @inverse C y x
}.
Next Obligation. apply (@inverse_inverse C). Defined.
Next Obligation. apply (@inverse_right_inverse C). Defined.
Next Obligation. apply (@inverse_left_inverse C). Defined.

(* TODO 
  Category with weak equivalences
  Homotopical categories
  Quillen model categories
  In enriched categories over V `hom x y` is an object in V.
  In internal categories over V `ob` as an object in V.
  Build enrichment as enrichment over bicategories.
  Then we can model the 'monoidal categories as bicategories of one object'
*)

(*

Class Op (T:Type) :=
{ op : T -> T
; op_op : ∀ (x : T), op (op x) = x 
}.

Program Instance Precategory_Op : Op Precategory :=
{ op := Op_Precategory
}.
Next Obligation. 
  unfold Op_Precategory. 
  unfold Op_Precategory_obligation_1.
  unfold Op_Precategory_obligation_2.
  simpl.
  admit.

Program Instance Pregroupoid_Op : Op Pregroupoid :=
{ op := Op_Pregroupoid
}.
Obligation 1.
  unfold Op_Pregroupoid.
  unfold Op_Pregroupoid_obligation_1.
  unfold Op_Pregroupoid_obligation_2.
  unfold Op_Pregroupoid_obligation_3.
  simpl.
  admit.

*) 

(*
Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : ∀ (x : A), R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : ∀ (x y : A), R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : ∀ (x y z : A), R y z -> R x y -> R x z.
*)