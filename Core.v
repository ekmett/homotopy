(* requires coq trunk newer than August 14th, 2014 *)

Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
(* Set Primitive Projections. *)
Set Shrink Obligations.
(* Set Universe Polymorphism. *)
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

(*
Notation "1" := (refl) : path_scope.
Notation "1" := (refl') : based_path_scope.
*)

Open Scope hom_scope.
Open Scope category_scope.

Class is_groupoid {ob : Type} (hom : ob → ob → Type) :=
{ is_groupoid_is_category :> is_category hom where "x ~> y" := (hom x y)
; inverse : ∀ {x y : ob}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y : ob} (f : x ~> y), inverse (inverse f) ~ f
; inverse_left_inverse : ∀ {x y : ob} (f : x ~> y), inverse f ∘ f ~ id
; inverse_right_inverse : ∀ {x y : ob} (f : x ~> y), f ∘ inverse f ~ id
}.

Coercion is_groupoid_is_category : is_groupoid >-> is_category.

Record groupoid :=
{ groupoid_category :> @category
; groupoid_is_groupoid :> is_groupoid (hom (C := groupoid_category))
}.

(* ; commutes : category_is_category groupoid_category ~ is_groupoid_is_category groupoid_is_groupoid *)

Existing Instance groupoid_is_groupoid.

Notation "! p" := (inverse p) (at level 40) : hom_scope.

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
Hint Unfold Paths.

Infix "∘" := path_compose : path_scope.
Notation "! p" := (path_inverse p) (at level 40) : path_scope.

(* based paths *)

Program Instance based_paths_is_category A : is_category (@based_paths A).
Program Instance based_paths_is_groupoid A : is_groupoid (@based_paths A).

Definition BasedPaths A : category := {| hom := @paths A |}.

Definition based_path_compose {A} := compose (hom:=@based_paths A).
Definition based_path_inverse {A} := inverse (hom:=@based_paths A).

Infix "∘" := based_path_compose : based_path_scope.
Notation "! p" := (based_path_inverse p) (at level 40) : based_path_scope.

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

Arguments map [C%category D%category] !F [x y] f%hom : rename.

(* Coercion map : functor >-> Funclass. *)

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
Program Definition ap `(f : A → B) := Build_functor (Paths A) (Paths B) f _ _ _.

Program Definition transport {A : Type} {P: A → Type} := Build_functor (Paths A) Types P _ _ _.

Program Definition apd {A : Type} {P : A → Type} {x y : A} (f: ∀ (a: A), P a) (p: x ~ y) :
  map transport p (f x) ~ f y := _.

Program Definition optransport {A: Type} {P: A → Type} := Build_functor (Op (Paths A)) Types _ _ _ _.

Program Definition coe := Build_functor (Paths Type) Types _ _ _ _.

Program Definition base {A} {P : A → Type} {u v : sigT P} := Build_functor (Paths A) Types _ _ _ _.

Program Definition based {A} := Build_functor (Paths A) (BasedPaths A) _ _ _ _.
Program Definition debased {A} := Build_functor (BasedPaths A) (Paths A) _ _ _ _.


Section inverses.
  Variable ob : Type.
  Variable hom : ob -> ob -> Type.
  Variable C : is_groupoid hom.

  Variable x y : ob.
  Variable f : hom x y.
  Variable g : hom y x.

  Program Definition as_left_inverse (H : g ~ !f) : g ∘ f ~ id.
  Proof.
    apply compose with (y := !f ∘ f).
    - apply paths_is_category.
    - apply (inverse_left_inverse f).
    - apply (map (ap (λ g, compose g f)) H).
  Defined.

  Program Definition as_right_inverse (H : g ~ !f) : f ∘ g ~ id.
  Proof.
    apply compose with (y := f ∘ !f).
    - apply paths_is_category.
    - apply (inverse_right_inverse f).
    - apply (map (ap (λ g, compose f g)) H).
  Defined.
End inverses.


(* h-levels 0..2 *)
Definition is_contractible (A : Type) := {x : A & ∀ y : A, y ~ x}.
Definition is_prop (A : Type) := ∀ (x y: A), is_contractible (x ~ y).
(* Definition is_prop (A : Type) := ∀ (x y : A), x ~ y. *)

Definition is_set (A : Type)  := ∀ (x y : A), is_prop (x ~ y).

(* Paulin-Mohring J / based path induction *)
Program Definition J'
  {A : Type}  (M : A) (C : ∀ (y : A), (based_paths M y) -> Type)
  (H : C M refl') (N : A) (P : based_paths M N) : C N P := _.

Program Definition J
  {A : Type}  (M : A) (C : ∀ (y : A), (@paths A M y) -> Type)
  (H : C M refl) (N : A) (P : @paths A M N) : C N P := _.

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

(* TODO: Hedberg's theorem showing types with decidable equalities are sets *)

Program Definition path_over `(B: A -> Type) `(p : x ~ y) (u : B x) (v : B y):= u ~ v.

(* TODO: replace these with a comma category ? *)
Definition fiber `(f : A → B) (y : B) := { x : A & f x ~ y }.

Ltac contract_fiber y p :=
  match goal with
  | [ |- is_contractible (@fiber _ _ ?f ?x) ] =>
    eexists (existT (fun z => f z ~ x) y p);
      let z := fresh "z" in
      let q := fresh "q" in
        intros [z q]
  end.

Definition is_weq {A B} (f : A → B) := ∀ (y : B), is_contractible (fiber f y).
Definition weq A B := { f : A → B & is_weq f }.

 
Ltac via x := apply @compose with (y := x).

Ltac category_tricks :=
  first
  [ apply compose
  ].

Program Definition opposite_ap A B (f: A -> B) (x y : A) (p : x ~ y) : ! map (ap f) p ~ map (ap f) (! p) := _.

Program Definition opposite_map `(f: functor C D) { gC : is_groupoid C}  { gD : is_groupoid D} {x y : C} (p : x ~> y) : ! map f p ~ map f (! p) := _.
Obligation 1.
  

Ltac path_tricks :=
  first
  [ apply opposite_ap
  | category_tricks
  ].


Lemma total_paths {A : Type} (P : A → Type) (x y : sigT P) (p : projT1 x ~ projT1 y) : (map transport p (projT2 x) ~ projT2 y) -> (x ~ y).
Proof.
  intros q.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.  
  path_induction.
  auto.
Defined.


Definition weq_Type {A B} (w : weq A B) : A → B := projT1 w.
Program Definition weq_types := Build_functor 
Coercion weq_Type : weq >-> Funclass.





(*
Higher Inductive circle : Type
  := base : circle
   | loop : base = base.
*)

Module Export circle.

  Private Inductive circle : Type := | base : circle.
  Axiom loop : base ~ base.

  (* dependent elimination *)
  Program Definition circle_ind (B: circle -> Type) (b : B base) (l : map (transport B) loop b ~ b) (x : circle) : B x.
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


(*
Definition is_contractible_join (A : Type) (p : is_contractible A) : is_contractible (is_contractible A).
Proof.
  destruct p.
  rapply existT.
  rapply existT.
  apply x.
  intros.
  apply (p y).
  intros.


Program Definition is_contractible_implies_is_prop (A : Type) (p : is_contractible A) : is_prop A := _.
Obligation 1.
  unfold is_prop.
  unfold is_contractible.
  assert (p' := p).
  destruct p.
  intros y z.
  rapply existT.
  - apply (! p z ∘ p y).
  - intros.



Program Definition is_prop_implies_is_set (A : Type) (p : is_prop A): is_set A := _.
Obligation 1.
  unfold is_set.
  unfold is_prop.
  unfold is_contractible.
  intros x y xy1 xy2.
  rapply existT.
  specialize (p a a).
  destruct p.
  path_induction.
  specialize (p x y).
  destruct p.
  path_induction.
  assert (q := p).
  assert (r := p).
  assert (s := p).
  specialize (p xy1).
  specialize (q xy2).
  assert (q' := inverse q).
  assert (qp := compose q' p).
  rapply existT.
  - apply qp. 
  - intros.
    path_induction.
    
  assert (blah := projT2 p).
  
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
(*
Program Definition gopf `(f : functor C D) { C' : is_groupoid C } := Build_functor (Op C) D f _ _ _.
Next Obligation.
  assert (L := inverse).
  assert (C'' := @op_is_groupoid C _ C').
  *)

(*
Lemma transport_fiber A B (f : A -> B) (x y : A) (z : B) (p : x ~ y) (q : f x ~ z) :
  map (transport (P := λ x, f x ~ z)) p q ~ q ∘ ! map (ap f) p.
Proof.
  induction p.
  via q.
  apply paths_is_category.
  via (q ∘ ! id (x := f a)). 
  apply paths_is_category.
  via (q ∘ ! id (x := f x)).
  
   
Program Definition weq_id {A} : weq A A := existT _ _ _.
Next Obligation.
  unfold is_weq.
  unfold weq_id_obligation_1.
  unfold is_contractible.
  unfold fiber.
  intros.
  rapply existT.
  rapply existT.
  apply y.
  apply refl.
  intros.
   

Program Instance weq_is_category : is_category weq.
Obligation 1.
  rapply existT.
  apply (fun x => x).
    

contract_fiber x (@refl _ x).
  


Obligation 1.
{ compose := _
}.

  *)

