(* requires coq trunk newer than August 14th, 2014 *)

Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Import Homotopy.Core.

Set Automatic Introduction.
Set Implicit Arguments.
Set Shrink Obligations.
Set Universe Polymorphism.

(* Product categories *)
Program Definition Product (C D : category) : category :=
 {| ob := prod (ob C) (ob D)
  ; hom := λ x y, prod (hom C (fst x) (fst y)) (hom D (snd x) (snd y))
 |}.
Obligation 1.
  apply pair.
  - apply id.
  - apply id.
Defined.
Obligation 2.
  simpl in *. 
  apply pair.
  - apply (compose h1 h).
  - apply (compose h2 h0).   
Defined.
Obligation 3.
  simpl in *.
  apply path_compose with (y := (h3 ∘ (h1 ∘ h), (h4 ∘ h2) ∘ h0)).
  - apply (ap (λ x, (x, (h4 ∘ h2) ∘ h0)) (compose_assoc (C := C) h3 h1 h)).
  - apply (ap (λ x, (h3 ∘ (h1 ∘ h), x)) (compose_assoc (C := D) h4 h2 h0)).
Defined.
Obligation 4.
  simpl in *.
  apply path_compose with (y := ((h3 ∘ h1) ∘ h, h4 ∘ (h2 ∘ h0))).
  - apply (ap (λ x, (x, (h4 ∘ (h2 ∘ h0)))) (compose_assoc_op (C := C) h3 h1 h)).
  - apply (ap (λ x, ((h3 ∘ h1) ∘ h, x)) (compose_assoc_op (C := D) h4 h2 h0)).
Defined.
Obligation 5.
  simpl in *.
  apply path_compose with (y := (h ∘ 1, h0)).
  - apply (ap (λ x, (x, h0))   (right_id (C := C) h)).
  - apply (ap (λ x, (h ∘ 1, x)) (right_id (C := D) h0)). 
Defined.
Obligation 6.
  simpl in *.
  apply path_compose with (y := (1 ∘ h, h0)).
  - apply (ap (λ x, (x, h0))   (left_id (C := C) h)).
  - apply (ap (λ x, (1 ∘ h, x)) (left_id (C := D) h0)). 
Defined.  
Obligation 7.
  simpl in *.
  apply path_compose with (y := (1 ∘ 1, 1)).
  - apply (ap (λ x, (x, 1)) (id_id (C := C))).
  - apply (ap (λ x, (1 ∘ 1, x)) (id_id (C := D))).
Defined.

Notation "C * D" := (Product C D) : category_scope.


(** Uniqueness of identity *)
Section unique_id.
  Variable C : category.
  Implicit Types x y : C.

  Definition unique_id (id0 id1 : ∀ x, x ~> x)
    (id1_left  : ∀ x y (f : x ~> y), f ~ id1 y ∘ f)
    (id0_right : ∀ x y (f : x ~> y), f ∘ id0 x ~ f)
    (x: C) : id0 x ~ id1 x :=
      id0_right x x (id1 x) ∘ id1_left x x (id0 x).

  Program Definition as_left_id {x y} (f : x ~> y) (i : y ~> y) (H : i ~ id) : i ∘ f ~ f :=
    left_id f ∘ ap (λ i, i ∘ f) H.

  Definition as_right_id {x y} (f : x ~> y) (i : x ~> x) (H: i ~ id) : f ∘ i ~ f :=
    right_id f ∘ ap (compose f) H.
End unique_id.

Arguments unique_id [C] f i H%hom id1_left id0_right : rename.
Arguments as_left_id [C x y] f i H%hom : rename.
Arguments as_right_id [C x y] f i H%hom : rename.

Section inverses.
  Variable C : groupoid.

  Variable x y : C.
  Variable f : C x y.
  Variable g : C y x.

  Program Definition as_left_inverse (H : g ~ inverse f) : g ∘ f ~ id :=
    inverse_left_inverse f ∘ ap (λ g, g ∘ f) H.

  Program Definition as_right_inverse (H : g ~ inverse f) : f ∘ g ~ id :=
    inverse_right_inverse f ∘ ap (compose f) H.

End inverses.

(** H-Levels *)

(* h-levels 0..2 *)
Definition is_contractible (A : Type) := {x : A & ∀ y : A, y ~ x}.
Definition is_prop (A : Type) := ∀ (x y : A), is_contractible (x ~ y).
Definition is_set (A : Type)  := ∀ (x y : A), is_prop (x ~ y).

(* Paulin-Mohring J / based path induction *)
Program Definition J
  {A : Type}  (M : A) (C : ∀ (y : A), (based_paths M y) -> Type)
  (H : C M refl') (N : A) (P : based_paths M N) : C N P := _.

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

Program Definition opap A B (f: A -> B) (x y : A) (p : x ~ y) : inverse (ap f p) ~ ap f (inverse p) := _.

Lemma total_paths {A : Type} (P : A → Type) (x y : sigT P) (p : x.1 ~ y.1) (q : p # x.2 ~ y.2) : x ~ y.
Proof.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.
  path_induction.
  auto.
Defined.

Program Definition transportD {A : Type} (B : A → Type) (C : ∀ a:A, B a → Type)
  {x1 x2 : A} (p : x1 ~ x2) (y : B x1) (z : C x1 y) : C x2 (p # y) := _.

(*
Definition transport_forall
  {A : Type} {P : A -> Type} {C : ∀ x, P x -> Type}
  {x1 x2 : A} (p : x1 ~ x2) (f : forall y : P x1, C x1 y)
  : (transport (λ x, ∀ y : P x, C x y) p f)
 == (λ y => transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y))))
  := match p with idpath => fun _ => 1 end.
*)


(*
Section category_eq.
  Variable C D  : category.
  Variable obs  : ob C ~ ob D.

  Program Definition transport_hom 
     : (ob C → ob C → Type) -> ob D -> ob D -> Type
     := transport (λ x, x -> x -> Type) obs.


  Definition homC' := transport_hom (hom C).

  Variable homs : homC' ~ hom D.


  Program Definition transport_id := _ (@id C) ~ @id D.
  Obligation 1.
   intros.
   assert (x0' := transport (fun x => x) (inverse obs) x0).

   specialize (x x0').

   assert (l := @ap12 ).
     f_ap.

   rapply (ap11 (λ  homs).
   assert ( := inverse obs # x0).
   apply (transport (λ x, D x x) obs).



  Definition transport_id' := transport_id homs.


End category_eq.
*)


Definition weq_Type {A B : Type} (w : weq A B) : A → B := w.1 .

Program Definition id_functor (C : category) := Build_functor C C _ _ _ _.

Program Definition compose_functor {C D E : category}
  (G : functor D E) (F: functor C D) :=
{| map_ob := λ x, map_ob G (map_ob F x)
 ; map := λ x y f, map G (map F f)
 |}.
Obligation 1.
  apply path_compose with (y := map G 1).
  - apply map_id.
  - apply (ap (λ g, map G g) (@map_id C D F x)).
Defined.
Next Obligation.
  apply path_compose with (y := map G (map F f ∘ map F g)).
  - apply (map (ap (λ g, map G g)) (@map_compose C D F x y z f g)).
  - apply map_compose.
Defined.

Program Definition id_id_functor {C} : compose_functor (id_functor C) (id_functor C) ~ id_functor C := _.

Program Definition eta `(f : A -> B) : f ~ (λ x, f x) := _.

Program Definition right_id_functor `(f : functor C D) : compose_functor f (id_functor C) ~ f := _.
Obligation 1.
  unfold compose_functor.
  unfold id_functor.
  destruct f.
  unfold id_functor_obligation_1.
  unfold id_functor_obligation_2.
  unfold id_functor_obligation_3.
  unfold id_functor_obligation_4.
  unfold compose_functor_obligation_1.
  unfold compose_functor_obligation_2.
  simpl in *.
  f_ap.
  Set Printing All.
  change map_id0 at 2 with (λ x : C, map_id0 x).
Abort right_id_functor.



(*
Higher Inductive circle : Type
  := base : circle
   | loop : base = base.
*)
       

Module Export circle.

  Private Inductive circle : Type := | base : circle.
  Axiom loop : base ~ base.

  (* dependent elimination *)
  Program Definition circle_ind
    (B: circle -> Type) (b : B base)
    (l : loop # b ~ b) (x : circle) : B x.
  Proof.
    destruct x.
    apply b.
  Defined.

  (* non-dependent elimination *)
  Program Definition circle_rect
    (B : Type) (b : B) (l : b ~ b) : circle -> B.
  Proof.
   intros.
   destruct H.
   apply b.
  Defined.

End circle.

(* a 1-category is an (∞,1)-category, where the hom-sets are actual sets. *)
Class is_category1 (C : category) :=
  is_category1_prop : ∀ {x y : C}, is_set (x ~> y).

Class is_thin (C : category) :=
  is_thin_prop : ∀ {x y : C}, is_prop (x ~> y).

Class is_strict (C : category) :=
  is_strict_prop : is_set C.


(*
Program Definition thin_is_category1 {C : category} (thin : is_thin C):  is_category1 C.
Definition is_contractible_join (A : Type) (p : is_contractible A) : is_contractible (is_cont
Program Definition is_contractible_implies_is_prop (A : Type) (p : is_contractible A) : is_prProgram Definition is_prop_implies_is_set (A : Type) (p : is_prop A): is_set A := _.
Program Definition opcoe := Build_functor (Op (Paths Type)) Types _ _ _ _.
Program Definition gopf `(f : functor C D) { C' : is_groupoid C } := Build_functor (Op C) D f
Program Definition weq_id {A} : weq A A := existT _ _ _.
Program Instance weq_is_category : is_category weq.
*)


(*
Lemma transport_fiber A B (f : A -> B) (x y : A) (z : B) (p : x ~ y) (q : f x ~ z) :
  transport (λ x, f x ~ z) p q ~ q ∘ inverse (ap f p).
Proof.
  induction p.
  apply path_compose with (y := q).
  apply path_compose with (y := q ∘ inverse id).
  apply path_compose with (y := q ∘ id).
*)
