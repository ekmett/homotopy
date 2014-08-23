(* Product categories *)

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

