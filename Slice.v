Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.

Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
Set Primitive Projections.
Set Shrink Obligations.
Set Universe Polymorphism.
Generalizable All Variables.

Notation "TYPE / I" := { x : TYPE & x -> I }.

Definition fiber {I: Type} (s : Type / I) (i : I) : Type :=
  match s with
  | existT _ X f => { x : X & f x = i }
  end.

Hint Unfold fiber.

Definition unfiber {I : Type} (f : I -> Type) : { x : Type & x -> I} :=
  existT _ {x : I & f x} (@projT1 _ _).

Hint Unfold unfiber.

(** These lemmas require Axiom K / UIP.

Lemma unfiber_fiber {I: Type} (s : Type / I) : unfiber (fiber s) = s.
Lemma fiber_unfiber {I: Type} (s : I → Type) (i : I) : fiber (unfiber s) i = s i. 

*)

(* Sigma -| Delta -| Pi *)

(* The pullback along k of (f : X -> J). *)
Definition Delta {I J : Type} (k : I -> J) (f : J -> Type) (i : I) : Type :=
  f (k i).

Hint Unfold Delta.

Definition Sigma {I J : Type} (k : I -> J) (f : I -> Type) (j : J) : Type :=  
  { i : I & k i = j & f i }.

Hint Unfold Sigma.

Definition Pi {I J : Type} (k : I -> J) (f : I -> Type) (j : J) : Type :=
  ∀ (i : I), k i = j → f i.  

Hint Unfold Pi.

(* dependent polynomial functor, or best sorority ever *)
Definition Poly {I P S O} (r : P -> I) (t : P -> S) (q : S -> O) (z : I -> Type) : O -> Type :=
  Sigma q (Pi t (Delta r z)).

Inductive IR (I O : Type) : Type
  := iota : ∀ (o : O), IR I O
   | sigma : ∀ (S : Type) (K : S -> IR I O), IR I O
   | delta : ∀ (P : Type) (K : (P -> I) -> IR I O), IR I O.

