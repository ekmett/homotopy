Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.

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
  existT (λ x : Type, x → I) {x : I & f x}
    (λ X : {x : I & f x}, let (x, _) := X in x).

Hint Unfold unfiber.

Lemma unfiber_fiber {I: Type} (s : Type / I) : unfiber (fiber s) = s.
Admitted.

Lemma fiber_unfiber {I: Type} (s : I → Type) (i : I) : fiber (unfiber s) i = s i. 
Admitted.
