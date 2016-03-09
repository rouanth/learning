Require Export SfLib.

(* ((Basic Properties of Relations)) *)

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* Hey! Where are the names? *)
(* Exercise: 2 stars, optional *)

Theorem total_relation_is_not_a_partial_function :
  not (partial_function total_relation).
Proof.
  unfold not.
  unfold partial_function.
  intros H.
  assert (total_relation 0 1).
    apply tot.
  apply (H 0 1 2) in H0.
  inversion H0.
  apply tot.
Qed.

(* END total_relation_not_partial_function. *)

(* Exercise: 2 stars, optional *)

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros.
  inversion H0.
Qed.

(* END. *)
