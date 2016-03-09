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

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

(* Exercise: 2 stars, optional *)

Theorem lt_trans' : transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    apply le_S. apply Hnm.
    apply le_S. apply IHHm'o.
Qed.

(* END. *)

(* Exercise: 2 stars, optional *)

Theorem lt_trans'' : transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
    inversion Hmo.
    apply le_S. inversion Hmo.
      rewrite <- H0. apply Hnm.
      apply IHo'. apply H0.
Qed.

(* END. *)
