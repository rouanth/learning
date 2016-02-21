Require Export Poly.

(* ((The apply Tactic)) *)

(* Exercise: 2 stars, optional (silly_ex) *)

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros H.
  apply H.
Qed.

(* END silly_ex. *)

(* Exercise: 3 stars (apply_exercise1) *)

Theorem rev_injective : forall l1 l2 : list nat,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  rewrite <- rev_involutive.
  replace l1 with (rev (rev l1)).
  Case "rev (rev l1) = rev (rev l2)".
    rewrite <- H.
    reflexivity.
  Case "l1 = rev (rev l1)".
    rewrite -> rev_involutive.
    reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  symmetry.
  apply rev_injective.
  rewrite -> rev_involutive.
  apply H.
Qed.

(* END apply_exercise1. *)

(* Exercise: 1 star, optional (apply_rewrite) *)

(* Apply matches the expression completely, including its conditions, against
* which rewrite is powerless.
* On the other hand, rewrite can be applied to parts of expressions, which is
* not true for apply.
*)

(* END apply_rewrite. *)

(* ((The apply ... with ... Tactic)) *)

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intros H H1.
  rewrite <- H1.
  apply H.
Qed.

(* Exercise: 3 stars, optional (apply_with_exercise) *)

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros H1 H2.
  apply trans_eq with m.
  Case "n + p = m".
    apply H2.
  Case "m = minustwo o".
    apply H1.
Qed.

(* END apply_with_exercise. *)

(* ((The inversion tactic)) *)

(* Exercise: 1 star (sillyex1) *)

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
  (x :: y :: l)%list = (z :: j)%list ->
  (y :: l)%list = (x :: j)%list ->
  x = y.
Proof.
  intros X x y z l j.
  intros H1 H2.
  inversion H2.
  reflexivity.
Qed.

(* END sillyex1. *)

(* Exercise: 1 star (sillyex2) *)

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
  (x :: y :: l)%list = nil ->
  (y :: l)%list = (z :: j)%list ->
  x = z.
Proof.
  intros X x y z l j.
  intros H1 H2.
  inversion H1.
Qed.

(* END sillyex2. *)

(* Exercise: 2 stars, optional (practice) *)

Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n H.
  destruct n.
  reflexivity.
  inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
  beq_nat n 0 = true -> n = 0.
Proof.
  intros n H.
  induction n as [|n'].
  reflexivity.
  inversion H.
Qed.

(* END practice. *)

