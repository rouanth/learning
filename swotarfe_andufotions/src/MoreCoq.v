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

(* ((Using Tactics on Hypotheses)) *)

(* Exercise: 3 stars (plus_n_n_injective) *)

Theorem plus_0_0_0 : forall (n m : nat), 0 = n + m -> n = 0.
Proof.
  intros n m H.
  induction n as [|n'].
    reflexivity.
    inversion H.
Qed.

Theorem plus_n_n_injective : forall (n m : nat), n + n = m + m -> n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    simpl in H.
    apply plus_0_0_0 in H.
    symmetry.
    apply H.
  Case "n = S n'".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
      rewrite -> H1.
      trivial.
Qed.

(* END plus_n_n_injective. *)

(* ((Varying the Induction Hypothesis)) *)

(* Exercise: 2 stars (beq_nat_true) *)

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m.
    SCase "m = 0".
      trivial.
    SCase "m = S m'".
      inversion H.
  Case "n = S n'".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      simpl in H.
      apply IHn' in H.
      rewrite -> H.
      trivial.
Qed.

(* END beq_nat_true. *)

(* Exercise: 2 stars, advanced (beq_nat_true_informal) *)

(* Performing an induction on n, we have the following cases:
* a) n is 0;
* b) n is an increment of another number.
* In the first case, the possible m are 0 or an increment of another number;
* the first case is trivial, while the second is contradictory by the
* definition of beq_nat.
* The inductive step is proving that for every non-zero n, if beq_nat n m is
* true, the numbers are equal.
* If m is zero, there is a contradiction: beq_nat 0 (S m') is always false.
* If m is non-zero, then, beq_nat (S n') (S m') being the same as
* beq_nat n' m', falls under the induction hypothesis.
*)

(* END beq_nat_true_informal. *)

(* Exercise: 3 stars (gen_dep_practice) *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|m l'].
  Case "l = nil".
    reflexivity.
  Case "l = m :: l'".
    intros n H.
    destruct n.
    SCase "n = 0".
      inversion H.
    SCase "n = S n'".
      inversion H.
      simpl.
      apply IHl'.
      trivial.
Qed.

(* END gen_dep_practice. *)

