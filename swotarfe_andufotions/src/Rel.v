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

(* Exercise: 1 star, optional *)

Theorem le_S_n : forall n m, (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
    apply le_n.
    apply (le_trans n (S n) m).
      apply le_S. apply le_n.
      apply H1.
Qed.

(* END. *)

(* And this one suddenly has a name. *)
(* Exercise: 2 stars, optional (le_Sn_n_inf) *)

(* Theorem: For every n, ~(S n ≤ n) *)

(* Proof.

Unfolding the definitions, we mush show that (S n <= n) can't be true for any
n.

By induction on n,

First we need to show that ~(1 <= 0). There is no constructor for `le` which
could prove (1 <= 0), so it can't be true.

Then we need to show that if (S n <= n) is False, then (S (S n) <= S n) is also
false. I. e., we need to prove that from (S (S n) <= S n) follows even False.

Applying le_S_n to it, we get (S n <= n). There is a contradiction between
~(S n <= n)
and
(S n <= n),
both of which are given. Thus, (S n <= n) can't be true.

*)

(* END le_Sn_n_inf. *)

(* Exercise: 1 star, optional *)

Theorem le_Sn_n : forall n, not (S n <= n).
Proof.
  intros n H.
  induction n.
    inversion H.
    apply le_S_n in H.
    apply IHn in H.
    apply H.
Qed.

(* END. *)

Definition symmetric {X : Type} (R : relation X) :=
  forall a b, R a b -> R b a.

(* Exercise: 2 stars, optional *)

Theorem le_not_symmetric : not (symmetric le).
Proof.
  intros H.
  unfold symmetric in H.
  assert (0 <= 1).
    apply le_S. apply le_n.
  apply H in H0.
  inversion H0.
Qed.

(* END. *)

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, R a b -> R b a -> a = b.

(* Exercise: 2 stars, optional *)

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a.
    intros. inversion H0. trivial.
    destruct b.
      intros. inversion H.
      intros. apply le_S_n in H. apply le_S_n in H0. apply IHa in H.
        rewrite -> H. trivial.
      apply H0.
Qed.

(* END. *)

(* Exercise: 2 stars, optional *)

Theorem le_step : forall n m p, n < m -> m <= S p -> n <= p.
Proof.
  unfold lt.
  intros.
  apply le_trans with (p := S p) in H.
  apply le_S_n in H.
  apply H.
  apply H0.
Qed.

(* END. *)

Inductive clos_refl_trans {X : Type} (R : relation X) : relation X :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z,
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Inductive refl_step_closure {X : Type} (R : relation X) : relation X :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                 R x y ->
                 refl_step_closure R y z ->
                 refl_step_closure R x z.
