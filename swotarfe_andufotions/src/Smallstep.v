Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import SfLib.
Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm  -> tm  -> tm.

Module SimpleArith1.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 => t1' ->
    P t1 t2 => P t1' t2
  | ST_Plus2 : forall n t2 t2',
    t2 => t2' ->
    P (C n) t2 => P (C n) t2'
  where " t '=>' t' " := (step t t').

(* Exercise: 1 star (test_step_2) *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      =>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof. apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst. Qed.
(* Proof. repeat constructor. Qed. *)

(* END test_step_2. *)

End SimpleArith1.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation "t '=>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'
  where "t '=>' t'" := (step t t').

(* Exercise: 3 stars, recommended (redo_determinism) *)

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hind.
  generalize dependent y2.
  induction Hind; intros; inversion H; subst; try solve by inversion 2;
    trivial.
  - rewrite IHHind with t1'0; trivial.
  - inversion H0; subst; try solve by inversion 2.
    rewrite IHHind with t2'0; trivial.
Qed.

(* END redo_determinism. *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t.
  - left. constructor.
  - right.
    destruct IHt1.
    + inversion H; subst. destruct IHt2; inversion H0; subst.
      * exists (C (n + n0)); constructor.
      * exists (P (C n) x);  constructor; assumption.
    + destruct H. exists (P x t2). constructor; assumption.
Qed.

Definition normal_form {X : Type} (R : X -> X -> Prop) (x : X) :=
  ~ exists x', R x x'.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  unfold normal_form.
  split; intros.
  - (* nf -> value *)
    assert (value t \/ exists t', t => t'). { apply strong_progress. }
    destruct H0.
    + assumption.
    + contradiction.
  - (* value -> nf *)
    intro CONTRA.
    solve by inversion 3.
Qed.

Module Temp2.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation "t '=>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n => P (C n) (C 0)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 => t2' ->
      P v1 t2 => P v1 t2'
  where "t '=>' t'" := (step t t').

(* Exercise: 2 stars, optional (value_not_same_as_normal_form) *)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 0).
  split.
  - constructor.
  - unfold normal_form. unfold not. intro CONTRA.
    apply CONTRA.
    exists (P (C 0) (C 0)).
    constructor.
Qed.

(* END value_not_same_as_normal_form. *)

End Temp2.
