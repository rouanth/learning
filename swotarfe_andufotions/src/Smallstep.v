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

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation "t '=>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 => t1' ->
      P t1 t2 => P t1' t2
  where "t '=>' t'" := (step t t').

(* Exercise: 3 stars, optional (value_not_same_as_normal_form') *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 0) (P (C 1) (C 2))).
  split.
  - intro CONTRA. inversion CONTRA.
  - unfold normal_form. unfold not. intro CONTRA.
    solve by inversion 3.
Qed.

(* END value_not_same_as_normal_form'. *)

End Temp3.

Module Temp4.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tif    : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true  : value ttrue
  | v_false : value tfalse.

Reserved Notation "t '=>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue  t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t t' t1 t2,
      t => t' ->
      tif t t1 t2 => tif t' t1 t2
  where "t '=>' t'" := (step t t').

Definition bool_step_prop1 :=
  tfalse => tfalse.

Definition bool_step_prop2 :=
  tif ttrue
    (tif ttrue ttrue ttrue)
    (tif tfalse tfalse tfalse) =>
  ttrue.

Definition bool_step_prop3 :=
  tif
    (tif ttrue ttrue ttrue)
    (tif ttrue ttrue ttrue)
    tfalse
  =>
  tif
    ttrue
    (tif ttrue ttrue ttrue)
    tfalse.

(* Exercise: 1 star (smallstep_bools) *)

Lemma bool_step_prop1_false :
  ~ bool_step_prop1.
Proof.
  unfold bool_step_prop1.
  intros contra. inversion contra.
Qed.

Lemma bool_step_prop2_false :
  ~ bool_step_prop2.
Proof.
  unfold bool_step_prop2.
  intros contra. inversion contra.
Qed.

Lemma bool_step_prop3_true :
  bool_step_prop3.
Proof.
  unfold bool_step_prop3.
  repeat constructor.
Qed.

(* END smallstep_bools. *)

(* Exercise: 3 stars, optional (progress_bool) *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  intros.
  induction t; try (left; constructor); right.
  destruct IHt1.
  - inversion H; subst; [ exists t2 | exists t3 ]; constructor.
  - destruct H. exists (tif x t2 t3). constructor. assumption.
Qed.

(* END progress_bool. *)

(* Exercise: 2 stars, optional (step_deterministic) *)

Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hind. generalize dependent y2.
  induction Hind; intros; inversion H; subst; trivial; try solve by inversion.
  apply IHHind in H4; subst; trivial.
Qed.

(* END step_deterministic. *)

Module Temp5.

(* Exercise: 2 stars (smallstep_bool_shortcut) *)

Reserved Notation "t '=>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue  t1 t2 => t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 => t2
  | ST_If : forall t t' t1 t2,
      t => t' ->
      tif t t1 t2 => tif t' t1 t2
  | ST_Same : forall t t',
      tif t t' t' => t'
  where "t '=>' t'" := (step t t').

Definition bool_step_prop4 :=
  tif (tif ttrue ttrue ttrue) tfalse tfalse => tfalse.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof. constructor. Qed.

(* END smallstep_bool_shortcut. *)

(* Exercise: 3 stars, optional (properties_of_altered_step) *)

Theorem tm_dec_eq : forall (t1 t2 : tm), { t1 = t2 } + { t1 <> t2 }.
Proof.
  induction t1; induction t2; subst; try (left; reflexivity);
    try (right; intros contra; solve by inversion).
  clear IHt2_1 IHt2_2 IHt2_3.
  destruct IHt1_1 with t2_1; destruct IHt1_2 with t2_2;
  destruct IHt1_3 with t2_3; subst; try (left; reflexivity);
    right; intro contra; inversion contra; contradiction.
Qed.

Theorem strong_progress : forall t,
  value t \/ (exists t', t => t').
Proof.
  induction t; try (left; constructor); right.
  destruct IHt1; inversion H; subst;
    [ exists t2 | exists t3 | exists (tif x t2 t3) ];
    constructor. assumption.
Qed.

Theorem step_deterministic : ~ deterministic step.
Proof.
  unfold deterministic. intros CONTRA.
  assert (tif (tif ttrue ttrue ttrue) ttrue ttrue => ttrue) by constructor.
  assert (tif (tif ttrue ttrue ttrue) ttrue ttrue => tif ttrue ttrue ttrue)
    by repeat constructor.
  assert (ttrue = tif ttrue ttrue ttrue) by
   (apply CONTRA with (tif (tif ttrue ttrue ttrue) ttrue ttrue); assumption).
  solve by inversion.
Qed.

(* Removing ST_If causes strong progress to fail since `tif` is not a value but
at the same time `tif i t e` won't, if `t` and `e` don't form a shortcut,
be able to make a step. *)

(* END properties_of_altered_step. *)

End Temp5.
End Temp4.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall x, multi R x x
  | multi_step : forall x y z,
                   R x y ->
                   multi R y z ->
                   multi R x z.

Notation " t '=>*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof.
  intros. econstructor. eassumption. constructor.
Qed.

Theorem multi_trans : forall X (R : relation X) (x y z : X),
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros. induction H.
  - assumption.
  - apply IHmulti in H0. generalize dependent H0. generalize dependent H.
    apply multi_step.
Qed.

(* Exercise: 1 star, optional (test_multistep_2) *)

Lemma test_multistep_2:
  C 3 =>* C 3.
Proof.
  apply multi_refl.
Qed.

(* END test_multistep_2. *)

(* Exercise: 1 star, optional (test_multistep_3) *)

Lemma test_multistep_3 :
  P (C 0) (C 3)
=>*
  P (C 0) (C 3).
Proof.
  apply multi_refl.
Qed.

(* END test_multistep_3. *)

(* Exercise: 2 stars (test_multistep_4) *)

Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  =>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  apply multi_step with (P (C 0) (P (C 2) (C (0 + 3)))); repeat constructor.
  apply multi_step with (P (C 0) (C (2 + (0 + 3)))); repeat constructor.
Qed.

(* END test_multistep_4. *)
