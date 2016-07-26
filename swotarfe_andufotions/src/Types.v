Require Import Coq.Arith.Arith.
Require Import SfLib.
Require Import Imp.
Require Import Smallstep.

Hint Constructors multi.

Inductive tm : Type :=
  | ttrue   : tm
  | tfalse  : tm
  | tif     : tm  -> tm  -> tm  -> tm
  | tzero   : tm
  | tsucc   : tm  -> tm
  | tpred   : tm  -> tm
  | tiszero : tm  -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true  : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero  : nvalue tzero
  | nv_succ  : forall t, nvalue t -> nvalue (tsucc t).

Definition value t := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold update.
Hint Unfold value.

Fixpoint nat_to_tm (n : nat) : tm :=
  match n with
    | 0   => tzero
    | S n => tsucc (nat_to_tm n)
  end.

Fixpoint bool_to_tm (b : bool) : tm :=
  if b then ttrue else tfalse.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue  : forall t1 t2,
      tif ttrue  t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If      : forall t t' t1 t2,
      t ==> t' ->
      tif t t1 t2 ==> tif t' t1 t2
  | ST_Succ    : forall t1 t2,
      t1 ==> t2 ->
      tsucc t1 ==> tsucc t2
  | ST_PredZero :
      tpred tzero ==> tzero
  | ST_PredSucc : forall t,
      tpred (tsucc t) ==> t
  | ST_Pred    : forall t1 t2,
      t1 ==> t2 ->
      tpred t1 ==> tpred t2
  | ST_IszeroZero :
      tiszero tzero ==> ttrue
  | ST_IszeroSucc : forall t,
      tiszero (tsucc t) ==> tfalse
  | ST_Iszero : forall t1 t2,
      t1 ==> t2 ->
      tiszero t1 ==> tiszero t2
  where "t1 '==>' t2" := (step t1 t2).

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* Exercise: 2 stars (some_term_is_stuck) *)

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue).
  split; intro contra; solve by inversion 3.
Qed.

(* END some_term_is_stuck. *)

(* Exercise: 3 stars, advanced (value_is_nf) *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t [bval | nval]; intro contra; destruct contra.
  - solve by inversion 2.
  - generalize dependent x.
    induction nval; intros; inversion H; subst.
    apply IHnval with t2; assumption.
Qed.

(* END value_is_nf. *)
