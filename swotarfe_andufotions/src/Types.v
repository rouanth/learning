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
      nvalue t ->
      tpred (tsucc t) ==> t
  | ST_Pred    : forall t1 t2,
      t1 ==> t2 ->
      tpred t1 ==> tpred t2
  | ST_IszeroZero :
      tiszero tzero ==> ttrue
  | ST_IszeroSucc : forall t,
      nvalue t ->
      tiszero (tsucc t) ==> tfalse
  | ST_Iszero : forall t1 t2,
      t1 ==> t2 ->
      tiszero t1 ==> tiszero t2
  where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

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
(*  induction t; inversion nval; intros; try solve by inversion.
    inversion H1; subst.
    apply IHt with t2; assumption.
Qed. *)
    induction nval; intros; inversion H; subst.
    apply IHnval with t2; assumption.
Qed.

(* END value_is_nf. *)

(* Exercise: 3 stars, optional (step_deterministic) *)

Lemma n_normal :
  forall n n', nvalue n -> (n ==> n' -> False).
Proof.
  intros. assert (value n) by (right; assumption).
  apply value_is_nf in H1. unfold normal_form in H1.
  apply H1. exists n'. assumption.
Qed.

Ltac nvalue_step :=
  match goal with
    H1 : nvalue ?E, H2 : ?E ==> ?F |- _ =>
        eapply n_normal in H1; eauto; contradiction
  end.

Ltac deterministic_tac :=
  match goal with
    H1 : ?R ?E ?F, H2 : forall e, ?R ?E e -> ?G = e |- _ =>
      solve [ apply H2 in H1; subst; trivial ]
  end
  || fail "is not a deterministic relation".

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros; inversion H0; subst; try solve by inversion;
    try solve_by_inversion_step (try nvalue_step); trivial;
    try deterministic_tac.
Qed.

(* END step_deterministic. *)

Inductive ty : Type :=
  | TBool : ty
  | TNat  : ty.

Reserved Notation "'|-' t '\in' S" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
      |- ttrue  \in TBool
  | T_False :
      |- tfalse \in TBool
  | T_If : forall (t1 t2 t3 : tm) (T : ty),
      |- t1 \in TBool ->
      |- t2 \in T ->
      |- t3 \in T ->
      |- tif t1 t2 t3 \in T
  | T_Zero :
      |- tzero \in TNat
  | T_Succ : forall t,
      |- t \in TNat ->
      |- tsucc t \in TNat
  | T_Pred : forall t,
      |- t \in TNat ->
      |- tpred t \in TNat
  | T_Iszero : forall t,
      |- t \in TNat ->
      |- tiszero t \in TBool
  where "'|-' t '\in' S" := (has_type t S).

Hint Constructors has_type.

(* Exercise: 1 star, optional (succ_hastype_nat__hastype_nat) *)

Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  intros. inversion H. assumption.
Qed.

(* END succ_hastype_nat__hastype_nat. *)

Lemma bool_canonical : forall t,
  value t -> (|- t \in TBool <-> bvalue t).
Proof.
  split; intros; inversion H0; subst; auto; inversion H; solve by inversion.
Qed.

Lemma nat_canonical : forall n,
  value n -> (|- n \in TNat <-> nvalue n).
Proof.
  split; intros.
  - inversion H; try assumption; solve by inversion 2.
  - induction H0; auto.
Qed.

(* Exercise: 3 stars (finish_progress) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros.
  induction H; auto.
  - right. destruct IHhas_type1.
    + apply bool_canonical in H; try assumption.
      inversion H; subst; [ exists t2 | exists t3 ]; auto.
    + destruct H2. exists (tif x t2 t3). auto.
  - destruct IHhas_type.
    + left. right. constructor. apply nat_canonical; auto.
    + right. destruct H0. exists (tsucc x). auto.
  - right. destruct IHhas_type.
    + apply nat_canonical in H; try assumption. clear H0.
      inversion H; subst; [ exists tzero | exists t0 ]; auto.
    + destruct H0. exists (tpred x). auto.
  - right. destruct IHhas_type.
    + apply nat_canonical in H; try assumption; clear H0.
      inversion H; subst; [ exists ttrue | exists tfalse ]; auto.
    + destruct H0. exists (tiszero x). auto.
Qed.

(* END finish_progress. *)

(* Exercise: 3 stars, advanced (finish_progress_informal) *)

(*
If the last rule in the derivation is `tsucc t`, then either |- t \in Nat or
there exists t' such that t ==> t'. In the first case, `tsucc t` is a value by
nv_succ and the fact that `t` is an nvalue by nat_canonical. In the second,
there exists a step (t ==> t' -> tsucc t ==> tsucc t').

If the last rule is `tpred t`, then either |- t \in Nat or there exists t' such
that t ==> t. In all these cases there exists a next step. If |- t \in Nat,
then it is an nvalue and is thus either an tzero, applicable for
`tpred tzero ==> tzero`, or tsucc t' for some nvalue t', applicable for
`tpred (tsucc t') ==> t'`. If `t ==> t'`, then `tpred t ==> tpred t'`.

If the last rule is `tiszero t`, then either |- t \in Nat and t in an nvalue,
or `t ==> t'` for some t'. In the first case, t can be tzero or tsucc t' for
some t', the first stepping into ttrue, the second stepping into tfalse. In the
case where `t ==> t'`, `tzero t ==> tzero t'`.
*)

(* END finish_progress_informal. *)

(* Exercise: 1 star (step_review) *)

(*
 + Every well-typed normal form is a value.
 + Every value is a normal form.
 + The single-step reduction relation is a partial function
   (i.e., it is deterministic).
 - The single-step reduction relation is a total function.
*)

(* END step_review. *)

(* Exercise: 2 stars (finish_preservation) *)

Theorem preservation : forall t t' T,
  |- t  \in T ->
  t ==> t'   ->
  |- t' \in T.
Proof with auto.
  intros t t' T Htt Hst. generalize dependent t'.
  induction Htt; intros; inversion Hst; subst...
  inversion Htt...
Qed.

(* END finish_preservation. *)

(* Exercise: 3 stars (preservation_alternate_proof) *)

Theorem preservation' : forall t t' T,
  |- t  \in T ->
  t ==> t'   ->
  |- t' \in T.
Proof with eauto.
  intros t t' T Htt Hst. generalize dependent T.
  induction Hst; intros; inversion Htt...
  inversion H1...
Qed.

(* END preservation_alternate_proof. *)