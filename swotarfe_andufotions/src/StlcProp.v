Require Import SfLib.
Require Import Imp.
Require Import Types.
Require Import Stlc.
Require Import Smallstep.

Module STLCProp.
Import STLC.

Lemma canonical_forms_bool : forall t,
  (fun _ => None) |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros. inversion H; subst; try solve by inversion; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  (fun _ => None) |- t \in TArrow T1 T2 ->
  value t ->
  (exists x u, t = tabs x T1 u).
Proof.
  intros. inversion H; subst; try inversion H0; subst.
  exists i. exists bd. trivial.
Qed.

(* Exercise: 3 stars, optional (progress_from_term_ind) *)

Theorem progress : forall t T,
  (fun _ => None) |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof.
  induction t; intros; auto; inversion H; subst.
  - solve by inversion.
  - right. destruct IHt1 with (TArrow T11 T); try assumption.
    + destruct (canonical_forms_fun t1 T11 T) as [x [u Hu]]; subst; eauto.
      apply IHt2 in H5. destruct H5 as [vt2 | [z Hex]]; eauto.
    + destruct H0 as [x Hex]. eauto.
  - right. destruct IHt1 with TBool; try assumption.
    + destruct (canonical_forms_bool t1); subst; eauto.
    + destruct H0 as [x Hex]. eauto.
Qed.

(* END progress_from_term_ind. *)
