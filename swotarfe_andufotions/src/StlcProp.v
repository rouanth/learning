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

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tapp t1 t2)
  | afi_abs  : forall x i T t,
      i <> x ->
      appears_free_in x t ->
      appears_free_in x (tabs i T t)
  | afi_if1 : forall x c t e,
      appears_free_in x c ->
      appears_free_in x (tif c t e)
  | afi_if2 : forall x c t e,
      appears_free_in x t ->
      appears_free_in x (tif c t e)
  | afi_if3 : forall x c t e,
      appears_free_in x e ->
      appears_free_in x (tif c t e)
.

Definition closed (t : tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
  appears_free_in x t ->
  Gamma |- t \in T ->
  exists T', Gamma x = Some T'.
Proof.
  intros x t.
  induction t; intros; inversion H0; subst; inversion H; subst; eauto.
  - apply IHt in H6; auto.
      destruct H6. unfold pupdate in H1. rewrite update_neq in H1; eauto.
Qed.

(* Exercise: 2 stars, optional (typable_empty__closed) *)

Corollary typable_empty__closed : forall t T,
  (fun _ => None) |- t \in T ->
  closed t.
Proof.
  unfold closed. intros. intro contra.
  apply (free_in_context x0 t T (fun _ => None)) in H; eauto.
  solve by inversion 2.
Qed.

(* END typable_empty__closed. *)
