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

Hint Constructors appears_free_in.

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

Lemma context_invariance : forall G G' t T,
  G  |- t \in T ->
  (forall x, appears_free_in x t -> G x = G' x) ->
  G' |- t \in T.
Proof with eauto.
  intros G G' t T Hin Hst.
  generalize dependent Hst. generalize dependent G'.
  induction Hin; intros; eauto; econstructor...
  - rewrite Hst in H...
  - unfold pupdate in *.
    apply IHHin; intros. unfold update. destruct (eq_id_dec i x0); subst...
Qed.

Lemma substitution_preserves_typing : forall G x U t v T,
  pupdate G x U   |- t \in T ->
  (fun _ => None) |- v \in U ->
  G |- [x := v] t \in T.
Proof with eauto.
  unfold pupdate.
  intros G x U t.
  generalize dependent U. generalize dependent x. generalize dependent G.
  induction t; simpl; intros; inversion H; subst...
  - destruct (eq_id_dec i x0); subst.
    + rewrite update_eq in H3. inversion H3; subst.
      eapply context_invariance...
      intros.
      apply typable_empty__closed in H0. unfold closed in H0.
      apply H0 in H1. contradiction.
    + rewrite update_neq in H3...
  - unfold pupdate in *.
    destruct (eq_id_dec i x0); subst.
    + eapply context_invariance...
      intros. inversion H1; subst.
      rewrite update_neq...
    + econstructor. unfold pupdate.
      eapply IHt...
      eapply context_invariance...
      intros.
      rewrite update_permute...
Qed.

Theorem preservation : forall t t' T,
  (fun _ => None) |- t \in T ->
  t ==> t' ->
  (fun _ => None) |- t' \in T.
Proof with eauto.
  remember (fun _ => (None : option ty)) as G.
  intros t t' T Ht. generalize dependent t'.
  induction Ht; intros; try solve by inversion.
  - inversion H; subst...
    + apply substitution_preserves_typing with T11...
      * inversion Ht1...
  - inversion H; subst...
Qed.

(* Exercise: 2 stars, optional (type_soundness) *)

Definition stuck (t : tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  (fun _ => None) |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  - apply progress in Hhas_type. destruct Hhas_type; contradiction.
  - apply preservation with (t' := y0) in Hhas_type; eauto.
Qed.

(* END type_soundness. *)
