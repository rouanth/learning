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

(* Exercise: 3 stars (types_unique) *)

Theorem type_unique : forall G t T T',
  G |- t \in T  ->
  G |- t \in T' ->
  T = T'.
Proof.
  intros G t. generalize dependent G.
  induction t; intros; inversion H; subst; inversion H0; subst; eauto;
    try solve by inversion.
  - rewrite H4 in H3. inversion H3. trivial.
  - assert (TArrow T11 T = TArrow T0 T') by eauto.
    inversion H1; eauto.
  - assert (T12 = T0) by eauto.
    subst; eauto.
Qed.

(* END types_unique. *)

(* Exercise: 1 star (progress_preservation_statement) *)

(* This is ridiculous. *)

Definition progress_statement:=
  forall t T,
  (fun _ => None) |- t \in T ->
  (~ stuck t).

Definition preservation_statement:=
  forall t t' T,
  (fun _ => None) |- t \in T ->
  t ==> t' ->
  (fun _ => None) |- t' \in T.

(* END progress_preservation_statement. *)

(* Exercise: 2 stars (stlc_variation1) *)

(*

  - Determinism of step (`tif ttrue t1 t2` ==> t1 and ==> zap)
  + Progress (there are no stuck values now, ever)
  - Preservation
    (Gamma |- ttrue \in TBool ->
     ttrue ==> t1 ->
     Gamma |- zap \in TArrow Bool Bool)

*)

(* END stlc_variation1. *)

(* Exercise: 2 stars (stlc_variation2) *)

(*

  - Determinism of step (`tapp (tabs x T tb) y)` ==> [x := y] tb
                         and ==> tapp foo y)
  + Progress
  - Preservation (`tabs x T tb` "loses" its type after reduction)

*)

(* END stlc_variation2. *)

(* Exercise: 2 stars (stlc_variation3) *)

(*

  + Determinism of step (removing rules can't break it)
  - Progress (`tapp (tif t1 t2 t3) t4` can't make a step but is not a value)
  + Preservation

*)

(* END stlc_variation3. *)

(* Exercise: 2 stars, optional (stlc_variation4) *)

(*

  - Determinism of step (`tif ttrue idBB idBB` ==> ttrue and ==> idBB)
  + Progress
  - Preservation (`tif ttrue idBB idBB` ==> ttrue and ==> idBB)

*)

(* END stlc_variation4. *)

(* Exercise: 2 stars, optional (stlc_variation5) *)

(*

  + Determinism of step
  - Progress (`|- t1 \in (TArrow TBool (TArrow TBool TBool)) ->
               |- t2 \in TBool ->
               |- t3 \in TBool -> |- t4 \in TBool ->
               |- tif (tapp t1 t2) t3 t4 \in TBool` but can't make a step).
  + Preservation

*)

(* END stlc_variation5. *)

(* Exercise: 2 stars, optional (stlc_variation6) *)

(*

  + Determinism of step
  - Progress (`tapp ttrue ttrue` has a type but won't make a step)
  + Preservation

*)

(* END stlc_variation6. *)

(* Exercise: 2 stars, optional (stlc_variation7) *)

(*

  + Determinism of step
  - Progress
    (`tif (tapp (tabs x TBool (tabs y TBool ttrue) ttrue) ttrue tfalse`
     would be well-typed but the next step would halt it`)
  + Preservation

*)

(* END stlc_variation7. *)

End STLCProp.

Module STLCArith.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat : ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

(* Exercise: 4 stars (stlc_arith) *)

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
    | tvar i   => if eq_id_dec i x then s else tvar i
    | tapp a b => tapp ([x := s] a) ([x := s] b)
    | tabs i tp bd => if eq_id_dec i x then tabs i tp bd
                      else tabs i tp ([x := s] bd)
    | tif0 c bt be => tif0 ([x := s] c) ([x := s] bt) ([x := s] be)
    | tsucc a => tsucc ([x := s] a)
    | tpred a => tpred ([x := s] a)
    | tmult a b => tmult ([x := s] a) ([x := s] b)
    | e => e
  end
  where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : tm -> Prop :=
  | v_abs   : forall x T t, value (tabs x T t)
  | v_nat   : forall n, value (tnat n).

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 ->
      (tapp (tabs x T t12) v2) ==> [x := v2] t12
  | ST_App1   : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_App2   : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tapp t1 t2 ==> tapp t1 t2'
  | ST_SuccNat : forall n,
      tsucc (tnat n) ==> tnat (S n)
  | ST_Succ : forall t t',
      t ==> t' ->
      tsucc t ==> tsucc t'
  | ST_PredNat : forall n,
      tpred (tnat n) ==> tnat (pred n)
  | ST_Pred : forall t t',
      t ==> t' ->
      tpred t ==> tpred t'
  | ST_MultNat : forall n1 n2,
      tmult (tnat n1) (tnat n2) ==> tnat (n1 * n2)
  | ST_Mult1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2 : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tmult t1 t2 ==> tmult t1 t2'
  | ST_If0True  : forall t e,
      tif0 (tnat 0) t e ==> t
  | ST_If0False : forall t e n,
      tif0 (tnat (S n)) t e ==> e
  | ST_If0 : forall c c' t e,
      c ==> c' ->
      tif0 c t e ==> tif0 c' t e
  where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).

Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Definition context := id -> option ty.

Definition pupdate { A : Type } (m : id -> option A) (x : id) (v : A) :=
  update m x (Some v).

Hint Unfold pupdate.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall G i T,
      G i = Some T ->
      G |- tvar i \in T
  | T_Abs : forall G i T11 bd T12,
      pupdate G i T11 |- bd \in T12 ->
      G |- tabs i T11 bd \in TArrow T11 T12
  | T_App : forall G a1 a2 T11 T12,
      G |- a1 \in TArrow T11 T12 ->
      G |- a2 \in T11 ->
      G |- tapp a1 a2 \in T12
  | T_Nat : forall G n,
      G |- tnat n \in TNat
  | T_Succ : forall G t,
      G |- t \in TNat ->
      G |- tsucc t \in TNat
  | T_Pred : forall G t,
      G |- t \in TNat ->
      G |- tpred t \in TNat
  | T_Mult : forall G t1 t2,
      G |- t1 \in TNat ->
      G |- t2 \in TNat ->
      G |- tmult t1 t2 \in TNat
  | T_If0 : forall G c t e T,
      G |- c \in TNat ->
      G |- t \in T ->
      G |- e \in T ->
      G |- (tif0 c t e) \in T
  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Lemma canonical_forms_nat : forall t,
  (fun _ => None) |- t \in TNat ->
  value t ->
  (exists n, t = tnat n).
Proof.
  intros. inversion H; subst; try solve by inversion; eauto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  (fun _ => None) |- t \in TArrow T1 T2 ->
  value t ->
  (exists x u, t = tabs x T1 u).
Proof.
  intros. inversion H; subst; try inversion H0; subst.
  exists i. exists bd. trivial.
Qed.

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
  - right. edestruct IHt; try eassumption.
    + destruct (canonical_forms_nat t); subst; eauto.
    + destruct H0; eauto.
  - right. edestruct IHt; try eassumption.
    + destruct (canonical_forms_nat t); subst; eauto.
    + destruct H0; eauto.
  - right. edestruct IHt1; try eassumption.
    + destruct (canonical_forms_nat t1); subst; eauto.
      edestruct IHt2; try eassumption.
      * destruct (canonical_forms_nat t2); subst; eauto.
      * destruct H1; eauto.
    + destruct H0; eauto.
  - right. edestruct IHt1; try eassumption.
    + destruct (canonical_forms_nat t1); subst; eauto.
      destruct x0; eauto.
    + destruct H0; eauto.
Qed.

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
  | afi_succ : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsucc t)
  | afi_pred : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpred t)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2)
  | afi_if1 : forall x c t e,
      appears_free_in x c ->
      appears_free_in x (tif0 c t e)
  | afi_if2 : forall x c t e,
      appears_free_in x t ->
      appears_free_in x (tif0 c t e)
  | afi_if3 : forall x c t e,
      appears_free_in x e ->
      appears_free_in x (tif0 c t e)
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

Corollary typable_empty__closed : forall t T,
  (fun _ => None) |- t \in T ->
  closed t.
Proof.
  unfold closed. intros. intro contra.
  apply (free_in_context x0 t T (fun _ => None)) in H; eauto.
  solve by inversion 2.
Qed.

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
  induction Ht; intros; subst; try solve
    [inversion H; subst; eauto].
  - inversion H; subst...
    + apply substitution_preserves_typing with T11...
      * inversion Ht1...
Qed.

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

(* END stlc_arith. *)

End STLCArith.
