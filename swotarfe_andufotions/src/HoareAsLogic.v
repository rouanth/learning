Require Import Imp.
Require Import Hoare.

Inductive hoare_proof : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,     hoare_proof P SKIP P
  | H_Asgn : forall P i a, hoare_proof (P [ i |-> a]) (i ::= a) P
  | H_Seq  : forall P P' P'' c1 c2,
               hoare_proof P  c1 P'  ->
               hoare_proof P' c2 P'' ->
               hoare_proof P (c1 ;; c2) P''
  | H_If   : forall P b t e P',
               hoare_proof (fun st => P st /\   bassn b st) t P' ->
               hoare_proof (fun st => P st /\ ~ bassn b st) e P' ->
               hoare_proof P (IFB b THEN t ELSE e FI) P'
  | H_While : forall P b c,
               hoare_proof (fun st => P st /\ bassn b st) c P ->
               hoare_proof P (WHILE b DO c END)
                 (fun st => P st /\ ~ bassn b st)
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
               hoare_proof P' c Q' ->
               (P ->> P') -> (Q' ->> Q) ->
               hoare_proof P  c Q
.

Lemma H_Consequence_pre : forall P P' c Q,
  hoare_proof P' c Q ->
  P ->> P' ->
  hoare_proof P  c Q.
Proof.
  intros. eapply H_Consequence; try eassumption.
  intros st X. assumption.
Qed.

Lemma H_Consequence_post : forall P c Q Q',
  hoare_proof P c Q' ->
  Q' ->> Q ->
  hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence; try eassumption.
  intros st X. assumption.
Qed.

(* Exercise: 2 stars (hoare_proof_sound) *)

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{ P }} c {{ Q }}.
Proof.
  intros.
  induction H.
  - apply hoare_skip.
  - apply hoare_asgn.
  - eapply hoare_seq; eassumption.
  - eapply hoare_if; eassumption.
  - apply hoare_while; assumption.
  - eapply hoare_consequence; eassumption.
Qed.

(* END hoare_proof_sound. *)

Definition wp (c : com) (Q : Assertion) : Assertion :=
  fun s => forall s', c / s ⇓ s' -> Q s'.

(* Exercise: 1 star (wp_is_precondition) *)

Lemma wp_is_precondition : forall c Q,
  {{ wp c Q }} c {{ Q }}.
Proof. unfold hoare_triple. auto. Qed.

(* END wp_is_precondition. *)

(* Exercise: 1 star (wp_is_weakest) *)

Lemma wp_is_weakest : forall c Q P',
  {{ P' }} c {{ Q }} -> forall st, P' st -> wp c Q st.
Proof.
  unfold hoare_triple. unfold wp. eauto.
Qed.

(* END wp_is_weakest. *)

(* Exercise: 5 stars (hoare_proof_complete) *)

Theorem hoare_proof_complete : forall P c Q,
  {{ P }} c {{ Q }} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
    + constructor.
    + intros st H. apply H.
    + intros st H. eapply HT. constructor. assumption.
  - (* i ::= a *)
    eapply H_Consequence_pre.
    + constructor.
    + intros st H. eapply HT. constructor. assumption.
  - (* c1 ;; c2 *)
    unfold hoare_triple in HT. apply H_Seq with (wp c2 Q);
      [apply IHc1 | apply IHc2]; unfold hoare_triple.
    + unfold wp. intros.
      apply HT with st; try apply E_Seq with st'; assumption.
    + auto.
  - (* IFB *)
    apply H_If;
      [ apply H_Consequence_pre with (wp c1 Q) |
        apply H_Consequence_pre with (wp c2 Q) ];
      unfold hoare_triple in IHc1; unfold hoare_triple in IHc2; auto;
      clear IHc1 IHc2; intros st [H H0] s' H'; apply HT with st; auto.
    + apply E_IfTrue; auto.
    + apply E_IfFalse; auto.
      destruct (beval st b) eqn : bevalb. contradiction. trivial.
  - (* WHILE *)
    unfold hoare_triple in HT.
    remember (wp (WHILE b DO c END) Q) as R.
    apply H_Consequence with (P' := R) (Q' := fun st => R st /\ ~ bassn b st).
    + apply H_While. apply IHc.
      unfold hoare_triple. intros. destruct H0. subst.
      unfold wp in H0. unfold wp. intros s' H'.
      apply H0.
      apply E_WhileLoop with st'; assumption.
    + intros st H. subst. intros st' H'. apply HT with st; assumption.
    + intros st [H h']. subst. apply H.
      apply E_WhileEnd.
      destruct (beval st b) eqn: bevalb.
      * contradiction.
      * trivial.
Qed.

(* END hoare_proof_complete. *)
