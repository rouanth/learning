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
