Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import SfLib.
Require Import Imp.

Definition Assertion := state -> Prop.

(* Exercise: 1 star, optional (assertions) *)

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
(* X = 3 *)

Definition as2 : Assertion := fun st => st X <= st Y.
(* X ≤ Y *)

Definition as3 : Assertion :=
          fun st => st X = 3 \/ st X <= st Y.
(* Either X = 3 or X ≤ Y *)

Definition as4 : Assertion :=
          fun st => st Z * st Z <= st X /\
                      ~ (((S (st Z)) * (S (st Z))) <= st X).
(* Z² ≤ X or not (Z² ≤ X), i. e. always true *)

Definition as5 : Assertion := fun st => True.
(* Any state matches *)

Definition as6 : Assertion := fun st => False.
(* No states match *)

End ExAssertions.


(* END assertions. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
        (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> Q) (at level 80) : hoare_spec_scope.

Definition hoare_triple
        (P : Assertion) (c : com) (Q : Assertion) : Prop :=
        forall st st',
        c / st ⇓ st' ->
        P st ->
        Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90,
        c at next level) : hoare_spec_scope.

(* Exercise: 1 star, optional (triples) *)

(*
   1) {{True}} c {{X = 5}}
   For all initial states, after `c` X is equal to 5.

   2) {{X = m}} c {{X = m + 5)}}
   After `c` X increases by 5.

   3) {{X ≤ Y}} c {{Y ≤ X}}
   If X was less or equal to Y before `c`, then after it this relation
   inverses.

   4) {{True}} c {{False}}
   `c` never terminates.

   5) {{X = m}}
      c
      {{Y = real_fact m}}    
   `c` assigns to Y the result of applying `real_fact` to X.

   6) {{True}}
      c
      {{(Z * Z) ≤ m ∧ ¬ (((S Z) * (S Z)) ≤ m)}}

    `c` never terminates.
*)

(* END triples. *)

(* Exercise: 1 star, optional (valid_triples) *)

(* 1, 2, 3, 6, 7, 8. *)

(* END valid_triples. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple.
  intros.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, not (P st)) ->
  {{ P }} c {{ Q }}.
Proof.
  unfold not.
  intros P Q c H st st' Hc Hp.
  apply H in Hp.
  inversion Hp.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{ Q [X |-> a] }} (X ::= a) {{ Q }}.
Proof.
  unfold assn_sub.
  unfold hoare_triple.
  intros Q X a st st' Hc Hp.
  inversion Hc; subst.
  assumption.
Qed.

(* Exercise: 2 stars (hoare_asgn_examples) *)

Example assn_sub_ex1 :
  {{ (fun st => st X <= 5) [ X |-> APlus (AId X) (ANum 1) ] }}
      X ::= APlus (AId X) (ANum 1)
  {{ fun st => st X <= 5 }}.
Proof.
  apply hoare_asgn.
Qed.

Example assn_sub_ex2 :
  {{ (fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3] }}
      X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof. apply hoare_asgn. Qed.

(* END hoare_asgn_examples. *)

(* Exercise: 2 stars (hoare_asgn_wrong) *)

Definition hoare_asgn_wrong :=
  forall X a, {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a }}.

Theorem hoare_asgn_wrong_is_wrong :
  not hoare_asgn_wrong.
Proof.
  unfold hoare_asgn_wrong. unfold hoare_triple.
  intro contra.
  remember (APlus (AId X) (ANum 1)) as a.
  remember (update empty_state X 2) as st.
  remember (update (update empty_state X 2) X 3) as st'.
  assert ((X ::= a) / st ⇓ st').
  { subst; apply E_Ass. }
  apply contra in H; try trivial.
  subst.
  simpl in H.
  rewrite update_eq in H.
  inversion H.
Qed.

(* END hoare_asgn_wrong. *)

(* Exercise: 3 stars, advanced (hoare_asgn_fwd) *)

Theorem hoare_asgn_fwd :
  (forall {X Y : Type} {f g : X -> Y},
    (forall (x : X), f x = g x) -> f = g) ->
  forall m a P,
  {{ fun st => P st /\ st X = m }}
    X ::= a
  {{ fun st => P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
  unfold hoare_triple.
  intros st st' Hc Hp.
  inversion Hc. destruct Hp. subst.
  replace (update (update st X (aeval st a)) X (st X)) with st.
  {
  split.
  - assumption.
  - rewrite update_eq. trivial.
  }
  apply functional_extensionality. intros x.
  unfold update.
  destruct (eq_id_dec X x); subst; trivial.
Qed.

(* END hoare_asgn_fwd. *)

(* Exercise: 2 stars, advanced (hoare_asgn_fwd_exists) *)

Theorem hoare_asgn_fwd_exists :
  (forall {X Y : Type} {f g : X -> Y},
    (forall (x : X), f x = g x) -> f = g) ->
  forall a P,
  {{ fun st => P st }}
    X ::= a
  {{ fun st => exists m, P (update st X m) /\ st X = aeval (update st X m) a }}.
Proof.
  intros functional_extensionality a P st st' Hc Hp.
  inversion Hc. subst.
  exists (st X).
  replace (update (update st X (aeval st a)) X (st X)) with st.
  {
    split.
    - assumption.
    - rewrite update_eq. trivial.
  }
  apply functional_extensionality. intros x.
  unfold update.
  destruct (eq_id_dec X x); subst; trivial.
Qed.

(* END hoare_asgn_fwd_exists. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{ P' }} c {{ Q }} ->
  P ->> P' ->
  {{ P  }} c {{ Q }}.
Proof.
  intros.
  intros st st' Hc Hp.
  unfold hoare_triple in H.
  apply H with st.
  - assumption.
  - apply H0. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{ P }} c {{ Q' }} ->
  Q' ->> Q ->
  {{ P }} c {{ Q  }}.
Proof.
  intros.
  intros st st' Hc Hp.
  apply H0.
  apply H with st; assumption.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{ P' }} c {{ Q' }} ->
  P  ->> P' ->
  Q' ->> Q  ->
  {{ P  }} c {{ Q  }}.
Proof.
  intros.
  intros st st' Hc Hp.
  apply H1.
  apply H with st.
  - assumption.
  - apply H0. assumption.
Qed.

(* Exercise: 2 stars (hoare_asgn_examples_2) *)

Example assn_sub_ex1' :
  {{ fun st  => st X + 1 <= 5 }}
    X ::= APlus (AId X) (ANum 1)
  {{ fun st' => st' X    <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - intros st H. unfold assn_sub. simpl. rewrite update_eq. assumption.
Qed.

Example assn_sub_ex2' :
  {{ fun st => 0 <= 3 /\ 3 <= 5 }}
    X ::= ANum 3
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - intros st H. unfold assn_sub. simpl. rewrite update_eq. assumption.
Qed.

(* END hoare_asgn_examples_2. *)
