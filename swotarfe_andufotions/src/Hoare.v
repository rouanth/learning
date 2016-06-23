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

Notation "P ->> Q" := (assert_implies P Q) (at level 80)
  : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> Q) (at level 80)
  : hoare_spec_scope.

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
  forall X a,
  {{ fun st => True }}
    X ::= a
  {{ fun st => st X = aeval st a }}.

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
  {{ fun st => exists m, P (update st X m) /\
                         st X = aeval (update st X m) a }}.
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

Theorem hoare_skip : forall P,
  {{ P }} SKIP {{ P }}.
Proof.
  unfold hoare_triple. intros. inversion H. subst. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{ Q }} c2 {{ R }} ->
  {{ P }} c1 {{ Q }} ->
  {{ P }} c1 ;; c2 {{ R }}.
Proof.
  intros P Q R c1 c2 Hc2 Hc1.
  intros st st' HSeq Hp.
  inversion HSeq; subst.
  apply Hc1 in H1. apply H1 in Hp.
  apply Hc2 in H4. apply H4 in Hp.
  assumption.
Qed.

Example hoare_asgn_example3 : forall a n,
  {{ fun st => aeval st a = n }}
    (X ::= a ;; SKIP)
  {{ fun st => st X = n }}.
Proof.
  intros. eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. subst. reflexivity.
Qed.

(* Exercise: 2 stars (hoare_asgn_example4) *)

Example hoare_asgn_example4 :
  {{ fun st => True }} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{ fun st => st X = 1 /\ st Y = 2 }}.
Proof.
  intros.
  assert ({{ fun _ => 1 = 1 }} X ::= ANum 1 {{ fun st => st X = 1 }} ).
  { eapply hoare_consequence_pre.
    - apply hoare_asgn.
    - intros st H. reflexivity. }
  assert ({{ fun st => st X = 1 /\ 2 = 2 }} Y ::= ANum 2
          {{ fun st => st X = 1 /\ st Y = 2 }}).
  { eapply hoare_consequence_pre.
    - eapply hoare_asgn.
    - intros st H'. unfold assn_sub. destruct H'.
      split.
      + rewrite update_neq. assumption. intros contra. inversion contra.
      + rewrite update_eq. reflexivity. }
  eapply hoare_seq.
  - eapply hoare_consequence_post.
    + eapply H0.
    + intros st H'. assumption.
  - eapply hoare_consequence.
    + eapply H.
    + intros st H'. reflexivity.
    + intros st H'. split. assumption. reflexivity.
Qed.

(* END hoare_asgn_example4. *)

(* Exercise: 3 stars (swap_exercise) *)

Definition swap_program : com :=
  Z ::= AId X;;
  X ::= AId Y;;
  Y ::= AId Z.

Theorem swap_exercise :
  {{ fun st => st X <= st Y }}
    swap_program
  {{ fun st => st Y <= st X }}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
  eapply hoare_seq.
  - apply hoare_asgn.
  - apply hoare_asgn.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H.
      unfold assn_sub.
      rewrite update_eq.
      rewrite update_permute.
      rewrite update_eq. simpl.
      rewrite update_permute.
      rewrite update_eq.
      rewrite update_neq.
      assumption.
      intros contra; inversion contra.
      intros contra; inversion contra.
      intros contra; inversion contra.
Qed.

(* END swap_exercise. *)

(* Exercise: 3 stars (hoarestate1) *)

Definition hoarestate1 := forall a n,
  {{ fun st => aeval st a = n }}
    X ::= (ANum 3) ;; Y ::= a
  {{ fun st => st Y = n }}.

Theorem hoarestate1_false :
  not hoarestate1.
Proof.
  unfold hoarestate1.
  intros contra.
  remember (update empty_state X 0) as stC.
  remember (AId X) as aC.
  assert ({{fun st : state => aeval st aC = 0}}
          X ::= ANum 3;; Y ::= aC
          {{fun st : state => st Y = 0}}).
  { apply contra. }
  assert ((X ::= ANum 3;; Y ::= aC) / stC ⇓
          (update (update stC X 3) Y (aeval (update stC X 3) (AId X)))).
  { subst. eapply E_Seq; apply E_Ass. }
  unfold hoare_triple in H.
  apply H in H0.
  - simpl in H0. repeat rewrite update_eq in H0. inversion H0.
  - subst. reflexivity.
Qed.

(* END hoarestate1. *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros. unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> not ((bassn b) st).
Proof.
  intros. unfold bassn.
  intros contra. rewrite H in contra. inversion contra.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{ fun st => P st /\ bassn b st }}       c1 {{ Q }} ->
  {{ fun st => P st /\ not (bassn b st) }} c2 {{ Q }} ->
  {{ P }} IFB b THEN c1 ELSE c2 FI {{ Q }}.
Proof.
  intros P Q b c1 c2 Hc1 Hc2 st st' Hc Hp.
  inversion Hc; subst;
  [ apply bexp_eval_true in H4 ; apply Hc1 with st |
    apply bexp_eval_false in H4; apply Hc2 with st ];
    try split; assumption.
Qed.

(* Exercise: 2 stars (if_minus_plus) *)

Theorem if_minus_plus :
  {{ fun st => True }}
    IFB (BLe (AId X) (AId Y))
      THEN (Z ::= AMinus (AId Y) (AId X))
      ELSE (Y ::= APlus  (AId X) (AId Z))
    FI
  {{ fun st => st Y = st X + st Z }}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold bassn. intros st H. destruct H.
      unfold assn_sub. simpl.
      rewrite update_neq. rewrite update_eq. rewrite update_neq.
      simpl in H0.
      assert (forall a b, b <= a -> a = b + (a - b)).
      { intros. omega. }
      apply H1. apply ble_nat_true. assumption.
      intros contra; inversion contra.
      intros contra; inversion contra.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold bassn. intros st H. destruct H.
      unfold assn_sub. simpl. rewrite update_eq.
      rewrite update_neq. rewrite update_neq.
      trivial.
      intros contra; inversion contra.
      intros contra; inversion contra.
Qed.

(* END if_minus_plus. *)
