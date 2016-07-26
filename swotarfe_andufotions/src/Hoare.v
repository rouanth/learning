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

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 80)
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
      apply H1. apply Nat.leb_le. assumption.
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


Module If1.

Inductive com :=
  | CSkip : com
  | CAss  : id   -> aexp -> com
  | CSeq  : com  -> com  -> com
  | CIf   : bexp -> com  -> com  -> com
  | CWhile: bexp -> com  -> com
  | CIf1  : bexp -> com  -> com.

(* Exercise: 4 stars (if1_hoare) *)


Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, SKIP / st ⇓ st
  | E_Ass  : forall st x ae,  (x ::= ae) / st ⇓ (update st x (aeval st ae))
  | E_Seq  : forall st st' st'' c1 c2,
               c1 / st  ⇓ st'  ->
               c2 / st' ⇓ st'' ->
               (c1 ;; c2) / st ⇓ st''
  | E_IfTrue  : forall st st' ct ce be,
               beval st be = true ->
               ct / st ⇓ st'   ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_IfFalse : forall st st' ct ce be,
               beval st be = false ->
               ce / st ⇓ st'    ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_WhileEnd : forall st c be,
               beval st be = false ->
               (WHILE be DO c END) / st ⇓ st
  | E_WhileLoop : forall st st' st'' c be,
               beval st be = true ->
               c / st ⇓ st' ->
               (WHILE be DO c END) / st' ⇓ st'' ->
               (WHILE be DO c END) / st  ⇓ st''
  | E_If1True  : forall st st' c b, beval st b = true ->
               c / st ⇓ st' ->
               (IF1 b THEN c FI) / st ⇓ st'
  | E_If1False : forall st c b, beval st b = false ->
               (IF1 b THEN c FI) / st ⇓ st
   where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Definition hoare_triple
        (P : Assertion) (c : com) (Q : Assertion) : Prop :=
        forall st st',
        c / st ⇓ st' ->
        P st ->
        Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90,
        c at next level) : hoare_spec_scope.

Theorem hoare_if1 : forall P Q b c,
  {{ fun st => P st /\ bassn b st }} c {{ Q }} ->
  (fun st => P st /\ ~ bassn b st) ->> Q ->
  {{ P }} IF1 b THEN c FI {{ Q }}.
Proof.
  intros P Q b c Ht Hf st st' Hc Hp.
  inversion Hc; subst;
    [ apply bexp_eval_true  in H1; apply Ht with st |
      apply bexp_eval_false in H3; apply Hf]; try split; assumption.
Qed.

(* OLD RULES *)

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

(* / OLD RULES *)

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
    IF1 BNot (BEq (AId Y) (ANum 0)) THEN
      X ::= APlus (AId X) (AId Y)
    FI
  {{ fun st => st X = st Z }}.
Proof.
  apply hoare_if1.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + intros st H. destruct H.
      unfold assn_sub. simpl.
      rewrite update_eq. rewrite update_neq.
      * assumption.
      * intros contra; inversion contra.
  - intros st H. destruct H.
    rewrite <- H.
    unfold not in H0. unfold bassn in H0.
    simpl in H0.
    destruct (beq_nat (st Y) 0) eqn: nzY.
    + apply beq_nat_true in nzY. rewrite nzY. rewrite <- plus_n_O.
      trivial.
    + simpl in H0. apply except. apply H0. trivial.
Qed.

End If1.

(* END if1_hoare. *)

Lemma hoare_while : forall P b c,
  {{ fun st => P st /\ bassn b st }} c {{ P }} ->
  {{ P }} WHILE b DO c END {{ fun st => P st /\ ~ bassn b st }}.
Proof.
  intros P b c Hb st st' Hc Hp.
  remember (WHILE b DO c END) as Wh.
  induction Hc; inversion HeqWh; subst.
  - apply bexp_eval_false in H. split; assumption.
  - clear IHHc1 HeqWh.
    apply bexp_eval_true in H.
    apply IHHc2.
    + trivial.
    + apply Hb with st; try split; assumption.
Qed.

Module RepeatExercise.

Inductive com :=
  | CSkip   : com
  | CAss    : id   -> aexp -> com
  | CSeq    : com  -> com  -> com
  | CIf     : bexp -> com  -> com  -> com
  | CWhile  : bexp -> com  -> com
  | CRepeat : com  -> bexp -> com.

(* Exercise: 4 stars (hoare_repeat) *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'REPEAT' c 'UNTIL' b 'END'" :=
  (CRepeat c b) (at level 80, right associativity).

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, SKIP / st ⇓ st
  | E_Ass  : forall st x ae,  (x ::= ae) / st ⇓ (update st x (aeval st ae))
  | E_Seq  : forall st st' st'' c1 c2,
               c1 / st  ⇓ st'  ->
               c2 / st' ⇓ st'' ->
               (c1 ;; c2) / st ⇓ st''
  | E_IfTrue  : forall st st' ct ce be,
               beval st be = true ->
               ct / st ⇓ st'   ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_IfFalse : forall st st' ct ce be,
               beval st be = false ->
               ce / st ⇓ st'    ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_WhileEnd : forall st c be,
               beval st be = false ->
               (WHILE be DO c END) / st ⇓ st
  | E_WhileLoop : forall st st' st'' c be,
               beval st be = true ->
               c / st ⇓ st' ->
               (WHILE be DO c END) / st' ⇓ st'' ->
               (WHILE be DO c END) / st  ⇓ st''
  | E_RepeatEnd : forall st st' c be,
               c / st ⇓ st' ->
               beval st' be = true ->
               (REPEAT c UNTIL be END) / st ⇓ st'
  | E_RepeatLoop : forall st st' st'' c be,
               c / st ⇓ st' ->
               beval st' be = false ->
               (REPEAT c UNTIL be END) / st' ⇓ st'' ->
               (REPEAT c UNTIL be END) / st ⇓ st''
   where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Definition hoare_triple
        (P : Assertion) (c : com) (Q : Assertion) : Prop :=
        forall st st',
        c / st ⇓ st' ->
        P st ->
        Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90,
        c at next level) : hoare_spec_scope.

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state ⇓
               update (update empty_state X 1) Y 1.
Proof.
  eapply E_RepeatEnd.
  eapply E_Seq.
  apply E_Ass.
  apply E_Ass.
  reflexivity.
Qed.

Theorem hoare_repeat_weak : forall Q b c,
  {{ Q }} c {{ Q }} ->
  {{ Q }} REPEAT c UNTIL b END {{ fun st => Q st /\ bassn b st }}.
Proof.
  intros Q b c Hfl st st' Hc Hp.
  remember (REPEAT c UNTIL b END) as rcom.
  induction Hc; inversion Heqrcom; subst.
    + apply bexp_eval_true  in H. split.
      - apply Hfl with st; assumption.
      - assumption.
    + apply bexp_eval_false in H.
      apply IHHc2. trivial.
      apply Hfl with st; try split; assumption.
Qed.

Theorem hoare_repeat : forall P Q b c,
  {{ P }} c {{ Q }} ->
  {{ fun st => Q st /\ ~ bassn b st }} c {{ Q }} ->
  {{ P }} REPEAT c UNTIL b END {{ fun st => Q st /\ bassn b st }}.
Proof.
  intros P Q b c Hfi Hni st st' Hc Hp.
  inversion Hc; subst.
  - apply bexp_eval_true in H4.
    split; try assumption.
    apply Hfi with st; try assumption.
  - assert (Q st'0).
    { apply Hfi with st; assumption. }
    clear Hp Hfi Hc H1.
    remember (REPEAT c UNTIL b END) as rcom.
    apply bexp_eval_false in H2.
    induction H5; inversion Heqrcom; subst.
    + apply bexp_eval_true in H0. split.
      * apply Hni with st0; try split; assumption.
      * assumption.
    + clear IHceval1 Heqrcom.
      apply bexp_eval_false in H0.
      apply IHceval2.
      * assumption.
      * trivial.
      * apply Hni with st0; try split; assumption.
Qed.

(* OLD RULES *)

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

(* / OLD RULES *)

Theorem hoare_repeat_ex1 :
  {{ fun st => st X > 0 }}
    REPEAT
      Y ::= AId X ;;
      X ::= AMinus (AId X) (ANum 1)
    UNTIL (BEq (AId X) (ANum 0)) END
  {{ fun st => st X = 0 /\ st Y > 0 }}.
Proof.
  apply hoare_consequence_post with
    ((fun st : state => st Y > 0 /\ bassn (BEq (AId X) (ANum 0)) st)).
  - apply hoare_repeat.
    + eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        { apply hoare_asgn. }
        { unfold assn_sub. intros st H.
          simpl. rewrite update_neq.
          { rewrite update_eq. assumption. }
          { intros contra; inversion contra. }
        }
    + eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        { apply hoare_asgn. }
        { unfold assn_sub. intros st H.
          simpl. rewrite update_neq.
          { rewrite update_eq. destruct H.
            unfold bassn in H0. simpl in H0.
            unfold not in H0.
            destruct (st X).
            - apply except. apply H0. reflexivity.
            - omega.
          }
          intros contra; inversion contra.
        }
  - unfold bassn. simpl. intros st H.
    destruct H.
    split; try assumption.
    destruct (st X).
    + trivial.
    + inversion H0.
Qed.

(* END hoare_repeat. *)

End RepeatExercise.

Module Himp.

Inductive com :=
  | CSkip  : com
  | CAss   : id   -> aexp -> com
  | CSeq   : com  -> com  -> com
  | CIf    : bexp -> com  -> com  -> com
  | CWhile : bexp -> com  -> com
  | CHavoc : id   -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'HAVOC' i" :=
  (CHavoc i) (at level 60).

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, SKIP / st ⇓ st
  | E_Ass  : forall st x ae,  (x ::= ae) / st ⇓ (update st x (aeval st ae))
  | E_Seq  : forall st st' st'' c1 c2,
               c1 / st  ⇓ st'  ->
               c2 / st' ⇓ st'' ->
               (c1 ;; c2) / st ⇓ st''
  | E_IfTrue  : forall st st' ct ce be,
               beval st be = true ->
               ct / st ⇓ st'   ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_IfFalse : forall st st' ct ce be,
               beval st be = false ->
               ce / st ⇓ st'    ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_WhileEnd : forall st c be,
               beval st be = false ->
               (WHILE be DO c END) / st ⇓ st
  | E_WhileLoop : forall st st' st'' c be,
               beval st be = true ->
               c / st ⇓ st' ->
               (WHILE be DO c END) / st' ⇓ st'' ->
               (WHILE be DO c END) / st  ⇓ st''
  | E_Havoc : forall st X n, (HAVOC X) / st ⇓ (update st X n)
   where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Definition hoare_triple
        (P : Assertion) (c : com) (Q : Assertion) : Prop :=
        forall st st',
        c / st ⇓ st' ->
        P st ->
        Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90,
        c at next level) : hoare_spec_scope.

(* Exercise: 3 stars (himp_hoare) *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
  fun st => forall n, Q (update st X n).

Theorem hoare_havoc : forall Q X,
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  intros Q X st st' Hc Hp.
  inversion Hc; subst.
  apply Hp.
Qed.

(* END himp_hoare. *)

End Himp.
