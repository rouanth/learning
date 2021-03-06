Require Export MoreCoq.

(* ((Conjunction (Logical "and"))) *)

(* Exercise: 2 stars (and_exercise) *)

Example and_exercise:
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  destruct n.
  Case "n = 0".
    split.
    SCase "0 = 0 ?".
      reflexivity.
    SCase "m = 0".
      simpl in H.
      rewrite H.
      reflexivity.
  Case "n != 0".
    inversion H.
Qed.

(* END and_exercise. *)

(* Exercise: 1 star, optional (proj2) *)

Theorem proj2 : forall (P Q : Prop), P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

(* END proj2. *)

(* Exercise: 2 stars (and_assoc) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  Case "P and Q".
    split.
    SCase "P".
      apply HP.
    SCase "Q".
      apply HQ.
  Case "R".
    apply HR.
Qed.

(* END and_assoc. *)

(* ((Iff)) *)

(* Exercise: 1 star, optional (iff_properties) *)

Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
  intros P.
  split.
  Case "P -> P #1".
    intros H.
    apply H.
  Case "P -> P #2".
    intros H.
    apply H.
Qed.

(* END iff_properties. *)

(* Exercise: 2 stars (or_distributes_over_and_2) *)

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  destruct H as [[HP|HQ] [HP2|HR]] eqn: Hd.
  Case "(true \/ _) /\ (true \/ _)".
    left.
    apply HP.
  Case "(true \/ _) /\ (_ \/ true)".
    left.
    apply HP.
  Case "(_ \/ true) /\ (true \/ _)".
    left.
    apply HP2.
  Case "(_ \/ true) /\ (_ \/ true)".
    right.
    split.
    SCase "Q".
      apply HQ.
    SCase "R".
      apply HR.
Qed.

(* END or_distributes_over_and_2. *)

(* Exercise: 1 star, optional (or_distributes_over_and) *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  split.
  Case "P \/ Q".
    destruct H as [HP | [HQ HR]] eqn: Hd.
    SCase "true \/ _".
      left.
      apply HP.
    SCase "_ \/ (true /\ true)".
      right.
      apply HQ.
  Case "P \/ R".
    destruct H as [HP | [HQ HR]] eqn: Hd.
    SCase "true \/ _".
      left.
      apply HP.
    SCase "_ \/ (true /\ true)".
      right.
      apply HR.
Qed.

(* END or_distributes_over_and. *)

(* Exercise: 2 stars, optional (andb_false) *)

Theorem andb_false : forall b c, andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b eqn : Hd.
  Case "b = true".
    simpl in H.
    right.
    apply H.
  Case "b = false".
    left.
    trivial.
Qed.

(* END andb_false. *)

(* Exercise: 2 stars, optional (orb_false) *)

Theorem orb_prop : forall b c, orb b c = true -> b = true \/ c = true.
Proof.
  intros b c.
  intros H.
  destruct b eqn : Hd.
  Case "b = true".
    left.
    trivial.
  Case "b = false".
    right.
    simpl in H.
    apply H.
Qed.

(* END orb_false. *)

(* Exercise: 2 stars, optional (orb_false_elim) *)

Theorem orb_false_elim : forall b c, orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b eqn : Hd.
  Case "b = true".
    inversion H.
  Case "b = false".
    split.
    SCase "false = false".
      trivial.
    SCase "c = false".
      simpl in H.
      apply H.
Qed.

(* END orb_false_elim. *)

(* ((Falsehood)) *)

(* Exercise: 2 stars, advanced (True) *)

Inductive True : Prop :=
  truth : True.

(* END True. *)

(* ((Negation)) *)

(* Exercise: 2 stars, advanced (double_neg_inf) *)

(* By definition of negation, ~~P means (P -> False) -> False, i. e. in order
* to prove a false statement P is enough, and the goal is to prove a false
* statement. Thus, (P -> False) -> False simplifies to just P, which is given.
*)

(* END double_neg_inf. *)

(* Exercise: 2 stars (contrapositive) *)

Theorem contrapositive : forall P Q : Prop, (P -> Q) -> (not Q -> not P).
Proof.
  intros P Q H.
  unfold not.
  intros G HP.
  apply G.
  apply H.
  apply HP.
Qed.

(* END contrapositive. *)

(* Exercise: 1 star (not_both_true_and_false) *)

Theorem not_both_true_and_false : forall P : Prop, not (P /\ not P).
Proof.
  intros P.
  unfold not.
  intros H.
  inversion H.
  apply H1.
  apply H0.
Qed.

(* END not_both_true_and_false. *)

(* Exercise: 1 star, advanced (informal_not_PNP) *)

(* not (P /\ not P), by definition of negation, is the same as (P /\ not P) ->
* False. By definition of /\, both P and `not P` must be true for the implied
* False to be true. `not P` unfolds into P -> False, that is, P is sufficient
* to prove False. P is a given to the implication. *)

(* END informal_not_PNP. *)

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2
    | (x :: l1')%list => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l nil.

(* Exercise: 5 stars (tr_rev) *)

Theorem snoc_append : forall (X : Type) (x : X) (l : list X),
  snoc l x = app l (cons x nil).
Proof.
  induction l; simpl; auto. rewrite -> IHl. trivial.
Qed.

Theorem rev_append_snoc_helper : forall X (x : list X) (a1 a2 : X),
  (a1 :: (x ++ a2 :: nil))%list = ((a1 :: x) ++ (a2 :: nil))%list.
Proof.
  induction x.
  - reflexivity.
  - reflexivity.
Qed.

Lemma rev_append_snoc : forall X (x1 x2 : list X) (a : X),
  rev_append x1 (x2 ++ a :: nil) = snoc (rev_append x1 x2) a.
Proof.
  intros X x.
  induction x.
  - simpl. intros. rewrite -> snoc_append. reflexivity.
  - simpl. intros. rewrite -> rev_append_snoc_helper. rewrite -> IHx.
    reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intro X.
  apply functional_extensionality.
  intro x.
  induction x.
  - reflexivity.
  - simpl. rewrite <- IHx. unfold tr_rev. simpl.
    replace (a :: nil)%list with (nil ++ a :: nil)%list.
    + rewrite -> rev_append_snoc. reflexivity.
    + reflexivity.
Qed.

(* END tr_rev. *)

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  unfold not.
  intros P P_ PF.
  apply PF.
  apply P_.
Qed.

(* Exercise: 3 stars (excluded_middle_irrefutable) *)

Theorem excluded_middle_irrefutable : forall P : Prop, ~ ~ (P \/ ~P).
Proof.
  unfold not.
  intros P H1.
  apply H1.
  right.
  intros P1.
  apply H1.
  left.
  apply P1.
Qed.

(* END excluded_middle_irrefutable. *)

Theorem ex_falso_quodlibet : forall P : Prop, False -> P.
Proof. intros P H. inversion H. Qed.

(* Exercise: 5 stars, advanced, optional (classical_axioms) *)

Definition pierce := forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition classic := forall P : Prop, not (not P) -> P.

Definition excluded_middle := forall P : Prop, P \/ not P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  not (not P /\ not Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (not P \/ Q).

Theorem P_or_false : forall P : Prop, P \/ False -> P.
Proof.
  intros P PoFH.
  destruct PoFH.
  apply H.
  inversion H.
Qed.

Theorem or_com : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q PQ.
  destruct PQ.
  right.
  apply H.
  left.
  apply H.
Qed.

Theorem pierce_implies_classic : pierce -> classic.
Proof.
  unfold pierce.
  unfold classic.
  intros pierce.
  intros P.
  unfold not.
  intros pff.
  apply pierce with (Q := False).
  intros pf.
  apply pff in pf.
  inversion pf.
Qed.

Theorem classic_implies_pierce : classic -> pierce.
Proof.
  unfold classic.
  unfold pierce.
  intros C.
  intros P Q PQP.
  unfold not in C.
  apply C.
  intros pf.
  apply pf.
  apply PQP.
  intros P_.
  apply pf in P_.
  inversion P_.
Qed.

Theorem classic_implies_excluded_middle : classic -> excluded_middle.
Proof.
  unfold classic.
  unfold excluded_middle.
  intros H.
  intros P.
  apply H.
  apply excluded_middle_irrefutable.
Qed.

Theorem excluded_middle_implies_classic :
  excluded_middle -> classic.
Proof.
  unfold excluded_middle.
  unfold classic.
  unfold not.
  intros EM P nnP.
  assert ((P \/ (P -> False)) -> P).
    intros kh.
    destruct kh.
    apply H.
    apply ex_falso_quodlibet.
    apply nnP.
    apply H.
  apply H.
  apply EM.
Qed.

Theorem classic_implies_de_morgan_not_and_not :
  classic -> de_morgan_not_and_not.
Proof.
  unfold classic.
  intros EM.
  unfold de_morgan_not_and_not.
  intros P Q Hand.
  unfold not in Hand.
  apply EM.
  unfold not.
  intros Hor.
  apply Hand.
  split.
  Case "P -> False".
    intros P_.
    apply Hor.
    left.
    apply P_.
  Case "Q -> False".
    intros Q_.
    apply Hor.
    right.
    apply Q_.
Qed.

Theorem de_morgan_not_and_not_implies_classic :
  de_morgan_not_and_not -> classic.
Proof.
  unfold de_morgan_not_and_not.
  unfold classic.
  unfold not.
  intros H.
  intros P.
  intros N.
  apply P_or_false.
  apply H.
  intros R.
  apply N.
  intros P_.
  apply N.
  destruct R.
  apply H0.
Qed.

Theorem classic_implies_implies_to_or : classic -> implies_to_or.
Proof.
  unfold classic.
  intros CL.
  unfold implies_to_or.
  intros P Q.
  intros H.
  apply CL.
  unfold not.
  intros H1.
  apply H1.
  left.
  intros P_.
  apply H1.
  right.
  apply H.
  apply P_.
Qed.

Theorem implies_to_or_implies_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  unfold not.
  intros ITO P.
  apply or_com.
  apply ITO.
  intros P_.
  apply P_.
Qed.

(* END classical_axioms. *)

(* Exercise: 2 stars (false_beq_nat) *)

Theorem false_beq_nat : forall n m : nat, n <> m ->  beq_nat n m = false.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    destruct m as [|m'].
    SCase "m = 0".
      intros H.
      unfold not in H.
      apply ex_falso_quodlibet.
      apply H.
      trivial.
    SCase "m = S m'".
      reflexivity.
  Case "n = S n'".
    destruct m as [|m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      intros H.
      simpl.
      apply IHn'.
      unfold not.
      unfold not in H.
      intros n'm'.
      apply H.
      rewrite -> n'm'.
      reflexivity.
Qed.

(* END false_beq_nat. *)

(* Exercise: 2 stars, optional (beq_nat_false) *)

Theorem beq_nat_false : forall n m : nat, beq_nat n m = false -> n <> m.
Proof.
  intros n m H.
  unfold not.
  intros nm.
  rewrite -> nm in H.
  rewrite <- beq_nat_refl in H.
  inversion H.
Qed.

(* END beq_nat_false. *)
