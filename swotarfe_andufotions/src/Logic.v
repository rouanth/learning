Require Export MoreCoq.

(* ((Conjunction (Logical "and"))) *)

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

