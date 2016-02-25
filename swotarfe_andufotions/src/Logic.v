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

