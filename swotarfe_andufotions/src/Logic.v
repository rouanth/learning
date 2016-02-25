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

