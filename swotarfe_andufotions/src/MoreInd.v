Require Export ProofObjects.

(* ((Induction Principles)) *)

(* Exercise: 2 stars, optional (plus_one_r') *)

Theorem plus_one_r' : forall n : nat, n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0". reflexivity.
  Case "S". intros. simpl. rewrite -> H. trivial.
Qed.

(* END plus_one_r'. *)

(* Exercise: 1 star, optional (rgb) *)

(* rgb_ind : forall (P : rgb -> Prop), P red -> P green -> P blue ->
   forall (r : rgb), P r. *)

(* END rgb. *)
