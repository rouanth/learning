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

(* Exercise: 1 star, optional (natlist1) *)

(* natlist_ind : forall (P : natlist -> Prop), P nnil ->
   (forall (l : natlist) (n : nat), P l -> P (ncons l n)) ->
   forall (l : natlist), P l. *)

(* END natlist1. *)

(* Exercise: 1 star, optional (byntree_ind) *)

(* byntree_ind : forall P : byntree -> Prop, P bempty ->
   (forall (y : yesno) (b : byntree), P (bleaf y b)) ->
   (forall (y : yesno) (b1 b2 : byntree), P (nbranch y b1 b2)) ->
   forall b : byntree, P b. *)

(* END byntree_ind. *)

(* Exercise: 1 star, optional (ex_set) *)

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat  -> ExSet -> ExSet.

(* END ex_set. *)

(* Exercise: 1 star, optional (tree) *)

(* forall (X : Type) (P : tree -> Prop),
   (forall (x : X), P (leaf x)) ->
   (forall (n1 n2 : tree), P n1 -> P n2 -> P (node n1 n2)) ->
   forall t : tree, P t.
*)

(* END tree. *)

(* Exercise: 1 star, optional (mytype) *)

Inductive mytype (X : Type) : Type :=
  | constr1 : X   -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

(* END mytype. *)