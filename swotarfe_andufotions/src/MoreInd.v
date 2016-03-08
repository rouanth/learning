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

(* Exercise: 1 star, optional (foo) *)

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

(* END foo. *)

(* Exercise: 1 star, optional (foo') *)

(* P f
P (C1 l f)
P C2
P f
*)

(* END foo'. *)

(* Exercise: 1 star, optional (plus_explicit_prop) *)

Definition plus_assoc_def (n m o : nat) :=
  (n + m) + o = n + (m + o).

Theorem plus_assoc' : forall n m o, plus_assoc_def n m o.
Proof.
  induction n.
    reflexivity.
    intros. unfold plus_assoc_def in IHn. unfold plus_assoc_def. simpl.
      rewrite -> IHn. trivial.
Qed.

Definition plus_comm_def (n m : nat) :=
  n + m = m + n.

Theorem plus_comm' : forall n m, plus_comm_def n m.
Proof.
  induction n.
    unfold plus_comm_def. intros. rewrite -> plus_0_r. reflexivity.
    intros. unfold plus_comm_def. rewrite <- plus_n_Sm. simpl.
      unfold plus_comm_def in IHn. rewrite -> IHn. reflexivity.
Qed.

(* END plus_explicit_prop. *)

(* ((Additional Exercises)) *)

(* Exercise: 2 stars, optional (foo_ind_principle) *)

(* P (foo1 X Y x)
P (foo2 X Y y)
forall (f : foo X Y), P f -> P (foo3 X Y f)
forall (f : foo X Y), P f.
*)

(* END foo_ind_principle. *)

(* Exercise: 2 stars, optional (bar_ind_principle) *)

Inductive bar_set : Set :=
  | bar1 : nat -> bar_set
  | bar2 : bar_set -> bar_set
  | bar3 : bool -> bar_set -> bar_set.

(* END bar_ind_principle. *)
