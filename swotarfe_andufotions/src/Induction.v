Require Export Basics.

(* ((Naming Cases)) *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Exercise: 2 stars (andb_true_elim2) *)

Theorem andb_true_elim2 :
  forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
      SCase "b = true".
        reflexivity.
      SCase "b = false".
        reflexivity.
Qed.

(* END andb_true_elim2. *)

(* ((Proof by Induction)) *)

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise: 2 stars (basic_induction) *)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction m as [|m'].
  Case "m = 0".
    rewrite -> plus_0_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite <- IHm'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* END basic_induction. *)

Fixpoint double (n : nat) :=
  match n with
    | O    => O
    | S n' => S (S (double n'))
  end.

(* Exercies: 2 starts (double_plus) *)

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    rewrite <- plus_n_Sm.
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* END double_plus. *)

(* Exercise: 1 start (destruct_induction) *)

(* `induction` is useful when dealing with inductive types: after proving the
* induction base, user is provided with a statement which assumes the
* correctness of the initial statement for a case of the previous inductive
* step. *)

(* END destruct_induction *)

(* Exercise: 4 stars (mult_comm) *)

Theorem plus_swap : forall n m p : nat,
   n + (m + p) = m + (n + p).
Proof.
   intros n m p.
   assert (H1: m + (n + p) = n + p + m).
     rewrite -> plus_comm.
     reflexivity.
   rewrite -> H1.
   assert (H2: m + p = p + m).
     rewrite -> plus_comm.
     reflexivity.
   rewrite -> H2.
   rewrite -> plus_assoc.
   reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_swap.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [|m'].
  Case "m = 0".
    rewrite -> mult_0_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> mult_n_Sm.
    reflexivity.
Qed.

(* END mult_comm. *)

(* Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> negation_fn_applied_twice.
    reflexivity.
    SCase "negb x = negb x".
      reflexivity.
Qed.

(* END evenb_n__oddb_Sn. *)
