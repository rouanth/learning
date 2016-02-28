Require Export Logic.

(* ((Inductively Defined Propositions)) *)

Inductive ev : nat -> Prop :=
  | ev_O  : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

(* Exercise: 1 star (double_even) *)

Theorem double_even: forall n, ev (double n).
Proof.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    apply ev_O.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

(* END double_even. *)

(* Exercise: 1 star (varieties_of_beauty) *)

(* An infinity, since we can add 0 as much as we like. *)

(* END varieties_of_beauty. *)

Inductive beautiful : nat -> Prop :=
  | bu_0   : beautiful 0
  | bu_3   : beautiful 3
  | bu_5   : beautiful 5
  | bu_sum : forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m).

(* Exercise: 2 stars (b_times2) *)

Theorem b_times2 : forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros n H.
  simpl.
  rewrite -> plus_0_r.
  apply bu_sum.
  apply H.
  apply H.
Qed.

(* END b_times2. *)

