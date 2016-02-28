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

(* Exercise: 3 stars (b_timesm) *)

Theorem b_timesm : forall n m, beautiful n -> beautiful (m * n).
Proof.
  intros n m H.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    apply bu_0.
  Case "m = S m'".
    simpl.
    apply bu_sum.
    apply H.
    apply IHm'.
Qed.

(* END b_timesm. *)

(* ((Using Evidence in Proofs)) *)

Inductive gorgeous : nat -> Prop :=
  | g_0     : gorgeous 0
  | g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
  | g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

(* Exercise: 1 star (gorgeous_tree) *)

(*

  ------------------ g_0
      gorgeous 0

      gorgeous n
  ------------------ g_plus3
   gorgeous (3 + n)

      gorgeous n
  ------------------ g_plus5
   gorgeous (5 + n)

*)

(* END gorgeous_tree. *)

(* Exercise: 1 star (gorgeous_plus13) *)

Theorem gorgeous_plus13 : forall n, gorgeous n -> gorgeous (13 + n).
Proof.
  intros n H.
  induction H.
  Case "g 13".
    simpl.
    apply g_plus5.
    apply g_plus5.
    apply g_plus3.
    apply g_0.
  Case "g (13 + (3 + n))".
    rewrite -> plus_swap.
    apply g_plus3.
    apply IHgorgeous.
  Case "g (13 + (5 + n))".
    rewrite -> plus_swap.
    apply g_plus5.
    apply IHgorgeous.
Qed.

(* END gorgeous_plus13. *)

Theorem gorgeous__beautiful : forall n, gorgeous n -> beautiful n.
Proof.
  intros n H.
  induction H.
  Case "b 0".
    apply bu_0.
  Case "b (3 + n)".
    apply bu_sum.
    apply bu_3.
    apply IHgorgeous.
  Case "b (5 + n)".
    apply bu_sum.
    apply bu_5.
    apply IHgorgeous.
Qed.

(* Exercise: 2 stars (gorgeous_sum) *)

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  Case "0 + m".
    simpl. apply H2.
  Case "3 + n + m".
    apply g_plus3. apply IHgorgeous.
  Case "5 + n + m".
    apply g_plus5. apply IHgorgeous.
Qed.

(* END gorgeous_sum. *)

(* Exercise: 3 stars, advanced (beautiful__gorgeous) *)

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H.
  induction H.
  Case "n = 0".
    apply g_0.
  Case "n = 3".
    apply g_plus3.
    apply g_0.
  Case "n = 5".
    apply g_plus5.
    apply g_0.
  Case "n = n' + m".
    apply gorgeous_sum.
    apply IHbeautiful1.
    apply IHbeautiful2.
Qed.

(* END beautiful__gorgeous. *)

(* Exercise: 3 stars, optional (g_times2) *)

Theorem g_times2 : forall n, gorgeous n -> gorgeous (2 * n).
Proof.
  intros n H.
  simpl.
  rewrite -> plus_0_r.
  apply gorgeous_sum.
    apply H.
    apply H.
Qed.

(* Huh? *)

(* END g_times2. *)

(* Exercise: 1 star (ev__even) *)

(* No since the evidence for ev (S n) where n is an arbitrary natural number
* can't be constructed. *)

(* END ev__even. *)

(* Exercise: 1 star (l_fails) *)

(* All we know is that n' is even; it tells us nothing about S n'. Since
* neither evidence not the evidence of the lack thereof can be constructed,
* we are unable to continue. *)

(* END l_fails. *)

(* Exercise: 2 stars (ev_sum) *)

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  Case "ev m -> ev (0 + m)".
    simpl.
    apply H2.
  Case "ev (S (S n) + m)".
    simpl.
    apply ev_SS.
    apply IHev.
Qed.

(* END ev_sum. *)

(* Exercise: 1 star, optional (ev_minus2_n) *)

(* We are ultimately left with a statement that ev (S (S n)) is true and sould
* prove that ev n is also true. But it's the first that follows from the
* second, not vice versa. *)

(* END ev_minus2_n. *)

(* Exercise: 1 star (inversion_practice) *)

Theorem SSSSev_even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

(* END inversion_practice. *)


