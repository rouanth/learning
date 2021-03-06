Require Export MoreLogic.

(* ((Proof Scripts and Proof Objects)) *)

(* Exercise: 1 star (six_is_beautiful) *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply (bu_sum 3 3 bu_3 bu_3).
Qed.

Definition six_is_beautiful' := bu_sum 3 3 bu_3 bu_3.

(* END six_is_beautiful. *)

(* Exercise: 1 star (nine_is_beautiful) *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  apply (bu_sum 3 6 bu_3 (bu_sum 3 3 bu_3 bu_3)).
Qed.

Definition nine_is_beautiful' := bu_sum 3 6 bu_3 (bu_sum 3 3 bu_3 bu_3).

(* END nine_is_beautiful. *)

(* ((Quantification, Implications and Functions)) *)

(* Exercise: 2 stars b_times2 *)

Definition b_times2' : forall (n : nat), beautiful n -> beautiful (2 * n) :=
  fun n E => bu_sum n (n + 0) E (bu_sum n 0 E bu_0).

(* END b_times2. *)

(* Exercise: 2 stars, optional (gorgeous_plus13_po) *)

Definition gorgeous_plus13_po : forall n, gorgeous n -> gorgeous (13 + n) :=
  fun n E => g_plus5 (8 + n) (g_plus5 (3 + n) (g_plus3 n E)).

(* END gorgeous_plus13_po. *)

(* Exercise: 1 star, optional (case_proof_objects) *)

Theorem and_example :
  (beautiful 0) /\ (beautiful 3).
Proof.
  split.
  Case "left".  apply bu_0.
  Case "right". apply bu_3.
Qed.

(* END case_proof_objects. *)

(* Exercise: 2 stars, optional (conj_fact) *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R E1 E2 =>
    match (E1, E2) with
      | (conj Pt Qt, conj Qt2 Rt) => @conj P R Pt Rt
    end.

(* END conj_fact. *)

(* Exercise: 2 stars, advanced, optional (beautiful_iff_gorgeous) *)

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  fun n => conj (beautiful__gorgeous n) (gorgeous__beautiful n).

(* END beautiful_iff_gorgeous. *)

(* Exercise: 2 stars, optional (or_commut'') *)

Definition or_commut : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q H =>
  match H with
    | or_intror Hp => or_introl Hp
    | or_introl Hq => or_intror Hq
  end.

(* END or_commut''. *)

(* Exercise: 2 stars, optional (ex_beautiful_Sn) *)

Definition p : ex (fun n => beautiful (S n)) :=
  ex_intro _ 2 bu_3.

(* END ex_beautiful_Sn. *)

(* ((Giving Explicit Arguments to Lemmas and Hypotheses)) *)

(* Exercise: 2 stars (trans_eq_example_redux) *)

Example trans_eq_example' : forall (a b c d e f : nat),
  (a :: b :: nil)%list = (c :: d :: nil)%list ->
  (c :: d :: nil)%list = (e :: f :: nil)%list ->
  (a :: b :: nil)%list = (e :: f :: nil)%list.
Proof.
  intros a b c d e f.
  apply (trans_eq _ _ (c :: d :: nil)%list).
Qed.

(* END trans_eq_example_redux. *)
