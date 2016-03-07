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
  fun n => fun E => bu_sum n (n + 0) E (bu_sum n 0 E bu_0).

(* END b_times2. *)
