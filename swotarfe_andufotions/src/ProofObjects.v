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
