Require Export Induction.

Module NatList.

(* ((Pairs of Numbers)) *)

Definition swap_pair (p : nat * nat) : nat * nat :=
  match p with
    | (x, y) => (y, x)
  end.

(* Exercise: 1 star (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p : nat * nat),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

(* END snd_fst_is_swap. *)
