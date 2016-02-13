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

(* Exercise: 1 star, optional (fst_swap_is_snd) *)

Theorem fst_swap_is_snd : forall (p : nat * nat),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

(* END fst_swap_is_snd. *)

Fixpoint repeat (n count : nat) : list nat :=
  match count with
    | O    => nil
    | S c' => cons n (repeat n c')
  end.

Definition hd (default : nat) (l : list nat) : nat :=
  match l with
    | cons h t => h
    | _        => default
  end.

Definition tl (l : list nat) : list nat :=
  match l with
    | cons h t => t
    | nil      => nil
  end.

(* Exercise: 2 stars (list_funs) *)

Fixpoint nonzeros (l : list nat) : list nat :=
  match l with
    | nil      => nil
    | cons h t => match h with
                    | O => nonzeros t
                    | n => cons n (nonzeros t)
                end
  end.

Example test_nonzeros :
  nonzeros (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: nil)%list
  = (1 :: 2 :: 3 :: nil)%list.
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : list nat) : list nat :=
  match l with
    | nil      => nil
    | cons h t => match oddb h with
                    | false => oddmembers t
                    | true  => cons h (oddmembers t)
                  end
  end.

Example test_oddmembers:
  oddmembers (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: nil)%list
  = (1 :: 3 :: nil)%list.
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : list nat) : nat :=
  length (oddmembers l).

Example test_countoddmembers1 :
  countoddmembers (1 :: 0 :: 3 :: 1 :: 4 :: 5 :: nil)%list = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2 :
  countoddmembers (0 :: 2 :: 4 :: nil)%list = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3 :
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* END list_funs. *)

(* Exercise: 3 stars, advanced (alternate) *)


(* END alternate. *)

