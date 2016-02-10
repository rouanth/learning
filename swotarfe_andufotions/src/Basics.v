Module Bycicles1.

(* ((Booleans)) *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* Exercise: 1 star (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
  Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
  Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
  Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
  Proof. reflexivity. Qed.

(* Exercise: 1 star (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
  Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
  Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
  Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
  Proof. reflexivity. Qed.

(* ((Numbers)) *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Bycicles1.