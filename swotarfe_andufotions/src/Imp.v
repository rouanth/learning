Require Export SfLib.

(* ((Arithmetic and Boolean Expressions)) *)

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | Beq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Fixpoint aeval (a : aexp) : nat :=
  match a with
    | ANum   n   => n
    | APlus  b c => (aeval b) + (aeval c)
    | AMinus b c => (aeval b) - (aeval c)
    | AMult  b c => (aeval b) * (aeval c)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
    | BTrue    => true
    | BFalse   => false
    | Beq c d  => beq_nat (aeval c) (aeval d)
    | BLe c d  => ble_nat (aeval c) (aeval d)
    | BNot k   => negb (beval k)
    | BAnd c d => (beval c) && (beval d)
  end.
