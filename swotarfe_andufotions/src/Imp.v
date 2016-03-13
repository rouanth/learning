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
  | Beq : bexp -> bexp -> bexp
  | BLe : bexp -> bexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


