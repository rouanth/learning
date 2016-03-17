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

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | APlus (ANum 0) b => optimize_0plus b
    | APlus b c => APlus (optimize_0plus b) (optimize_0plus c)
    | AMinus b c => AMinus (optimize_0plus b) (optimize_0plus c)
    | AMult b c => AMult (optimize_0plus b) (optimize_0plus c)
  end.

Theorem optimize_0plus_sound''': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  induction a; simpl. trivial.
  destruct a1; simpl. destruct n. simpl. apply IHa2.
                      simpl. rewrite IHa2. trivial.

(* Exercise: 3 stars (optimize_0plus_b) *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | Beq c d => Beq (optimize_0plus c) (optimize_0plus d)
    | BLe c d => BLe (optimize_0plus c) (optimize_0plus d)
    | BNot k  => BNot (optimize_0plus_b k)
    | BAnd c d => BAnd (optimize_0plus_b c) (optimize_0plus_b d)
    | e => e
  end.



(* END optimize_0plus_b. *)
