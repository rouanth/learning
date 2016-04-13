Require Import Imp.

(* ((Evaluation Function)) *)

Notation "'LETOPT' x <== e1 'IN' e2" :=
   (match e1 with
      | Some x => e2
      | None => None
   end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state := 
  match i with
    | 0    => None
    | S i' =>
    match c with
      | CSkip     => Some st
      | CAss  x a => Some (update st x (aeval st a))
      | CSeq  c d => LETOPT st' <== ceval_step st c i' IN ceval_step st' d i'
      | CIf b t e => if beval st b then ceval_step st t i'
                                     else ceval_step st e i'
      | CWhile b k => if beval st b
                      then LETOPT st' <== ceval_step st k i'
                           IN ceval_step st' c i'
                      else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) := 
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Eval compute in 
  (test_ceval empty_state
    (
      X ::= ANum 2;;
      IFB BLe (AId X) (ANum 1)
        THEN Y ::= ANum 3
        ELSE Z ::= ANum 4
      FI
    )).

(* Exercise: 2 stars (pup_to_n) *)

Example pup_to_n_1 :
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* END pup_to_n. *)

(* Exercise: 2 stars, optional (peven) *)

Definition peven : com :=
  Z ::= ANum 1;;
  WHILE BLe (ANum 1) (AId X) DO
    X ::= AMinus (AId X) (ANum 1);;
    IFB BEq (AId Z) (ANum 1) THEN Z ::= ANum 0 ELSE Z ::= ANum 1 FI
  END
.

Example peven_test :
  test_ceval (update empty_state X 5) peven
  = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven_test2 :
  test_ceval (update empty_state X 10) peven
  = Some (0, 0, 1).
Proof. reflexivity. Qed.

(* END peven. *)
