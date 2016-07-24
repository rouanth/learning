Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import SfLib.
Require Import Imp.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm  -> tm  -> tm.

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
    P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
    t1 => t1' ->
    P t1 t2 => P t1' t2
  | ST_Plus2 : forall n t2 t2',
    t2 => t2' ->
    P (C n) t2 => P (C n) t2'
  where " t '=>' t' " := (step t t').

(* Exercise: 1 star (test_step_2) *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      =>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof. apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst. Qed.
(* Proof. repeat constructor. Qed. *)

(* END test_step_2. *)
