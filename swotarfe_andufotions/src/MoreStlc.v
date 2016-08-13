Require Import SfLib.
Require Import Types.
Require Import Smallstep.
Require Import Stlc.

(* Exercise: 1 star, optional (halve_fix) *)

(*
halve_fix = fix (\f : Nat -> Nat.
              forall x : Nat.
                if x == 0 then 0 else
                if pred x == 0 then 0 else
                1 + f (pred (pred x)))
*)

(* END halve_fix. *)
