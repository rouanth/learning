Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import SfLib.
Require Import Imp.
Require Import Hoare.

(* Exercise: 2 stars (if_minus_plus_reloaded) *)

(*
   {{ True }}
  IFB X ≤ Y THEN
      {{ True /\ X ≤ Y           }} ⇾
      {{ Y = X + (Y - X)         }}
    Z ::= Y - X
      {{ Y = X + Z               }}
  ELSE
      {{ True /\ ~ (X ≤ Y)       }} ⇾
      {{ X + Z = X + Z           }}
    Y ::= X + Z
      {{ Y = X + Z               }}
  FI
    {{ Y = X + Z }}
*)

(* END if_minus_plus_reloaded. *)