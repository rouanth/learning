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

(* Exercise: 2 stars (slow_assignment) *)

(*
        {{ X = m               }} ->
        {{ X + 0 = m           }}
      Y ::= 0;;
        {{ X + Y = m           }}
      WHILE X ≠ 0 DO
        {{ X + Y = m /\ X ≠ 0  }} ->
        {{ (X - 1) + Y = m - 1 }}
        X ::= X - 1;;
        {{ X + Y = m - 1       }} ->
        {{ X + (Y + 1) = m     }}
        Y ::= Y + 1
        {{ X + Y = m           }}
      END
        {{ X + Y = m /\ X = 0  }} ->
        {{ Y = m               }}
*)

(* END slow_assignment. *)

(* Exercise: 3 stars, optional (add_slowly_decoration) *)

(*
        {{ X = m /\ Z = n            }} ->
        {{ X + Z = m + n             }}
      WHILE X ≠ 0 DO
        {{ X + Z = m + n /\ X ≠ 0    }} ->
        {{ (X - 1) + (Z + 1) = m + n }}
         Z ::= Z + 1;;
        {{ (X - 1) + Z = m + n       }}
         X ::= X - 1
        {{ X + Z = m + n             }}
      END
        {{ X + Z = m + n /\ X = 0    }}
        {{ Z = n + m                 }}
*)

(* END add_slowly_decoration. *)
