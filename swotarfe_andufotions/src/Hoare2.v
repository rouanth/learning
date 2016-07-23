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

Fixpoint parity x :=
  match x with
    | 0 => 0
    | 1 => 1
    | S (S x') => parity x'
  end.

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  intros.
  inversion H; subst.
  * trivial.
  * inversion H0; subst.
    + trivial.
    + simpl. rewrite <- minus_n_O. trivial.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
Proof.
  intros.
  destruct x; try destruct x; try trivial.
  assert (2 <= S (S x)). { intros. omega. }
  contradiction.
Qed.

(* Exercise: 3 stars, optional (parity_formal) *)

Theorem parity_correct : forall m,
  {{ fun st => st X = m }}
  (* parity X = parity m *)
  WHILE BLe (ANum 2) (AId X) DO
    (* {{ parity X = parity m /\ X >= 2 }} -> *)
    (* {{ parity (X - 2) = parity m     }}    *)
    X ::= AMinus (AId X) (ANum 2)
    (* {{ parity X = parity m           }}    *)
  END
  (* {{ parity X = parity m /\ X <= 2   }} -> *)
  {{ fun st => st X = parity m }}.
Proof.
  intros.
  eapply hoare_consequence with (P' := fun st => parity (st X) = parity m).
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assert_implies. intros.
      destruct H. unfold assn_sub. simpl. rewrite update_eq.
      rewrite <- H.
      apply parity_ge_2.
      unfold bassn in H0. simpl in H0.
      clear H.
      destruct (st X); try destruct n; inversion H0. omega.
  - unfold assert_implies. intros. rewrite H. trivial.
  - simpl. unfold assert_implies. intros. destruct H.
    unfold bassn in H0. simpl in H0.
    rewrite <- H. clear H.
    symmetry.
    apply parity_lt_2.
    destruct (st X); try destruct n.
    + intro; inversion H.
    + intro; inversion H; inversion H2.
    + intro. apply H0. trivial.
Qed.

(* END parity_formal. *)
