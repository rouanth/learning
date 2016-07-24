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
        {{ X = m               }} ->>
        {{ X + 0 = m           }}
      Y ::= 0;;
        {{ X + Y = m           }}
      WHILE X ≠ 0 DO
        {{ X + Y = m /\ X ≠ 0  }} ->>
        {{ (X - 1) + Y = m - 1 }}
        X ::= X - 1;;
        {{ X + Y = m - 1       }} ->>
        {{ X + (Y + 1) = m     }}
        Y ::= Y + 1
        {{ X + Y = m           }}
      END
        {{ X + Y = m /\ X = 0  }} ->>
        {{ Y = m               }}
*)

(* END slow_assignment. *)

(* Exercise: 3 stars, optional (add_slowly_decoration) *)

(*
        {{ X = m /\ Z = n            }} ->>
        {{ X + Z = m + n             }}
      WHILE X ≠ 0 DO
        {{ X + Z = m + n /\ X ≠ 0    }} ->>
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
    (* {{ parity X = parity m /\ X >= 2 }} ->> *)
    (* {{ parity (X - 2) = parity m     }}     *)
    X ::= AMinus (AId X) (ANum 2)
    (* {{ parity X = parity m           }}     *)
  END
  (* {{ parity X = parity m /\ X <= 2   }} ->> *)
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

(* Exercise: 3 stars (factorial) *)

(*
    {{ X = m }} ⇾
    {{ 1 * X! = m!                          }}
  Y ::= 1;;
    {{ Y * X! = m!                          }}
  WHILE X ≠ 0
  DO   {{ Y * X! = m! /\ X ≠ 0                 }} ⇾
       {{ (Y * X) * (X - 1)! = m!              }}
     Y ::= Y * X;;
       {{ Y * (X - 1)! = m!                    }}
     X ::= X - 1
       {{ Y * X! = m!                          }}
  END
    {{ Y * X! = m! /\ X = 0                    }} ⇾
    {{ Y = m! }}
*)

(* END factorial. *)

(* Exercise: 3 stars (Min_Hoare) *)

(*
  {{ True }} ⇾
  {{ 0 + min a b = min a b }}
  X ::= a;;
  {{ 0 + min X b = min a b }}
  Y ::= b;;
  {{ 0 + min X Y = min a b }}
  Z ::= 0;;
  {{ Z + min X Y = min a b }}
  WHILE (X ≠ 0 /\ Y ≠ 0) DO
  {{ Z + min X Y = min a b /\ X ≠ 0 /\ Y ≠ 0 }} ⇾
  {{ (Z + 1) + min (X - 1) (Y - 1) = min a b }}
  X := X - 1;;
  {{ (Z + 1) + min X (Y - 1) = min a b }}
  Y := Y - 1;;
  {{ (Z + 1) + min X Y = min a b }}
  Z := Z + 1
  {{ Z + min X Y = min a b }}
  END
  {{ Z + min X Y = min a b /\ (X = 0 \/ X = 0) }} ⇾
  {{ Z = min a b }}
*)

(* END Min_Hoare. *)

(* Exercise: 3 stars (two_loops) *)

(*
    {{ True }} ⇾
    {{ c = 0 + 0 + c                          }}
  X ::= 0;;
    {{ c = X + 0 + c                          }}
  Y ::= 0;;
    {{ c = X + Y + c                          }}
  Z ::= c;;
    {{ Z = X + Y + c                          }}
  WHILE X ≠ a DO
      {{ Z = X + Y + c /\ X ≠ a                 }} ⇾
      {{ Z + 1 = (X + 1) + Y + c                }}
    X ::= X + 1;;
      {{ Z + 1 = X + Y + c                      }}
    Z ::= Z + 1
      {{ Z = X + Y + c                          }}
  END;;
    {{ Z = X + Y + c /\ X = a                 }} ⇾
    {{ Z = a + Y + c                          }}
  WHILE Y ≠ b DO
      {{ Z = a + Y + c /\ Y ≠ b                 }} ⇾
      {{ Z + 1 = a + (Y + 1) + c                }}
    Y ::= Y + 1;;
      {{ Z + 1 = a + Y + c                      }}
    Z ::= Z + 1
      {{ Z = a + Y + c                          }}
  END
    {{ Z = a + Y + c /\ Y = b                   }} ⇾
    {{ Z = a + b + c }} 
*)

(* END two_loops. *)

(* Exercise: 4 stars, optional (dpow2_down) *)

(*

  {{ True }} ->>
  {{ 1 = 2^(0 + 1) - 1 /\ 1 = 2^0 }}
  X ::= 0;;
  {{ 1 = 2^(X + 1) - 1 /\ 1 = 2^X }}
  Y ::= 1;;
  {{ Y = 2^(X + 1) - 1 /\ 1 = 2^X }}
  Z ::= 1;;
  {{ Y = 2^(X + 1) - 1 /\ Z = 2^X }}
  WHILE X ≠ m DO
    {{ Y = 2^(X + 1) - 1 /\ Z = 2^X /\ X ≠ m }} ->>
    {{ Y + 2 * Z = 2^((X + 1) + 1) - 1 /\ 2 * Z = 2^(X + 1) }}
    Z ::= 2 * Z;;
    {{ Y + Z = 2^((X + 1) + 1) - 1 /\ Z = 2^(X + 1) }}
    Y ::= Y + Z;;
    {{ Y = 2^((X + 1) + 1) - 1 /\ Z = 2^(X + 1) }}
    X ::= X + 1
    {{ Y = 2^(X + 1) - 1 /\ Z = 2^X }}
  END
  {{ Y = 2^(X + 1) - 1 /\ Z = 2^X /\ X = m }} ->>
  {{ Y = 2^(m+1) - 1 }}

*)

(* END dpow2_down. *)

(* Exercise: 1 star, optional (wp) *)

(*
  1) {{ X = 5 }}  SKIP  {{ X = 5 }}

  2) {{ Y + Z = 5 }}  X ::= Y + Z {{ X = 5 }}

  3) {{ True }}  X ::= Y  {{ X = Y }}

  4) {{ X = 0 /\ Z + 1 = 5 \/ X <> 0 /\ W + 2 = 5 }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

  5) {{ False }}
     X ::= 5
     {{ X = 0 }}

  6) {{ False }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }} 
*)

(* END wp. *)

Definition is_wp P c Q :=
  {{ P }} c {{ Q }} /\
  forall P', {{ P' }} c {{ Q }} -> (P' ->> P).

(* Exercise: 3 stars, advanced, optional (is_wp_formal) *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1))
    (fun st => st X <= 5).
Proof.
  unfold is_wp. split.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold assn_sub. unfold assert_implies. intros.
      simpl.
      rewrite update_eq.
      omega.
  - unfold hoare_triple.
    unfold assert_implies.
    intros.
    apply H with (st' := update st X (st Y + 1)) in H0.
    + rewrite update_eq in H0. omega.
    + constructor.
Qed.

(* END is_wp_formal. *)

(* Exercise: 2 stars, advanced, optional (hoare_asgn_weakest) *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  split.
  - apply hoare_asgn.
  - unfold hoare_triple. unfold assert_implies. unfold assn_sub.
    intros.
    apply H with st; try assumption. constructor.
Qed.

(* END hoare_asgn_weakest. *)
