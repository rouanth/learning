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

(* Exercise: 2 stars, advanced, optional (hoare_havoc_weakest) *)

Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : id),
  {{ P }} HAVOC X {{ Q }} ->
  P ->> havoc_pre X Q.
Proof.
  unfold hoare_triple. unfold assert_implies. unfold havoc_pre.
  intros.
  apply H with st; try assumption. constructor.
Qed.

End Himp2.

(* END hoare_havoc_weakest. *)

Inductive dcom : Type :=
  | DCSkip : Assertion -> dcom
  | DCSeq  : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp -> Assertion -> dcom
  | DCIf   : bexp -> Assertion -> dcom
                  -> Assertion -> dcom
                  -> Assertion -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre   : Assertion -> dcom -> dcom
  | DCPost  : dcom -> Assertion -> dcom.

Notation "'SKIP' {{ P }}" :=
  (DCSkip P) (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" :=
  (DCAsgn l a P) (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" :=
  (DCWhile b Pbody d Ppost) (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}" :=
  (DCIf b P d P' d' Q) (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d" :=
  (DCPre P d) (at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d" :=
  (DCPre P d) (at level 90) : dcom_scope.
Notation "d '->>' {{ P }}" :=
  (DCPost d P) (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' " :=
  (DCSeq d d') (at level 80, right associativity) : dcom_scope.

Delimit Scope dcom_scope with dcom.

Fixpoint extract (d : dcom) : com :=
  match d with
    | DCSkip _ => SKIP
    | DCSeq d1 d2 => (extract d1) ;; (extract d2)
    | DCAsgn i a _ => i ::= a
    | DCIf b _ t _ e _ => IFB b THEN (extract t) ELSE (extract e) FI
    | DCWhile b _ d _ => WHILE b DO (extract d) END
    | DCPre _ d => extract d
    | DCPost d _ => extract d
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
    | DCSkip P => P
    | DCSeq _ d => post d
    | DCAsgn _ _ q => q
    | DCIf _ _ _ _ _ q => q
    | DCWhile _ _ _ q => q
    | DCPre _ d => post d
    | DCPost _ q => q
  end.

Fixpoint pre (d : dcom) : Assertion :=
  match d with
    | DCSkip P => fun st => True
    | DCSeq d _ => pre d
    | DCAsgn _ _ _ => fun st => True
    | DCIf _ _ _ _ _ _ => fun st => True
    | DCWhile _ _ _ _ => fun st => True
    | DCPre q _ => q
    | DCPost d _ => pre d
  end.

Definition dec_correct (d : dcom) :=
  {{pre d}} (extract d) {{post d}}.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
    | DCSkip q => P ->> q
    | DCSeq d1 d2 => (verification_conditions P d1) /\
                     (verification_conditions (post d1) d2)
    | DCAsgn i a q => P ->> q [i |-> a]
    | DCIf b qt t qe e qp => ((fun st => P st /\ bassn b st) ->> qt)
                          /\ ((fun st => P st /\ ~ bassn b st) ->> qe)
                          /\ (post t ->> qp) /\ (post e ->> qp)
                          /\ (verification_conditions qt t)
                          /\ (verification_conditions qe e)
    | DCWhile b qb d qp => P ->> post d
                          /\ ((fun st => post d st /\ bassn b st)   ->> qb)
                          /\ ((fun st => post d st /\ ~ bassn b st) ->> qp)
                          /\ (verification_conditions qb d)
    | DCPre q d => P ->> q /\ verification_conditions q d
    | DCPost d q => verification_conditions P d /\ (post d ->> q)
  end.

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{ P }} (extract d) {{ post d }}.
Proof.
  induction d; simpl; intros P H.
  - eapply hoare_consequence_pre. apply hoare_skip. assumption.
  - destruct H. eapply hoare_seq; [apply IHd2 | apply IHd1]; assumption.
  - eapply hoare_consequence_pre. eapply hoare_asgn. assumption.
  - destruct H. destruct H0. destruct H1. destruct H2. destruct H3.
    apply hoare_if; eapply hoare_consequence;
      try apply IHd1; try apply IHd2; try eassumption.
  - destruct H. destruct H0. destruct H1.
    eapply hoare_consequence.
    + apply hoare_while. eapply hoare_consequence_pre; try apply IHd;
        eassumption.
    + assumption.
    + assumption.
  - destruct H. eapply hoare_consequence_pre.
    + apply IHd. eassumption.
    + assumption.
  - destruct H. eapply hoare_consequence_post; try apply IHd; assumption.
Qed.

Tactic Notation "verify" :=
  apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite update_eq;
  repeat (rewrite update_neq; [| (intro X; inversion X)]);
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
          [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try omega.

(* Exercise: 3 stars, advanced (slow_assignment_dec) *)

Example slow_assignment_dec (m:nat) : dcom :=
  (
        {{ fun st => st X = m     }} ->>
        {{ fun st => st X + 0 = m }}
      Y ::= ANum 0
        {{ fun st => st X + st Y = m }} ;;
      WHILE (BNot (BEq (AId X) (ANum 0))) DO
        {{ fun st => st X + st Y = m /\
           bassn (BNot (BEq (AId X) (ANum 0))) st }}
        {{ fun st => (st X - 1) + st Y = m - 1 /\ m > 0 }}
        X ::= AMinus (AId X) (ANum 1)
        {{ fun st => st X + st Y = m - 1 /\ m > 0 }} ;; ->>
        {{ fun st => st X + (st Y + 1) = m     }}
        Y ::= APlus (AId Y) (ANum 1)
        {{ fun st => st X + st Y = m           }}
      END
        {{ fun st => st X + st Y = m /\ st X = 0  }} ->>
        {{ fun st => st Y = m               }}
)%dcom.

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof.
  intros. verify.
Qed.

(* END slow_assignment_dec. *)

(* Exercise: 4 stars, advanced (factorial_dec) *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Example factorial_dec (n : nat) : dcom :=
(
  {{ fun st => st X = n           }}
    Y ::= ANum 1
  {{ fun st => st Y * real_fact (st X) = real_fact n }} ;;
    WHILE (BNot (BEq (AId X) (ANum 0))) DO
      {{ fun st => st Y * (st X * real_fact (st X - 1)) = real_fact n
         /\ ~ st X = 0 }} ->>
      {{ fun st => (st Y * st X) * real_fact (st X - 1) = real_fact n
         /\ ~ st X = 0 }}
        Y ::= AMult (AId Y) (AId X)
      {{ fun st => st Y * real_fact (st X - 1) = real_fact n
         /\ st X <> 0 }} ;;
        X ::= AMinus (AId X) (ANum 1)
      {{ fun st => st Y * real_fact (st X) = real_fact n }}
    END
  {{ fun st => st Y * real_fact (st X) = real_fact n /\ st X = 0 }} ->>
  {{ fun st => st Y = real_fact n }}
) % dcom.

Theorem factorial_dec_correct : forall n,
  dec_correct (factorial_dec n).
Proof.
  intros. verify.
  - destruct (st X). apply ex_falso_quodlibet. apply H0. trivial.
    simpl in *. rewrite <- minus_n_O. assumption.
  - rewrite <- H. rewrite mult_assoc. trivial.
  - rewrite <- H. simpl. rewrite mult_1_r. trivial.
Qed.

(* END factorial_dec. *)
