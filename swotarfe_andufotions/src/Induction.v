Require Export Basics.

(* ((Naming Cases)) *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Exercise: 2 stars (andb_true_elim2) *)

Theorem andb_true_elim2 :
  forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
      SCase "b = true".
        reflexivity.
      SCase "b = false".
        reflexivity.
Qed.

(* END andb_true_elim2. *)

(* ((Proof by Induction)) *)

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise: 2 stars (basic_induction) *)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction m as [|m'].
  Case "m = 0".
    rewrite -> plus_0_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite <- IHm'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* END basic_induction. *)

Fixpoint double (n : nat) :=
  match n with
    | O    => O
    | S n' => S (S (double n'))
  end.

(* Exercies: 2 starts (double_plus) *)

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    rewrite <- plus_n_Sm.
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* END double_plus. *)

(* Exercise: 1 start (destruct_induction) *)

(* `induction` is useful when dealing with inductive types: after proving the
* induction base, user is provided with a statement which assumes the
* correctness of the initial statement for a case of the previous inductive
* step. *)

(* END destruct_induction *)

(* Exercise: 4 stars (mult_comm) *)

Theorem plus_swap : forall n m p : nat,
   n + (m + p) = m + (n + p).
Proof.
   intros n m p.
   assert (H1: m + (n + p) = n + p + m).
     rewrite -> plus_comm.
     reflexivity.
   rewrite -> H1.
   assert (H2: m + p = p + m).
     rewrite -> plus_comm.
     reflexivity.
   rewrite -> H2.
   rewrite -> plus_assoc.
   reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_swap.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [|m'].
  Case "m = 0".
    rewrite -> mult_0_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> mult_n_Sm.
    reflexivity.
Qed.

(* END mult_comm. *)

(* Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> negation_fn_applied_twice.
    reflexivity.
    SCase "negb x = negb x".
      reflexivity.
Qed.

(* END evenb_n__oddb_Sn. *)

(* (( More Excercises )) *)

(* Exercise: 3 stars, optional (more_exercises) *)

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.  

Theorem zero_nbeq_S : forall n : nat,
  beq_nat O (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [|p'].
  Case "p = 0".
    simpl.
    rewrite -> H.
    reflexivity.
  Case "p = S p'".
    simpl.
    rewrite -> IHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_0_r.
  reflexivity.
Qed.

Theorem excluded_middle : forall b : bool,
  orb b (negb b) = true.
Proof.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b.
  Case "b = true".
    simpl.
    rewrite -> excluded_middle.
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p'].
  Case "p = 0".
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    reflexivity.
  Case "p = S p'".
    rewrite -> mult_n_Sm.
    rewrite -> mult_n_Sm.
    rewrite -> mult_n_Sm.
    rewrite -> IHp'.
    assert (H : m + (n * p' + m * p') = n * p' + (m + m * p')).
      rewrite -> plus_swap.
      reflexivity.
    rewrite <- plus_assoc.
    rewrite -> H.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> mult_plus_distr_r.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* END more_exercises. *)

(* Exercise: 2 stars, optional (beq_nat_refl) *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. 
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* END beq_nat_refl. *)

(* Exercise: 2 stars, optional (plus_swap') *)

Theorem plus_swap' : forall n m p : nat,
   n + (m + p) = m + (n + p).
Proof.
   intros n m p.
   assert (H1: m + (n + p) = n + p + m).
     rewrite -> plus_comm.
     reflexivity.
   rewrite -> H1.
   replace (m + p) with (p + m).
   Case "continuing the proof".
     rewrite -> plus_assoc.
     reflexivity.
   Case "replacement m + p -> p + m".
     rewrite -> plus_comm.
     reflexivity.
Qed.

(* END plus_swap'. *)

(* Exercise: 3 stars (binary_commute) *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|p'|p'].
  Case "b = bO".
    reflexivity.
  Case "b = bD p'".
    reflexivity.
  Case "b = bT p'".
    simpl.
    rewrite -> IHp'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

(* END binary_commute. *)

(* Exercise: 5 stars, advanced (binary_inverse) *)

(* a) *)

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | O    => bO
    | S p' => incr (nat_to_bin p')
  end.

Theorem nat_to_bin_bin_to_nat_eq : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* b) *)

(* The problem lies in the fact that bO = bD bO = bD .. bD bO which creates a
* non-linear mapping from natural to binary numbers. *)

(* c) *)

Fixpoint dbl (b : bin) : bin :=
  match b with
    | bO => bO
    | b' => bD b'
  end.

Fixpoint normalize (b : bin) : bin :=
  match b with
    | bO => bO
    | bD p' => dbl (normalize p')
    | bT p' => bT (normalize p')
  end.

Theorem bin_normalize : forall b : bin,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [|b'|b'].
  Case "b = bO".
    reflexivity.
  Case "b = bD b'".
    simpl.
    rewrite <- IHb'.
    assert (dbl_doubles : forall n : nat,
            nat_to_bin (n + n) = dbl (nat_to_bin n)).
      intros n.
      induction n as [|n'].
      SCase "n = 0".
        reflexivity.
      SCase "n = S n'".
        simpl.
        rewrite <- plus_n_Sm.
        simpl.
        rewrite -> IHn'.
        assert (H : forall b : bin, incr (incr (dbl b)) = dbl (incr b)).
          induction b as [|p|p].
          SSCase "b = bO".
            reflexivity.
          SSCase "b = bD p".
            reflexivity.
          SSCase "b = bT p".
            reflexivity.
        rewrite -> H.
        reflexivity.
    rewrite -> dbl_doubles.
    reflexivity.
  Case "b = bT b'".
    simpl.
    rewrite <- IHb'.
    assert (H: forall n : nat, incr (nat_to_bin (n + n)) = bT (nat_to_bin n)).
      induction n as [|n']. 
      SCase "n = 0".
        reflexivity.
      SCase "n = S n'".
        rewrite <- plus_n_Sm.
        simpl.
        rewrite -> IHn'.
        reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

(* END binary_inverse. *)

