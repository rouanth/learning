Module Bycicles1.

(* ((Booleans)) *)

(* Exercise: 1 star (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true  => negb b2
    | false => true
  end.

Example test_nandb1: (nandb true false) = true.
  Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
  Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
  Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
  Proof. reflexivity. Qed.

(* END nandb. *)

(* Exercise: 1 star (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
  Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
  Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
  Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
  Proof. reflexivity. Qed.

(* END andb3. *)

(* ((Numbers)) *)

End Bycicles1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* Exercise: 1 star (factorial) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S p => (S p) * (factorial p)
  end.

Example test_factorial1: (factorial 3) = 6.
  Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. reflexivity. Qed.

(* END factorial. *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
           | O    => true
           | S m' => false
         end
  | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(* Exercise: 2 stars (blt_nat) *)

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
  Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
  Proof. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
  Proof. reflexivity. Qed.

(* END blt_nat. *)

(* ((Proof by Rewriting)) *)

(* Exercise: 1 star (plus_id_exercise) *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o NM MO.
  rewrite -> NM.
  rewrite -> MO.
  reflexivity.
Qed.

(* END plus_id_exercise. *)

(* Excercise: 2 stars (mult_S_1) *)

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.

(* END mult_S_1. *)

(* ((Proof by Case Analysis)) *)

(* Exercise: 1 star (zero_nbeq_plus_1) *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

(* END zero_nbeq_plus_1. *)

(* ((More Exercises)) *)

(* Exercise: 2 stars (boolean_functions) *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

(* END boolean_functions. *)

(* Exercise: 2 stars (andb_eq_orb) *)

Lemma andb_true_b:
  forall b : bool, andb true b = b.
Proof.
  intros b.
  reflexivity. 
Qed.

Lemma orb_false_b:
  forall b : bool, orb false b = b.
Proof.
  intros b.
  reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b.
  rewrite <- andb_true_b.
  rewrite -> H.
  reflexivity.
  rewrite <- orb_false_b.
  rewrite <- H.
  reflexivity.
Qed.

(* END andb_eq_orb. *)

(* Exercise: 3 stars (binary) *)

Inductive bin : Type :=
  | bO : bin
  | bD : bin -> bin
  | bT : bin -> bin.

Fixpoint incr (b : bin) : bin :=
  match b with
    | bO   => bT bO
    | bD p => bT p
    | bT p => bD (incr p)
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | bO   => O
    | bD p => 2 * (bin_to_nat p)
    | bT p => S (2 * (bin_to_nat p))
  end.

Example test_bin_incr1: bin_to_nat bO = 0.
  Proof. reflexivity. Qed.

Example test_bin_incr2: bin_to_nat (incr (incr (incr bO))) = 3.
  Proof. reflexivity. Qed.

Example test_bin_incr3: bin_to_nat (incr (incr (incr (incr (incr bO))))) = 5.
  Proof. reflexivity. Qed.

Example test_bin_incr4: bin_to_nat (incr (bT (bD (bT bO)))) = 6.
  Proof. reflexivity. Qed.

Example test_bin_incr5: bin_to_nat (incr (bD (bT (bT (bT bO))))) = 15.
  Proof. reflexivity. Qed.

(* END binary. *)

(* ((Fixpoint and Structural Recursion (Advanced))) *)

(* Exercise: 2 stars, optional (decreasing) *)

(*

Fixpoint fall_apart (n : nat) : nat :=
  match n with
    | O    => fall_apart (S O)
    | S O  => fall_apart (S (S O))
    | S (S O) => O
    | S p  => fall_apart p
  end.

*)

(* END decreasing. *)
