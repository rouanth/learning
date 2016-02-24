Require Export Poly.

(* ((The apply Tactic)) *)

(* Exercise: 2 stars, optional (silly_ex) *)

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros H.
  apply H.
Qed.

(* END silly_ex. *)

(* Exercise: 3 stars (apply_exercise1) *)

Theorem rev_injective : forall l1 l2 : list nat,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  rewrite <- rev_involutive.
  replace l1 with (rev (rev l1)).
  Case "rev (rev l1) = rev (rev l2)".
    rewrite <- H.
    reflexivity.
  Case "l1 = rev (rev l1)".
    rewrite -> rev_involutive.
    reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  symmetry.
  apply rev_injective.
  rewrite -> rev_involutive.
  apply H.
Qed.

(* END apply_exercise1. *)

(* Exercise: 1 star, optional (apply_rewrite) *)

(* Apply matches the expression completely, including its conditions, against
* which rewrite is powerless.
* On the other hand, rewrite can be applied to parts of expressions, which is
* not true for apply.
*)

(* END apply_rewrite. *)

(* ((The apply ... with ... Tactic)) *)

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intros H H1.
  rewrite <- H1.
  apply H.
Qed.

(* Exercise: 3 stars, optional (apply_with_exercise) *)

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros H1 H2.
  apply trans_eq with m.
  Case "n + p = m".
    apply H2.
  Case "m = minustwo o".
    apply H1.
Qed.

(* END apply_with_exercise. *)

(* ((The inversion tactic)) *)

(* Exercise: 1 star (sillyex1) *)

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
  (x :: y :: l)%list = (z :: j)%list ->
  (y :: l)%list = (x :: j)%list ->
  x = y.
Proof.
  intros X x y z l j.
  intros H1 H2.
  inversion H2.
  reflexivity.
Qed.

(* END sillyex1. *)

(* Exercise: 1 star (sillyex2) *)

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
  (x :: y :: l)%list = nil ->
  (y :: l)%list = (z :: j)%list ->
  x = z.
Proof.
  intros X x y z l j.
  intros H1 H2.
  inversion H1.
Qed.

(* END sillyex2. *)

(* Exercise: 2 stars, optional (practice) *)

Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros n H.
  destruct n.
  reflexivity.
  inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
  beq_nat n 0 = true -> n = 0.
Proof.
  intros n H.
  induction n as [|n'].
  reflexivity.
  inversion H.
Qed.

(* END practice. *)

(* ((Using Tactics on Hypotheses)) *)

(* Exercise: 3 stars (plus_n_n_injective) *)

Theorem plus_0_0_0 : forall (n m : nat), 0 = n + m -> n = 0.
Proof.
  intros n m H.
  induction n as [|n'].
    reflexivity.
    inversion H.
Qed.

Theorem plus_n_n_injective : forall (n m : nat), n + n = m + m -> n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    simpl in H.
    apply plus_0_0_0 in H.
    symmetry.
    apply H.
  Case "n = S n'".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
      rewrite -> H1.
      trivial.
Qed.

(* END plus_n_n_injective. *)

(* ((Varying the Induction Hypothesis)) *)

(* Exercise: 2 stars (beq_nat_true) *)

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m.
    SCase "m = 0".
      trivial.
    SCase "m = S m'".
      inversion H.
  Case "n = S n'".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      simpl in H.
      apply IHn' in H.
      rewrite -> H.
      trivial.
Qed.

(* END beq_nat_true. *)

(* Exercise: 2 stars, advanced (beq_nat_true_informal) *)

(* Performing an induction on n, we have the following cases:
* a) n is 0;
* b) n is an increment of another number.
* In the first case, the possible m are 0 or an increment of another number;
* the first case is trivial, while the second is contradictory by the
* definition of beq_nat.
* The inductive step is proving that for every non-zero n, if beq_nat n m is
* true, the numbers are equal.
* If m is zero, there is a contradiction: beq_nat 0 (S m') is always false.
* If m is non-zero, then, beq_nat (S n') (S m') being the same as
* beq_nat n' m', falls under the induction hypothesis.
*)

(* END beq_nat_true_informal. *)

(* Exercise: 3 stars (gen_dep_practice) *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|m l'].
  Case "l = nil".
    reflexivity.
  Case "l = m :: l'".
    intros n H.
    destruct n.
    SCase "n = 0".
      inversion H.
    SCase "n = S n'".
      inversion H.
      simpl.
      apply IHl'.
      trivial.
Qed.

(* END gen_dep_practice. *)

(* Exercise: 3 stars, advanced, optional (index_after_last_informal) *)

(* Let l be a list. By induction on l we can prove that, for every list, if
 * its length equals the requested index, function index for these index and
 * list returns None.
 * 
 * If l is an empty list, the case is trivial: for every empty list the
 * index function return None.
 *
 * If l is created by adding an element to an existing list, that is,
 * presented in the form `cons m l'` where m is a single element and l' is a
 * list, then we should perform a case analysis for the index, using the
 * induction hypothesis: if an index equals the list's length, index n l' =
 * None.
 *
 * If the index is zero, it can't be equal to the list's length by definition
 * of length.
 *
 * If the index in an increment of another number, we have length (m :: l') =
 * S n', which simplifies to length l' = n'. That condition matches the one in
 * the induction hypothesis, so we apply it.
*)

(* END index_after_last_informal. *)

(* Exercise: 3 stars, optional (gen_dep_practice_more) *)

Theorem length_snoc''' : forall (n : nat) (X : Type) (v : X) (l : list X),
  length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [|m l'].
  Case "l = nil".
    intros n H.
    simpl in H.
    rewrite <- H.
    reflexivity.
  Case "l = m :: l'".
    intros n H.
    destruct n.
    SCase "n = 0".
      inversion H.
    SCase "n = S n'".
      inversion H.
      rewrite -> H1.
      apply IHl' in H1.
      simpl.
      rewrite -> H1.
      trivial.
Qed.

(* END gen_dep_practice_more. *)

(* Exercise: 3 stars, optional (app_length_cons) *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat)
  , length (l1 ++ (x :: l2))%list = n -> S (length (l1 ++ l2)%list) = n.
Proof.
  intros X l1.
  induction l1 as [|m l1'].
  Case "l1 = nil".
    simpl.
    intros l2 x n H.
    apply H.
  Case "l1 = m :: l1'".
    simpl.
    intros l2 x n H.
    destruct n.
      inversion H.
      inversion H.
      rewrite -> H1.
      apply IHl1' in H1.
      rewrite -> H1.
      trivial.
Qed.

(* END app_length_cons. *)

(* Exercise: 4 stars, optional (app_length_twice) *)

Theorem app_nil_invariant : forall (X : Type) (l : list X), app l nil = l.
Proof.
  intros X l.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    trivial.
Qed.

Theorem length_app_comm : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length (l2 ++ l1).
Proof.
  intros X l1.
  induction l1 as [|m l1'].
  Case "l1 = nil".
    intros l2.
    rewrite -> app_nil_invariant.
    reflexivity.
  Case "l1 = m :: l1'".
    intros l2.
    simpl.
    rewrite -> IHl1'.
    induction l2.
    SCase "l2 = nil".
      reflexivity.
    SCase "l2 = a :: l2".
      simpl.
      rewrite -> IHl2.
      reflexivity.
Qed.

Theorem app_length_twice : forall (X : Type) (n : nat) (l : list X),
  length l = n -> length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  generalize dependent X.
  induction l as [|m l'].
  Case "l = nil".
    intros n H.
    inversion H.
    reflexivity.
  Case "l = m :: l'".
    intros n H.
    simpl.
    rewrite <- length_app_comm.
    simpl.
    destruct n.
    SCase "n = 0".
      inversion H.
    SCase "n = S n'".
      rewrite <- plus_n_Sm.
      simpl.
      inversion H.
      rewrite <- IHl'.
      trivial.
      trivial.
Qed.

(* END app_length_twice. *)

(* Exercise: 3 stars, optional (double_induction) *)

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P.
  intros P00.
  intros Pm0.
  intros P0n.
  intros Pmn.
  intros m.
  induction m as [|m'].
  Case "m = 0".
    induction n as [|n'].
    SCase "n = 0".
      apply P00.
    SCase "n = S n'".
      apply P0n.
      apply IHn'.
  Case "m = S m'".
    destruct n as [|n'].
    SCase "n = 0".
      apply Pm0.
      apply IHm'.
    SCase "n = S n'".
      apply Pmn.
      apply IHm'.
Qed.

(* END double_induction. *)

(* Exercise: 1 star (override_shadow) *)

Theorem override_shadow : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2.
  intros H.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "k1 = k2".
    trivial.
  Case "k1 /= k2".
    trivial.
Qed.

(* END override_shadow. *)

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match (l1, l2) with
    | (nil, _) => nil
    | (_, nil) => nil
    | (cons h1 t1, cons h2 t2) => cons (h1, h2) (combine t1 t2)
  end.

(* Exercise: 3 stars, optional (combine_split) *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y.
  intros l.
  induction l as [|x l'].
  Case "l = nil".
    intros l1 l2 H.
    inversion H.
    reflexivity.
  Case "l = x :: l'".
    destruct x.
    simpl.
    destruct (split l') as [l'1 l'2].
    intros l1 l2 H.
    destruct l1.
    SCase "l1 = nil".
      inversion H.
    SCase "l1 = z :: l1'".
      destruct l2.
      SSCase "l2 = nil".
        inversion H.
      SSCase "l2 = m :: l2'".
        simpl.
        inversion H.
        rewrite -> IHl'.
        trivial.
        rewrite -> H2.
        rewrite -> H4.
        trivial.
Qed.

(* END combine_split. *)

(* Exercise: 2 stars (destruct_eqn_practice) *)

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  Case "b = true".
    destruct (f true) eqn: H. 
    SCase "f true = true".
      rewrite -> H.
      apply H.
    SCase "f true = false".
      destruct (f false) eqn: H2.
      SSCase "f false = true".
        apply H.
      SSCase "f false = false".
        apply H2.
  Case "b = false".
    destruct (f false) eqn: H.
    SCase "f false = true".
      destruct (f true) eqn: H2.
      SSCase "f true = true".
        apply H2.
      SSCase "f true = false".
        apply H.
    SCase "f false = false".
      rewrite -> H.
      apply H.
Qed.

(* END destruct_eqn_practice. *)

(* Exercise: 2 stars (override_same) *)

Theorem override_same : forall (X : Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H.
  unfold override.
  destruct (beq_nat k1 k2) eqn: H1.
  Case "k1 = k2".
    apply beq_nat_true in H1.
    rewrite -> H1 in H.
    symmetry.
    apply H.
  Case "k1 /= k2".
    trivial.
Qed.

(* END override_same. *)

(* ((Additional Exercises)) *)

(* Exercise: 3 stars (beq_nat_sym) *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m.
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      reflexivity.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      simpl.
      apply IHn'.
Qed.

(* END beq_nat_sym. *)

(* Exercise: 3 stars, advanced, optional (beq_nat_sym_informal) *)

(* We shall prove it by the induction on n.
*
* The inductive base -- beq 0 m = beq m 0 -- is simple to prove: if m is zero,
* both sides evaluate to truth, otherwise both evaluate to false, by
* definition of beq_nat.
*
* For the inductive step we have beq_nat (S n') m = beq_nat m (S n'), and the
* inductive hypothesis is that for all natural numbers m beq_nat n' m =
* beq_nat m n'. Case analysis on m gives us the following: for m = 0 both
* sides of beq_nat (S n') 0 = beq_nat 0 (S n') equal to zero for every n'; if
* m is a successor of some another number m', then beq_nat (S n') (S m') =
* beq_nat (S m') (S n') evaluates to beq_nat n' m' = beq_nat m' n', which
* corresponds to the inductive hypothesis.
*)

(* END beq_nat_sym_informal. *)

