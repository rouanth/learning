Require Export PropL.

(* ((Existential Quantification)) *)

(* Exercise: 1 star, optional (english_exists) *)

(* ex nat (fun n => beautiful (S n)) means:
There exists such natural number n that the following number has property
"beautiful" *)

(* END english_exists. *)

(* Exercise: 1 star (dist_not_exists) *)

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
  unfold not.
  intros X P H1 H2.
  inversion H2.
  apply H.
  apply H1.
Qed.

(* END dist_not_exists. *)

(* Exercise: 3 stars, optional (not_exists_dist) *)

Theorem not_exists_dist : excluded_middle -> forall (X : Type) (P : X -> Prop),
  not (exists x, not (P x)) -> (forall x, P x).
Proof.
  unfold not.
  intros EM X P H x.
  apply excluded_middle_implies_classic in EM.
  unfold classic in EM.
  unfold not in EM.
  apply EM.
  intros pxf.
  apply H.
  exists x.
  apply pxf.
Qed.

(* END not_exists_dist. *)

(* Exercise: 2 stars (dist_exists_or) *)

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  Case "a -> b".
    intros H.
    inversion H.
    inversion H0.
    left.
    exists x.
    apply H1.
    right.
    exists x.
    apply H1.
  Case "a <- b".
    intros H.
    inversion H.
    inversion H0.
    exists x.
    left.
    apply H1.
    inversion H0.
    exists x.
    right.
    apply H1.
Qed.

(* END dist_exists_or. *)

(* ((Evidence-Carrying Booleans)) *)

Theorem eq_nat_dec : forall n m : nat, { n = m } + { n <> m }.
Proof.
  induction n.
  Case "n = 0".
    destruct m.
    SCase "m = 0".
      left.
      trivial.
    SCase "m = S m".
      right.
      intros H.
      inversion H.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      right.
      intros H.
      inversion H.
    SCase "m = S m".
      destruct IHn with (m := m).
      left. apply f_equal. apply e.
      right. intros H. apply n0. inversion H. trivial.
Defined.

Definition override' {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if eq_nat_dec k k' then x else f k'.

(* Exercise: 1 star (override_shadow') *)

Theorem override_shadow' : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  trivial.
  trivial.
Qed.

(* ((Additional Exercises)) *)

(* Exercise: 3 stars (all_forallb) *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil  : all P nil
  | all_cons : forall x l, P x -> all P l -> all P (cons x l).

Theorem forallb_true_all: forall (X : Type) (test : X -> bool) (l : list X),
  all (fun x => test x = true) l -> forallb test l = true.
Proof.
  intros X test l.
  induction l.
    reflexivity.
    intros H.
    simpl.
    inversion H.
    rewrite -> H2.
    simpl.
    apply IHl.
    apply H3.
Qed.

Theorem forallb_false_not_all :
  forall (X : Type) (test : X -> bool) (l : list X),
  not (all (fun x => test x = true) l) -> forallb test l = false.
Proof.
  intros X test l.
  unfold not.
  induction l.
  Case "l = nil".
    intros H.
    apply ex_falso_quodlibet.
    apply H.
    apply all_nil.
  Case "l = a :: l".
    intros H.
    simpl.
    destruct (test a) eqn: Q.
    SCase "test a = true".
      simpl.
      apply IHl.
      intros H'.
      apply H.
      apply all_cons.
      apply Q.
      apply H'.
    SCase "test a = false".
      reflexivity.
Qed.

(* END all_forallb. *)
