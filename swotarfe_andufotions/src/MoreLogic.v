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

(* Exercise: 4 stars, advanced (filter_challenge) *)

Inductive merged {X : Type} : list X -> list X -> list X -> Prop :=
  | merged_nil   : merged nil nil nil
  | merged_left  : forall x l1 l2 l3,
                     merged l1 l2 l3 -> merged (x :: l1) l2 (x :: l3)
  | merged_right : forall x l1 l2 l3,
                     merged l1 l2 l3 -> merged l1 (x :: l2) (x :: l3).

Theorem filter_spec : forall (X : Type) (f : X -> bool) (l l1 l2 : list X),
  (all (fun b => f b = true)  l1) ->
  (all (fun b => f b = false) l2) ->
  merged l1 l2 l ->
  filter f l = l1.
Proof.
  intros X f l.
  induction l.
  Case "l = nil".
    intros l1 l2 H1 H2 H3.
    inversion H3.
    reflexivity.
  Case "l = a :: l".
    simpl.
    intros l1 l2 H1 H2 H3.
    inversion H3.
    SCase "merged_left".
      inversion H1.
      SSCase "l1 = nil".
        rewrite <- H7 in H0.
        inversion H0.
      SSCase "x0 :: l5 = l1".
        rewrite <- H9 in H0.
        inversion H0.
        rewrite <- H11 in H7.
        rewrite -> H in H7.
        rewrite -> H7.
        replace (filter f l) with l5.
        trivial.
        symmetry.
        apply IHl with (l2 := l2).
        apply H8.
        apply H2.
        rewrite <- H12.
        apply H5.
    SCase "merged_right".
      inversion H2.
      SSCase "l2 = nil".
        rewrite <- H7 in H4.
        inversion H4.
      SSCase "x0 :: l5 = l2".
        rewrite <- H9 in H4.
        inversion H4.
        rewrite <- H11 in H7.
        rewrite -> H in H7.
        rewrite -> H7.
        apply IHl with (l2 := l3).
        apply H1.
        rewrite <- H12 in H8.
        apply H8.
        apply H5.
Qed.

(* END filter_challenge. *)

(* Exercise: 5 stars, advanced, optional (filter_challenge_2) *)

Theorem filter_empty : forall (X : Type) (test : X -> bool) (l : list X),
  filter test l = nil -> all (fun x => test x = false) l.
Proof.
  intros X test l.
  induction l.
  Case "l = nil".
    intros H.
    apply all_nil.
  Case "l = a :: l".
    intros H.
    simpl in H.
    destruct (test a) eqn: TA.
    SCase "test a = true".
      inversion H.
    SCase "test a = false".
      apply all_cons.
      apply TA.
      apply IHl.
      apply H.
Qed.

Theorem subseq_all : forall (X : Type) (P : X -> Prop) (l1 l2 : list X),
  all P l1 -> subseq l2 l1 -> all P l2.
Proof.
  intros X P l1.
  induction l1.
  Case "l1 = nil".
    intros.
    inversion H0.
    apply all_nil.
  Case "l1 = a :: l1".
    intros.
    inversion H.
    inversion H0.
    apply all_nil.
    generalize dependent H7.
    generalize dependent H4.
    apply IHl1.
    apply all_cons.
    apply H3.
    generalize dependent H7.
    generalize dependent H4.
    apply IHl1.
Qed.

Theorem filter_subseq :
  forall (X : Type) (test : X -> bool) l,
  subseq (filter test l) l.
Proof.
  intros X test.
  induction l.
  Case "l = nil".
    simpl.
    apply subseq_nil.
  Case "l = a :: l".
    simpl.
    destruct (test a).
    SCase "test a = true".
      apply subseq_cons'.
      apply IHl.
    SCase "test a = false".
      apply subseq_cons.
      apply IHl.
Qed.

Theorem all_cons_inv : forall (X : Type) (P : X -> Prop) (x : X) (l : list X),
  all P (x :: l) -> all P l.
Proof.
  intros X P x l H.
  inversion H.
  apply H3.
Qed.

Theorem filter_spec_2_helper :
  forall (X : Type) (test : X -> bool) (n : nat) (l ls : list X),
  length l <= n ->
  subseq ls l -> (all (fun x => test x = true) ls) ->
  length ls <= length (filter test l).
Proof.
  intros X test n.
  induction n.
  Case "n = 0".
    intros l ls Hn Hs.
    inversion Hn.
    apply length_nil_zero in H0.
    rewrite -> H0 in Hs.
    inversion Hs.
    simpl.
    intros.
    apply O_le_n.
  Case "n = S n".
    destruct l.
    SCase "l = nil".
      intros ls Hn Hs.
      inversion Hs.
      simpl.
      intros.
      apply O_le_n.
    SCase "l = a :: l".
      intros ls Hn.
      generalize dependent ls.
      simpl in Hn.
      apply Sn_le_Sm__n_le_m in Hn.
      simpl.
      destruct (test x) eqn : Htx.
      SSCase "test x = true".
        destruct ls.
        SSSCase "ls = nil".
          simpl.
          intros.
          apply O_le_n.
        SSSCase "ls = x0 :: ls".
          intros Hs Ht.
          simpl.
          apply n_le_m__Sn_le_Sm.
          apply all_cons_inv in Ht.
          inversion Hs.
          SSSSCase "cons".
            assert (subseq ls l).
            apply subseq_cons_inv in H1.
            apply H1.
            apply IHn.
            apply Hn.
            apply H3.
            apply Ht.
          SSSSCase "cons'".
            apply IHn.
            apply Hn.
            apply H0.
            apply Ht.
      SSCase "test x = false".
        intros ls Hs Ht.
        inversion Hs.
        SSSCase "ls = nil".
          simpl. apply O_le_n.
        SSSCase "cons".
          apply IHn.
          apply Hn.
          apply H1.
          apply Ht.
        SSSCase "cons'".
          rewrite <- H0 in Ht.
          inversion Ht.
          rewrite -> H in H5.
          rewrite -> H5 in Htx.
          inversion Htx.
Qed.

Theorem filter_spec_2 :
  forall (X : Type) (test : X -> bool) (l ls : list X),
  subseq ls l ->
  (all (fun x => test x = true) ls) ->
  length ls <= length (filter test l).
Proof.
  intros.
  apply filter_spec_2_helper with (n := length l).
  apply le_n.
  apply H.
  apply H0.
Qed.

(* END filter_challenge_2. *)

(* Exercise: 4 stars, advanced (no_repeats) *)

Inductive appears_in {X : Type} (a : X) : list X -> Prop :=
  | ai_here  : forall l,   appears_in a (a :: l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b :: l).

Lemma appears_in_app : forall (X : Type) (xs ys : list X) (x : X),
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs.
  induction xs.
  Case "xs = nil".
    intros ys x H.
    simpl in H.
    right.
    apply H.
  Case "xs = a :: xs".
    intros ys x H.
    simpl in H.
    inversion H.
    left.
    apply ai_here.
    apply IHxs in H1.
    inversion H1.
    left.
    apply ai_later.
    apply H3.
    right.
    apply H3.
Qed.

Lemma app_appears_in : forall (X : Type) (xs ys : list X) (x : X),
  appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs.
  induction xs.
  Case "xs = nil".
    intros ys x H.
    inversion H.
    inversion H0.
    simpl. apply H0.
  Case "xs = a :: xs".
    intros ys x H.
    inversion H.
    inversion H0.
    apply ai_here.
    simpl.
    apply ai_later.
    apply IHxs.
    left.
    apply H2.
    simpl.
    apply ai_later.
    apply IHxs.
    right.
    apply H0.
Qed.

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | dis_nil  : forall l, disjoint nil l 
  | dis_cons : forall x l1 l2, disjoint l1 l2 -> not (appears_in x l2) ->
                disjoint (x :: l1) l2.

Inductive no_repeats {X : Type} : list X -> Prop :=
  | nr_nil  : no_repeats nil
  | nr_cons : forall x l, no_repeats l -> not (appears_in x l) ->
                no_repeats (x :: l).

Theorem disjoint_app_no_repeats : forall (X : Type) (l1 l2 : list X),
  disjoint l1 l2 -> no_repeats l1 -> no_repeats l2 -> no_repeats (l1 ++ l2).
Proof.
  induction l1.
  Case "l1 = nil".
    intros. simpl. apply H1.
  Case "l1 = a :: l1".
    intros. simpl.
    inversion H0.
    inversion H.
    apply nr_cons.
    apply IHl1.
    apply H8.
    apply H4.
    apply H1.
    unfold not.
    intros.
    apply appears_in_app in H11.
    inversion H11.
    unfold not in H5.
    apply H5.
    apply H12.
    unfold not in H10.
    apply H10.
    apply H12.
Qed.

(* END no_repeats. *)

(* Exercise: 3 stars (nostutter) *)

Inductive nostutter {X : Type} : list X -> Prop :=
  | nost_nil  : nostutter nil
  | nost_one  : forall a, nostutter (a :: nil)%list
  | nost_cons : forall a b l, not (a = b) -> nostutter (b :: l)%list ->
                  nostutter (a :: b :: l)%list.

Example test_nostutter1 : nostutter (3 :: 1 :: 4 :: 1 :: 5 :: 6 :: nil)%list.
Proof. repeat constructor; auto. Qed.

Example test_nostutter2 : forall (X : Type), nostutter (@nil X).
Proof. repeat constructor; auto. Qed.

Example test_nostutter3 : nostutter (5 :: nil)%list.
Proof. repeat constructor; auto. Qed.

Example test_nostutter4 : not (nostutter (3 :: 1 :: 1 :: 4 :: nil)%list).
Proof.
  intro.
  repeat match goal with
    h : nostutter _ |- _ => inversion h; clear h; subst end.
  contradiction H1; trivial.
Qed.

(* END nostutter. *)

(* Exercise: 4 stars, advanced (pigeonhole principle) *)

Lemma appears_in_app_split : forall (X : Type) (x : X) (l : list X),
  appears_in x l -> exists l1, exists l2, (l = l1 ++ (x :: l2))%list.
Proof.
  intros X x l H.
  induction l.
  Case "l = nil".
    inversion H.
  Case "l = a :: l".
    inversion H.
    SCase "a = x".
      exists nil.
      exists l.
      reflexivity.
    SCase "appears_in x l".
      apply IHl in H1.
      destruct H1.
      destruct H1.
      exists (a :: x0)%list.
      exists x1.
      rewrite -> H1.
      reflexivity.
Qed.

Inductive repeats {X : Type} : list X -> Prop :=
  | rep_n    : forall x l, appears_in x l -> repeats (x :: l)
  | rep_cons : forall x l, repeats l -> repeats (x :: l).

Theorem pure_functions : forall (X Y : Type) (f : X -> Y) (x1 x2 : X),
  x1 = x2 -> f x1 = f x2.
Proof.
  intros X Y f x1 x2 H.
  rewrite -> H.
  trivial.
Qed.

Theorem appears_app_comm : forall (X : Type) (x : X) (l1 l2 : list X),
  appears_in x (l1 ++ l2) -> appears_in x (l2 ++ l1).
Proof.
  intros.
  apply appears_in_app in H.
  apply or_comm in H.
  apply app_appears_in in H.
  apply H.
Qed.

Theorem length_app_comm : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length (l2 ++ l1).
Proof.
  intros X l1 l2.
  rewrite -> app_length.
  rewrite -> app_length.
  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem pigeonhole_principle :
  excluded_middle ->
  forall (X : Type) (l1 l2 : list X),
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM.
  intros X l1. induction l1 as [|x l1'].
  Case "l1 = nil".
    intros. inversion H0.
  Case "l1 = x :: l1'".
    intros.
    assert (appears_in x (x :: l1')).
      apply ai_here.
    apply H in H1.
    apply appears_in_app_split in H1.
    inversion H1.
    inversion H2.
    rewrite -> H3 in H0.
    rewrite -> length_app_comm in H0.
    unfold lt in H0.
    simpl in H0.
    apply Sn_le_Sm__n_le_m in H0.
    rewrite -> H3 in H.
    assert (forall z : X, appears_in z (x :: l1') ->
        appears_in z (x :: (x1 ++ x0))%list).
      intros z Hz.
      apply H in Hz.
      apply appears_app_comm in Hz.
      simpl in Hz.
      apply Hz.
    (* Excluded middle *)
    assert (appears_in x l1' \/ not (appears_in x l1')).
      apply EM.
    destruct H5.
    SCase "x appears in l1'".
      apply rep_n.
      apply H5.
    SCase "x does not appear in l1'".
      apply rep_cons.
      apply IHl1' with (l2 := (x1 ++ x0)%list).
      intros x2 Hh.
      assert (x2 = x \/ not (x2 = x)).
        apply EM.
      destruct H6.
      SSCase "x2 = x".
        rewrite -> H6 in Hh.
        apply H5 in Hh.
        inversion Hh.
      SSCase "x2 <> x".
        apply ai_later with (b := x) in Hh.
        apply H4 in Hh.
        inversion Hh.
        apply H6 in H8.
        inversion H8.
        apply H8.
        unfold lt.
        apply H0.
Qed.

(* END pigeonhole principle. *)
