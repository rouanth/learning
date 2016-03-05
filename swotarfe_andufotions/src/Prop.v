Require Export Logic.

(* ((Inductively Defined Propositions)) *)

Inductive ev : nat -> Prop :=
  | ev_O  : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

(* Exercise: 1 star (double_even) *)

Theorem double_even: forall n, ev (double n).
Proof.
  induction n as [|n'].
  Case "n = 0".
    simpl.
    apply ev_O.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

(* END double_even. *)

(* Exercise: 1 star (varieties_of_beauty) *)

(* An infinity, since we can add 0 as much as we like. *)

(* END varieties_of_beauty. *)

Inductive beautiful : nat -> Prop :=
  | bu_0   : beautiful 0
  | bu_3   : beautiful 3
  | bu_5   : beautiful 5
  | bu_sum : forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m).

(* Exercise: 2 stars (b_times2) *)

Theorem b_times2 : forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros n H.
  simpl.
  rewrite -> plus_0_r.
  apply bu_sum.
  apply H.
  apply H.
Qed.

(* END b_times2. *)

(* Exercise: 3 stars (b_timesm) *)

Theorem b_timesm : forall n m, beautiful n -> beautiful (m * n).
Proof.
  intros n m H.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    apply bu_0.
  Case "m = S m'".
    simpl.
    apply bu_sum.
    apply H.
    apply IHm'.
Qed.

(* END b_timesm. *)

(* ((Using Evidence in Proofs)) *)

Inductive gorgeous : nat -> Prop :=
  | g_0     : gorgeous 0
  | g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
  | g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

(* Exercise: 1 star (gorgeous_tree) *)

(*

  ------------------ g_0
      gorgeous 0

      gorgeous n
  ------------------ g_plus3
   gorgeous (3 + n)

      gorgeous n
  ------------------ g_plus5
   gorgeous (5 + n)

*)

(* END gorgeous_tree. *)

(* Exercise: 1 star (gorgeous_plus13) *)

Theorem gorgeous_plus13 : forall n, gorgeous n -> gorgeous (13 + n).
Proof.
  intros n H.
  induction H.
  Case "g 13".
    simpl.
    apply g_plus5.
    apply g_plus5.
    apply g_plus3.
    apply g_0.
  Case "g (13 + (3 + n))".
    rewrite -> plus_swap.
    apply g_plus3.
    apply IHgorgeous.
  Case "g (13 + (5 + n))".
    rewrite -> plus_swap.
    apply g_plus5.
    apply IHgorgeous.
Qed.

(* END gorgeous_plus13. *)

Theorem gorgeous__beautiful : forall n, gorgeous n -> beautiful n.
Proof.
  intros n H.
  induction H.
  Case "b 0".
    apply bu_0.
  Case "b (3 + n)".
    apply bu_sum.
    apply bu_3.
    apply IHgorgeous.
  Case "b (5 + n)".
    apply bu_sum.
    apply bu_5.
    apply IHgorgeous.
Qed.

(* Exercise: 2 stars (gorgeous_sum) *)

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  Case "0 + m".
    simpl. apply H2.
  Case "3 + n + m".
    apply g_plus3. apply IHgorgeous.
  Case "5 + n + m".
    apply g_plus5. apply IHgorgeous.
Qed.

(* END gorgeous_sum. *)

(* Exercise: 3 stars, advanced (beautiful__gorgeous) *)

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H.
  induction H.
  Case "n = 0".
    apply g_0.
  Case "n = 3".
    apply g_plus3.
    apply g_0.
  Case "n = 5".
    apply g_plus5.
    apply g_0.
  Case "n = n' + m".
    apply gorgeous_sum.
    apply IHbeautiful1.
    apply IHbeautiful2.
Qed.

(* END beautiful__gorgeous. *)

(* Exercise: 3 stars, optional (g_times2) *)

Theorem g_times2 : forall n, gorgeous n -> gorgeous (2 * n).
Proof.
  intros n H.
  simpl.
  rewrite -> plus_0_r.
  apply gorgeous_sum.
    apply H.
    apply H.
Qed.

(* Huh? *)

(* END g_times2. *)

(* Exercise: 1 star (ev__even) *)

(* No since the evidence for ev (S n) where n is an arbitrary natural number
* can't be constructed. *)

(* END ev__even. *)

(* Exercise: 1 star (l_fails) *)

(* All we know is that n' is even; it tells us nothing about S n'. Since
* neither evidence not the evidence of the lack thereof can be constructed,
* we are unable to continue. *)

(* END l_fails. *)

(* Exercise: 2 stars (ev_sum) *)

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  Case "ev m -> ev (0 + m)".
    simpl.
    apply H2.
  Case "ev (S (S n) + m)".
    simpl.
    apply ev_SS.
    apply IHev.
Qed.

(* END ev_sum. *)

(* Exercise: 1 star, optional (ev_minus2_n) *)

(* We are ultimately left with a statement that ev (S (S n)) is true and sould
* prove that ev n is also true. But it's the first that follows from the
* second, not vice versa. *)

(* END ev_minus2_n. *)

(* Exercise: 1 star (inversion_practice) *)

Theorem SSSSev_even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

(* END inversion_practice. *)

(* Exercise: 3 stars, advanced (ev_ev__ev) *)

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2.
  Case "ev (0 + m)".
    simpl in H1.
    apply H1.
  Case "ev (S (S n) + m)".
    simpl in H1.
    inversion H1.
    generalize dependent H0.
    apply IHev.
Qed.

(* END ev_ev__ev. *)

(* Exercise: 3 stars, optional (ev_plus_plus) *)

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p.
  intros H1 H2.
  assert (ev ((n + m) + (n + p)) -> ev (m + p)).
  Case "ev ((n + p) + (n + p)) -> ev (m + p)".
    rewrite <- plus_swap.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite <- double_plus.
    intros Z.
    apply ev_ev__ev with (n := double n).
    SCase "ev (double n + (m + p))".
      rewrite -> plus_assoc.
      apply Z.
    SCase "ev (double n)".
      apply double_even.
  apply H.
  apply ev_sum.
  apply H1.
  apply H2.
Qed.

(* END ev_plus_plus. *)

(* ((Discussion and Variations)) *)

(* Exercise: 4 stars (palindromes) *)

Theorem snoc_append : forall (X : Type) (x : X) (l : list X),
  snoc l x = app l (cons x nil).
Proof.
  induction l; simpl; auto. rewrite -> IHl. trivial.
Qed.

Theorem app_assoc : forall (X : Type) (l1 l2 l3 : list X),
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  induction l1; auto; simpl. intros. rewrite <- IHl1. trivial.
Qed.

Theorem distr_rev : forall (X : Type) (l1 l2 : list X),
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  induction l1; intros; simpl.
  Case "l1 = nil".
    rewrite -> app_nil_invariant.
    trivial.
  Case "l1 = x :: l1'".
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    rewrite <- app_assoc.
    rewrite -> IHl1.
    trivial.
Qed.

Inductive pal {X : Type} : list X -> Prop :=
  | pal_nil : pal nil
  | pal_one : forall x, pal (x :: nil)
  | pal_app : forall a l, pal l -> pal (a :: l ++ a :: nil)%list.

Theorem pal_app_rev : forall (X : Type) (l : list X), pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|n l'].
    simpl.
    apply pal_nil.
    simpl.
    rewrite -> snoc_append.
    rewrite <- app_assoc.
    apply pal_app.
    apply IHl'.
Qed.

Theorem pal_rev : forall (X : Type) (l : list X), pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
  Case "nil = rev nil".
    reflexivity.
  Case "x :: nil = rev (x :: nil)".
    reflexivity.
  Case "(a :: l ++ a :: nil) = rev (a :: (l ++ a :: nil))".
    simpl.
    rewrite -> distr_rev.
    simpl.
    rewrite -> snoc_append.
    rewrite <- IHpal.
    trivial.
Qed.

(* END palindromes. *)

(* Exercise: 5 stars, optional (palindrome_converse) *)

Theorem list_lengths_eq : forall (X : Type) (l1 l2 : list X),
  l1 = l2 -> length l1 = length l2.
Proof. intros X l1 l2 H. rewrite -> H. trivial. Qed.

Theorem app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1; simpl; auto. Qed.

Theorem plus_n_Sm_neq_n : forall n m : nat, n + S m <> n.
Proof.
  intros n.
  induction n.
  Case "n = 0".
    simpl.
    unfold not.
    intros m H.
    inversion H.
  Case "n = S n'".
    intros m.
    unfold not.
    intros H.
    inversion H.
    generalize dependent H1.
    unfold not in IHn.
    apply IHn.
Qed.

Theorem app_inversion : forall (X : Type) (l1 l2 l3 : list X),
  app l1 l3 = app l2 l3 -> l1 = l2.
Proof.
  intros X l1.
  induction l1.
  Case "l1 = nil".
    intros l2.
    induction l2.
    SCase "l2 = nil".
      trivial.
    SCase "l2 = a :: l2".
      intros l3 H.
      simpl in H.
      apply list_lengths_eq in H.
      simpl in H.
      rewrite -> app_length in H.
      rewrite -> plus_comm in H.
      rewrite -> plus_n_Sm in H.
      symmetry in H.
      apply plus_n_Sm_neq_n in H.
      inversion H.
  Case "l1 = a :: l1".
    simpl.
    induction l2.
    SCase "l2 = nil".
      simpl.
      intros l3 H.
      apply list_lengths_eq in H.
      replace (a :: (l1 ++ l3))%list with ((a :: l1) ++ l3)%list in H.
      rewrite -> app_length in H.
      rewrite -> plus_comm in H.
      simpl in H.
      apply plus_n_Sm_neq_n in H.
      inversion H.
      reflexivity.
    SCase "l2 = a0 :: l2".
      intros l3 H.
      inversion H.
      apply IHl1 in H2.
      rewrite -> H2.
      reflexivity.
Qed.

Theorem rev_pal : forall (X : Type) (x : X) (l : list X),
  (x :: l)%list = rev (l ++ (x :: nil))%list -> l = rev l.
Proof.
  intros X x l H.
  simpl in H.
  symmetry in H.
  rewrite <- rev_involutive in H.
  simpl in H.
  rewrite -> snoc_append in H.
  assert (forall (Y : Type) (l1 l2 : list Y), l1 = l2 -> rev l1 = rev l2).
    intros Y l1 l2 Z. rewrite -> Z. trivial.
  apply H0 in H.
  rewrite -> rev_involutive in H.
  rewrite -> rev_involutive in H.
  apply app_inversion in H.
  apply H.
Qed.

Theorem rev_pal_gen : forall (X : Type) (x : X) (l : list X),
  (x :: l)%list = rev (x :: l) ->
  l = nil \/
  l <> nil /\ (forall z l', l = (l' ++ z :: nil)%list -> l' = rev l').
Proof.
  intros X x l.
  induction l as [|n lt].
  Case "l = nil".
    intros H.
    left.
    trivial.
  Case "l = n :: lt".
    intros H.
    right.
    split.
    SCase "l <> nil".
      unfold not.
      intros K.
      inversion K.
    SCase "l' = rev l'".
      intros z l' Ht.
      rewrite -> Ht in H.
      simpl in H.
      rewrite -> snoc_append in H.
      replace (l' ++ z :: nil)%list with (snoc l' z) in H.
      rewrite -> rev_snoc in H.
      inversion H.
      rewrite -> snoc_append in H2.
      apply app_inversion in H2.
      apply H2.
      apply snoc_append.
Qed.

Theorem length_nil_zero : forall (X : Type) (l : list X),
  length l = 0 -> l = nil.
Proof.
  induction l. auto. intros H. inversion H.
Qed.

Theorem ble_nat_trans : forall (n m p : nat),
  ble_nat n m = true -> ble_nat m p = true -> ble_nat n p = true.
Proof.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    destruct m.
    SCase "m = 0".
      intros p H.
      inversion H.
    SCase "m = S m".
      destruct p.
      SSCase "p = 0".
        intros H1 H2.
        inversion H2.
      SSCase "p = S p".
        simpl.
        apply IHn.
Qed.

Theorem palindrome_converse_helper : forall (X : Type) (n : nat) (l : list X),
  ble_nat (length l) n = true -> l = rev l -> pal l.
Proof.
  induction n.
  Case "n = 0".
    intros l H1 H2.
    assert (ble_nat (length l) 0 = true -> l = nil).
      induction l.
      trivial.
      simpl.
      intros H.
      inversion H.
    apply H in H1.
    rewrite -> H1.
    apply pal_nil.
  Case "n = S n".
    intros l H1 H2.
    inversion H2.
    destruct l.
    SCase "l = nil".
      apply pal_nil.
    SCase "l = x :: l".
      simpl in H2.
      rewrite -> snoc_append in H2.
      destruct (rev l) eqn : K.
      SSCase "rev l = nil".
        inversion H2.
        apply pal_one.
      SSCase "rev l = x0 :: l0".
        inversion H2.
        destruct H2.
        rewrite <- H4.
        rewrite <- H3.
        rewrite <- H.
        apply rev_pal_gen in H.
        destruct H.
        SSSCase "l = nil".
          rewrite -> H.
          apply pal_one.
        SSSCase "l = l0 ++ x0 :: nil".
          destruct H.
          rewrite -> H4.
          rewrite -> H3.
          apply pal_app.
          apply IHn.
          rewrite -> H4 in H1.
          simpl in H1.
          rewrite -> app_length in H1.
          simpl in H1.
          rewrite <- plus_n_Sm in H1.
          rewrite -> plus_0_r in H1.
          assert (forall k : nat, ble_nat k (S k) = true).
            induction k. reflexivity. simpl. apply IHk.
          apply ble_nat_trans with (m := S (length l0)).
          apply H2.
          apply H1.
          apply H0 with (z := x0) (l' := l0).
          apply H4.
Qed.

(* It seems to be impossible to prove the theorem by induction on lists since
* knowing that the tail of our list is a palindrome does not allow us to prove
* that the tail without the last element -- an argument to pal_app -- is also
* a palindrome.
*
* So instead we do an induction on list length and prove that if every list
* of a lesser length than the current one with the property (l' = rev l') is
* a palindrome, so it the current one with the same property.
*)

Theorem palindrome_converse : forall (X : Type) (l : list X),
  l = rev l -> pal l.
Proof.
  intros X l.
  apply palindrome_converse_helper with (n := length l).
  symmetry.
  apply ble_nat_refl.
Qed.

(* END palindrome_converse. *)

(* Exercise: 2 stars (total_relation) *)

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

(* END total_relation. *)

(* Exercise: 2 stars (empty_relation) *)

Inductive empty_relation : nat -> nat -> Prop := .

(* END empty_relation. *)

(* Exercise: 2 stars, optional (le_exercises) *)

Lemma le_trans : forall n m o, m <= n -> n <= o -> m <= o.
Proof.
  induction n.
  Case "n = 0".
    induction m.
    SCase "m = 0".
      intros o H1 H2.
      apply H2.
    SCase "m = S m".
      intros o H1 H2.
      inversion H1.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      induction o.
      SSCase "o = 0".
        intros H1 H2.
        apply le_n.
      SSCase "o = S o".
        intros H1 H2.
        inversion H2.
        rewrite <- H0.
        apply H1.
        apply le_S.
        apply IHo.
        apply H1.
        apply H0.
    SCase "m = S m".
      induction o.
      SSCase "o = 0".
        intros H1 H2.
        inversion H2.
      SSCase "o = S o".
        intros H1 H2.
        inversion H1.
        apply H2.
        inversion H2.
        rewrite -> H4 in H1.
        apply H1.
        apply le_S.
        generalize dependent H4.
        generalize dependent H1.
        apply IHo.
Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
  induction n.
  Case "n = 0".
    apply le_n.
  Case "n = S n".
    apply le_S.
    apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  induction n.
  Case "n = 0".
    induction m.
    SCase "m = 0".
      intros H.
      apply le_n.
    SCase "m = S m".
      intros H.
      apply le_S.
      apply IHm.
      inversion H.
      apply H1.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      intros H.
      inversion H.
    SCase "m = S m".
      intros H.
      inversion H.
      apply le_n.
      apply le_S.
      generalize dependent H1.
      apply IHm.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m, S n <= S m -> n <= m.
Proof.
  induction n.
  Case "n = 0".
    intros m H.
    apply O_le_n.
  Case "n = S n".
    induction m.
    SCase "m = 0".
      intros H.
      inversion H.
      inversion H1.
    SCase "m = S m".
      intros H.
      inversion H.
      apply le_n.
      apply le_S.
      generalize dependent H1.
      apply IHm.
Qed.

Theorem le_plus_l : forall a b, a <= a + b.
Proof.
  intros a b.
  generalize dependent a.
  induction b.
  Case "b = 0".
    intros a.
    rewrite -> plus_0_r.
    apply le_n.
  Case "b = S b".
    intros a.
    rewrite <- plus_n_Sm.
    apply le_S.
    apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  destruct m.
  Case "m = 0".
    inversion H.
  Case "m = S m".
    apply Sn_le_Sm__n_le_m in H.
    inversion H.
    SCase "n1 + n2 = m".
      split.
      SSCase "S n1 <= S (n1 + n2)".
        apply n_le_m__Sn_le_Sm.
        apply le_plus_l.
      SSCase "S n2 <= S (n1 + n2)".
        apply n_le_m__Sn_le_Sm.
        rewrite -> plus_comm.
        apply le_plus_l.
    SCase "n1 + n2 <= pred m".
      split.
      SSCase "S n1 <= S (S m0)".
        apply n_le_m__Sn_le_Sm.
        apply le_S.
        apply le_trans with (n := n1 + n2).
        apply le_plus_l.
        apply H0.
      SSCase "S n2 <= S (S m0)".
        apply n_le_m__Sn_le_Sm.
        apply le_S.
        apply le_trans with (n := n1 + n2).
        rewrite -> plus_comm.
        apply le_plus_l.
        apply H0.
Qed.

Theorem lt_S : forall n m, n < m -> n < S m.
Proof.
  unfold lt.
  intros n m H.
  apply le_S.
  apply H.
Qed.

Theorem ble_nat_true : forall n m, ble_nat n m = true -> n <= m.
Proof.
  induction n.
  Case "n = 0".
    intros m H.
    apply O_le_n.
  Case "n = S n".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m".
      simpl in H.
      apply n_le_m__Sn_le_Sm.
      generalize dependent H.
      apply IHn.
Qed.

Theorem le_ble_nat : forall n m, n <= m -> ble_nat n m = true.
Proof.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    intros m H.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m".
      simpl.
      apply Sn_le_Sm__n_le_m in H.
      generalize dependent H.
      apply IHn.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros n m o H1 H2.
  apply le_ble_nat.
  apply ble_nat_true in H1.
  apply ble_nat_true in H2.
  generalize dependent H2.
  generalize dependent H1.
  apply le_trans.
Qed.

(* END le_exercises. *)

(* Exercise: 2 stars, optional (ble_nat_false) *)

Theorem ble_nat_false : forall n m, ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros n m H1 H2.
  apply le_ble_nat in H2.
  rewrite -> H2 in H1.
  inversion H1.
Qed.

(* END ble_nat_false. *)

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall n m o, R n m o -> R (S n) m (S o)
  | c3 : forall n m o, R n m o -> R n (S m) (S o)
  | c4 : forall n m o, R (S n) (S m) (S (S o)) -> R n m o
  | c5 : forall n m o, R n m o -> R m n o.

(* Exercise: 3 stars (R_provability2) *)

(*
1)
   R 1 1 2 : c1 -> c2 -> c3
   R 2 2 6 is not provable.
2) c5 allows us to swap n with m, but it doesn't change anything: any
proposition is constructed with c1, c2, c3 and c4, with c1 being proven for
equal n and m, c4 changing n and m in the same way, and c2 and c3 being
symmetric in regard to n and m in a sense that c2 can be constructed from c3
by c4, and vice versa; thus, from the set of rules one of c2, c3, c5 can be
removed without affecting the set of provable propositions.
3) Assuming from the previous question that c5 can be removed without
affecting the set of provable propositions, we can by brief analysis conclude
that the condition for c4 can only be constructed by applying c2 and c3 to
some other proposition; but c4 is a reverse of c2 and c3 and thus brings us
back to the proposition we've started with, not affecting the set of provable
propositions.
*)

(* END R_provability2. *)

(* Exercise: 3 stars, optional (R_fact) *)

Theorem R_plus : forall n m o : nat, R n m o -> o = n + m.
Proof.
  intros n m o R.
  induction R.
  Case "0 = 0 + 0".
    reflexivity.
  Case "S o = S n + m".
    rewrite -> IHR.
    reflexivity.
  Case "S o = n + S m".
    rewrite <- plus_n_Sm.
    rewrite -> IHR.
    reflexivity.
  Case "o = n + m".
    rewrite <- plus_n_Sm in IHR.
    inversion IHR.
    trivial.
  Case "o = m + n".
    rewrite -> plus_comm.
    apply IHR.
Qed.

Theorem plus_R : forall n m : nat, R n m (n + m).
Proof.
  induction n.
  Case "n = 0".
    induction m.
    SCase "m = 0".
      simpl.
      apply c1.
    SCase "m = S m".
      simpl.
      simpl in IHm.
      apply c3.
      apply IHm.
  Case "n = S n".
    simpl.
    intros m.
    apply c2.
    apply IHn.
Qed.

(* END R_fact. *)

End R.

(* Exercise: 4 stars, advanced (subsequence) *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_nil  : forall l, subseq nil l
  | subseq_cons : forall x l1 l2, subseq l1 l2 -> subseq l1 (x :: l2)
  | subseq_cons': forall x l1 l2, subseq l1 l2 -> subseq (x :: l1) (x :: l2).

Theorem subseq_refl : forall l, subseq l l.
Proof.
  induction l.
  apply subseq_nil.
  apply subseq_cons'.
  apply IHl.
Qed.

Theorem subseq_app_t : forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  generalize dependent l3.
  induction H.
  intros l3. apply subseq_nil.
  intros l3. simpl. apply subseq_cons. apply IHsubseq.
  intros L3. simpl. apply subseq_cons'. apply IHsubseq.
Qed.

Theorem subseq_cons_inv : forall x l1 l2, subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros x l1 l2 H.
  induction l2.
  Case "l2 = nil".
    inversion H.
  Case "l2 = a :: l2".
    inversion H.
    SCase "subseq (x :: l1) l2 -> subseq l1 (a :: l2)".
      apply subseq_cons.
      apply IHl2.
      apply H2.
    SCase "subseq l1 l2 -> subseq l1 (a :: l2)".
      apply subseq_cons.
      apply H1.
Qed.

Theorem subseq_trans : forall l1 l2 l3,
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l3.
  induction H1.
    intros l3 H2. apply subseq_nil.
    intros l3 H2. apply IHsubseq. generalize dependent H2.
      apply subseq_cons_inv.
    intros l3 H2. induction l3. inversion H2. inversion H2.
      apply subseq_cons. apply IHl3. apply H3.
      apply subseq_cons'. apply IHsubseq. apply H0.
Qed.

(* END subsequence. *)

(* Exercise: 2 stars, optional (R_provability) *)

(*
R 2 [1; 0] : c1 -> c2 -> c2
R 1 [1; 2; 1; 0] : c1 -> c2 -> c2 -> c2 -> c3 -> c3 -> c2 -> c3
R 6 [3; 2; 1; 0] is not provable
*)

(* END R_provability. *)

(* ((Programming with Propositions)) *)

(* Exercise: 3 stars (combine_odd_even) *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_info :
  forall (Podd Peven : nat -> Prop) (n : nat),
  (oddb n = true  -> Podd  n) ->
  (oddb n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n).
    apply H1. trivial.
    apply H2. trivial.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = true ->
  Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite -> H2 in H1.
  apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  oddb n = false ->
  Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite -> H2 in H1.
  apply H1.
Qed.

(* END combine_odd_even. *)

(* Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)

Fixpoint true_upto_n__true_everywhere (n : nat) (f : nat -> Prop) : Prop :=
    match n with
      | O    => forall m : nat, f m
      | S n' => f n -> true_upto_n__true_everywhere n' f
    end.

Example true_upto_n_example :
  (true_upto_n__true_everywhere 3 ev =
  (ev 3 -> ev 2 -> ev 1 -> forall m : nat, ev m)).
Proof. reflexivity. Qed.

(* END true_upto_n__true_everywhere. *)
