Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.omega.Omega.
Require Export Imp.

(* Exercise: 2 stars (equiv_classes) *)

(* [
  [a, d, f, g], -- do not terminate
  [b, e],       -- y ::= 0
  [c, h],       -- SKIP
  [i]           -- if x < y, then x = y; else loop
] *)

(* END equiv_classes. *)

Definition cequiv (c1 c2 : com) :=
  forall st st', c1 / st ⇓ st' <-> c2 / st ⇓ st'.

(* Exercise: 2 stars (skip_right) *)

Theorem skip_right: forall c, cequiv (c ;; SKIP) c.
Proof.
  intros c st st'.
  split.
  Case "SKIP -> c".
    intros. inversion H. inversion H5. subst. assumption.
  Case "c -> SKIP".
    intros. apply E_Seq with (st' := st'). assumption. apply E_Skip.
Qed.

(* END skip_right. *)

Definition bequiv b1 b2 :=
  forall st, beval st b1 = beval st b2.

(* Exercise: 2 stars (IFB_false) *)

Theorem IFB_false : forall b c1 c2,
  bequiv b BFalse -> cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
  intros.
  intros st st'.
  split.
  Case "->".
    intro. inversion H0; subst.
      unfold bequiv in H.
        assert (beval st b = beval st BFalse) by apply H. rewrite -> H6 in H1.
        inversion H1.
      assumption.
  Case "<-".
    intro.
    apply E_IfFalse.
    unfold bequiv in H.
    rewrite -> H.
    reflexivity.
    assumption.
Qed.

(* END skip_right. *)

(* Exercise: 3 stars (swap_if_branches) *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  intros st st'.
  split.
  Case "->".
    intro. inversion H; subst; [apply E_IfFalse | apply E_IfTrue];
      simpl; try (rewrite -> H5; reflexivity);
      apply H6.
  Case "<-".
    intro. inversion H; subst; [apply E_IfFalse | apply E_IfTrue];
      simpl in H5; try assumption; destruct (beval st b); simpl in H5; trivial;
        try inversion H5.
Qed.

(* END swap_if_branches. *)

(* Exercise: 2 stars, advanced, optional (WHILE_false_informal) *)

(* We must prove that WHILE b DO c END behaves like SKIP if `b` is equivalent
to BFalse. For this, we must prove that SKIP yields the same result as loop
with false statement and vice versa.

First, let's prove that SKIP can be replaced with WHILE b DO c END, where `b`
can be replaced with BFalse. SKIP doesn't change the state of the program, and
so the initial and final states are the same. This property also holds for loop
termination rule E_WhileEnd. This rule also requires that the loop condition
evaluates to `false` under the current environment, and we prove this by
evaluating BFalse to which the loop condition of our loop is equivalent.

To prove the reverse, let's consider two cases: this iteration of WHILE is the
last and thus doesn't change the state of the program -- which corresponds to
the only evaluation rule for SKIP -- or this iteration is intermediary -- but
this can't be true since `b` evaluates to `false`.

*)

(* END WHILE_false_informal. *)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st ⇓ st' ).
Proof.
  intros b c st st' Hb H.
  remember (WHILE b DO c END) as rule.
  induction H; inversion Heqrule; subst.
  - rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity.
Qed.

(* Exercise: 2 stars, recommended (WHILE_true) *)

Theorem WHILE_true : forall b c,
  bequiv b BTrue ->
  cequiv (WHILE b DO c END) (WHILE BTrue DO SKIP END).
Proof.
  split; intro; apply WHILE_true_nonterm in H0;
   [inversion H0 | apply H | inversion H0 | unfold bequiv; intro; reflexivity].
Qed.

(* END WHILE_true. *)

Theorem loop_unrolling: forall b c,
  cequiv (WHILE b DO c END) (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  split; intro.
  - inversion H; subst.
    + apply E_IfFalse. assumption. apply E_Skip.
    + apply E_IfTrue. assumption. apply E_Seq with (st' := st'0).
      assumption. assumption.
  - inversion H; subst.
    + inversion H6; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + inversion H6; subst.
      apply E_WhileEnd. assumption.
Qed.

(* Exercise: 2 stars, optional (seq_assoc) *)

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3)).
Proof.
  split; intro.
  - inversion H; subst. inversion H2; subst.
    apply E_Seq with (st' := st'1). assumption.
    apply E_Seq with (st' := st'0). assumption. assumption.
  - inversion H; subst. inversion H5; subst.
    apply E_Seq with (st' := st'1).
    apply E_Seq with (st' := st'0).
    assumption. assumption. assumption.
Qed.

(* END seq_assoc. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.

(* Exercise: 2 stars, recommended (assign_aequiv) *)

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros.
  split; intro.
  - replace st' with (update st X (aeval st e)).
    + apply E_Ass.
    + inversion H0; subst.
      apply functional_extensionality. intro x.
      apply update_same.
      apply H.
  - inversion H0; subst.
    replace (update st X (aeval st e)) with st.
    + apply E_Skip.
    + apply functional_extensionality; intro x.
      symmetry; apply update_same.
      apply H.
Qed.

(* END assign_aequiv. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  split.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp), aequiv a1 a2 -> aequiv a2 a1.
Proof.
  unfold aequiv.
  intros.
  symmetry.
  apply H.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  intros. intro st. rewrite -> H. apply H0.
Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  split.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp), bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros. symmetry. apply H.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  intros. intro st. rewrite -> H. apply H0.
Qed.

Lemma refl_cequiv : forall c, cequiv c c.
Proof.
  split; intros; assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros; split; rewrite -> H; apply H0.
Qed.

Lemma trans_cequiv : forall c1 c2 c3,
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros. intros st st'.
  apply iff_trans with (c2 / st ⇓ st'). apply H. apply H0.
Qed.

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros. split; intro;
    inversion H0; subst;
    [ rewrite -> H | rewrite <- H];
    apply E_Ass.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  intros. split; intro.
  - remember (WHILE b1 DO c1 END) as While.
    induction H1; inversion HeqWhile; subst.
    + apply E_WhileEnd.
      rewrite <- H.
      assumption.
    + apply E_WhileLoop with (st' := st').
      * rewrite <- H. assumption.
      * apply H0. assumption.
      * apply IHceval2. reflexivity.
  - remember (WHILE b1' DO c1' END) as While.
    induction H1; inversion HeqWhile; subst.
    + apply E_WhileEnd.
      rewrite -> H.
      assumption.
    + apply E_WhileLoop with (st' := st').
      * rewrite -> H. assumption.
      * apply H0. assumption.
      * apply IHceval2. reflexivity.
Qed.

(* Exercise: 3 stars, optional (CSeq_congruence) *)

Theorem CSeq_congruence : forall c1 c2 c1' c2',
  cequiv c1 c1' -> cequiv c2 c2' -> cequiv (c1 ;; c2) (c1' ;; c2').
Proof.
  intros. split; intro;
    [ remember (c1 ;; c2) as Seq | remember (c1' ;; c2') as Seq];
    induction H1; inversion HeqSeq; subst;
    apply E_Seq with (st' := st');
    [ apply H | apply H0 | apply H | apply H0 ]; assumption.
Qed.

(* END CSeq_congruence. *)

(* Exercise: 3 stars (CIf_congruence) *)

Theorem CIf_congruence : forall b b' ct ct' ce ce',
  bequiv b b' -> cequiv ct ct' -> cequiv ce ce' ->
  cequiv (IFB b THEN ct ELSE ce FI) (IFB b' THEN ct' ELSE ce' FI).
Proof.
  intros. intros st st'.
  split; intros.
  - remember (IFB b THEN ct ELSE ce FI) as If.
    induction H2; inversion HeqIf; subst.
    + apply E_IfTrue.
      * rewrite <- H. apply H2.
      * apply H0. apply H3.
    + apply E_IfFalse.
      * rewrite <- H. apply H2.
      * apply H1. apply H3.
  - remember (IFB b' THEN ct' ELSE ce' FI) as If.
    induction H2; inversion HeqIf; subst.
    + apply E_IfTrue.
      * rewrite -> H. apply H2.
      * apply H0. apply H3.
    + apply E_IfFalse.
      * rewrite -> H. apply H2.
      * apply H1. apply H3.
Qed.

(* END CIf_congruence. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp), aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans : com  -> com)  : Prop :=
  forall (c : com),  cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
    | ANum n    => ANum n
    | AId  i    => AId i
    | APlus n m =>  match (fold_constants_aexp n, fold_constants_aexp m) with
                      | (ANum n', ANum m') => ANum (n' + m')
                      | (n', m') => APlus n' m'
                    end
    | AMinus n m => match (fold_constants_aexp n, fold_constants_aexp m) with
                      | (ANum n', ANum m') => ANum (n' - m')
                      | (n', m') => AMinus n' m'
                    end
    | AMult n m  => match (fold_constants_aexp n, fold_constants_aexp m) with
                      | (ANum n', ANum m') => ANum (n' * m')
                      | (n', m') => AMult n' m'
                    end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp (AMult (APlus (ANum 1) (ANum 2)) (AId X)) =
    AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp (AMinus (AId X) (APlus (AMult (ANum 0)
    (ANum 6)) (AId Y))) = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq  a b => match (fold_constants_aexp a, fold_constants_aexp b) with
                    | (ANum n', ANum m') => if beq_nat n' m'
                         then BTrue else BFalse
                    | (n', m') => BEq n' m'
                  end
    | BLe  a b => match (fold_constants_aexp a, fold_constants_aexp b) with
                    | (ANum n', ANum m') => if ble_nat n' m'
                         then BTrue else BFalse
                    | (n', m') => BLe n' m'
                  end
    | BNot a   => match fold_constants_bexp a with
                    | BTrue => BFalse
                    | BFalse => BTrue
                    | e => BNot e
                  end
    | BAnd a b => match (fold_constants_bexp a, fold_constants_bexp b) with
                    | (_, BFalse) => BFalse
                    | (BFalse, _) => BFalse
                    | (BTrue, BTrue) => BTrue
                    | (a', b') => BAnd a' b'
                  end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue))) = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp (BAnd (BEq (AId X) (AId Y))
                            (BEq (ANum 0)
                                 (AMinus (ANum 2)
                                         (APlus (ANum 1) (ANum 1))))) =
    BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
    | SKIP => SKIP
    | i ::= a => CAss i (fold_constants_aexp a)
    | a ;; b  => CSeq (fold_constants_com a) (fold_constants_com b)
    | IFB b THEN ct ELSE ce FI => match fold_constants_bexp b with
        | BTrue => fold_constants_com ct
        | BFalse => fold_constants_com ce
        | b' => IFB b' THEN (fold_constants_com ct)
                       ELSE (fold_constants_com ce) FI
      end
    | WHILE b DO c END => match fold_constants_bexp b with
        | BTrue => WHILE BTrue DO SKIP END
        | BFalse => SKIP
        | b' => WHILE (fold_constants_bexp b) DO
                      (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* After constant folding: *)
     (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
END).
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  intros a st.
  induction a; simpl; try reflexivity;
  destruct (fold_constants_aexp a1); destruct (fold_constants_aexp a2); simpl;
    rewrite IHa1; rewrite IHa2; reflexivity.
Qed.

(* Exercise: 3 stars, optional (fold_bexp_Eq_informal) *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  intros b st.
  induction b; simpl; try reflexivity.
  - remember (fold_constants_aexp a) as a';
    remember (fold_constants_aexp a0) as a0'.
    replace (aeval st a) with (aeval st a')
      by (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a0) with (aeval st a0')
      by (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct (fold_constants_aexp a); destruct (fold_constants_aexp a0);
    rewrite Heqa'; rewrite Heqa0'; simpl; try reflexivity.
    destruct (beq_nat n n0); reflexivity.
  - remember (fold_constants_aexp a) as a';
    remember (fold_constants_aexp a0) as a0'.
    replace (aeval st a) with (aeval st a')
      by (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a0) with (aeval st a0')
      by (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct (fold_constants_aexp a); destruct (fold_constants_aexp a0);
    rewrite Heqa'; rewrite Heqa0'; simpl; try reflexivity.
    destruct (ble_nat n n0); reflexivity.
  - remember (fold_constants_bexp b) as b'.
    rewrite -> IHb.
    destruct (fold_constants_bexp b); rewrite Heqb'; try reflexivity.
  - remember (fold_constants_bexp b1) as b1';
    remember (fold_constants_bexp b2) as b2'.
    assert (forall b, b && false = false) by (destruct b; reflexivity).
    destruct (fold_constants_bexp b1); destruct (fold_constants_bexp b2);
    rewrite IHb1; rewrite IHb2; rewrite Heqb1'; rewrite Heqb2';
    try reflexivity; simpl; try apply H.
Qed.

(* END fold_bexp_Eq_informal. *)

Theorem IFB_true : forall b c1 c2,
  bequiv b BTrue ->
  cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
  split; intros.
  - inversion H0; subst.
    + assumption.
    + rewrite H in H6. inversion H6.
  - apply E_IfTrue.
    + rewrite H. reflexivity.
    + assumption.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP.
Proof.
  split; intros.
  - inversion H0; subst.
    + apply E_Skip.
    + rewrite H in H3. inversion H3.
  - inversion H0; subst.
    apply E_WhileEnd.
    rewrite H. reflexivity.
Qed.

(* Exercise: 3 stars (fold_constants_com_sound) *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  intros c; induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence; apply fold_constants_aexp_sound.
  - apply CSeq_congruence; assumption.
  - assert (bequiv b (fold_constants_bexp b)) by
      apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn: bfb;
      try (apply CIf_congruence; assumption).
    + apply trans_cequiv with c1.
      * apply IFB_true; assumption.
      * assumption.
    + apply trans_cequiv with c2.
      * apply IFB_false; assumption.
      * assumption.
  - assert (bequiv b (fold_constants_bexp b)) by
      apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn: bfb;
      try (apply CWhile_congruence; assumption).
    + apply WHILE_true; assumption.
    + apply WHILE_false; assumption.
Qed.

(* END fold_constants_com_sound. *)

(* Exercise: 4 stars, advanced, optional (optimize_0plus) *)

Fixpoint optimize_0_aexp (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | AId  i => AId  i
    | APlus e1 e2 =>
        match (optimize_0_aexp e1, optimize_0_aexp e2) with
          | (ANum 0, e) => e
          | (e, ANum 0) => e
          | (e1', e2')  => APlus e1' e2'
        end
    | AMinus e1 e2 =>
        match (optimize_0_aexp e1, optimize_0_aexp e2) with
          | (e, ANum 0) => e
          | (e1', e2')  => AMinus e1' e2'
        end
    | AMult  e1 e2 =>
        match (optimize_0_aexp e1, optimize_0_aexp e2) with
          | (ANum 0, e) => ANum 0
          | (e, ANum 0) => ANum 0
  (*        | (ANum 1, e) => e
          | (e, ANum 1) => e *)
          | (e1, e2)    => AMult e1 e2
        end
  end.

Fixpoint optimize_0_bexp (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq n m => BEq (optimize_0_aexp n) (optimize_0_aexp m)
    | BLe n m => BLe (optimize_0_aexp n) (optimize_0_aexp m)
    | BAnd n m => match (optimize_0_bexp n, optimize_0_bexp m) with
                    | (BFalse, _) => BFalse
                    | (_, BFalse) => BFalse
                    | (BTrue,  e) => e
                    | (e, BTrue ) => e
                    | (e1, e2)    => BAnd e1 e2
                  end
    | BNot n => BNot (optimize_0_bexp n)
  end.

Fixpoint optimize_0_com (c : com) : com :=
  match c with
    | SKIP => SKIP
    | i ::= a => CAss i (optimize_0_aexp a)
    | a ;; b  => CSeq (optimize_0_com a) (optimize_0_com b)
    | IFB b THEN ct ELSE ce FI => IFB (optimize_0_bexp b)
                                  THEN (optimize_0_com ct)
                                  ELSE (optimize_0_com ce) FI
    | WHILE b DO c END => WHILE (optimize_0_bexp b) DO (optimize_0_com c) END
  end.

Theorem optimize_0_aexp_sound :
  atrans_sound optimize_0_aexp.
Proof.
  unfold atrans_sound. unfold aequiv.
  intros.
  induction a; try reflexivity; simpl;
    rewrite IHa1; rewrite IHa2;
    destruct (optimize_0_aexp a1); destruct (optimize_0_aexp a2);
    try destruct n; try destruct n0; simpl; symmetry;
      try apply plus_n_O;
      try apply minus_n_O;
      try apply mult_n_O;
    try reflexivity.
Qed.

Theorem optimize_0_bexp_sound :
  btrans_sound optimize_0_bexp.
Proof.
  unfold btrans_sound. unfold bequiv.
  intros.
  induction b; try reflexivity; simpl;
    try (replace (aeval st (optimize_0_aexp a)) with (aeval st a)
           by apply optimize_0_aexp_sound;
         replace (aeval st (optimize_0_aexp a0)) with (aeval st a0)
           by apply optimize_0_aexp_sound); try reflexivity.
    - rewrite <- IHb; reflexivity.
    - remember (optimize_0_bexp b1) as b1eq.
      remember (optimize_0_bexp b2) as b2eq.
      destruct b1eq; destruct b2eq; rewrite IHb1; rewrite IHb2; simpl;
        try apply andb_false_r; try apply andb_true_r;
        reflexivity.
Qed.

Theorem skip_left : forall c, cequiv (SKIP ;; c) c.
Proof.
  intros.
  split; intros.
  - inversion H; subst. inversion H2; subst. assumption.
  - apply E_Seq with (st' := st). apply E_Skip. assumption.
Qed.

Theorem optimize_0_com_sound :
  ctrans_sound optimize_0_com.
Proof.
  unfold ctrans_sound.
  induction c; simpl.
   - apply refl_cequiv.
   - apply CAss_congruence; apply optimize_0_aexp_sound.
   - apply CSeq_congruence; assumption.
   - apply CIf_congruence; try assumption.
     apply optimize_0_bexp_sound.
   - apply CWhile_congruence; try assumption.
     apply optimize_0_bexp_sound.
Qed.

(* END optimize_0plus. *)

Inductive var_not_used_in_aexp (X : id) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp X (ANum n)
  | VNUVar : forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus : forall a b,
      var_not_used_in_aexp X a -> var_not_used_in_aexp X b ->
      var_not_used_in_aexp X (APlus a b)
  | VNUMinus : forall a b,
      var_not_used_in_aexp X a -> var_not_used_in_aexp X b ->
      var_not_used_in_aexp X (AMinus a b)
  | VNUMult : forall a b,
      var_not_used_in_aexp X a -> var_not_used_in_aexp X b ->
      var_not_used_in_aexp X (AMult a b)
.

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | AId i' => if eq_id_dec i i' then u else AId i'
    | APlus n m  => APlus  (subst_aexp i u n) (subst_aexp i u m)
    | AMinus n m => AMinus (subst_aexp i u n) (subst_aexp i u m)
    | AMult  n m => AMult  (subst_aexp i u n) (subst_aexp i u m)
  end.

(* Exercise: 4 stars, optional (better_subst_equiv) *)

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  intros.
  induction H; simpl; try reflexivity;
    try (rewrite IHvar_not_used_in_aexp1;
      rewrite IHvar_not_used_in_aexp2;
      reflexivity).
  apply update_neq; assumption.
Qed.

Definition subst_equiv_weaker_property := forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 -> 
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem unused_var_does_not_matter :
  forall i n a st,
    var_not_used_in_aexp i a ->
    aeval st a = aeval (update st i n) a.
Proof.
  intros.
  induction a; inversion H; subst; simpl;
    try rewrite IHa1; try rewrite IHa2; try assumption; try reflexivity.
  - symmetry. apply update_neq. assumption.
Qed.

Theorem better_subst_equiv : subst_equiv_weaker_property.
Proof.
  intros i1 i2 a1 a2 Hvnu.
  split; intros; inversion H; inversion H2; inversion H5; subst;
    apply E_Seq with (update st i1 (aeval st a1)); try assumption;
    [ replace (aeval (update st i1 (aeval st a1)) a2) with
            (aeval (update st i1 (aeval st a1)) (subst_aexp i1 a1 a2)) |
      replace (aeval (update st i1 (aeval st a1)) (subst_aexp i1 a1 a2)) with
            (aeval (update st i1 (aeval st a1)) a2) ];
    try apply E_Ass;
    clear H H2 H5 i2; generalize dependent i1; generalize dependent a1;
    induction a2; intros; simpl; try rewrite IHa2_1; try rewrite IHa2_2;
      try reflexivity; try assumption;
    destruct (eq_id_dec i1 i); try reflexivity;
      subst; rewrite update_eq; [symmetry; apply unused_var_does_not_matter |
        apply unused_var_does_not_matter]; assumption.
Qed.

(* END better_subst_equiv. *)

(* Exercise: 3 stars, optional (inequiv_exercise) *)

Theorem inequiv_exercise:
  not (cequiv (WHILE BTrue DO SKIP END) SKIP).
Proof.
  intro contra.
  remember empty_state as st.
  assert (SKIP / st ⇓ st).
  { apply E_Skip. }
  assert (not (WHILE BTrue DO SKIP END / st ⇓ st)).
  { apply loop_never_stops. }
  unfold not in H0.
  apply contra in H.
  apply H0.
  apply H.
Qed.

(* END inequiv_exercise. *)

Module Himp.

Inductive com :=
  | CSkip : com
  | CAss  : id   -> aexp -> com
  | CSeq  : com  -> com  -> com
  | CIf   : bexp -> com  -> com  -> com
  | CWhile: bexp -> com  -> com
  | CHavoc: id   -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

(* Exercise: 2 stars (himp_ceval) *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, SKIP / st ⇓ st
  | E_Ass  : forall st x ae,  (x ::= ae) / st ⇓ (update st x (aeval st ae))
  | E_Seq  : forall st st' st'' c1 c2,
               c1 / st  ⇓ st'  ->
               c2 / st' ⇓ st'' ->
               (c1 ;; c2) / st ⇓ st''
  | E_IfTrue  : forall st st' ct ce be,
               beval st be = true ->
               ct / st ⇓ st'   ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_IfFalse : forall st st' ct ce be,
               beval st be = false ->
               ce / st ⇓ st'    ->
               (IFB be THEN ct ELSE ce FI) / st ⇓ st'
  | E_WhileEnd : forall st c be,
               beval st be = false ->
               (WHILE be DO c END) / st ⇓ st
  | E_WhileLoop : forall st st' st'' c be,
               beval st be = true ->
               c / st ⇓ st' ->
               (WHILE be DO c END) / st' ⇓ st'' ->
               (WHILE be DO c END) / st  ⇓ st''
  | E_Havoc : forall st id n, (HAVOC id) / st ⇓ (update st id n)
   where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Example havoc_example1 : (HAVOC X) / empty_state ⇓ update empty_state X 0.
Proof. apply E_Havoc. Qed.

Example havoc_example2 : (HAVOC Z) / empty_state ⇓ update empty_state Z 42.
Proof. apply E_Havoc. Qed.

(* END himp_ceval. *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall st st', c1 / st ⇓ st' <-> c2 / st ⇓ st'.

(* Exercise: 3 stars (havoc_swap) *)

Definition pXY :=
  HAVOC X ;; HAVOC Y.

Definition pYX :=
  HAVOC Y ;; HAVOC X.

Theorem sym_havoc :
  forall X Y st st', ((HAVOC X ;; HAVOC Y) / st ⇓ st')
                  -> ((HAVOC Y ;; HAVOC X) / st ⇓ st').
Proof.
  intros X Y st st'.
  intros; inversion H; inversion H2; inversion H5; subst.
  destruct (eq_id_dec X Y).
  - rewrite e. apply E_Seq with (update st Y n); apply E_Havoc.
  - replace (update (update st X n) Y n0) with (update (update st Y n0) X n).
    + apply E_Seq with (update st Y n0); apply E_Havoc.
    + apply functional_extensionality. intro x. apply update_permute.
      intro contra. apply n1. symmetry. assumption.
Qed.

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ not (cequiv pXY pYX).
Proof.
  left.
  unfold pXY. unfold pYX.
  split; apply sym_havoc.
Qed.

(* END havoc_swap. *)

(* Exercise: 4 stars, optional (havoc_copy) *)

Definition ptwice :=
  HAVOC X ;; HAVOC Y.

Definition pcopy :=
  HAVOC X ;; Y ::= AId X.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ not (cequiv ptwice pcopy).
Proof.
  right.
  unfold ptwice. unfold pcopy. unfold cequiv. intro contra.
  remember empty_state as st.
  remember (update st X 1) as st'.
  remember (update st' Y 2) as st''.
  assert ((HAVOC X;; HAVOC Y) / st ⇓ st'').
  { apply E_Seq with st'; subst; apply E_Havoc. }
  rewrite contra in H.
  inversion H; inversion H2; inversion H5; subst.
  simpl in H12.
  assert (update (update empty_state X n) Y (update empty_state X n X) Y =
      update (update empty_state X 1) Y 2 Y).
  { rewrite H12. trivial. }
  assert (update (update empty_state X n) Y (update empty_state X n X) X =
      update (update empty_state X 1) Y 2 X).
  { rewrite H12. trivial. }
  clear contra H H2 H5.
  assert (update (update empty_state X n) Y (update empty_state X n X) X = n).
  { reflexivity. }
  assert (update (update empty_state X n) Y (update empty_state X n X) Y = n).
  { reflexivity. }
  assert (update (update empty_state X 1) Y 2 X = 1).
  { reflexivity. }
  assert (update (update empty_state X 1) Y 2 Y = 2).
  { reflexivity. }
  clear H12.
  rewrite H0 in H2. rewrite H2 in H4.
  rewrite H1 in H . rewrite H3 in H.
  rewrite H4 in H.
  inversion H.
Qed.

(* END havoc_copy. *)

(* Exercise: 5 stars, advanced (p1_p2_equiv) *)

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  not (p1 / st ⇓ st').
Proof.
  unfold not.
  intros st st' HXnz contra.
  remember p1.
  generalize dependent HXnz.
  induction contra; unfold p1 in Heqc; inversion Heqc; subst; intro.
  - simpl in H.
    apply false_beq_nat in HXnz. rewrite HXnz in H. inversion H.
  - clear H. clear Heqc. apply IHcontra2.
    + reflexivity.
    + intro contra.
      inversion contra1; inversion H1; inversion H4; subst.
      simpl in contra.
      rewrite update_eq in contra.
      rewrite plus_comm in contra.
      inversion contra.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  not (p2 / st ⇓ st').
Proof.
  unfold not.
  intros st st' HXnz contra.
  remember p2.
  generalize dependent HXnz.
  induction contra; unfold p2 in Heqc; inversion Heqc; subst; intro.
  - simpl in H.
    apply false_beq_nat in HXnz. rewrite HXnz in H. inversion H.
  - clear H Heqc. apply IHcontra2.
    + reflexivity.
    + intro contra.
      inversion contra1; subst.
      contradiction.
Qed.

Theorem p1_p2_cequiv : cequiv p1 p2.
Proof.
  unfold p1. unfold p2.
  intros st.
  destruct (st X) eqn : stX.
  - split; intro; inversion H; subst;
    try (apply E_WhileEnd; assumption);
      simpl in H2; destruct (beq_nat (st X) 0) eqn: bnX;
        try inversion H2;
        apply beq_nat_false in bnX; contradiction.
  - assert (st X <> 0).
    { intro contra. rewrite stX in contra. inversion contra. }
    clear stX.
    split; intro; inversion H0; subst; try (simpl in H5;
      apply false_beq_nat in H; rewrite H in H5; inversion H5).
    + remember p1_may_diverge as pmd; unfold p1 in pmd.
      apply pmd with (st' := st') in H. contradiction.
    + remember p2_may_diverge as pmd; unfold p2 in pmd.
      apply pmd with (st' := st') in H. contradiction.
Qed.

(* END p1_p2_equiv. *)

(* Exercise: 4 stars, advanced (p3_p4_inequiv) *)

Definition p3 :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 :=
  X ::= ANum 0;;
  Z ::= ANum 1.

Theorem p3_p4_inequiv : not (cequiv p3 p4).
Proof.
  remember (update empty_state X 1) as st.
  remember (update  st X 0) as st'.
  remember (update st' Z 2) as st''.
  assert (p3 / st ⇓ st'').
  { unfold p3. apply E_Seq with (update st Z 1).
    + subst. apply E_Ass.
    + subst st' st''.
      replace (update (update st X 0) Z 2) with
              (update (update (update st Z 1) X 0) Z 2).
      * apply E_WhileLoop with (update (update (update st Z 1) X 0) Z 2).
        { subst. reflexivity. }
        { apply E_Seq with (update (update st Z 1) X 0); apply E_Havoc. }
        apply E_WhileEnd.
        subst; reflexivity.
      * apply functional_extensionality.
        intros x.
        subst.
        unfold update.
        destruct (eq_id_dec Z x); destruct (eq_id_dec X x); reflexivity.
  }
  assert (not (p4 / st ⇓ st'')).
  { unfold p4. intro contra.
    inversion contra; inversion H5; subst.
    simpl in H9.
    assert (update st'0 Z 1 Z = 1).
      apply update_eq.
    assert (update (update (update empty_state X 1) X 0) Z 2 Z = 2).
      apply update_eq.
    rewrite H9 in H0. rewrite H0 in H1. inversion H1.
  }
  intros contra.
  apply contra in H.
  contradiction.
Qed.

(* END p3_p4_inequiv. *)

(* Exercise: 5 stars, advanced, optional (p5_p6_equiv) *)

Definition p5 :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 :=
  X ::= ANum 1.

Lemma CAss_helper :
  forall st st' x n, st' = update st x (aeval st n) -> ((x ::= n) / st ⇓ st').
Proof.
  intros. subst. apply E_Ass. Qed.

Lemma p5_X_1 :
  forall st st', p5 / st ⇓ st' -> st' = update st X 1.
Proof.
  intros.
  remember p5.
  induction H; inversion Heqc; subst; simpl in H.
  - clear Heqc.
    assert (st X = 1).
    { destruct (beq_nat (st X) 1) eqn: bqn.
      + apply beq_nat_true in bqn. assumption.
      + inversion H.
    }
    unfold update.
    apply functional_extensionality.
    intros x.
    destruct (eq_id_dec X x).
    + subst; assumption.
    + trivial.
  - clear IHceval1 Heqc H1.
    assert (st'' = update st' X 1).
    { apply IHceval2. reflexivity. }
    clear IHceval2.
    rewrite H1. clear H1 H.
    inversion H0; subst.
    apply functional_extensionality.
    intros x.
    apply update_shadow.
Qed.

Lemma p5_X_1_2 :
  forall st, p5 / st ⇓ update st X 1.
Proof.
  intro.
  destruct (eq_nat_dec (st X) 1).
  - unfold p5.
    replace (update st X 1) with st.
    apply E_WhileEnd.
    simpl. rewrite e. reflexivity.
    apply functional_extensionality.
    intros x. symmetry. apply update_same. assumption.
  - unfold p5.
    apply E_WhileLoop with (update st X 1).
    + apply false_beq_nat in n. simpl. rewrite n. reflexivity.
    + apply E_Havoc.
    + apply E_WhileEnd.
      reflexivity.
Qed.

Theorem p5_p6_cequiv :
  cequiv p5 p6.
Proof.
  split; intros.
  - apply p5_X_1 in H.
    subst. unfold p6.
    apply E_Ass.
  - inversion H; subst. simpl. simpl in H.
    apply p5_X_1_2.
Qed.

(* END p5_p6_equiv. *)

End Himp.
