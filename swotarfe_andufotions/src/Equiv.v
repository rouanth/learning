Require Export Imp.
Require Import Coq.Logic.FunctionalExtensionality.

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
