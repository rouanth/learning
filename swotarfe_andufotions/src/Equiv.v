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
