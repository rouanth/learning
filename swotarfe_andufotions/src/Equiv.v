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
