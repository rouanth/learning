Require Import Omega.
Require Import Imp.

(* ((Evaluation Function)) *)

Notation "'LETOPT' x <== e1 'IN' e2" :=
   (match e1 with
      | Some x => e2
      | None => None
   end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state := 
  match i with
    | 0    => None
    | S i' =>
    match c with
      | CSkip     => Some st
      | CAss  x a => Some (update st x (aeval st a))
      | CSeq  c d => LETOPT st' <== ceval_step st c i' IN ceval_step st' d i'
      | CIf b t e => if beval st b then ceval_step st t i'
                                     else ceval_step st e i'
      | CWhile b k => if beval st b
                      then LETOPT st' <== ceval_step st k i'
                           IN ceval_step st' c i'
                      else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) := 
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* Exercise: 2 stars (pup_to_n) *)

Example pup_to_n_1 :
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* END pup_to_n. *)

(* Exercise: 2 stars, optional (peven) *)

Definition peven : com :=
  Z ::= ANum 1;;
  WHILE BLe (ANum 1) (AId X) DO
    X ::= AMinus (AId X) (ANum 1);;
    IFB BEq (AId Z) (ANum 1) THEN Z ::= ANum 0 ELSE Z ::= ANum 1 FI
  END
.

Example peven_test :
  test_ceval (update empty_state X 5) peven
  = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven_test2 :
  test_ceval (update empty_state X 10) peven
  = Some (0, 0, 1).
Proof. reflexivity. Qed.

(* END peven. *)

Theorem ceval_step__ceval : forall c st st',
  (exists i, ceval_step st c i = Some st') ->
  c / st ⇓ st'.
Proof.
  intros.
  inversion H as [i E].
  clear H.
  generalize dependent st.
  generalize dependent st'.
  generalize dependent c.
  induction i; intros.
  (* Case "contradiction" *)
  - inversion E.
  (* Case "at least one level of execution was performed" *)
  - destruct c; inversion E; subst.
      constructor.
      constructor.
      (* SCase "c ;; d" *)
      + destruct (ceval_step st c1 i) eqn: H.
        (* SSCase "exists state `s`" *)
        * apply E_Seq with (st' := s). apply IHi. apply H. apply IHi. apply H0.
        (* SSCase "c1 did not execute" *)
        * inversion H0.
      (* SCase "IFB" *)
      + destruct (beval st b) eqn: H; apply IHi in H0;
        [apply E_IfTrue | apply E_IfFalse]; try apply H; try apply H0.
      (* SCase "WHILE" *)
      + destruct (beval st b) eqn: H.
        (* SSCase "going on with the loop" *)
        * destruct (ceval_step st c i) eqn: I.
          (* SSSCase "current iteration returned a result" *)
          { apply E_WhileLoop with (st' := s). apply H.
            apply (IHi _ _ _ I).
            apply (IHi _ _ _ H0). }
          (* SSSCase "current iteration did not return" *)
          { inversion H0. }
        (* SSCase "leaving the loop" *)
        * inversion H0; subst.
          apply E_WhileEnd.
          apply H.
Qed.

(* Exercise: 4 stars (ceval_step__ceval_inf) *)

(* Theorem: if there exists some integer `i` after which ceval_step of command
c with initial state st returns a new state st', then c / st ⇓ st'.

Let's take a fixed value i. By induction on it,

if i = 0, then ceval_step couldn't have returned a state; by contradiction,
the induction base is proved.

The inductive step is: if c / st ⇓ st' holds for a computation which returns
after i steps, then adding a new step does not change the result of the
computation and, as such, does not break the relation.

Let's analyze all the cases for command c and prove that for each of them
incrementing i does not change the result.

For SKIP and assignment, the case is simple: it is evident that step counter is
not used in their operation simply by looking at the function definition.

For sequential execution c1 ;; c2, we analyze the two cases: if c1 executed
normally, then the process of updating the state corresponds to the one in the
E_Seq. Otherwise, we arrive at contradiction: if c1 returned Nothing, the whole
function couldn't have returned Some st'.

For conditional operator, we analyze `true` and `false` branches separately,
for each applying the corresponding constructor: E_IfTrue and E_IfFalse,
respectively.

For loops, the condition can be `true` or `false` for each iteration; we shall
separate the cases. If a new iteration occurs, then it must have returned some
state; otherwise, the whole loop would have returned Nothing; thus, relation
(loop body) / (initial state on this iteration) ⇓ (state after iteration) holds
by E_WhileTrue. If, on the other hand, we're leaving the loop, then the
function does not change the state, and (loop) / st ⇓ st holds by E_WhileEnd.

*)

(* END ceval_step__ceval_inf. *)

Theorem ceval_step_more : forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1; intros.
    - (* Case "returned after 0 steps" *)
      inversion H0.
    - (* Case "returned after (S i1) steps" *)
      destruct i2.
      + (* SCase "S _ <= 0" *)
        inversion H.
      + (* SCase "S i1 <= S i2" *)
        apply le_S_n in H.
        destruct c; inversion H0; simpl; try reflexivity.
          * (* SSCase ";;  " *)
            destruct (ceval_step st c1 i1) eqn: Heq.
              apply (IHi1 i2) in Heq; try assumption. rewrite -> Heq.
                rewrite -> H2. apply IHi1; try assumption.
              inversion H2.
          * (* SSCase "IFB " *)
            destruct (beval st b) eqn: Heq;
              rewrite -> H2; apply IHi1; assumption.
          * (* SSCase "While" *)
            destruct (beval st b) eqn: Heq.
              rewrite -> H2.
              destruct (ceval_step st c i1) eqn: Heq'.
                assert (ceval_step st c i2 = Some s)
                  by apply (IHi1 _ _ _ _ H Heq').
                rewrite -> H1.
                apply IHi1; assumption.
                inversion H2.
             trivial.
Qed.

(* Exercise: 3 stars (ceval__ceval_step) *)

Theorem ceval__ceval_step : forall c st st',
  c / st ⇓ st' -> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce; try (exists 1; reflexivity).
    - (* Case "c1 ;; c2" *)
      destruct IHHce1. destruct IHHce2.
      exists (S (x + x0)).
        simpl.
        assert (ceval_step st c1 (x + x0) = Some st').
          apply (ceval_step_more x). omega. assumption.
        rewrite -> H1. apply (ceval_step_more x0). omega. assumption.
    - (* Case "IFB True" *)
      destruct IHHce. exists (S x). simpl. rewrite -> H. assumption.
    - (* Case "IFB False" *)
      destruct IHHce. exists (S x). simpl. rewrite -> H. assumption.
    - (* Case "While False" *)
      exists 1. simpl. rewrite -> H. trivial.
    - (* Case "While True" *)
      destruct IHHce1. destruct IHHce2.
      exists (S (x + x0)).
      simpl. rewrite -> H.
      assert (ceval_step st c (x + x0) = Some st').
        apply (ceval_step_more x). omega. assumption.
      rewrite -> H2.
      apply (ceval_step_more x0). omega. assumption.
Qed.

(* END ceval__ceval_step. *)
