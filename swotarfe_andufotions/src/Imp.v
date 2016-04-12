Require Export SfLib.

(* ((Arithmetic and Boolean Expressions)) *)

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | Beq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Fixpoint aeval (a : aexp) : nat :=
  match a with
    | ANum   n   => n
    | APlus  b c => (aeval b) + (aeval c)
    | AMinus b c => (aeval b) - (aeval c)
    | AMult  b c => (aeval b) * (aeval c)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
    | BTrue    => true
    | BFalse   => false
    | Beq c d  => beq_nat (aeval c) (aeval d)
    | BLe c d  => ble_nat (aeval c) (aeval d)
    | BNot k   => negb (beval k)
    | BAnd c d => (beval c) && (beval d)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
    | ANum n => ANum n
    | APlus (ANum 0) b => optimize_0plus b
    | APlus b c => APlus (optimize_0plus b) (optimize_0plus c)
    | AMinus b c => AMinus (optimize_0plus b) (optimize_0plus c)
    | AMult b c => AMult (optimize_0plus b) (optimize_0plus c)
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  induction a; try (simpl; rewrite IHa1; rewrite IHa2); try reflexivity.
  destruct a1; simpl; simpl in IHa1;
    try (rewrite IHa1; rewrite IHa2; reflexivity).
  destruct n; simpl; rewrite IHa2; reflexivity.
Qed.

(* ((Coq Automation)) *)

(* Exercise: 3 stars (optimize_0plus_b) *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | Beq c d => Beq (optimize_0plus c) (optimize_0plus d)
    | BLe c d => BLe (optimize_0plus c) (optimize_0plus d)
    | BNot k  => BNot (optimize_0plus_b k)
    | BAnd c d => BAnd (optimize_0plus_b c) (optimize_0plus_b d)
    | e => e
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  induction b; simpl; repeat (rewrite optimize_0plus_sound); try trivial.
  rewrite IHb. trivial.
  rewrite IHb1. rewrite IHb2. trivial.
Qed.

(* END optimize_0plus_b. *)

(* Exercise: 4 stars, optional (optimizer) *)

Fixpoint soph_opt_a (a : aexp) : aexp :=
  match a with
    | APlus  b c => match (soph_opt_a b, soph_opt_a c) with
                      | (ANum 0, e) => e
                      | (e, ANum 0) => e
                      | (e, f     ) => APlus e f
                    end
    | AMult  b c => match (soph_opt_a b, soph_opt_a c) with
                      | (ANum 0, e) => ANum 0
                      | (e, ANum 0) => ANum 0
                      | (ANum 1, e) => e
                      | (e, ANum 1) => e
                      | (e, f     ) => AMult e f
                    end
    | AMinus b c => match (soph_opt_a b, soph_opt_a c) with
                      | (e, ANum 0) => e
                      | (e, f     ) => AMinus e f
                    end
    | e => e
  end.

Fixpoint soph_opt_b (b : bexp) : bexp :=
  match b with
    | Beq c d => match (soph_opt_a c, soph_opt_a d) with
                   | (ANum n, ANum m) => if beq_nat n m then BTrue else BFalse
                   | (e, f          ) => Beq e f
                 end
    | BLe c d => match (soph_opt_a c, soph_opt_a d) with
                   | (ANum n, ANum m) => if ble_nat n m then BTrue else BFalse
                   | (e, f          ) => Beq e f
                 end
    | BNot k  => match (soph_opt_b k) with
                   | BTrue  => BFalse
                   | BFalse => BTrue
                   | e      => BNot e
                 end
    | BAnd c d => match (soph_opt_b c, soph_opt_b d) with
                   | (BFalse, e) => BFalse
                   | (e, BFalse) => BFalse
                   | (BTrue,  e) => e
                   | (e,  BTrue) => e
                   | (e, f     ) => BAnd e f
                  end
    | e => e
end.

Fixpoint soph_opt_a_soft (a : aexp) : aexp :=
  match a with
    | APlus  (ANum 0) e => soph_opt_a_soft e
    | APlus  e (ANum 0) => soph_opt_a_soft e
    | APlus  e f        => APlus  (soph_opt_a_soft e) (soph_opt_a_soft f)
    | AMult  (ANum 0) e => ANum 0
    | AMult  e (ANum 0) => ANum 0
    | AMult  e f        => AMult  (soph_opt_a_soft e) (soph_opt_a_soft f)
    | AMinus e (ANum 0) => soph_opt_a_soft e
    | AMinus e f        => AMinus (soph_opt_a_soft e) (soph_opt_a_soft f)
    | e => e
end.

Fixpoint soph_opt_b_soft (b : bexp) : bexp :=
  match b with
    | Beq  (ANum n) (ANum m) => if beq_nat n m then BTrue else BFalse
    | Beq  c        d        => Beq (soph_opt_a_soft c) (soph_opt_a_soft d)
    | BLe  (ANum n) (ANum m) => if ble_nat n m then BTrue else BFalse
    | BLe  c        d        => BLe (soph_opt_a_soft c) (soph_opt_a_soft d)
    | BNot BTrue             => BFalse
    | BNot BFalse            => BTrue
    | BNot e                 => BNot (soph_opt_b_soft e)
    | BAnd BFalse   e        => BFalse
    | BAnd e        BFalse   => BFalse
    | BAnd BTrue    e        => soph_opt_b_soft e
    | BAnd e        BTrue    => soph_opt_b_soft e
    | BAnd e        f        => BAnd (soph_opt_b_soft e) (soph_opt_b_soft f)
    | e => e
end.

Theorem minus_0_r : forall n, n - 0 = n.
Proof.
  induction n; reflexivity.
Qed.

Theorem soph_opt_a_soft_sound : forall a, aeval (soph_opt_a_soft a) = aeval a.
Proof.
  induction a; try trivial;
    destruct a1; destruct a2;
        try (destruct n); try (destruct n0); simpl;
        simpl in IHa1; try (rewrite IHa1);
        simpl in IHa2; try (rewrite IHa2);
    try (rewrite plus_0_r); try (rewrite minus_0_r); try (rewrite mult_0_r);
    reflexivity.
Qed.

Theorem soph_opt_b_soft_sound : forall b, beval (soph_opt_b_soft b) = beval b.
Proof.
  induction b; try reflexivity;
    try (destruct a; destruct a0;
      unfold soph_opt_b_soft; unfold beval;
        repeat (rewrite soph_opt_a_soft_sound); trivial); simpl.
      destruct (beq_nat n n0); reflexivity.
      destruct (ble_nat n n0); reflexivity.
    destruct b; simpl; simpl in IHb; try (rewrite IHb); reflexivity.
    destruct b1; destruct b2; simpl;
      try (simpl in IHb1; rewrite IHb1); try (simpl in IHb2; rewrite IHb2);
      try (rewrite andb_true_r); try (rewrite andb_false_r); trivial.
Qed.

(* END optimizer. *)

(* ((Evaluation as a Relation)) *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum   : forall n, aevalR (ANum n) n
  | E_APlus  : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m ->
                 aevalR (APlus  e1 e2) (n + m)
  | E_AMinus : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m ->
                 aevalR (AMinus e1 e2) (n - m)
  | E_AMult  : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m ->
                 aevalR (AMult  e1 e2) (n * m)
.

Theorem aeval_iff_aevalR : forall a n,
  aevalR a n <-> aeval a = n.
Proof.
  split.
  intros H; induction H; subst; reflexivity.
  generalize dependent n.
  induction a; intros; subst; constructor; try apply IHa1;
    try apply IHa2; reflexivity.
Qed.

(* Exercise: 3 stars (bevalR) *)

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue  : bevalR BTrue  true
  | E_BFalse : bevalR BFalse false
  | E_Beq    : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m ->
                 bevalR (Beq e1 e2) (beq_nat n m)
  | E_BLe    : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m ->
                 bevalR (BLe e1 e2) (ble_nat n m)
  | E_BNot   : forall e b, bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd   : forall e1 e2 b1 b2, bevalR e1 b1 -> bevalR e2 b2 ->
                 bevalR (BAnd e1 e2) (b1 && b2).

Theorem beval_iff_bevalR : forall a b,
  bevalR a b <-> beval a = b.
Proof.
  split.
  intros H; induction H; try apply aeval_iff_aevalR in H;
    try apply aeval_iff_aevalR in H0; subst; reflexivity.
  generalize dependent b.
  induction a; intros; subst; constructor; try apply aeval_iff_aevalR;
    try apply IHa; try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* END bevalR. *)

End AExp.

(* Exercise: 1 star, optional (neq_id) *)

Lemma neq_id : forall (T : Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  unfold not.
  intros.
  destruct (eq_id_dec x y).
    contradiction.
  trivial.
Qed.

(* END neq_id. *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(* Exercise: 1 star (update_eq) *)

Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros.
  unfold update.
  apply eq_id.
Qed.

(* END update_eq. *)

(* Exercise: 1 star (update_neq) *)

Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->
  (update st x2 n) x1 = (st x1).
Proof.
  intros.
  unfold update.
  apply neq_id.
  apply H.
Qed.

(* END update_neq. *)

(* Exercise: 1 star (update_example) *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  unfold update.
  intros.
  apply neq_id.
  intro.
  inversion H.
Qed.

(* END update_example. *)

(* Exercise: 1 star (update_shadow) *)

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
  (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros.
  unfold update.
  destruct (eq_id_dec x2 x1); trivial.
Qed.

(* END update_shadow. *)

(* Exercise: 2 stars (update_same) *)

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros.
  unfold update.
  destruct (eq_id_dec x1 x2); subst; reflexivity.
Qed.

(* END update_same. *)

(* Exercise: 3 stars (update_permute) *)

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 ->
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  unfold update.
  intros.
  destruct (eq_id_dec x1 x3).
  subst. symmetry. apply neq_id. apply H.
  reflexivity.
Qed.

(* END update_permute. *)

(* ((Commands)) *)

Inductive aexp : Type :=
  | ANum   : nat  -> aexp
  | AId    : id   -> aexp
  | APlus  : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult  : aexp -> aexp -> aexp.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
    | ANum   n   => n
    | AId    i   => st i
    | APlus  b c => (aeval st b) + (aeval st c)
    | AMinus b c => (aeval st b) - (aeval st c)
    | AMult  b c => (aeval st b) * (aeval st c)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
    | BTrue    => true
    | BFalse   => false
    | BEq c d  => beq_nat (aeval st c) (aeval st d)
    | BLe c d  => ble_nat (aeval st c) (aeval st d)
    | BNot k   => negb (beval st k)
    | BAnd c d => (beval st c) && (beval st d)
  end.

Inductive com : Type :=
  | CSkip  : com
  | CAss   : id   -> aexp -> com
  | CSeq   : com  -> com  -> com
  | CIf    : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

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

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ((Evaluation)) *)

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

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
   where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   ⇓ (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  apply E_Ass.
  apply E_IfFalse.
  reflexivity.
  apply E_Ass.
Qed.

(* Exercise: 2 stars (ceval_example2) *)

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ⇓
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
  apply E_Ass.
  apply E_Seq with (update (update empty_state X 0) Y 1).
  apply E_Ass.
  apply E_Ass.
Qed.

(* END ceval_example2. *)

(* Exercise: 3 stars, advanced (pup_to_n) *)

Definition pup_to_n : com :=
  Y ::= ANum 0;;
  WHILE (BNot (BEq (ANum 0) (AId X))) DO
    Y ::= APlus  (AId X) (AId Y);;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ⇓
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n.
  apply E_Seq with (update (update empty_state X 2) Y 0).
  apply E_Ass.
  apply E_WhileLoop with (update (update (update (update empty_state
    X 2) Y 0) Y 2) X 1).
  reflexivity.
  apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2);
    apply E_Ass.
  apply E_WhileLoop with (update (update (update (update (update (update
    empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
  reflexivity.
  apply E_Seq with (update (update (update (update (update
    empty_state X 2) Y 0) Y 2) X 1) Y 3); apply E_Ass.
  apply E_WhileEnd.
  reflexivity.
Qed.

(* END pup_to_n. *)

(* ((Reasoning About Imp Programs)) *)

(* Exercise: 3 stars (XtimesYinZ_spec) *)

Theorem XtimesYinZ_spec : forall st st' x y,
  st X = x -> st Y = y -> XtimesYinZ / st ⇓ st' -> st' Z = x * y.
Proof.
  intros.
  inversion H1.
  subst.
  reflexivity.
Qed.

(* END XtimesYinZ_spec. *)

(* Exercise: 3 stars (loop_never_stops) *)

Theorem loop_never_stops : forall st st',
  ~(loop / st ⇓ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef; subst.
  inversion H.
  apply IHcontra2. trivial.
Qed.

(* END loop_never_stops. *)

Inductive sinstr : Type :=
  | SPush : nat -> sinstr
  | SLoad : id -> sinstr
  | SPlus : sinstr
  | SMinus : sinstr
  | SMult : sinstr.

(* Exercise: 3 stars (stack_compiler) *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
    | nil => stack
    | cons h t => let nst := match h with
                    | SPush n => cons n stack
                    | SLoad i => cons (st i) stack
                    | SPlus  => match stack with
                                  | (n1 :: n2 :: r) => ((n1 + n2) :: r)
                                  | _ => stack
                                end
                    | SMinus => match stack with
                                  | (n1 :: n2 :: r) => ((n2 - n1) :: r)
                                  | _ => stack
                                end
                    | SMult  => match stack with
                                  | (n1 :: n2 :: r) => ((n1 * n2) :: r)
                                  | _ => stack
                                end
                    end
                   in s_execute st nst t
  end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
    | ANum n     => (SPush n :: nil)
    | AId  i     => (SLoad i :: nil)
    | APlus  a b => (s_compile a ++ s_compile b ++ SPlus  :: nil)
    | AMinus a b => (s_compile a ++ s_compile b ++ SMinus :: nil)
    | AMult  a b => (s_compile a ++ s_compile b ++ SMult  :: nil)
  end.

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

(* END stack_compiler. *)
