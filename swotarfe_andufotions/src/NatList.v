Require Export Induction.

Module NatList.

(* ((Pairs of Numbers)) *)

Definition swap_pair (p : nat * nat) : nat * nat :=
  match p with
    | (x, y) => (y, x)
  end.

(* Exercise: 1 star (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p : nat * nat),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

(* END snd_fst_is_swap. *)

(* Exercise: 1 star, optional (fst_swap_is_snd) *)

Theorem fst_swap_is_snd : forall (p : nat * nat),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

(* END fst_swap_is_snd. *)

Fixpoint repeat (n count : nat) : list nat :=
  match count with
    | O    => nil
    | S c' => cons n (repeat n c')
  end.

Definition hd (default : nat) (l : list nat) : nat :=
  match l with
    | cons h t => h
    | _        => default
  end.

Definition tl (l : list nat) : list nat :=
  match l with
    | cons h t => t
    | nil      => nil
  end.

(* Exercise: 2 stars (list_funs) *)

Fixpoint nonzeros (l : list nat) : list nat :=
  match l with
    | nil      => nil
    | cons h t => match h with
                    | O => nonzeros t
                    | n => cons n (nonzeros t)
                end
  end.

Example test_nonzeros :
  nonzeros (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: nil)%list
  = (1 :: 2 :: 3 :: nil)%list.
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : list nat) : list nat :=
  match l with
    | nil      => nil
    | cons h t => match oddb h with
                    | false => oddmembers t
                    | true  => cons h (oddmembers t)
                  end
  end.

Example test_oddmembers:
  oddmembers (0 :: 1 :: 0 :: 2 :: 3 :: 0 :: 0 :: nil)%list
  = (1 :: 3 :: nil)%list.
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : list nat) : nat :=
  length (oddmembers l).

Example test_countoddmembers1 :
  countoddmembers (1 :: 0 :: 3 :: 1 :: 4 :: 5 :: nil)%list = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2 :
  countoddmembers (0 :: 2 :: 4 :: nil)%list = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3 :
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* END list_funs. *)

(* Exercise: 3 stars, advanced (alternate) *)

Fixpoint alternate (l1 l2 : list nat) : list nat :=
  match (l1, l2) with
    | (l, nil) => l
    | (nil, l) => l
    | (cons h1 t1, cons h2 t2) => (h1 :: h2 :: alternate t1 t2)%list
  end.

Example test_alternate1:
  alternate (1 :: 2 :: 3 :: nil)%list (4 :: 5 :: 6 :: nil)%list
  = (1 :: 4 :: 2 :: 5 :: 3 :: 6 :: nil)%list.
Proof. reflexivity. Qed.

Example test_alternate2: alternate (1 :: nil)%list (4 :: 5 :: 6 :: nil)%list =
  (1 :: 4 :: 5 :: 6 :: nil)%list.
Proof. reflexivity. Qed.

Example test_alternate3: alternate (1 :: 2 :: 3 :: nil)%list (4 :: nil)%list =
  (1 :: 4 :: 2 :: 3 :: nil)%list.
Proof. reflexivity. Qed.

Example test_alternate4: alternate nil (20 :: 30 :: nil)%list
  = (20 :: 30 :: nil)%list.
Proof. reflexivity. Qed.

(* END alternate. *)

Definition bag := list nat.

(* Exercise: 3 stars (bag_functions) *)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => O
    | cons h t => match beq_nat h v with
                    | true  => S (count v t)
                    | false => count v t
                  end
  end.

Example test_count1: count 1 (1 :: 2 :: 3 :: 1 :: 4 :: 1 :: nil)%list = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 (1 :: 2 :: 3 :: 1 :: 4 :: 1 :: nil)%list = 0.
Proof. reflexivity. Qed. 

Definition bag_sum l1 l2 : bag := app  l1 l2.

Example test_sum1 :
  count 1 (bag_sum (1 :: 2 :: 3 :: nil)%list (1 :: 4 :: 1 :: nil)%list) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.

Example test_add1: count 1 (add 1 (1 :: 4 :: 1 :: nil)%list) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 (1 :: 4 :: 1 :: nil)%list) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match count v s with
    | O => false
    | _ => true
  end.

Example test_member1 : member 1 (1 :: 4 :: 1 :: nil)%list = true.
Proof. reflexivity. Qed.

Example test_member2 : member 2 (1 :: 4 :: 1 :: nil)%list = false.
Proof. reflexivity. Qed.

(* END bag_functions. *)

(* Exercise: 3 stars, optional (bag_more_functions) *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | cons h t => match beq_nat h v with
                    | true  => t
                    | false => cons h (remove_one v t)
                  end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 (2 :: 1 :: 5 :: 4 :: 1 :: nil)%list) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 (2 :: 1 :: 4 :: 1 :: nil)%list) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 (2 :: 1 :: 4 :: 5 :: 1 :: 4 :: nil)%list) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 (2 :: 1 :: 5 :: 4 :: 5 :: 1 :: 4 :: nil)%list) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | cons h t => match beq_nat v h with
                    | true => remove_all v t
                    | false => cons h (remove_all v t)
                  end
  end.

Example test_remove_all1:
  count 5 (remove_all 5 (2 :: 1 :: 5 :: 4 :: 1 :: nil)%list) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2:
  count 5 (remove_all 5 (2 :: 1 :: 4 :: 1 :: nil)%list) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3:
  count 4 (remove_all 5 (2 :: 1 :: 4 :: 5 :: 1 :: 4 :: nil)%list) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4:
  count 5 (remove_all 5 (2 :: 1 :: 5 :: 4 :: 5 :: 1 :: 4 :: 5 :: 1 :: 4
  :: nil)%list) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
    | nil => true
    | cons h t => match ble_nat (count h s1) (count h s2) with
                    | false => false
                    | true  => subset t s2
                  end
  end.

Example test_subset1 :
  subset (1 :: 2 :: nil)%list (2 :: 1 :: 4 :: 1 :: nil)%list = true.
Proof. reflexivity. Qed.

Example test_subset2 :
  subset (1 :: 2 :: 2 :: nil)%list (2 :: 1 :: 4 :: 1 :: nil)%list = false.
Proof. reflexivity. Qed.

(* END bag_more_functions. *)

(* Exercise: 3 stars (bag_theorem) *)

Theorem bag_add_incr_count :
  forall (b : bag), forall (n : nat), count n (add n b) = 1 + count n b.
Proof.
  intros b n.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem bag_add_n_not_incr_count_m :
  forall (b : bag), forall (n m : nat),
  (beq_nat m n = false) ->
  count n (add m b) = count n b.
Proof.
  intros b n m H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(* END bag_theorem. *)

Fixpoint snoc (l : list nat) (v : nat) : list nat :=
  match l with
    | nil => (v :: nil)%list
    | (h :: t)%list => (h :: (snoc t v))%list
  end.

Fixpoint rev (l : list nat) : list nat :=
  match l with
    | nil => nil
    | (h :: t)%list => snoc (rev t) h
  end.

(* Exercise: 3 stars (list_exercises) *)

Theorem app_nil_end : forall l : list nat,
  app l nil = l.
Proof.
  intros l.
  induction l as [|v l'].
  Case "l = nil".
    reflexivity.
  Case "l = v :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [|v l'].
  Case "l = nil".
    reflexivity.
  Case "l = v :: l'".
    simpl.
    assert (forall z : list nat, forall m : nat,
            rev (snoc z m) = (m :: rev z)%list).
    SCase "proving rev (snoc l v) = v :: rev l".
      intros z m.
      induction z as [|m' z'].
      SSCase "z = nil".
        reflexivity.
      SSCase "z = m' :: z'".
        simpl.
        rewrite -> IHz'.
        reflexivity.
    rewrite -> H.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : list nat,
  app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  intros l1 l2 l3.
  induction l1 as [|m l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = m :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : list nat,
  app l1 (app l2 (app l3 l4)) = app (app (app l1 l2) l3) l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Theorem snoc_append : forall (l : list nat) (n : nat),
  snoc l n = app l (n :: nil)%list.
Proof.
  intros l n.
  induction l as [|m l'].
  Case "l = nil".
    reflexivity.
  Case "l = m :: l'".
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

Theorem rev_reverses : forall (l : list nat) (n : nat),
  rev (l ++ n :: nil)%list = (n :: rev l)%list.
Proof.
  intros l n.
  induction l as [|m l'].
  Case "l = nil".
    reflexivity.
  Case "l = m :: l'".
    simpl.
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : list nat,
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [|m l1'].
  Case "l1 = nil".
    rewrite -> app_nil_end.
    reflexivity.
  Case "l1 = m :: l1'".
    simpl.
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    rewrite -> IHl1'.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Theorem nonzeros_app : forall l1 l2 : list nat,
  nonzeros (l1 ++ l2)%list = (nonzeros l1 ++ nonzeros l2)%list.
Proof.
  intros l1 l2.
  induction l1 as [|m l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = m : l1'".
    simpl.
    rewrite -> IHl1'.
    destruct m.
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      reflexivity.
Qed.

(* END list_exercises. *)

