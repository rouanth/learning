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

(* ((Induction on Lists)) *)

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

(* ((List Exercises, Part 1)) *)

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

(* Exercise: 2 stars (beq_natlist) *)

Fixpoint beq_natlist (l1 l2 : list nat) : bool :=
  match (l1, l2) with
    | (nil, nil) => true
    | (cons h t, nil) => false
    | (nil, cons h t) => false
    | (cons h1 t1, cons h2 t2) => match beq_nat h1 h2 with
                                    | true => beq_natlist t1 t2
                                    | false => false
                                  end
  end.

Example test_beq_natlist1 : beq_natlist nil nil = true.
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist (1 :: 2 :: 3 :: nil)%list (1 :: 2 :: 3 :: nil)%list = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist (1 :: 2 :: 3 :: nil)%list (1 :: 2 :: 4 :: nil)%list = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : list nat,
  true = beq_natlist l l.
Proof.
  intros l.
  induction l as [|m l'].
  Case "l = nil".
    reflexivity.
  Case "l = m :: l'".
    simpl.
    rewrite <- beq_nat_refl.
    rewrite <- IHl'.
    reflexivity.
Qed.

(* END beq_natlist. *)

(* ((List Exercises, Part 2)) *)

(* Exercise: 2 stars (list_design) *)

Theorem cons_snoc_app : forall (l1 l2 : list nat) (n m : nat),
  (snoc l1 n ++ snoc l2 m)%list = (l1 ++ (n :: l2) ++ (m :: nil))%list.
Proof.
  intros l1 l2 n m.
  replace (n :: l2)%list with (n :: nil ++ l2)%list.
  rewrite -> app_assoc.
  replace (l1 ++ n :: nil ++ l2)%list with ((l1 ++ n :: nil) ++ l2)%list.
  replace (l1 ++ n :: nil)%list with (snoc l1 n).
  rewrite <- app_assoc.
  rewrite <- snoc_append.
  reflexivity.
  Case "snoc l1 n = (l1 ++ n :: nil)".
    rewrite <- snoc_append.
    reflexivity.
  Case "(l1 ++ [n]) ++ l2 = l1 ++ [n] ++ l2".
    rewrite <- app_assoc.
    reflexivity.
  Case "(n :: nil ++ l2)%list = (n :: l2)%list".
    reflexivity.
Qed.

(* END list_design. *)

(* Exercise: 3 stars, advanced (bag_proofs) *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)%list) = true.
Proof. reflexivity. Qed.

Theorem remove_decreases_count : forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [|n s'].
  Case "s = []".
    reflexivity.
  Case "s = n :: s'".
    destruct n.
    SCase "n = 0".
      simpl.
      assert (forall n : nat, ble_nat n (S n) = true).
      SSCase "ble_nat n (S n) = true".
        intros n.
        induction n as [|n'].
        SSSCase "n = 0".
          reflexivity.
        SSSCase "n = S n'".
          simpl.
          rewrite <- IHn'.
          reflexivity.
      rewrite -> H.
      reflexivity.
    SCase "n = S n'".
      simpl.
      rewrite -> IHs'.
      reflexivity.
Qed.

(* END bag_proofs. *)

(* Exercise: 3 stars, optional (bag_count_sum) *)

Theorem bag_count_sum : forall (s d : bag) (n : nat),
  ble_nat (count n s) (count n (bag_sum s d)) = true.
Proof.
  intros s d n.
  induction s as [|m s'].
  Case "s = nil".
    reflexivity.
  Case "s = m :: s'".
    simpl.
    destruct (beq_nat m n).
    SCase "m = n".
      simpl.
      rewrite -> IHs'.
      reflexivity.
    SCase "m != n".
      rewrite -> IHs'.
      reflexivity.
Qed.

(* END bag_count_sum. *)

(* Exercise: 4 stars, advanced (rev_injective) *)

Theorem rev_injective : forall l1 l2 : list nat,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  rewrite <- rev_involutive.
  replace l1 with (rev (rev l1)).
  Case "rev (rev l1) = rev (rev l2)".
    rewrite <- H.
    reflexivity.
  Case "l1 = rev (rev l1)".
    rewrite -> rev_involutive.
    reflexivity.
Qed.

(* END rev_injective. *)

(* ((Options)) *)

Definition option_elim (n : nat) (o : option nat) : nat :=
  match o with
    | None => n
    | Some z => z
  end.

(* Exercise: 2 stars (hd_opt) *)

Definition hd_opt (l : list nat) : option nat :=
  match l with
    | nil => None
    | cons h t => Some h
  end.

Example test_hd_opt1 : hd_opt nil = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt (1 :: nil)%list = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt (5 :: 6 :: nil)%list = Some 5.
Proof. reflexivity. Qed.

(* END hd_opt *)

(* Exercise: 1 star, optional (option_elim_hd) *)

Theorem option_elim_hd : forall (l : list nat) (default : nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n l'".
    reflexivity.
Qed.

(* END option_elim_hd. *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) :
  dictionary := (record key value d).

Fixpoint find (key : nat) (d : dictionary) : option nat :=
  match d with
    | empty => None
    | record key' val d' => if beq_nat key key'
                               then (Some val)
                               else (find key d')
  end.

(* Exercise: 1 star (dictionary_invariant1) *)

Theorem dictionary_invariant1 : forall (d : dictionary) (k v : nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(* END dictionary_invariant1. *)

(* Exercise: 1 star (dictionary_invariant1) *)

Theorem dictionary_invariant2 : forall (d : dictionary) (m n o : nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros d m n o.
  intros H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(* END dictionary_invariant1. *)

End Dictionary.

End NatList.
