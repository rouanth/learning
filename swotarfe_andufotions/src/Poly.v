Require Export Induction.
(* ((Polymorphism)) *)

Fixpoint snoc {X : Type} (l : list X) (n : X) : (list X) :=
  match l with
    | nil => (n :: nil)%list
    | cons h t => (h :: snoc t n)%list
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
    | nil => nil
    | cons h t => snoc (rev t) h
  end.

(* Exercise: 2 stars (mumble_grumble) *)

(* 
Inductive mumble : Type :=
  | a : mumble
  | b : mumble → nat → mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble → grumble X
  | e : X → grumble X.

Which of the following are well-typed elements of grumble X for some type X?
- d (b a 5)      // the type cannot be inferred
+ d mumble (b a 5)
+ d bool (b a 5)
+ e bool true
+ e mumble (b c 0)
- e bool (b c 0) // (b c 0) is a mumble, not bool
- c              // is a mumble
*)

(* END mumble_grumble. *)

(* Exercise: 2 stars (baz_num_elts) *)

(* None. There are no sinks. *)

(* END baz_num_elts. *)

(* Exercise: 2 stars, optional (poly_exercises) *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | O => nil
    | S c' => (n :: repeat n c')%list
  end.

Example test_repeat1 : repeat true 2 = (true :: true :: nil)%list.
Proof. reflexivity. Qed.

Theorem nil_app : forall X : Type, forall l : list X,
  app nil l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc : forall X : Type, forall v : X, forall l : list X,
  rev (snoc l v) = (v :: rev l)%list.
Proof.
  intros X v l.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    assert (forall Z : Type, forall z : list Z, forall m : Z,
            rev (snoc z m) = (m :: rev z)%list).
    SCase "proving rev (snoc l v) = v :: rev l".
      intros Z z m.
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

Theorem snoc_with_append :
  forall X : Type, forall l1 l2 : list X, forall v : X,
  snoc (l1 ++ l2)%list v = (l1 ++ snoc l2 v)%list.
Proof.
  intros X l1 l2 v.
  induction l1 as [|n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = n :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

(* END poly_exercises. *)

(* Exercise: 1 star, optional (combine_checks) *)

(* combine : forall X Y : Type, -> list X -> list Y -> list (X * Y) *)

(* Eval compute in (combine [1; 2] [false; false; true; true])
= [(1, false), (2, false)]
*)

(* END combine_checks. *)

(* Exercise: 2 stars (split) *)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | nil => (nil, nil)
    | cons (x, y) t => match split t with
                         (xt, yt) => ((x :: xt)%list, (y :: yt)%list)
                       end
  end.

Example test_split:
  split ((1, false) :: (2, false) :: nil)%list =
  ((1 :: 2 :: nil)%list, (false :: false :: nil)%list).
Proof. reflexivity. Qed.

(* END split. *)

(* Exercise: 1 star, optional (hd_opt_poly) *)

Definition hd_opt { X : Type } (l : list X) : option X :=
  match l with
    | nil => None
    | cons h t => Some h
  end.

Example test_hd_opt1 : hd_opt (1 :: 2 :: nil)%list = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2 :
  hd_opt ((1 :: nil)%list :: (2 :: nil)%list :: nil)%list =
  Some (1 :: nil)%list.
Proof. reflexivity. Qed.

(* END hd_opt_poly. *)

(* ((Functions as Data)) *)

Definition prod_curry { X Y Z : Type }
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* Exercise: 2 stars, advanced (currying) *)

Definition prod_uncurry { X Y Z : Type }
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with (x, y) => f x y end.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  replace (prod_curry (prod_uncurry f) x y) with ((prod_uncurry f) (x, y)).
    reflexivity.
    reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.
Qed.

(* END currying. *)

Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X :=
  match l with
    | nil => nil
    | cons h t => if f h then cons h (filter f t) else filter f t
  end.

(* Exercise: 2 stars (filter_even_gt7) *)

Definition filter_even_gt7_1 (l : list nat) : list nat :=
  filter (fun x => ((evenb x) && negb (ble_nat 7 x))%bool) l.

(* END filter_even_gt7. *)

(* Exercise: 3 stars (partition) *)

Definition partition {X : Type} (f : X -> bool) (l : list X)
  : list X * list X :=
  (filter f l, filter (fun x => negb (f x)) l).

Example test_partition1 : partition oddb (1 :: 2 :: 3 :: 4 :: 5 :: nil)%list =
  ((1 :: 3 :: 5 :: nil)%list, (2 :: 4 :: nil)%list).
Proof. reflexivity. Qed.

Example test_partition2 :
  partition (fun x => false) (5 :: 9 :: 0 :: nil)%list =
  (nil, (5 :: 9 :: 0 :: nil)%list).
Proof. reflexivity. Qed.

(* END partition. *)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
    | nil => nil
    | cons h t => (f h :: map f t)%list
  end.

(* Exercise: 3 stars (map_rev) *)

Theorem map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1 ++ map f l2)%list.
Proof.
  intros X Y f l1 l2.
  induction l1 as [|n l1'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l1'".
    simpl.
    rewrite <- IHl1'.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    assert (forall (Z : Type) (j : list Z) (k : Z),
            snoc j k = (j ++ (k :: nil))%list).
      intros Z j k.
      induction j as [|m j'].
      SCase "j = nil".
        reflexivity.
      SCase "j = m :: j'".
        simpl.
        rewrite -> IHj'.
        reflexivity.
    rewrite -> H.
    rewrite -> H.
    rewrite <- IHl'.
    rewrite -> map_app.
    reflexivity.
Qed.

(* END map_rev. *)

(* Exercise: 2 stars (flat_map) *)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
    | nil => nil
    | cons h t => (f h ++ flat_map f t)%list
  end.

Example test_flat_map1:
  flat_map (fun n => (n :: n :: n :: nil)%list) (1 :: 5 :: 4 :: nil)%list =
  (1 :: 1 :: 1 :: 5 :: 5 :: 5 :: 4 :: 4 :: 4 :: nil)%list.
Proof. reflexivity. Qed.

(* END flat_map. *)

(* Exercise: 1 star, advanced (fold_types_different) *)

(* rev = fold (fun x y => snoc y x) *)

(* END fold_types_different. *)

Definition constfun {X : Type} (x : X) : nat -> X := fun k => x.

Definition override {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if beq_nat k k' then x else f k'.

(* Exercise: 1 star (override_example) *)

Theorem override_example : forall (b : bool),
  override (constfun b) 3 true 2 = b.
Proof.
  intros b.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

(* END override_example. *)

(* Exercise: 2 stars (override_neq) *)

Theorem override_neq : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f.
  intros H1.
  intros H2.
  unfold override.
  rewrite -> H2.
  rewrite -> H1.
  trivial.
Qed.

(* END override_neq. *)

(* ((Additional Exercises)) *)

Fixpoint fold { X Y : Type } (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    | nil => b
    | cons h t => f h (fold f t b)
  end.

(* Exercise: 2 stars (fold_length) *)

Definition fold_length { X : Type } (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length (4 :: 7 :: 0 :: nil)%list = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X), fold_length l = length l.
Proof.
  intros X l.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

(* END fold_length. *)

(* Exercise: 3 stars (fold_map) *)

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => cons (f x) y) l nil.

Theorem fold_map_correct : forall (X Y : Type) (l : list X) (f : X -> Y),
  map f l = fold_map f l.
Proof.
  intros X Y l f.
  induction l as [|n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

(* END fold_map. *)

Fixpoint index { X : Type } (n : nat) (l : list X) : option X :=
  match l with
    | nil => None
    | cons h t => if beq_nat n 0 then Some h else index (pred n) t
  end.

(* Exercise: 2 stars, advanced (index_informal) *)

(* Performing an induction over the given list, we have the following cases.
* If the list is empty, the case is trivial: no elements are present, and the
* function returns None.
* If the list is non-empty, then its length is not zero; thus the index in the
* remaining list can't be zero, and the inductive step applies. *)

(* END index_informal. *)

Module Church.

Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition zero : nat := fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : nat := fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : nat := fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(* Exercise: 4 stars, advanced (church_numerals) *)

Definition succ (n : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) => m X (n X f).

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) => m (X -> X) (n X) (one X f).

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

(* END church_numerals. *)

End Church.

