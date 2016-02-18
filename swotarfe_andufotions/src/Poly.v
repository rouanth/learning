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

Check @hd_opt.

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
Proof.

(* END currying. *)

