(* ((Polymorphism)) *)

Fixpoint snoc (X : Type) (l : list X) (n : X) : (list X) :=
  match l with
    | nil => (n :: nil)%list
    | cons m l' => (m :: snoc X l' m)%list
  end.

Fixpoint rev (X : Type) (l : list X) : list X :=
  match l with
    | nil => nil
    | cons h t => snoc X (rev X t) h
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


