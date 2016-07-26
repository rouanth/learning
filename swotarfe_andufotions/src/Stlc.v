Require Import Imp.
Require Import Smallstep.
Require Import Types.

Module STLC.

Inductive ty :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

Inductive tm :=
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : id -> ty -> tm -> tm
  | ttrue  : tm
  | tfalse : tm
  | tif    : tm -> tm -> tm -> tm
.

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
    | tvar i   => if eq_id_dec i x then s else tvar i
    | tapp a b => tapp ([x := s] a) ([x := s] b)
    | tabs i tp bd => if eq_id_dec i x then tabs i tp bd
                      else tabs i tp ([x := s] bd)
    | tif c bt be => tif ([x := s] c) ([x := s] bt) ([x := s] be)
    | e => e
  end
  where "'[' x ':=' s ']' t" := (subst x s t).

(* Exercise: 3 stars (substi) *)

Inductive substi (s : tm) (x : id) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tvar x) s
  | s_var2 : forall i,
      i <> x ->
      substi s x (tvar i) (tvar i)
  | s_app  : forall a a' b b',
      substi s x a a' ->
      substi s x b b' ->
      substi s x (tapp a b) (tapp a' b')
  | s_abs1 : forall tp bd,
      substi s x (tabs x tp bd) (tabs x tp bd)
  | s_abs2 : forall i tp bd bd',
      i <> x ->
      substi s x bd bd' ->
      substi s x (tabs i tp bd) (tabs i tp bd')
  | s_if   : forall c c' t t' e e',
      substi s x c c' ->
      substi s x t t' ->
      substi s x e e' ->
      substi s x (tif c t e) (tif c' t' e')
  | s_true :
      substi s x ttrue ttrue
  | s_false :
      substi s x tfalse tfalse
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x := s] t = t' <-> substi s x t t'.
Proof.
  split; intro.
  - generalize dependent t'.
    induction t; simpl; intros; subst; auto;
      destruct (eq_id_dec i x0); subst; auto.
  - induction H; simpl; subst; auto;
      try rewrite eq_id; try rewrite neq_id; auto.
Qed.

(* END substi. *)

Inductive value : tm -> Prop :=
  | v_abs   : forall x T t, value (tabs x T t)
  | v_true  : value ttrue
  | v_false : value tfalse.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
      value v2 ->
      (tapp (tabs x T t12) v2) ==> [x := v2] t12
  | ST_App1   : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_App2   : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tapp t1 t2 ==> tapp t1 t2'
  | ST_IfTrue  : forall t e,
      tif ttrue t e ==> t
  | ST_IfFalse : forall t e,
      tif tfalse t e ==> e
  | ST_If : forall c c' t e,
      c ==> c' ->
      tif c t e ==> tif c' t e
  where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).

Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Notation idB    := (tabs x TBool (tvar x)).
Notation idBB   := (tabs x (TArrow TBool TBool) (tvar x)).
Notation idBBBB := (tabs x (TArrow (TArrow TBool TBool) (TArrow TBool TBool))
                           (tvar x)).

(* Exercise: 2 stars (step_example3) *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. apply v_abs.
  eapply multi_step.
    apply ST_AppAbs. apply v_abs.
  simpl. apply multi_refl.
Qed.

Lemma step_example5_with_normalize :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof. normalize. Qed.

(* END step_example3. *)

Definition context := id -> option ty.

Definition pupdate { A : Type } (m : id -> option A) (x : id) (v : A) :=
  update m x (Some v).

Hint Unfold pupdate.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall G i T,
      G i = Some T ->
      G |- tvar i \in T
  | T_Abs : forall G i T11 bd T12,
      pupdate G i T11 |- bd \in T12 ->
      G |- tabs i T11 bd \in TArrow T11 T12
  | T_App : forall G a1 a2 T11 T12,
      G |- a1 \in TArrow T11 T12 ->
      G |- a2 \in T11 ->
      G |- tapp a1 a2 \in T12
  | T_True : forall G,
      G |- ttrue \in TBool
  | T_False : forall G,
      G |- tfalse \in TBool
  | T_If : forall G c t e T,
      G |- c \in TBool ->
      G |- t \in T ->
      G |- e \in T ->
      G |- (tif c t e) \in T
  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* Exercise: 2 stars, optional (typing_example_2_full) *)

Example typing_example_2_full :
  (fun _ => None) |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  apply T_Abs. apply T_Abs.
  unfold pupdate.
  apply T_App with TBool. apply T_Var. reflexivity.
  apply T_App with TBool. apply T_Var. reflexivity.
  apply T_Var. reflexivity.
Qed.

(* END typing_example_2_full. *)

(* Exercise: 2 stars (typing_example_3) *)

Example typing_example_3 :
  exists T,
    (fun _ => None) |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in T.
Proof with auto.
  exists (TArrow (TArrow TBool TBool)
    ((TArrow (TArrow TBool TBool) (TArrow TBool TBool)))).
  repeat econstructor.
Qed.

(* END typing_example_3. *)

End STLC.
