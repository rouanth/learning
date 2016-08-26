Require Import SfLib.
Require Import Types.
Require Import Smallstep.
Require Import Stlc.
Require Import Imp.

(* Exercise: 1 star, optional (halve_fix) *)

(*
halve_fix = fix (\f : Nat -> Nat.
              forall x : Nat.
                if x == 0 then 0 else
                if pred x == 0 then 0 else
                1 + f (pred (pred x)))
*)

(* END halve_fix. *)

Module STLCExtended.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty
  | TUnit  : ty
  | TProd  : ty -> ty -> ty
  | TSum   : ty -> ty -> ty
  | TList  : ty -> ty.

Inductive tm : Type :=
  | tvar  : id -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : id -> ty -> tm -> tm

  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm

  | tpair : tm -> tm -> tm
  | tfst  : tm -> tm
  | tsnd  : tm -> tm

  | tunit : tm

  | tlet  : id -> tm -> tm -> tm

  | tinl  : ty -> tm -> tm
  | tinr  : ty -> tm -> tm
  | tcase : tm -> id -> tm -> id -> tm -> tm

  | tnil  : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase: tm -> tm -> id -> id -> tm -> tm

  | tfix  : tm -> tm
.

(* Exercise: 4 stars, optional (STLC_extensions) *)

Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
    | tvar i   => if eq_id_dec i x then s else tvar i
    | tapp a b => tapp (subst x s a) (subst x s b)
    | tabs i T a => tabs i T (if eq_id_dec i x then a else (subst x s a))

    | tnat n   => tnat n
    | tsucc a  => tsucc (subst x s a)
    | tpred a  => tpred (subst x s a)
    | tmult a b => tmult (subst x s a) (subst x s b)
    | tif0 c a b => tif0 (subst x s c) (subst x s a) (subst x s b)

    | tpair a b => tpair (subst x s a) (subst x s b)
    | tfst a => tfst (subst x s a)
    | tsnd a => tsnd (subst x s a)

    | tunit  => tunit

    | tlet i d b => if eq_id_dec i x
                    then tlet i (subst x s d) (subst x s b)
                    else tlet i d b

    | tinl T a => tinl T (subst x s a)
    | tinr T a => tinr T (subst x s a)
    | tcase bd x1 t1 x2 t2 => tcase (subst x s bd)
        x1 (if eq_id_dec x x1 then t1 else subst x s t1)
        x2 (if eq_id_dec x x2 then t2 else subst x s t2)

    | tnil T => tnil T
    | tcons h t => tcons (subst x s h) (subst x s t)
    | tlcase c tn x1 x2 tc => tlcase (subst x s c) (subst x s tn)
        x1 x2 (if eq_id_dec x1 x then tc else if eq_id_dec x2 x then tc else
               (subst x s tc))

    | tfix t => tfix (subst x s t)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
            value (tabs x T t)
  | v_nat : forall n,
            value (tnat n)
  | v_pair : forall t1 t2,
            value t1 -> value t2 -> value (tpair t1 t2)
  | v_unit : value tunit
  | v_inl  : forall T t,
            value t ->
            value (tinl T t)
  | v_inr  : forall T t,
            value t ->
            value (tinr T t)
  | v_lnil : forall T, value (tnil T)
  | v_cons : forall th tt,
            value th ->
            value tt ->
            value (tcons th tt)
.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
      value v ->
      tapp (tabs x T t) v ==> [x := v] t
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tapp t1 t2 ==> tapp t1 t2'
  | ST_Succ1 : forall t t',
      t ==> t' ->
      tsucc t ==> tsucc t'
  | ST_SuccNat : forall n,
      tsucc (tnat n) ==> tnat (S n)
  | ST_Pred1 : forall t t',
      t ==> t' ->
      tpred t ==> tpred t'
  | ST_PredNat : forall n,
      tpred (tnat n) ==> tnat (pred n)
  | ST_Mult1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2 : forall t1 t2 t2',
      t2 ==> t2' ->
      tmult t1 t2 ==> tmult t1 t2'
  | ST_MultNats : forall n1 n2,
      tmult (tnat n1) (tnat n2) ==> tnat (n1 * n2)
  | ST_If01 : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif0 t1 t2 t3 ==> tif0 t1' t2 t3
  | ST_If0Zero : forall t2 t3,
      tif0 (tnat 0) t2 t3 ==> t2
  | ST_If0Nonzero : forall n t2 t3,
      tif0 (tnat (S n)) t2 t3 ==> t3
  | ST_Pair1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tpair t1 t2 ==> tpair t1' t2
  | ST_Pair2 : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tpair t1 t2 ==> tpair t1 t2'
  | ST_Fst1 : forall t t',
      t ==> t' ->
      tfst t ==> tfst t'
  | ST_FstPair : forall t1 t2,
      value t1 ->
      value t2 ->
      tfst (tpair t1 t2) ==> t1
  | ST_Snd1 : forall t t',
      t ==> t' ->
      tsnd t ==> tsnd t'
  | ST_SndPair : forall t1 t2,
      value t1 ->
      value t2 ->
      tsnd (tpair t1 t2) ==> t2
  | ST_Let1 : forall x tb tb' tc,
      tb ==> tb' ->
      tlet x tb tc ==> tlet x tb' tc
  | ST_Let : forall x tb tc,
      value tb ->
      tlet x tb tc ==> [x := tb] tc
  
  where "t1 '==>' t2" := (step t1 t2).

(* END STLC_extensions. *)

End STLCExtended.

