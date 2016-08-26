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
                    then tlet i d b
                    else tlet i (subst x s d) (subst x s b)

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
  | ST_Inl : forall T t t',
      t ==> t' ->
      tinl T t ==> tinl T t'
  | ST_Inr : forall T t t',
      t ==> t' ->
      tinr T t ==> tinr T t'
  | ST_Case : forall c c' x1 b1 x2 b2,
      c ==> c' ->
      tcase c x1 b1 x2 b2 ==> tcase c' x1 b1 x2 b2
  | ST_CaseL : forall T c x1 b1 x2 b2,
      value c ->
      tcase (tinl T c) x1 b1 x2 b2 ==> [x1 := c] b1
  | ST_CaseR : forall T c x1 b1 x2 b2,
      value c ->
      tcase (tinr T c) x1 b1 x2 b2 ==> [x2 := c] b2
  | ST_Cons1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tcons t1 t2 ==> tcons t1' t2
  | ST_Cons2 : forall t1 t2 t2',
      t2 ==> t2' ->
      tcons t1 t2 ==> tcons t1 t2'
  | ST_Lcase1 : forall c c' tn xh xt tc,
      c ==> c' ->
      tlcase c tn xh xt tc ==> tlcase c' tn xh xt tc
  | ST_LcaseNil : forall T tn xh xt tc,
      tlcase (tnil T) tn xh xt tc ==> tn
  | ST_LcaseCons : forall th tt tn xh xt tc,
      value th ->
      value tt ->
      tlcase (tcons th tt) tn xh xt tc ==> [xt := tt] [xh := th] tc
  | ST_Fix1 : forall t t',
      t ==> t' ->
      tfix t ==> tfix t'
  | ST_Fix : forall F x T t,
      F = tabs x T t ->
      tfix F ==> [x := tfix F] t
  where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).

Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Definition context := id -> option ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Definition pupdate { A : Type } (m : id -> option A) (x : id) (v : A) :=
  update m x (Some v).

Hint Constructors step.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_App : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in (TArrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- tapp t1 t2 \in T2
  | T_Abs : forall Gamma x t T1 T2,
      (pupdate Gamma x T1) |- t \in T2 ->
      Gamma |- tabs x T1 t \in TArrow T1 T2
  | T_Nat : forall Gamma n,
      Gamma |- tnat n \in TNat
  | T_Succ : forall Gamma tn,
      Gamma |- tn \in TNat ->
      Gamma |- tsucc tn \in TNat
  | T_Pred : forall Gamma tn,
      Gamma |- tn \in TNat ->
      Gamma |- tpred tn \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in TNat ->
      Gamma |- tmult t1 t2 \in TNat
  | T_If0 : forall Gamma T tc tt te,
      Gamma |- tc \in TNat ->
      Gamma |- tt \in T ->
      Gamma |- te \in T ->
      Gamma |- tif0 tc tt te \in T
  | T_Pair : forall Gamma t1 T1 t2 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- tpair t1 t2 \in TProd T1 T2
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t \in TProd T1 T2 ->
      Gamma |- tfst t \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t \in TProd T1 T2 ->
      Gamma |- tsnd t \in T2
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  | T_Let : forall Gamma x tl Tl t T,
      Gamma |- tl \in Tl ->
      (pupdate Gamma x Tl) |- t \in T ->
      Gamma |- tlet x tl t \in T
  | T_Inl : forall Gamma t T1 T2,
      Gamma |- t \in T1 ->
      Gamma |- tinl T2 t \in TSum T1 T2
  | T_Inr : forall Gamma t T1 T2,
      Gamma |- t \in T2 ->
      Gamma |- tinr T1 t \in TSum T1 T2
  | T_Case : forall Gamma tc x Tx tx y Ty ty T,
      Gamma |- tc \in TSum Tx Ty ->
      (pupdate Gamma x Tx) |- tx \in T ->
      (pupdate Gamma y Ty) |- ty \in T ->
      Gamma |- tcase tc x tx y ty \in T
  | T_Nil : forall Gamma T,
      Gamma |- tnil T \in TList T
  | T_Cons : forall Gamma t1 t2 T,
      Gamma |- t1 \in T ->
      Gamma |- t2 \in TList T ->
      Gamma |- tcons t1 t2 \in TList T
  | T_Lcase : forall Gamma tc tn xh xt tht Tl T,
      Gamma |- tc \in TList Tl ->
      Gamma |- tn \in T ->
      (pupdate (pupdate Gamma xh Tl) xt (TList Tl)) |- tht \in T ->
      Gamma |- tlcase tc tn xh xt tht \in T
  | T_Fix : forall Gamma t T,
      Gamma |- t \in TArrow T T ->
      Gamma |- tfix t \in T
  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Module Examples.

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).
Notation x := (Id 9).
Notation y := (Id 10).
Notation processSum := (Id 11).
Notation n := (Id 12).
Notation eq := (Id 13).
Notation m := (Id 14).
Notation evenodd := (Id 15).
Notation even := (Id 16).
Notation odd := (Id 17).
Notation eo := (Id 18).

Hint Extern 2 (has_type _ (tapp _ _) _) =>
  eapply T_App; auto.
(* You'll want to uncomment the following line once
   you've defined the T_Lcase constructor for the typing
   relation: *)

Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.

Hint Extern 2 (_ = _) => compute; reflexivity.

Module Numtest.

(* if0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  tif0
    (tpred
      (tsucc
        (tpred
          (tmult
            (tnat 2)
            (tnat 0)))))
    (tnat 5)
    (tnat 6).

Example typechecks :
  (fun r => None) |- test \in TNat.
Proof.
  unfold test.
  (* This typing derivation is quite deep, so we need to increase the
     max search depth of auto from the default 5 to 10. *)
  auto 10.
Qed.

Example numtest_reduces :
  test ==>* tnat 5.
Proof.
  unfold test. normalize.
Qed.

End Numtest.


Module Prodtest.

(* ((5,6),7).fst.snd *)
Definition test :=
  tsnd
    (tfst
      (tpair
        (tpair
          (tnat 5)
          (tnat 6))
        (tnat 7))).

Example typechecks :
  (fun a => None) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.

End Prodtest.

Module LetTest.

(* let x = pred 6 in succ x *)
Definition test :=
  tlet
    x
    (tpred (tnat 6))
    (tsucc (tvar x)).

Example typechecks :
  (fun a => None) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.

End LetTest.

Module Sumtest1.

(* case (inl Nat 5) of
     inl x => x
   | inr y => y *)

Definition test :=
  tcase (tinl TNat (tnat 5))
    x (tvar x)
    y (tvar y).

Example typechecks :
  (fun a => None) |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tnat 5).
Proof. unfold test. normalize. Qed.

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => if0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition test :=
  tlet
    processSum
    (tabs x (TSum TNat TNat)
      (tcase (tvar x)
         n (tvar n)
         n (tif0 (tvar n) (tnat 1) (tnat 0))))
    (tpair
      (tapp (tvar processSum) (tinl TNat (tnat 5)))
      (tapp (tvar processSum) (tinr TNat (tnat 5)))).

Example typechecks :
  (fun a => None) |- test \in (TProd TNat TNat).
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tpair (tnat 5) (tnat 0)).
Proof. unfold test. normalize. Qed.

End Sumtest2.

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of
     nil => 0
   | x::y => x*x *)

Definition test :=
  tlet l
    (tcons (tnat 5) (tcons (tnat 6) (tnil TNat)))
    (tlcase (tvar l)
       (tnat 0)
       x y (tmult (tvar x) (tvar x))).

Example typechecks :
  (fun a => None) |- test \in TNat.
Proof. unfold test. eauto 20. Qed.

Example reduces :
  test ==>* (tnat 25).
Proof. unfold test. normalize. Qed.

End ListTest.

Module FixTest1.

(* fact := fix
             (\f:nat->nat.
                \a:nat.
                   if a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  tfix
    (tabs f (TArrow TNat TNat)
      (tabs a TNat
        (tif0
           (tvar a)
           (tnat 1)
           (tmult
              (tvar a)
              (tapp (tvar f) (tpred (tvar a))))))).

Example fact_typechecks :
  (fun a => None) |- fact \in (TArrow TNat TNat).
Proof. unfold fact. auto 10. Qed.

Example fact_example:
  (tapp fact (tnat 4)) ==>* (tnat 24).
Proof. unfold fact. normalize. Qed.

End FixTest1.

Module FixTest2.

(* map :=
     \g:nat->nat.
       fix
         (\f:nat->nat.
            \l:nat.
               case l of
               |  -> 
               | x::l -> (g x)::(f l)) *)
Definition map :=
  tabs g (TArrow TNat TNat)
    (tfix
      (tabs f (TArrow (TList TNat) (TList TNat))
        (tabs l (TList TNat)
          (tlcase (tvar l)
            (tnil TNat)
            a l (tcons (tapp (tvar g) (tvar a))
                         (tapp (tvar f) (tvar l))))))).

Example map_typechecks :
  (fun a => None) |- map \in
    (TArrow (TArrow TNat TNat)
      (TArrow (TList TNat)
        (TList TNat))).
Proof. unfold map. auto 10. Qed.

Example map_example :
  tapp (tapp map (tabs a TNat (tsucc (tvar a))))
         (tcons (tnat 1) (tcons (tnat 2) (tnil TNat)))
  ==>* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))).
Proof. unfold map. normalize. Qed.

End FixTest2.

Module FixTest3.

(* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if0 m then (if0 n then 1 else 0)
             else if0 n then 0
             else eq (pred m) (pred n))   *)

Definition equal :=
  tfix
    (tabs eq (TArrow TNat (TArrow TNat TNat))
      (tabs m TNat
        (tabs n TNat
          (tif0 (tvar m)
            (tif0 (tvar n) (tnat 1) (tnat 0))
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tapp (tvar eq)
                              (tpred (tvar m)))
                      (tpred (tvar n)))))))).

Example equal_typechecks :
  (fun a => None) |- equal \in (TArrow TNat (TArrow TNat TNat)).
Proof. unfold equal. auto 10.
Qed.

Example equal_example1:
  (tapp (tapp equal (tnat 4)) (tnat 4)) ==>* (tnat 1).
Proof. unfold equal. normalize. Qed.

Example equal_example2:
  (tapp (tapp equal (tnat 4)) (tnat 5)) ==>* (tnat 0).
Proof. unfold equal. normalize. Qed.

End FixTest3.

Module FixTest4.

(* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. if0 n then 1 else eo.snd (pred n) in
              let o = \n:Nat. if0 n then 0 else eo.fst (pred n) in
              (e,o)) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)
*)

Definition eotest :=
  tlet evenodd
    (tfix
      (tabs eo (TProd (TArrow TNat TNat) (TArrow TNat TNat))
        (tpair
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 1)
              (tapp (tsnd (tvar eo)) (tpred (tvar n)))))
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tfst (tvar eo)) (tpred (tvar n))))))))
  (tlet even (tfst (tvar evenodd))
  (tlet odd (tsnd (tvar evenodd))
  (tpair
    (tapp (tvar even) (tnat 3))
    (tapp (tvar even) (tnat 4))))).

Example eotest_typechecks :
  (fun a => None) |- eotest \in (TProd TNat TNat).
Proof. unfold eotest. eauto 30.
Qed.

Example eotest_example1:
  eotest ==>* (tpair (tnat 0) (tnat 1)).
Proof. unfold eotest. normalize. Qed.

End FixTest4.

End Examples.

(* END STLC_extensions. *)

End STLCExtended.

