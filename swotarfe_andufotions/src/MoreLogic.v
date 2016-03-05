Require Export PropL.

(* Exercise: 1 star, optional (english_exists) *)

(* ex nat (fun n => beautiful (S n)) means:
There exists such natural number n that the following number has property
"beautiful" *)

(* END english_exists. *)

(* Exercise: 1 star (dist_not_exists) *)

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
  unfold not.
  intros X P H1 H2.
  inversion H2.
  apply H.
  apply H1.
Qed.

(* END dist_not_exists. *)