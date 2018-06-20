(* -*- coding: utf-8; mode:coq -*-
 * Auto-generated - Do not edit or overwrite!
 *)

Require Import Arith. (* ouvre droit, notamment, à 'auto with arith' *)

Section exo1.
  
  

  (* Programme annoté :

  { y = 2 }
    Auto0:x <- (y + 3)
  { (x = 5 and y = 2) }

  *)

  (* Valeurs des Weakest Least Preconditions (WLP) *)
  Definition Post (x y : nat) := (x = 5 /\ y = 2).
  Definition Pre (x y : nat) := y = 2.
  Definition Auto0 (x y : nat) := ((y + 3) = 5 /\ y = 2).

  (* Obligations de preuve engendrées *)
  Lemma obligation_Pre : forall x y : nat,
    (y = 2 -> ((y + 3) = 5 /\ y = 2)).
  Proof.
    intros.
    split.
    rewrite H.
    trivial.
    assumption.
  Qed.
  

  

End exo1.
