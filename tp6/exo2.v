(* -*- coding: utf-8; mode:coq -*-
 * Auto-generated - Do not edit or overwrite!
 *)

Require Import Arith. (* ouvre droit, notamment, à 'auto with arith' *)

Section exo2.
  
  Parameter a b : nat.

  (* Programme annoté :

  { (x = a and y = b) }
    Auto0:t <- x    
    Auto1:x <- y    
    Auto2:y <- t
  { (x = b and y = a) }

  *)

  (* Valeurs des Weakest Least Preconditions (WLP) *)
  Definition Post (t x y : nat) := (x = b /\ y = a).
  Definition Pre (t x y : nat) := (x = a /\ y = b).
  Definition Auto2 (t x y : nat) := (x = b /\ t = a).
  Definition Auto1 (t x y : nat) := (y = b /\ t = a).
  Definition Auto0 (t x y : nat) := (y = b /\ x = a).

  (* Obligations de preuve engendrées *)
  Lemma obligation_Pre : forall t x y : nat,
    ((x = a /\ y = b) -> (y = b /\ x = a)).
  Proof.
    intros.
    destruct H.
    split.
    assumption.
    assumption.
  Qed.
  

  

End exo2.
