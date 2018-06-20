(* -*- coding: utf-8; mode:coq -*-
 * Auto-generated - Do not edit or overwrite!
 *)

Require Import Arith. (* ouvre droit, notamment, à 'auto with arith' *)

Section exo3.
  
  (* Il existe une fonction, qui réalise une certaine spécification *)

  Variable fact : nat -> nat.
  Axiom fact_spec_zero : fact 0 = 1.
  Axiom fact_spec_succ : forall x : nat, x > 0 -> fact x = x * fact (x - 1).

  Parameter n : nat.

  (* Programme annoté :

  { (n >= 0 and x = n) }
    Auto0:f <- 1    
    Inv:assert (fact(n) = (f * fact(x)) and x >= 0);    
    Auto4:while (x > 0) {
        Auto1:f <- (f * x)      
        Auto2:x <- (x - 1)
      }
  { (fact(n) = f and x = 0) }

  *)

  (* Valeurs des Weakest Least Preconditions (WLP) *)
  Definition Post (f x : nat) := ((fact n) = f /\ x = 0).
  Definition Pre (f x : nat) := (n >= 0 /\ x = n).
  Definition Auto4 (f x : nat) := ((fact n) = (f * (fact x)) /\ x >= 0).
  Definition Auto2 (f x : nat) := ((fact n) = (f * (fact (x - 1))) /\ (x - 1) >= 0).
  Definition Auto1 (f x : nat) := ((fact n) = ((f * x) * (fact (x - 1))) /\ (x - 1) >= 0).
  Definition Inv (f x : nat) := ((fact n) = (f * (fact x)) /\ x >= 0).
  Definition Auto0 (f x : nat) := ((fact n) = (1 * (fact x)) /\ x >= 0).

  (* Obligations de preuve engendrées *)
  Lemma obligation_Pre : forall f x : nat,
    ((n >= 0 /\ x = n) -> ((fact n) = (1 * (fact x)) /\ x >= 0)).
  Proof.
    intros.
    destruct H.
    subst.
    split.
    auto with arith.
    assumption.
  Qed.

  
  Lemma obligation_Inv_false : forall f x : nat,
    (((fact n) = (f * (fact x)) /\ x >= 0) -> (x <= 0 -> ((fact n) = f /\ x = 0))).
  Proof.
    intros.
    destruct H.
    split.
    assert(x=0).
    auto with arith.
    subst.
    rewrite fact_spec_zero in H.
    auto with arith.
    assert(f*1=f).
    auto with arith.
    rewrite H2 in H.
    assumption.
    auto with arith.
  Qed.

  Lemma obligation_Inv_true : forall f x : nat,
    (((fact n) = (f * (fact x)) /\ x >= 0) -> (x > 0 -> ((fact n) = ((f * x) * (fact (x - 1))) /\ (x - 1) >= 0))).
  Proof.
    intros.
    destruct H.
    split.
    rewrite H.
    rewrite fact_spec_succ.
    auto with arith.
    assumption.
    auto with arith.
  Qed.
  

  

End exo3.
