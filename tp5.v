(** TP5 : Lemme du diamant, pour prouver la confluence du lambda-calcul *)



(** Prédicats inductifs : relations **)

(* Le type [A -> A -> Prop] des formules paramétrées par deux éléments
de A sert à représenter les relations sur A. *)
Definition relation A := A -> A -> Prop.

(* Mais on peut aussi définir des relations de relations comme par
example l'inclusion entre les relations. *)
Definition incl A : relation (relation A) := fun R1 R2 => 
  forall x y, R1 x y -> R2 x y.

(* Definissez la relation maximale, la relation minimale (i.e. la
relation vide) ainsi que la relation identité. *)
Definition rel_full A : relation A := fun x y => True.
Definition rel_empty A : relation A := fun x y => False.
Definition rel_id A : relation A := fun x y => x = y.

(* Étant donnée une relation, définissez la relation réciproque. *)
Definition converse A (R : relation A) := fun x y => R y x.

(* On peut aussi définir des propriétés sur les relations comme par
exemple la transitivité : *)
Definition transitive A (R : relation A) : Prop  := 
  forall x y z, R x y -> R y z -> R x z.

(* Définissez la réflexivité et la symétrie: *)
Definition reflexive A (R : relation A) : Prop := forall n, R n n.
Definition symmetric A (R : relation A) : Prop := forall x y, R x y -> R y x.


(* Dans cette section nous allons fabriquer la cloture reflexive
transitive d'une relation. *)

Section Star. 

(* On suppose qu'on dispose d'un type A et d'une relation sur A. *)
Variable A : Type. 
Variable R : A -> A -> Prop. 

(* On définit le prédicat inductif suivant : *)
Inductive star : A -> A -> Prop :=
  | star_refl : forall a, star a a
  | star_R : forall a b c, R a b -> star b c -> star a c.

Lemma R_star : incl A R star.
Proof.
  intros x y Rxy.
  apply (star_R x y y).
    assumption.
    constructor.
Qed.

Lemma star_trans : transitive A star.
Proof.
  intros x y z p. induction p.
    intros q. assumption.
    intros q. apply star_R with b.
      assumption.
      apply IHp. assumption.
Qed.

Definition plus x y := exists z, R x z /\ star z y.

Lemma R_plus : forall x y, R x y -> plus x y.
Proof.
  intros x y p. exists y. split.
    assumption.
    constructor.
Qed.

Lemma plus_trans :transitive A plus.
Proof.
  intros x y z p q.
  destruct p as [s [p1 p2]].
  destruct q as [t [q1 q2]].
  exists s. split.
    assumption.
    apply star_trans with t.
      apply star_trans with y.
        assumption.
        apply R_star. assumption.
      assumption.
Qed.

Check star_trans.  
End Star.
Check star_trans.




(** Définition de la confluence **)


Variable A : Type.
Variable R : relation A.

Notation "a => b" := (R a b) (at level 42).
Notation "a =>* b" := (star _ R a b) (at level 42).
Notation "a =>+ b" := (plus _ R a b) (at level 42).


Definition confl_wrt (x : A) :=
  forall n1 n2:A, (x =>* n1 /\ x =>* n2) -> exists p:A, n1 =>* p /\ n2=>* p.

Definition confl := forall x, confl_wrt x.



(** Propriété et lemme du diamant *)


Definition dia_wrt (x : A) := ...

Definition dia := forall x, dia_wrt x.

Lemma dia_one_square: dia -> forall x y, x =>* y -> forall z, x => z ->
  exists k, z =>* k /\ y => k.
Proof.
...
Qed.


Lemma diaconfl : dia -> confl.
Proof.
...
Qed.






