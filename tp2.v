Require Import Arith.

(* Quelques tactiques utiles, qu'on verra au fur et a mesure :
  - assert (un énoncé) H12
  - replace (un terme) with (un autre)
  - inversion H.    
  - ((auto with arith : seulement quand la tactique est EXPLICITEMENT autorisée)) *)


(** Partie I : Petits prédicats inductifs *)

(* Réflechissez un peu au sens de nat -> Prop *)

(*A.nat -> Prop est un predicat sur les entiers*)

(* En plus des types de données inductifs, Coq permet de définir des
propriétés inductives. Par exemple, la propriété que un nat est pair
peut être définie de la facon suivante : *)

Inductive even : nat -> Prop := 
  | even_zero : even 0 
  | even_succ : forall n, even n -> even (S (S n)).


(*                   even n 
   --------       -------------- 
    even 0        even (S (S n))     *)


(* Définissez vous-même le prédicat "odd" pour designer les
impairs. Essayez de trouver une définition avec UN SEUL
constructeur. *)

Inductive odd : nat -> Prop :=
  | odd_succ : forall n, even n -> odd (S n).

(* [inversion H] est une tactique compliquée qui élimine les cas
impossibles dans les types inductifs. Servez-vous en pour prouver : *)

Lemma not_even: ~ odd 0.
  intros H.
  inversion H.
Qed.

Lemma odd_even : forall n, odd n -> even (S n).
  intros.
  inversion H.
  apply even_succ.
  apply H0.
Qed.

Lemma eventwo_times : forall n, even (n * 2).
  intros.
  induction n.
  *
    simpl.
    apply even_zero.
  *
    simpl.
    apply even_succ.
    apply IHn.
Qed.

Lemma odd_or_even : forall n, even n \/ odd n.
  intros.
  induction n.
  *
    left.
    apply even_zero.
  *
    destruct IHn.
    right.
    apply odd_succ.
    apply H.
    left.
    apply odd_even.
    apply H.
Qed.

Lemma evenS_odd : forall n, even (S n) -> odd n.
  intros.
  inversion H.
  apply odd_succ.
  apply H1.
Qed.

Lemma oddS_even : forall n, odd (S n) -> even n.
  intros.
  inversion H.
  apply H1.
Qed.

(* Conseil: utilisez inversion. *)
Lemma odd_and_even : forall n, ~ (even n /\ odd n).
  induction n.
  *
    unfold not.
    intros.
    destruct H.
    apply not_even.
    apply H0.
  *
    unfold not.
    intros H0.
    destruct IHn.
    destruct H0.
    split.
    apply oddS_even.
    apply H0.
    apply evenS_odd.
    apply H.
Qed.




(** Prédicats inductifs : relations *)

(* Le type [A -> A -> Prop] des formules paramétrées par deux éléments
de A sert à représenter les relations sur A. *)
Definition relation A := A -> A -> Prop.

(* Par exemple la relation [div] est une [relation nat] *)

(* Mais on peut aussi définir des relations de relations comme par
example l'inclusion entre les relations. *)
Definition incl A : relation (relation A) := fun R1 R2 => 
  forall x y, R1 x y -> R2 x y.

(* Definissez la relation maximale, la relation minimale (i.e. la
relation vide) ainsi que la relation identité. *)
Definition rel_full A : relation A :=
  fun x y => True.
Definition rel_empty A : relation A :=
  fun x y => False. 
Definition rel_id A : relation A :=
  fun x y => x=y.

(* Étant donnée une relation, définissez la relation réciproque. *)
Definition converse A (R : relation A) :=
  fun x y => R y x.

(* On peut aussi définir des propriétés sur les relations comme par
exemple la transitivité : *)
Definition transitive A (R : relation A) : Prop  := 
  forall x y z, R x y -> R y z -> R x z.

(* Définissez la réflexivité et la symétrie: *)
Definition reflexive A (R : relation A) : Prop :=
  forall x, R x x.
Definition symmetric A (R : relation A) : Prop :=
  forall x y, R x y -> R y x.

(* Pour vous chauffer, prouvez le lemme suivant. Indice: Utilisez la
tactique [unfold D] pour déplier la définition D. La tactique [compute
in H] permet de normaliser le type de H *)
Lemma incl_conv : forall A R, incl A R (converse A R) -> symmetric A R.
  intros.
  compute in H.
  compute.
  apply H.
Qed.

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

(* Prouvez que R est incluse dans sa cloture. *)
Lemma R_star : incl A R star.
  compute.
  intros.
  apply star_R with y.
  apply H.
  apply star_refl.
Qed.

(* Prouvez que la cloture est transitive. Indice : Dans [apply h with
t], le mot-clef 'with' permet de donner à apply les arguments qu'il
n'arrive pas à inférer. *)
Lemma star_trans : transitive _ star.
  compute.
  intros.
  induction H.
  *
    apply H0.
  *
    apply IHstar in H0.
    apply star_R with b.
    apply H.
    apply H0.
Qed.

(* En passant, vous pouvez démontrer ça aussi. *)
Lemma star_ass : forall a b c, star a b -> R b c -> star a c.
Proof.
  intros.
  apply R_star in H0.
  apply star_trans with b.
  apply H.
  apply H0.
Qed.
  
Lemma star_sym : symmetric _ R -> symmetric _ star.
Proof.
  compute.
  intros.
  induction H0.
  apply star_refl.
  apply H in H0.
  apply star_ass with b.
  apply IHstar.
  apply H0.
Qed.

Check star_trans.  
End Star.
Check star_trans.






(** Partie II : Sémantique à grands pas *)

(* Considérons la grammaire d'expressions suivante, avec les mots
inhabituels "Randombit" et "AssertZero", qui sont expliqués plus
bas. *)

Inductive expr : Set :=
  | N : nat -> expr
  | Randombit : expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | AssertZero : expr -> expr -> expr.

(* Donnez une sémantique à grand pas avec le sens suivant :
  - N n
      représente l'entier n
      
      -------
      N n → n
  
  - Plus, Mult et Minus
      comme en cours
      
      e₁ → n₁     e₂ → n₂ 
      -------------------
      Plus e₁ e₂ → n₁ + n₂
      
  
  - Randombit
      peut engendrer 0
      peut engendrer 1
      
      ------------       ------------
      Randombit → 0      Randombit → 1
  
  - AssertZero e1 e2
      s'assure que e1 peut réduire vers 0 et se comporte comme e2 dans
      ce cas.
      
      e₁ → 0        e₂ → n₂
      ---------------------
      AssertZero e₁ e₂ → n₂
*)

Inductive bs : expr -> nat -> Prop := 
  | bs_nat : forall n, bs (N n) n
  | bs_Randombit0 : bs Randombit 0
  | bs_Randombit1 : bs Randombit 1
  | bs_Plus : forall e1 e2 n m, bs e1 n -> bs e2 m -> bs (Plus e1 e2) (n+m)
  | bs_Mult : forall e1 e2 n m, bs e1 n -> bs e2 m -> bs (Mult e1 e2) (n*m)
  | bs_Minus : forall e1 e2 n m, bs e1 n -> bs e2 m -> bs (Minus e1 e2) (n-m)
  | bs_AssertZero : forall e1 e2 n, bs e1 0 -> bs e2 n -> bs (AssertZero e1 e2) n
.                                                         
(* Question :
  
Essayez de définir une telle sémantique pour faire en sorte que
"AssertZero e1 e2" se comporte comme "e2" si "e1" ne peut PAS se
réduire vers 0. Coq accepte-t'il la définition ? Pourquoi ? *)

Lemma expression_example :
  bs (AssertZero (Minus (Minus (N 2) Randombit) Randombit) (Mult (N 5) (N 3))) 15.
 (* replace expr1 with expr2 => substitue expr1 par expr2 et un but apparait pour prouver l'égalité *)


Qed.


(* On va vouloir définir une fonction d'évaluation des expressions; pour ça, on se débarasse de RandomBit et 
    on le remplace par Zero et Un, qui valent toujours zero et un! Commentez les expressions et redéfinissez-les ainsi. *)




(* Définissez maintenant une fonction récursive eval qui calcule la valeur d'une expression 
    arithmétique. Pour le cas ou un AssertZero échoue, considérez que la valeur retournée par l'assert est 0. *)

Fixpoint eval (e : expr) : nat := match e with
 | ...
end.

(* On va maintenant prouver  qu'on a défini une fonction qui est correcte vis-à-vis de 
	la sémantique à grand pas des expressions *)

Lemma eval_correct : forall (e : expr) (n : nat), bs e n -> eval e = n.

Qed.

(* Peut-on prouver le lemme opposé? (c'est-à-dire que si eval e = n, alors on a bs e n). Pourquoi? *)








