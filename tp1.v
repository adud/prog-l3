(*
Adresse email des TDmen : [Prenom].[Nom]@ens-lyon.fr

Pour avoir les raccourcis comme il faut :
- Lancer "coqide" 
- Edit > Preferences > Shortcuts > Modifiers for Navigation Menu
- Changer vers <alt> uniquement (en sélectionnant/désélectionnant les cases)
- Cliquer sur OK
- Quitter coqide
- Relancer coqide
*)



(* Table des matières du TP:
	1. Découverte de coq
	2. Démonstrations élémentaires
	3. Inductions structurelles
	4. Calcul Propositionnel
	5. Arithmétique *)

(** TP n°1 : Introduction à Coq **)

(** Partie 1 : Découverte de coq **)

(* Toutes les expressions bien formées de Coq ont un type que l'on
peut demander à l'interpréteur grâce à la commande "Check" : *)

Check 3. (* "nat" : type des entiers naturels *)
Check 2 + 2. 
Check (plus 2 2). (* + est une notation "infixe" de la fonction plus *)
Check plus.  (* fonction qui prend deux "nat"s et renvoie un "nat" *)


(* Les types sont eux-mêmes des expressions bien formées de Coq, elles
ont donc également un type. *)

Check nat. (* "Set" est le type des types de données. *)

Check nat -> nat -> nat.


(* On peut également demander à Coq de nous donner la définition d'une 
d'une expression déjà définie; on utilise pour ça la commande "Print". *) 

Print nat.
Print plus.


(* On peut bien sûr définir de nouvelles fonctions *) 

Definition facteur_deux (n : nat) := 2 * n.
Check facteur_deux.
Print facteur_deux.


(* Et on utilise la syntaxe suivante pour faire des définitions
récursives: *)

Fixpoint double (n : nat) :=
  match n with 
    | 0 => 0
    | S p => S (S (double p))
  end.

Print double.


(* Sur le même modèle implémentez la fonction [somme_jusqu_a : nat -> nat] qui
calcule la somme des premiers entiers *)

Fixpoint somme_jusqu_a (n : nat ) :=
    match n with
    |0 => 0
    |S p => n + somme_jusqu_a p
    end.
(* ... Complétez ici ... *)

Eval compute in somme_jusqu_a 10.



(** Partie 2 : Démonstrations élementaires **)


(* En plus des types de données et des programmes, coq permet également 
de manipuler des formules. À commencer par les égalités : *)

Check 0 = 0. (* "Prop" : type des formules logiques. *)
Check 0 = 1. (* "Prop" : type des formules logiques, même si elles sont fausses! *)

(* Enfin, Coq permet de prouver les formules à l'aide d'un système de 
   "tactiques" de preuves. 
   Voici la liste des tactiques que nous allons explorer: 
    reflexivity , intros , simpl , rewrite , induction
    (l'utilisation de toute autre tactique, trouvée sur internet par exemple, est prohibée) *)
Lemma zero_egale_zero :
  0 = 0.
Proof.
reflexivity. (* Comme on le verra plus tard, c'est la tactique qui
                  résout les égalités triviales. *)
Qed.

Lemma deux_plus_deux_egale_quatre : 
  2+2 = 4.
Proof.
simpl. (* Cette tactique nous sera très utile dans la suite, elle
                  sert à effectuer les pas de calcul dans les buts. *)
reflexivity.
Qed.

(* On dispose également de quantificateurs pour fabriquer les formules :*)
Check (forall x y : nat, x+y = y + x). (* Une formule qui nous dit que + est commutatif. *)

(* Il y a quelques tactiques qu'il faudra apprendre à utiliser.
   Voici un exemple de preuve un peu moins triviales. Pouvez-vous 
   retranscrire cette preuve simple en "mathématiques informelles" ? *)

(* On dispose également d'une égalité entre les termes de 
   coq qui vient avec trois tactiques pour les manipuler: 
      - [reflexivity] : permet de prouver les but de la forme t=t. 
      - [symmetry] : permet de transformer un but t₁ = t₂ en t₂ = t₁.
      - [rewrite H] : si H est une hypothèse de la forme "t₁ = t₂"
        cette tactique remplace dans le but courant les sous-termes
        de la forme t₁ par t₂.
      - [rewrite <-H] : si H est une hypothèse de la forme "t₁ = t₂"
        cette tactique remplace dans le but courant les sous-termes
        de la forme t₂ par t₁.  *)

Lemma double_egale_multiple_de_deux : 
  forall n, double n = n * 2.
intros n. (*soit n entier*)
induction n. (*par récurrence sur n*)
+ simpl. (*initialisation par calcul*)
  reflexivity. (*par réflexivité*)
+ simpl. (*heredite, calcul*)
  rewrite IHn. (*par hypothese de recurrence*)
  reflexivity. (*par reflexivite*)
Qed.


(* "+", "*" ou "-" en début de ligne servent uniquement à mettre structurer et indenter la preuve;
   mathématiquement, cela revient à ne rien faire *)


(* Les deux tactiques centrales de COQ sont 
     - [intros H] : l'équivalent de "soit H" et de "supposons que..."
                   dans les maths informelles, [intros H] introduit une
                   hypothèse H dans le contexte.
       (notez qu'il est également permis d'invoquer [intros H1 H2 H3]
       à la place de [intros A. intros B. intros C.]  pour faire des 
       intros successifs)
     - [apply H] : permet d'invoquer l'hypothèse nommée H. *)




Lemma egalite_transitive :
  forall (x y z : nat), x = y -> y = z -> x = z.
Proof.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.


(** Partie 3: Définitions inductives, inductions structurelles *)


(* Jusqu'ici, on a utilisés la commande induction 
   pour réaliser des récurrences sur les entiers; 
   cependant, les entiers sont des types inductifs! Regardez à nouveau: *)

Print nat.
Print plus.


(* De facon informelle, quand on definit un type inductif on donne
toutes les manières de construire un élément de ce type.  Un entier
naturel est soit zéro (construit par le constructeur "O"), soit le
successeur d'un autre entier naturel (construit par le constructeur
"S").
  
                      n : nat 
   ----------      --------------
    0 : nat          S n : nat    
  
Un autre exemple : le type "bool" des booleens est également inductif:
  
    -----------          ------------
    true : bool          false : bool      *)

Print bool.

(* Un booléen est soit 0, soit 1; soit vrai, soit faux. *)

(* En coq, on peut aussi définir de nouveaux types inductifs! Par exemple, les listes. La
définition ressemble à celle que l'on aurait fait en Caml: *)

Inductive liste_nat := 
 | liste_vide : liste_nat
 | cons : nat -> liste_nat -> liste_nat.


(* On définit le type "liste_nat" de liste des entiers naturels avec deux
constructeurs : "liste_vide" qui permet de construire la liste vide et
"cons_nat" qui permet de construire une nouvele liste à partir d'un
entier et une liste.
                                      l : liste_nat                 n : nat
   ------------------------         -----------------------------------------
    liste_vide : liste_nat                  cons_nat n l : liste_nat
*)



(* Et on peut définir comment concaténer deux listes, comme on a fait plus tôt pour
calculer le double d'un entier: *)

Fixpoint concat (l l' : liste_nat) := match l with
 | liste_vide => l'
 | cons n l'' => cons n (concat l'' l')
end.



(* Complétez la définition de la mesure de la longueur d'une liste d'entiers: *)

Fixpoint longueur l := match l with
 | liste_vide => 0
 | cons n l' => 1 + longueur l'
end.



(* Chaque fois qu'on définit un type inductif, Coq génère un principe
d'induction pour ce type. *)

Check liste_nat_ind.
Check nat_ind.
Check bool_ind.

(* Ce principe va être automatiquement invoqué quand on utilise la
tactique [induction]. Morale : on peut utiliser [induction] pour faire
de preuves sur tous les types inductifs. *)


(* On peut désormais prouver les lemmes suivants : *)

Lemma concat_vide : forall (l : liste_nat), concat liste_vide l = l.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Lemma vide_concat : forall (l : liste_nat), concat l liste_vide = l.
Proof.
   intros.
   induction l.
   * simpl.
   reflexivity.
   *
   simpl.
   rewrite IHl.
   reflexivity.
Qed.


Lemma longueur_concat : forall (l l' : liste_nat), longueur (concat l l') = longueur l + longueur l'.
Proof.
    intros.
    induction l.
    *
    simpl.
    reflexivity.
    *
    simpl.
    rewrite IHl.
    reflexivity.
Qed.


(** Partie 4 : Calcul propositionnel **)

(* A vous de jouer maintenant! *)

Lemma trivial1 : forall P : Prop, P -> P.
Proof.
    intros.
    apply H.
Qed.


Lemma trivial2: forall P Q R:Prop, (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
    intros.
    apply H.
    *
    apply H1.
    *
    apply H0.
    apply H1.
Qed.


(* Coq fournit les connecteurs logiques usuels :
       connecteur ┃ destructeur ┃ constructeur
      ━━━━━━━━━━━━╋━━━━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━
          P /\ Q  ┃ [destruct]  ┆  [split]
          P \/ Q  ┃ [destruct]  ┆  [left] et [right]
  exists x:nat, P ┃ [destruct]  ┆  [exists t]
          False   ┃ [destruct]  ┆  aucun

  Il est donc désormais autorisé d'utiliser, en plus des tactiques déjà explorées, les tactiques suivantes:
   apply , destruct , split , left , right , exists

  Mais, encore une fois, aucune autre tactique n'est autorisée!
*)

Lemma conj1: forall P Q:Prop, P /\ Q -> P.
Proof.
    intros.
    destruct H.
    apply H.
Qed.

Lemma conj2: forall P Q:Prop, P /\ Q -> Q.
Proof.
    intros.
    destruct H.
    apply H0.
Qed.

Lemma conj3: forall P Q:Prop, P -> Q -> P /\ Q.
Proof.
    intros.
    split.
    apply H.
    apply H0.
Qed.

Lemma or1 : forall P Q:Prop, P -> P \/ Q.
Proof.
    intros.
    left.
    apply H.
Qed.

Lemma or2 : forall P Q:Prop, Q -> P \/ Q.
Proof.
    intros.
    right.
    apply H.
Qed.

Lemma or3 : forall P Q R:Prop, P \/ Q -> (P -> R) -> (Q -> R) -> R.
Proof.
    intros.
    destruct H.
    * apply H0.
    apply H.
    *
    apply H1.
    apply H.
Qed.

(* En COQ, la proposition fausse, ou "l'absurde", est appelée "False". *)

Lemma ex_falso: forall P:Prop, False -> P. (* si on suppose l'absurde, on peut tout démontrer *)
Proof.
    intros.
    destruct H.
Qed.

Notation "~ P" := (P -> False). (* On définit la négation ainsi: la proposition "Non P", notée ~ P,
                                   est vraie si supposer P permet de prouver l'absurde *)


Lemma not_not : forall P:Prop, P -> ~~P.
Proof.
    intros P H H0.
    apply H0.
    apply H.
Qed.

Lemma morgan1 : forall P Q:Prop, 
  ~P \/ ~Q -> ~(P /\ Q).
Proof.
    intros.
    intros H0.
    destruct H0.
    destruct H.
    *
    apply H.
    apply H0.
    *
    apply H.
    apply H1.
Qed.

Lemma morgan2 : forall P Q:Prop, 
  ~P /\ ~Q -> ~(P \/ Q).
Proof.
    intros.
    intros H1.
    destruct H.
    destruct H1.
    *
    apply H.
    apply H1.
    *
    apply H0.
    apply H1.
Qed.


(* En coq on peut également définition des propositions
   qui dépendent de paramètre. Cela permet de représenter
   d'autres relations que l'égalité *)

Definition leq (n m : nat) := exists k, n+k = m.
Check leq. (* Méditez le type de la relation. *)


Lemma leq_reflexive : 
  forall x, leq x x.
Proof.
    intros.
    exists 0.
    induction x.
    *
    simpl.
    apply zero_egale_zero.
    *
    simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma plus_associative:
  forall x y z, x+(y+z)=(x+y)+z.
Proof.
  intros.
  induction x.
  *simpl.
   reflexivity.
  *simpl.
   rewrite IHx.
   reflexivity.
Qed.

Lemma leq_transitive : 
  forall x y z, leq x y -> leq y z -> leq x z.
Proof.
  intros.
  destruct H.
  destruct H0.
  exists (x0+x1).
  rewrite<- H0.
  rewrite<- H.
  apply plus_associative.
Qed.
(** Partie 5 : Arithmétique **)

(* Rappel: on utilise la tactique simpl, pour simplifier les calculs. *)
Lemma zero_plus : forall x:nat, 0 + x = x.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma exists_factor : 
  exists n, exists m , n * (m+1) = 35.
Proof.
  exists 5.
  exists 6.
  simpl.
  reflexivity.
Qed.

(* La tactique simpl ne marche par pour prouver la proposition
   suivante. Pourquoi ? *)

Lemma plus_zero : forall x:nat, x + 0 = x.
Proof.

(* Il va nous faloir démontrer le résultat par récurrence sur la
   forme de x. 
   La tactique [induction x] invoque automatiquement le 
   principe d'induction pour prouver un but par induction sur 
   la variable x. *)

  induction x.
  *
    reflexivity.
  *
    simpl.
    rewrite IHx.
    reflexivity.
(* Il faut ensuite prouver le cas de base et l'hérédité...*) 

Qed.

Lemma plus_assoc : forall a b c, (a + b) + c = a + (b + c).
Proof.
  symmetry.
  apply plus_associative.
Qed.

Lemma mult_zero : forall a, a*0 = 0.
Proof.
  induction a.
  *
    simpl.
    reflexivity.
  *
    simpl.
    apply IHa.
Qed.





(** Pour aller plus loin **)

(* Pour finir, quelques exercices pour occuper les plus rapides d'entre vous :*)

(* N'hésitez pas à faire des lemmes intermédiaires !*)


(* Ce  n'est pas aussi trivial qu'il n'y paraît. *)


Lemma add1_trv : forall a, S a = 1+a.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma add1_comm : forall a, S a = a+1.
Proof.
  intros.
  induction a.
  *
    apply zero_plus.    
  *
    simpl.
    rewrite IHa.
    reflexivity.
Qed.
    
Lemma plus_comm : forall a b, a + b = b + a.
Proof.
  induction b.
  *
    simpl.
    apply plus_zero.
  *
    rewrite add1_trv.
    rewrite plus_associative.
    rewrite<- add1_comm.
    simpl.
    rewrite IHb.
    reflexivity.
Qed.

Lemma mult_distrib_gauche : forall a b c, a * (b + c) = a * b + a * c.
Proof.
  induction a.
  *
  simpl.
  reflexivity.
  *
    simpl.
    intros.
    rewrite IHa.
    rewrite plus_assoc.
    rewrite 
Qed.

Lemma mult_distrib_droite : forall a b c, (b + c) * a = b * a + c * a.
Proof.
...
Qed.

Lemma mult_comm : forall a b, a * b = b * a.
Proof.
  induction a.
  *
    simpl.
    symmetry.
    apply mult_zero.
  *
    intros.
    simpl.
    Print Nat.mul.
    rewrite. 
Qed.

Lemma identite : 
  forall a b, (a + b)*(a+b) = a*a + 2*a*b + b*b.
Proof.
...
Qed.

(* Écrivez la fonction [power] qui calcule les puissances entières : *)
Fixpoint power a b := 
...

Infix "^" := power.

Lemma power_exp: 
  forall a n m, a^(n + m) = a^n * a^m.
Proof.
...
Qed.

Lemma closed:
  forall n a b c, 3 <= n -> a^n + b^n = c^n -> a = c \/ b = c.
Proof.
...
Qed.

