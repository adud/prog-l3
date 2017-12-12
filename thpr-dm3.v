(* DM : Equivalence des sémantiques petits et grands pas*)

(* Ce DM est la suite du TP4; la première partie du fichier correspond simplement au corrigé du TP4. 
Les définitions pour les sémantiques opérationnelles petit et grand pas sont données, ainsi que les preuves 
de l'implication grand pas -> petit pas. 
Le but du DM est de montrer l'autre sens de l'implication: grand pas -> petit pas. Puis de 
montrer le déterminisme de la sémantique à grand pas. *)



(* PREMIÈRE PARTIE : rappel des définitions pour la sémantique de IMP,
  preuves des lemmes prouvant l'implication execute => ss *)
(* IL N'Y A RIEN À COMPLÉTER DANS CETTE PARTIE *)

Require Import List.

(* Les valeurs calculées seront des entiers. *)
Definition value := nat.
(* Les addresses seront implémentées par des entiers. *)
Definition addr := nat.   
(* La mémoire sera représentée par une liste de couples adresse/valeur *)
Definition env := list (addr * value). 

(* Le prédicat (get l a x) signifie que (a,x) ∈ l. 
   Il est axiomatisé par les règles suivantes : 
                                    get l a x
  ────────────────── head  a≠b ──────────────────── tail
  get ((a,x)::l) a x            get ((b,y)::l) a x

*)
Inductive get : env -> addr -> value -> Prop :=
| get_head : forall a x l, get ((a,x)::l) a x
| get_tail : forall a x b y l, get l a x->~a=b->get ((b,y)::l) a x.

(* Le prédicat (update l a y l') signifie que l' est obtenu en 
   remplaçant la première occurence de (a,_) dans l par (a,y). *)
(* 
                                                       update l a x l'
  ──────────────────────────────── head  a≠b ────────────────────────────────── tail
  update ((a,x)::l) a y ((a,y)::l)            update ((b,y)::l) a x ((b,y)::l')

*)
Inductive update : env -> addr -> value -> env -> Prop :=
|update_head : forall a x l y, update ((a,x)::l) a y ((a,y)::l)
|update_tail : forall a x l' b y l, update l a x l' -> ~a=b -> update ((b,y)::l) a x ((b,y)::l').


(* Les termes arithmétiques du langage sont donnés par
   la grammaire suivante *)
Inductive aexpr : Type :=
   | zero : aexpr
   | var : addr -> aexpr
   | succ : aexpr -> aexpr
   | pred : aexpr -> aexpr. 

(* On a aussi des expressions booleens*)
Inductive bexpr : Type :=
   | blt : aexpr -> aexpr -> bexpr
   | bneq : aexpr -> aexpr -> bexpr.

(* Les programmes sont donnés par : *)
Inductive prg : Type :=
   | skip : prg
   | seq : prg -> prg -> prg
   | ass : addr -> aexpr -> prg 
   | ifte : bexpr -> prg -> prg -> prg
   | while : bexpr -> prg -> prg.

Notation "# x" := (var x) (at level 0).
Notation "x << y" := (blt x y) (at level 70).
Notation "x <<>> y" := (bneq x y) (at level 70).
Notation "A ; B" := (seq A B) (at level 100, right associativity).
Notation "A <- B" := (ass A B) (at level 80, right associativity).



(* Sémantique grand pas pour les expressions arithmetiques:
                         get ρ x n              <ρ|t> ⇓ n
  ──────────── zero    ───────────── var   ────────────────── succ
  <ρ|zero> ⇓ 0         <ρ|var x> ⇓ n       <ρ|succ t> ⇓ (S n)

        <ρ|t> ⇓ (S n)              <ρ|t> ⇓ 0
       ────────────── pred_S    ────────────── pred_0
       <ρ|pred t> ⇓ n           <ρ|pred t> ⇓ 0

 *)



Inductive aeval : env -> aexpr -> value -> Prop :=
|aeval_zero : forall l, aeval l zero 0
|aeval_var : forall l x n, get l x n->aeval l #x n
|aeval_succ : forall l t n, aeval l t n->aeval l (succ t) (S n)
|aeval_pred_S : forall l t n, aeval l t (S n)->aeval l (pred t) n
|aeval_pred_0 : forall l t, aeval l t 0-> aeval l (pred t) 0.
(*Sémantique grand pas pour les expressions booleenes.*)
(*
   <ρ|x> ⇓ n   <ρ|y> ⇓ m   n < m 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ true        


   <ρ|x> ⇓ n   <ρ|y> ⇓ m   m <= n 
  ─────────────────────────────── 
         <ρ|x<<y> ⇓ false        
*)

Inductive beval : env -> bexpr -> bool -> Prop :=
|beval_true : forall rho x n m y, aeval rho x n-> aeval rho y m-> n<m -> beval rho (x<<y) true
|beval_false : forall rho x n y m, aeval rho x n->aeval rho y m->m<=n->beval rho (x<<y) false
|beval_true_neq : forall rho x n y m, aeval rho x n->aeval rho y m->n<>m->beval rho (x<<>>y) true
|beval_false_neq : forall rho x n y m, aeval rho x n->aeval rho y m->n=m->beval rho (x<<>>y) false.



(* Sémantique grand pas pour les programmes. *)
Inductive execute : env -> prg -> env -> Prop :=
|execute_skip : forall sigma, execute sigma skip sigma
|execute_seq : forall o o' o'' c1 c2, execute o c1 o'->execute o' c2 o''->execute o (c1;c2) o''
|execute_ifte_t : forall c1 c2 o o' b, beval o b true->execute o c1 o'->execute o (ifte b c1 c2) o'
|execute_ifte_f : forall c1 c2 o o' b, beval o b false->execute o c2 o'->execute o (ifte b c1 c2) o'
|execute_while_false : forall b c o, beval o b false->execute o (while b c) o
|execute_while_true : forall b o o' c o'', beval o b true->execute o c o'->execute o' (while b c) o''->execute o (while b c) o''
|execute_assign : forall o o' x a n, aeval o a n->update o x n o'->execute o (x<-a) o'.




Check sym_eq.
Check plus_n_Sm.



(* On maintenant s'intéresser à une sémantique à petits pas
   en montrer son équivalence avec la sémantique à grands pas
   donnée par execute *)
Reserved Notation "A => B" (at level 80). 

Definition state := (prg * env)%type.
Notation "[ π | p ]" := (π,p).

Inductive ss : state -> state -> Prop :=
  | ss_ass : forall s s' i a x, aeval s a x -> update s i x s' -> [i <- a | s] => [skip | s']
  | ss_seq_skip : forall s c, [skip ; c | s] => [ c | s ] 
  | ss_seq_seq : forall s s' c c' d, [c | s] => [c'|s'] -> [c ; d|s] => [ c' ; d | s']
  | ss_ifte_true : forall s b c d, beval s b true -> [ ifte b c d | s ] => [ c | s ]
  | ss_ifte_false : forall s b c d, beval s b false -> [ ifte b c d | s ] => [ d | s ]
  | ss_while : forall s b c, [ while b c | s ] => [ ifte b (c ; while b c) skip | s ]
where "A => B" := (ss A B). 


(* L'évaluation d'un programme correspond à la clôture 
   réflexive transitive de la sémantique à petit-pas.
   La définir inductivement permet de raisonner 
   dessus plus facilement.
*)

Section Star. 
Variable A : Type. 
Variable R : A -> A -> Prop. 

Inductive star : A -> A -> Prop :=
  | star_refl : forall a, star a a
  | star_R : forall a b c, R a b -> star b c -> star a c. 

Lemma star_trans : forall a b c, star a b -> star b c -> star a c.
intros.
Proof.
induction H.
apply H0.
apply star_R with b.
apply H.
apply IHstar.
apply H0.
Qed.

End Star.

Notation "A =>* B" := (star _ ss A B) (at level 20).

(* On va maintenant montrer l'équivalence entre les deux sémantiques. *)

(* On commence par grands pas -> petits pas. *)
(* Le séquencement ';' est géré de manière différente
   par les deux sémantiques : *)
Check execute_seq.
Check ss_seq_skip.
Check ss_seq_seq.

(* On va montrer que =>* peut traiter ';' de manière similaire
   à ss_seq_seq :
     pour tous p q r e1 e2,
   [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2]
*)

(* La tactique [induction H] est insuffisante
   pour certains prédicats inductifs dépendants.
   Commencez par décommenter les lignes suivantes
   et essayer de continuer la preuve ...
*)
(*
Goal forall p q r e1 e2,
  [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2].
intros. induction H.
...
*)
(* Cette difficulté se résoud en renforcant le principe d'induction.
   On utilise pour cela la tactique [assert P].
*)

(* Astuce : la tactique [injection H] permet d'utiliser l'injectivité
     des constructeurs (en particulier du constructeur de paires)
*)

Lemma seq_trans : forall p q r e1 e2,
  [p | e1] =>* [q | e2] -> [p ; r | e1] =>* [q ; r | e2].
assert (H : forall s1 s2, s1 =>* s2 -> forall p q r e1 e2, 
  s1 = [ p | e1 ] -> s2 = [ q | e2 ] -> [ p ; r | e1 ] =>* [ q ; r | e2 ]).
Proof.
intros s1 s2 H.
induction H.
- intros.
  rewrite H in H0.
  injection H0.
  intros.
  rewrite H1.
  rewrite H2.
  apply star_refl.
- intros.
  inversion H.
  + rewrite H1 in H5.
    injection H5.
    intros.
    rewrite <-H8.
    rewrite <-H7.
    apply star_R with [skip;r|s'].
    apply ss_seq_seq.
    apply ss_ass with x.
    apply H3.
    apply H4.
    apply IHstar.
    symmetry in H6.
    apply H6.
    apply H2.
  + rewrite H1 in H3.
    injection H3.
    intros.
    symmetry in H6.
    rewrite H6.
    symmetry in H5.
    rewrite H5.
    symmetry in H4.
    apply star_R with [c0;r|s].
    apply ss_seq_seq.
    apply ss_seq_skip.
    apply IHstar.
    apply H4.
    apply H2.
  + rewrite H1 in H4.
    injection H4.
    intros.
    symmetry in H7.
    rewrite H7.
    symmetry in H6.
    rewrite H6.
    apply star_R with [(c';d);r|s'].
    apply ss_seq_seq.
    apply ss_seq_seq.
    apply H3.
    apply IHstar.
    symmetry.
    apply H5.
    apply H2.
  + rewrite H1 in H4.
    injection H4.
    intros.
    symmetry in H7.
    rewrite H7.
    apply star_R with [c0;r|s].
    symmetry in H6.
    rewrite H6.
    apply ss_seq_seq.
    apply ss_ifte_true.
    apply H3.
    apply IHstar.
    symmetry.
    apply H5.
    apply H2.
  + rewrite H1 in H4.
    injection H4.
    intros.
    symmetry in H7.
    rewrite H7.
    symmetry in H6.
    rewrite H6.
    apply star_R with [d;r|s].
    apply ss_seq_seq.
    apply ss_ifte_false.
    apply H3.
    apply IHstar.
    symmetry; apply H5.
    apply H2.
  + rewrite H1 in H3.
    injection H3; intros.
    subst.
    apply star_R with [ifte b0 (c0; while b0 c0) skip ; r|e1]; try trivial.
    apply ss_seq_seq.
    apply ss_while.
    apply IHstar.
    reflexivity.
    reflexivity.
- intros.
  apply H with [p|e1] [q|e2].
  apply H0.
  repeat reflexivity.
  reflexivity.
Qed.


Lemma skip_exe_neutre : forall p e1 e2, execute e1 p e2 <-> execute e1 (p;skip) e2.
Proof.
intros.
split.
intros.
apply execute_seq with e2.
apply H.
apply execute_skip.
intros.
inversion H.
inversion H5.
symmetry in H8; rewrite H8.
apply H3.
Qed.


(* Vous pouvez maintenant montrer que *)
Lemma execute_sse : forall p e1 e2,
  execute e1 p e2 -> [p | e1] =>* [skip | e2].
Proof.
intros.
induction H.
apply star_refl.
apply star_trans with [skip;c2|o'].
apply seq_trans.
apply IHexecute1.
apply star_R with [c2|o'].
apply ss_seq_skip.
apply IHexecute2.
apply star_R with [c1|o].
apply ss_ifte_true.
apply H.
apply IHexecute.
apply star_R with [c2|o].
apply ss_ifte_false.
apply H.
apply IHexecute.
apply star_R with [ifte b (c; while b c) skip|o].
apply ss_while.
apply star_R with [skip|o].
apply ss_ifte_false.
apply H.
apply star_refl.
apply star_R with [ifte b (c; while b c) skip|o].
apply ss_while.
apply star_R with [c;while b c|o].
apply ss_ifte_true.
apply H.
apply star_trans with [skip;while b c|o'].
apply seq_trans.
apply IHexecute1.
apply star_R with [while b c|o'].
apply ss_seq_skip.
apply IHexecute2.
apply star_R with [skip|o'].
apply ss_ass with n.
apply H.
apply H0.
apply star_refl.
Qed.


(* DEUXIÈME PARTIE : preuve de l'implication ss => execute *)
(* TOUTES LES PREUVES DANS CETTE PARTIE DOIVENT ÊTRE COMPLÉTÉES.
  N'HÉSITEZ PAS À SUIVRE LES INDICATIONS DONNÉES, ET ÉVENTUELLEMENT
  À FAIRE LA PREUVE SUR PAPIER POUR NE PAS PERDRE LE FIL *)


(* L'objetif est de montrer le lemme ss_execute, qui dit que si
  [p | e1] =>* [skip | e2], alors execute e1 p e2 *)
(* Pour gérer l'induction sur la longueur de la réduction =>*,
  on commence par prouver le lemme ss_execute_aux, qui traite le cas d'une
  seule réduction => :
  si [p1 | e1] => [p2 | e2], alors pour tout e3,
  execute e2 p2 e3 implique execute e2 p1 e3 *)

(* Prouvons tout d'abord les quatre lemmes suivants afin de se faciliter
  la tâche lors de la preuve de ss_execute_aux *)

(* La preuve semble ici très simple : execute e2 skip e3
  ne peut provenir que de la règle execute_skip, et on doit
  alors avoir e2 = e3. *)
(* La tactique inversion, appliquée sur l'hypothèse
  execute e2 skip e3, est en fait une version améliorée du destruct.
  Elle génère un cas pour chaque constructeur (règle) de execute,
  conserve les égalités pour les arguments de execute, puis élimine
  si possible les cas menant à une contradiction *)
(* Ici, inversion va générer un cas pour chaque règle de execute,
  mais seule la règle execute_skip est conservée car les autres
  mènent à une contradiction.*)

(* N'oubliez pas d'aider Coq lorsque sa tactique apply H ne permet
  pas de deviner tous les arguments de H :
- apply H with t : lorsque H n'a qu'un seul argument non inféré
  par apply : on lui dit alors de prendre le terme t.
- apply H with (x1 := t1) (x2 := t2) ... (xn := tn), lorsque H
  possède n arguments x1 x2 ... xn (les désigner par le nom qu'ils portent 
  dans le "forall ..." du type de H) qu'apply n'a pas pu inférer.
*)

Lemma ss_execute_aux_ass : forall e1 e2 e3 i a x,
  aeval e1 a x -> update e1 i x e2 ->
  execute e2 skip e3 -> execute e1 (i <- a) e3.
Proof.
  intros.
  inversion H1.
  apply execute_assign with x.
  apply H.
  symmetry in H4.
  rewrite H4.
  apply H0.
Qed.


(* rien à signaler *)
Lemma ss_execute_aux_seq_skip : forall e1 e2 c, 
  execute e1 c e2 -> execute e1 (skip; c) e2.
Proof.
  intros.
  apply execute_seq with e1.
  apply execute_skip.
  apply H.
Qed.


(* Là encore, inversion permettra de déduire toutes les informations
  utiles de execute e2 (c'; d) e2. *)
Lemma ss_execute_aux_seq_seq : forall e1 e2 e3 c c' d,
  (forall e, execute e2 c' e -> execute e1 c e) ->
  execute e2 (c'; d) e3 -> execute e1 (c; d) e3.
Proof.
  intros.
  inversion H0.
  apply execute_seq with o'.
  apply H.
  apply H4.
  apply H6.
Qed.

(* Le cas du while est un tout petit peu plus délicat que les autres,
  car la sémantique ss n'utilise qu'un constructeur pour while, tandis que
  execute en a deux0 *)
(* une bonne utilisation de inversion doit ici générer deux cas, reflétant
  deux constructeurs de execute, l'un dans le cas où b est vrai, l'autre
  lorsqu'il est faux. *)
Lemma ss_execute_aux_while : forall e1 e2 b c,
  execute e1 (ifte b (c; while b c) skip) e2 -> execute e1 (while b c) e2.
Proof.
  intros.
  inversion H.
  inversion H6.
  Print execute.
  apply execute_while_true with o'0.
  apply H5.
  apply H10.
  apply H12.
  inversion H6.
  rewrite<- H9.
  apply execute_while_false.
  apply H5.
Qed.


(* On peut maintenant passer à la preuve de ss_execute_aux. *)
(* Vous pouvez essayer de continuer la preuve commençant
  directement par une induction : *)
(*
Lemma ss_execute_aux : forall p1 p2 e1 e2,
  [p1 | e1] => [p2 | e2] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3.
Proof.
intros until 1. induction H.
intros.
*)
(* On remarque que induction semble perdre des informations
  très utiles en cours de route : des corrélations entre certains
  termes disparaissent lorsque les termes sont remplacés par des
  variables génériques sans corrélations particulières. *)
(* Afin de conserver ces corrélations (comme inversion le fait là où
  destruct perd ces informations), on propose de réécrire le lemme
  à prouver à l'aide d'une formulation H qui introduit explicitement
  les égalités que l'on souhaite conserver lors du passage à l'induction. *)

Lemma ss_execute_aux : forall p1 p2 e1 e2,
  [p1 | e1] => [p2 | e2] ->
  forall e3, execute e2 p2 e3 -> execute e1 p1 e3.
Proof.

assert (H: forall s1 s2, s1=>s2 -> forall p1 p2 e1 e2, s1=[p1|e1] ->
s2=[p2|e2]-> forall e3, execute e2 p2 e3 ->execute e1 p1 e3).

+
  intros until 1.
  induction H.
  *
    intros.
    inversion H1.
    inversion H2.
    apply ss_execute_aux_ass with (x:=x) (e2:=s').
    rewrite<- H6.
    apply H.
    rewrite<- H6.
    apply H0.
    rewrite H7,H8.
    apply H3.
  *
    intros.
    inversion H.
    inversion H0.
    apply ss_execute_aux_seq_skip.
    rewrite <-H4,H6.
    apply H1.
  *
    intros.
    inversion H0.
    inversion H1.
    apply ss_execute_aux_seq_seq with (e2:=e2) (c':=c').
    apply IHss.
    rewrite H5.
    reflexivity.
    rewrite H7.
    reflexivity.
    rewrite H6.
    apply H2.
  *
    intros.
    inversion H0.
    inversion H1.
    apply execute_ifte_t.
    rewrite<- H5.
    apply H.
    rewrite<- H5.
    rewrite H7.
    apply H2.
  *    
    intros.
    inversion H0.
    inversion H1.
    apply execute_ifte_f.
    rewrite<- H5.
    apply H.
    rewrite<- H5.
    rewrite H7.
    apply H2.
  *
    intros.
    inversion H.
    inversion H0.
    apply ss_execute_aux_while.
    rewrite H4 in H6.
    rewrite H6,H5.
    apply H1.
    
+
  intros.
  apply H with (s1:=[p1|e1])(s2:=[p2|e2])(p2:=p2)(e2:=e2).
  apply H0.
  reflexivity.
  reflexivity.
  apply H1.
Qed.


(* On termine enfin la preuve que ss implique execute *)
(* Pour rappel, la clôture réflexive transitive de =>, notée =>*,
  a été définie plus haut, dans la section Star de la partie 1. *)
(* Attention à l'utilisation brutale de l'induction, qui risque de faire
  disparaître des corrélations essentielles ! *)
(* Pour cela, on pourra généraliser l'énoncé avec un assert H qui introduit
  explicitement les égalités à conserver. N'hésitez pas à vous inspirer de
  ce qui a été fait pour ss_execute_aux. *)

Lemma sse_execute : forall p e1 e2,
  [ p | e1 ] =>*  [ skip | e2 ] -> execute e1 p e2.
Proof.
  assert (H:forall s1 s2:state,
             s1=>* s2 ->
             forall p e1 e2,
               s1 = [p|e1] -> s2 = [skip|e2] -> execute e1 p e2).
  +
  intros until 1.
  induction H.
    *
      intros.
      rewrite H in H0.
      inversion H0.
      apply execute_skip.
    *
      intros.
      destruct b.
      apply ss_execute_aux with (p2:=p0)(e2:=e).
      rewrite<- H1.
      apply H.
      apply IHstar.
      reflexivity.
      apply H2.
  +
    intros.
    apply H with (s1:=[p|e1])(s2:=[skip|e2]).
    apply H0.
    reflexivity.
    reflexivity.
Qed.



(* TROISIÈME PARTIE : déterminisme de la sémantique de IMP *)
(* TOUTES LES PREUVES DANS CETTE PARTIE DOIVENT ÊTRE COMPLÉTÉES.
  N'HÉSITEZ PAS À SUIVRE LES INDICATIONS DONNÉES, ET ÉVENTUELLEMENT
  À FAIRE LA PREUVE SUR PAPIER POUR NE PAS PERDRE LE FIL *)

(* Dans cette partie à nouveau, inversion joue un rôle clé pour
  extraire toutes les informations d'un type inductif dépendant *)
(* Astuce : si les hypothèses contiennent H1 : a = b et H2 : a <> b,
  alors le but doit pouvoir se prouver automatiquement puisqu'on a
  une contradiction. Pour cela, étant donné que (H2 H1) a le type False,
  on pourra simplement invoquer destruct (H2 H1). *)
(* Si on a une contradiction du type H : 0 = S n, ou toute autre égalité
  où les constructeurs ne peuvent pas correspondre, on pourra conclure
  avec discriminate H *)
(* La tactique replace t with u remplace dans le but courant le terme t
  par le terme u. L'égalité t = u sera alors prouvée dans un but ultérieur.
  replace t with u in H permet de faire la même chose dans l'hypothèse H *)

Lemma get_det : forall s a v1, get s a v1 -> forall v2, get s a v2 -> v2 = v1.
Proof.
  intros.
  induction H.
  inversion H0.
  reflexivity.
  destruct H6.
  reflexivity.
  apply IHget.
  inversion H0.
  symmetry in H2.
  destruct (H1 H2).
  apply H7.
Qed.


Lemma update_det : forall s a v s1, update s a v s1 -> forall s2, update s a v s2 -> s2 = s1.
Proof.
  intros until 1.
  induction H.
  intros.
  inversion H.
  reflexivity.
  destruct H7.
  reflexivity.

  intros.
  inversion H1.
  symmetry in H2.
  destruct (H0 H2).
  assert (HH:l'0 = l').
  apply IHupdate.
  apply H8.
  rewrite HH.
  reflexivity.
Qed.


Lemma succ_inj : forall m n, S m = S n -> m = n.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Lemma aeval_det : forall a s n1, aeval s a n1 -> forall n2, aeval s a n2 -> n2 = n1.
Proof.
  intros a s.
  induction a.
  intros.
  inversion H.
  inversion H0.
  reflexivity.

  intros.
  apply get_det with(a:=a)(s:=s).
  inversion H.
  apply H3.
  inversion H0.
  apply H3.

  intros.
  inversion H.
  inversion H0.
  assert (HH:n0=n).
  apply IHa.
  apply H3.
  apply H7.
  rewrite HH.
  reflexivity.

  intros.
  inversion H.
  inversion H0.
  assert (HH:S n2 = S n1).
  apply IHa.
  apply H3.
  apply H7.
  apply succ_inj.
  apply HH.
  admit.
  admit.  
Admitted.


Lemma npp :forall n m, n<=m -> m<n -> False.
  admit.
Admitted.
Lemma beval_det : forall a s b1, beval s a b1 -> forall b2, beval s a b2 -> b2 = b1.
Proof.
  intros a s.
  induction a.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
  subst.
  assert(HH:n0=n).
  apply aeval_det with (a:=a)(s:=s).
  apply H3.
  apply H10.

  assert(HHH:m=m0).
  apply aeval_det with(a:=a0)(s:=s).
  apply H12.
  apply H5.
  rewrite<- HHH,HH in H14.
  assert(False).
  apply npp with (n:=m)(m:=n).
  apply H14.
  apply H7.
  destruct H1.

  inversion H0.
  subst.
  assert(HH:n0=n).
  apply aeval_det with (a:=a)(s:=s).
  apply H3.
  apply H10.

  assert(HHH:m=m0).
  apply aeval_det with(a:=a0)(s:=s).
  apply H12.
  apply H5.
  rewrite<- HHH,HH in H14.
  assert(False).
  apply npp with (n:=m)(m:=n).
  apply H7.
  apply H14.
  destruct H1.


  reflexivity.

  intros.
  inversion H.
  inversion H0.
  reflexivity.
  assert(HH:n0=n).
  apply aeval_det with(a:=a)(s:=s).
  apply H3.
  apply H10.
  assert(HHH:m0=m).
  apply aeval_det with (a:=a0)(s:=s).
  apply H5.
  apply H12.
  rewrite HH,HHH in H14.
  destruct (H7 H14).
  inversion H0.
  assert(HH:n0=n).
  apply aeval_det with(a:=a)(s:=s).
  apply H3.
  apply H10.
  assert(HHH:m0=m).
  apply aeval_det with (a:=a0)(s:=s).
  apply H5.
  apply H12.
  rewrite HH,HHH in H14.
  destruct (H14 H7).
  
  reflexivity.
  
Qed.

Lemma bs_det : forall s p s1, execute s p s1 -> forall s2, execute s p s2 -> s2 = s1.
Proof.
...
Qed.



