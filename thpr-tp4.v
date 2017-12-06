                      (* Théorie de la programmation: TP #4 *)

(* L'objectif ce TP est de définir les sémantiques 
à petit et grand pas de IMP et de prouver un sens 
de leur équivalence. *)


(* NB: contrairement à la sémantique donnée en cours,
       nous n'avons pas de notation pour "calcul terminé" autre que skip.*)

Require Import List.
(* On utilise des listes de couples adresses*valeurs pour représenter 
les variables et stocker leurs valeurs. Une adresse représente une variable. *)


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


Intuitivement, get l a x est vraie quand la valeur de la variable a dans l'environnement l est x.

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
   | var : addr -> aexpr (* variable *)
   | succ : aexpr -> aexpr (* Successeur dans nat. *)
   | pred : aexpr -> aexpr. (* Prédecesseur dans nat. Attention, on veut que pred 0 = 0! *)

(* On a aussi des expressions booleens*)
Inductive bexpr : Type :=
   | blt : aexpr -> aexpr -> bexpr (* 'a < b' *)
   | bneq : aexpr -> aexpr -> bexpr. (* 'a != b' *)

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


(* Voilà, le seul programme qui nous intéressera. 
 * On cherchera à montrer dans la suite qu'il implémente l'addition
 *)
Definition add :=
     while (zero <<  #0)
       (0 <- pred #0; 
        1 <- succ #1).

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
|aeval_var : forall l x n, get l x n->  aeval l #x n
|aeval_succ : forall l x n, aeval l x n -> aeval l (succ x) (S n)
|aeval_pred_S : forall l x n,aeval l x (S n) -> aeval l (pred x) n
|aeval_pred_0 : forall l x,aeval l x 0 -> aeval l (pred x) 0.
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
|beval_true_blt: forall l x y m n, aeval l x n -> aeval l y m -> n < m -> beval l (x<<y) true
|beval_false_blt: forall l x y m n, aeval l x n -> aeval l y m -> m <= n -> beval l (x<<y) false
|beval_true_neq: forall l x y m n, aeval l x n -> aeval l y m -> n <> m -> beval l (x<<>>y) true
|beval_false_neq: forall l x y m n, aeval l x n -> aeval l y m -> n = m -> beval l (x<<>>y) false.

(* Sémantique grand pas pour les programmes. *)
(*
  Remplir les champs de la définition d'execute pour qu'elle corresponde
  à la sémantique à grands pas suivante

                       <ρ|c₁> ⇓ ρ''   <ρ''|c₂> ⇓ ρ'
  ──────────── skip   ──────────────────────────── seq
  <ρ|skip> ⇓ ρ               <ρ|c₁ ; c₂> ⇓ ρ'            


  <ρ|b> ⇓ true   <ρ|c₁> ⇓ ρ'             <ρ|b> ⇓ false   <ρ|c₂> ⇓ ρ'
  ─────────────────────────── ifte_t     ─────────────────────────── ifte_f
    <ρ|ifte b c₁ c₂> ⇓ ρ'                  <ρ|ifte b c₁ c₂> ⇓ ρ'                       


  <ρ|b> ⇓ true   <ρ|c> ⇓ ρ''  <ρ''|while b c> ⇓ ρ'
  ───────────────────────────────────────────────── while_true
                <ρ|while b c> ⇓ ρ'

  <ρ|b> ⇓ false
  ──────────────────── while_false
  <ρ|while b c> ⇓ ρ

  <ρ|a> ⇓ n   update ρ l n ρ'
  ──────────────────────────── assign
      <ρ|assign l a> ⇓ ρ'
*)

Inductive execute : env -> prg -> env -> Prop :=
|execute_skip : forall sigma, execute sigma skip sigma
|execute_seq : forall rho rho1 rho2 c1 c2, execute rho c1 rho2 -> execute rho2 c2 rho1 
-> execute rho (c1;c2) rho1
|execute_ifte_t : forall rho rho1 b c1 c2, beval rho b true -> execute rho c1 rho1 
-> execute rho (ifte b c1 c2) rho1
|execute_ifte_f : forall rho rho1 b c1 c2, beval rho b false -> execute rho c2 rho1 
-> execute rho (ifte b c1 c2) rho1
|execute_while_false : forall rho b c, beval rho b false -> execute rho (while b c) rho
|execute_while_true : forall rho rho' rho'' b c, beval rho b true -> execute rho c rho'' 
-> execute rho'' (while b c) rho' -> execute rho (while b c) rho'
|execute_assign : forall rho rho' a l n, aeval rho a n -> update rho l n rho'
-> execute rho (l <- a) rho'.

(* On va maintenant montrer que add est correcte *)
(* Astuces :
   - Appliquez les constructeurs adéquats pour résoudre les buts. 
   - Quand le système n'arrive pas à inférer l'argument d'une 
     application vous pouvez le lui préciser à l'aide de "with" et de 
     la syntaxe suivante : "apply execute_while_true with x"
   - Certains lemmes de la bibliothèque standard
     pourront vous etre utiles : sym_eq, plus_n_Sm
*)
Check sym_eq.
Check plus_n_Sm.
Print le.

SearchAbout (0 < S _).

Lemma correctness : forall x y,
    execute ((0,x)::(1,y)::nil) add ((0,0)::(1,x+y)::nil).
Proof.    
    induction x.
    intros.
    *unfold add.
    apply execute_while_false.
    apply beval_false_blt with 0 0.
    apply aeval_zero.
    apply aeval_var.
    apply get_head.
    apply le_n.
    *
    unfold add.
    intros.
    apply execute_while_true with ((0,x)::(1,S y)::nil).
    apply beval_true_blt with (S x) 0.
    apply aeval_zero.
    apply aeval_var.
    apply get_head.
    apply Lt.lt_0_Sn.
    apply execute_seq with ((0,x)::(1,y)::nil).
    apply execute_assign with x.
    apply aeval_pred_S.
    apply aeval_var.
    apply get_head.
    apply update_head.
    apply execute_assign with (S y).
    apply aeval_succ.
    apply aeval_var.
    apply get_tail.
    apply get_head.
    intros ?.
    inversion H.
    apply update_tail.
    apply update_head.
    intros ?.
    inversion H.
    simpl.
    rewrite plus_n_Sm.
    apply IHx.
Qed.

(* On maintenant s'intéresser à une sémantique à petits pas
   en montrer son équivalence avec la sémantique à grands pas
   donnée par execute *)
Reserved Notation "A => B" (at level 80). 

Definition state := (prg * env)%type.
Notation "[ π | p ]" := (π,p).

(* Définir la sémantique à petit pas de IMP. *)
Inductive ss : state -> state -> Prop :=
  | ss_ass : forall s s' i a x, aeval s a x -> update s i x s' -> [i <- a | s] => [skip | s']
  | ss_seq_skip : forall s c, [skip ; c | s] => [ c | s ] 
  | ss_seq_seq : (* TODO *)
  | ss_ifte_true : (* TODO *)
  | ss_ifte_false : (* TODO *)
  | ss_while : (* TODO *)
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
Qed.

Lemma skip_exe_neutre : forall p e1 e2, execute e1 p e2 <-> execute e1 (p;skip) e2.
Qed.

(* Vous pouvez maintenant montrer que *)
Lemma execute_sse : forall p e1 e2,
  execute e1 p e2 -> [p | e1] =>* [skip | e2].
Qed.



