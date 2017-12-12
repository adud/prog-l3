(*******************************************************
  Récapitulatif des tactiques et commandes vues au TP1
********************************************************)

(* Je ne rentrerai pas dans les détails, donc ce court fichier (à la
   rigueur approximative) ne saurait se substituer au manuel de
   référence si vous souhaitez avoir des renseignements précis

     https://coq.inria.fr/distrib/current/refman/

   Ceci étant dit, n'hésitez pas à nous contacter pour toute
   question.

   Il doit exister moult cheatsheets qui traînent sur l'internet si
   vous souhaitez quelque chose de plus synthétique. Une rapide
   recherche me permet de trouver

     andrej.com/coq/cheatsheet.pdf

   qui me parait couvrir ce dont on aura besoin durant le semestre
   (ce qui n'est pas encore le cas pour ce fichier...).

   Le fichier est grosso modo coupé en trois:
   * quelques commandes de vernaculaire
   * quelques tactiques
   * quelques éléments sur le langage de tactique

   Les scripts ci-dessous ne servent qu'à illustrer les tactiques.
   Ne reproduisez pas ces horreurs SVP.
*)


(**************
  VERNACULAIRE
***************)

(* Déclarons d'abord quelques constantes qui habiterons notre contexte
   global pour illustrer plus facilement nos tactiques.
   Pour ce faire, on utilise la commande du vernaculaire
   "Variable [ident] : [type]."
*)

Variable n : nat.

(* Des propositions et des prédicats sur les entiers. *)
Variable A B C : Prop.
Variable P Q R : nat -> Prop.

(* Definition [ident] [(ident {: typ}] list] {: [typ]} := [term].
     Donne un nom à un objet mathématique.
     Il n'est pas nécessaire de donner le type si Coq peut l'inférer. *)

Definition fois_deux (k : nat) : nat := k * 2.
Definition plus_deux (k : nat) : nat := S (S k).

(* Check [term].
     Demande à Coq d'afficher le type d'un objet. *)

Check A.
Check fois_deux.
Check (plus_deux n).

(* Print [ident].
     Demande à Coq d'afficher la définition d'un objet (en plus de son type).
*)

Print A. (* Pas grand chose à afficher... *)
Print fois_deux.

(* Search [ident list].
    "Search bla." retourne toutes les définitions mentionnant bla dans leur
    type. Utile pour chercher des lemmes dans la bibliothèque standard.
    On peut spécifier plusieurs arguments pour affiner le résultat.
    On peut également spécifier des "termes à trous" pour chercher certains
    motifs.
*)

Search nat.
Search mult eq 0.
Search (_ -> _).
Search ((forall _, _ -> _) -> _).

(* Locate
    Permet de trouver quelles sont les définitions associées à une notation.
*)

Locate "_ + _".
Locate "_ <= _".
Locate "<=".
Locate "_ -> _".
Locate "exists".

(* "Inductive" permet de définir des types de données et des prédicats
    inductifs. Je préfère rappeler quelques exemples plutot que de donner
    une grammaire :) *)

Print nat.
Print list.

Inductive est_dans {A : Type} (x : A) : list A -> Prop :=
| est_la : forall l, est_dans x (cons x l)
| sera_la : forall l, est_dans x l -> forall y, est_dans x (cons y l).

(* Mais listons les définitions qu'un "Inductive bla" introduit dans le contexte:
   - un nouveau type/prédicat nommé bla
   - des constructeurs: un pour chaque cas
   - un principe d'induction

  Voyons sur le dernier exemple ce que ça donne. *)

Check est_dans. (* le prédicat *)
Check est_la. (* le premier constructeur *)
Check sera_la. (* le second constructeur *)
Check est_dans_ind. (* un principe d'induction automatiquement généré *)


(* "Fixpoint" permet de faire des définitions de fonction par induction
   structurelle. Coq vérifie grace à des critères syntaxiques que la
   récurrence est bien fondée. *)

Fixpoint molopo (n : nat) (m : nat) :=
  match n with
   0 => 1
 | S k => m * (S k) * molopo k (S m)
  end.

(* En réalité, cette commande n'est pas nécessaire; c'est du sucre
   syntaxique autour de "fix", qui peut très bien être utilisé dans une
   Definition *)
Print molopo.

(* Par ailleurs, les commandes suivantes vous montre que les principes
   d'inductions générés par "Inductive" sont vraiment des objets dérivés
   et non pas primitifs du noyau. *)
Print est_dans_ind.
Print nat_rect.





(***********
  TACTIQUES
************)



(* intros [ident list]

    Face à des quantifications universelles ou des implications,
    introduit les objets sur lesquels on quantifie/les hypothèses
    dans le contexte.
    
   Variantes:
   * "intro" introduit exactement un objet/une hypothèse
   * "intros" sans plus d'argument introduit un nombre maximal
     d'hypothèses; c'est équivalent à "repeat intro".
     Attention, cela ne déplie pas forcément les notations.
   * "intros u v z" introduit trois objets/hypothèses en les
     nommant "u" "v" et "z" dans le contexte. Cela échouera si
     une variable ne correspond à aucune hypothèse/objet à introduire.
   * on peut mettre des "?" et des "_" à la place des variables. "?"
     indique à Coq de choisir lui même le nom de variable, les
     wildcards "_" indiquent à Coq de supprimer l'hypothèse du contexte
     après l'avoir introduite si possible.
*)

Goal forall x, P x -> forall y, Q y -> ~ R x.
  intro.
  generalize x; clear x.
  intros.
  (* Remarquez que bien que ~ R x ≡ R x -> False, Coq n'a pas introduit R x,
     car il n'a déplié la notation... C'est assez traitre des fois. *)
  generalize x H y H0; clear x H y H0.
  intros u HP y HQ HR.
Abort.

(* apply [hyp]

     "apply H" tente d'unifier la conclusion de H (ie, la proposition
     la plus à droite des flèches et des quantifications universelles)
     et utilise l'hypothèse. Si elle a des prémisses, cela génère les
     buts correspondants qui seront à prouver.

  Variantes:
  * "apply H"
  * on peut aussi manipuler les hypothèses via apply; ainsi, "apply H in H'"
    va tenter d'unifier le type de H' avec une prémisse de H et d'instancier
    H avec H'. Si il manque des prémisses pour obtenir la conclusion de H',
    des sous-buts seront générés.
  * on peut chaîner les apply en séparant les hypothèses par des virgules:
    "apply H1, H2, H3." équivaut à apply H1; (apply H2; apply H3)
  * "exact H" si l'hypothèse correspond *exactement* au but à prouver
*)

Goal (forall x, B -> A -> P x) -> B -> forall y, P y.
  intros.
  apply H.
Abort.

Goal (forall x, Q x -> A -> P x) -> forall y z, Q z -> P y.
  intros.
  apply H in H0.
Abort.

(* rewrite [hyp]

     Quand la conclusion de H est de type "t = u", rewrite H remplace
     les occurences de t par u dans le but

   Remarques:
   * "rewrite <-H" permet de substituer u par t (comme si l'égalité
     était renversée)
   * "rewrite H in H'" effectuera la substitution dans H' au lieu
     du but
   * en pratique, si rewrite est utilisée avec une hypothèse du type
     "forall x, t(x) = u(x)", rewrite va d'abord chercher à unifier
     t(x) avec un sous-terme du but et réécrire toutes les occurences
     de ce sous-terme en particulier. Il est possible t(x) soit unifiable
     à un autre sous-terme, auquel cas il en sera pas réécrit tout de suite.

     TL;DR, "repeat (rewrite H)" n'est pas équivalent à "rewrite H" quand
     le type de H est un peu compliqué
*)

Goal forall x y z, x = y -> S x = S z -> S z = S y.
  intros.
  rewrite <-H.
  rewrite H0.
  rewrite <-H0.
  rewrite H in H0.
  reflexivity.
Qed.

(* simpl

     Permet à Coq de réduire des expression trivialement calculables.
     Il est courant de l'utiliser lors de preuves par induction, typiquement
     pour déplier la définition de u_{n+1} en terme de u_n.
*)

Goal 2 + 2 = 4.
  simpl.
  reflexivity.
Qed.

Goal S n + n = S (2 * n).
  simpl.
Abort.

(* reflexivity, symmetry, transitivity z

     Tactiques spécifiques au traitement de l'égalité.
     * reflexivity clos les buts "x = x" (et équivaut à apply eq_refl)
     * symmetry transforme le but "x = y" en "y = x"
     * transitivity z clos "x = y" pour demander de prouver "x = z" et
       "z = y"

     Si vous essayez avec d'autres relations, Coq vous criera dessus
     en disant que vous avez pas déclaré de Setoids homologués ou un truc
     du genre.
*)

Goal forall x y z : nat, x = y -> z = y -> x = z.
  intros.
  transitivity y.
  + assumption.
  + symmetry.
    symmetry in H0.
    symmetry.
    exact H0.
Qed.

(* assumption

   Résoud le but si il correspond à une hypothèse.
*)

Goal A -> B -> A.
  intros; assumption.
Qed.

(* left, right

    En présence d'un but du type "A \/ B", génère un but "A" ou 
    un but "B" selon la direction choisie
*)

Goal A -> A \/ B.  
  left.
  assumption.
Qed.

(* split

    Lorsqu'une conjonction est en but, génère un but par branche
    de la conjonction. *)

Goal A -> B -> A /\ B.
  intros; split; assumption.
Qed.

(* unfold [ident]

    Déplie une définition dans le but.
    "unfold [ident] in *" la déplie partout dans le contexte en plus du but.
*)

Definition super := True /\ n = 2 + 8.

Goal super -> n + 0 = 10.
  unfold super.
  fold super.
  intros.
  unfold super in *.
  unfold plus.
  destruct H.
  rewrite H0.
  reflexivity.
Qed.


(* exists

    Face à un but "exists x, P x", "exists t" permet de passer au
    but "P t" en donnant "t" comme témoin de l'existentielle.
*)

Goal exists x, Q x.
  exists (S n).
Abort.

Goal A -> ~ A -> B.
  intros.
  apply H0 in H.
  destruct H.
Qed.

(* destruct [term]

     "destruct H" effectue une analyse de cas sur H
     et introduit les arguments des constructeurs
     correspondants dans le contexte.

     tl;dr analyse de cas généralisée
*)

Goal A /\ B -> A.
  intros.
  destruct H.
Abort.

Goal A \/ B -> A.
  intros H.
  destruct H.
  assumption.
Abort.

Goal forall t : list nat, t = nil \/ t <> nil.
   intros.
   destruct t.
Abort.

Goal (exists x, P x) -> exists z, P z /\ P z.
  intros.
  destruct H.
Abort.

Goal False -> A.
  intros.
  destruct H.
Abort.

(* induction [term]

     "induction n" amorce un raisonnement par induction pour
     prouver le but.

     Notez qu'il est souvent nécessaire de renforcer l'hypothèse
     d'induction; cela se fait en se donnant un but plus général
     à prouver (via cut ou assert).
*)

Goal P 0 -> forall k, P k.
  intros.
  induction k.
  apply H.
Abort.

Goal forall P (t : list nat), P nil -> P t.
  intros P0 t.
  induction t.
  auto.
Abort.

(* assert [term]

     "assert P" ouvre un but pour prouver la proposition P, qui
     aura ensuite une hypothèse associée dans le contexte.

     "cut P" remplit essentiellement le même rôle, en inversant
     l'ordre des buts et en introduisant un peu de bureaucratie...
*)

Goal A -> (A \/ B) /\ (A \/ B) /\ (A \/ B).
  intro.
  assert (A \/ B).
  + left; apply H.
  + clear H0.
    cut (A \/ B).
    - intros; repeat split; apply H0.
    - left; assumption.
Qed.

(* subst

   Simplifie et élimine des égalités triviales
   du contexte du type "variable = terme" autant que possible.

   Moralement équivalent à une suite de "rewrite [<-]H in *" et
   de "clear H" pour H bien choisis.

*)

Goal forall k z, n = S k -> k = S (S z) -> n = z.
  intros.
  subst.
Abort.

Goal forall k, k = S n -> n = k -> False.
  intros.
  subst.
Abort.

(* inversion [hyp]

     Analyse de cas qui généralise destruct. Utile sur les prédicats
     définis inductivement dont les constructeurs font apparaitre
     des dépendences non triviales dans leur construction
     (par exemple, le_S).

     Va générer des égalités dans ce dernier cas; souvent utile de
     faire un subst juste après.
*)

Print le.

Goal forall m k z, n <= m -> k <= z -> m < k -> True.
  intros.
  inversion H.
  + (* cas le_n *) constructor.
  + (* cas le_S *) inversion H2.
                   - constructor.
                   - subst.
Abort.

(* injection [term]

   Prend en argument en égalité et dérive toutes les égalités qui
   découlent de l'injectivité des types inductifs.

   (transforme le but un petit peu comme cut; il faut souvent faire
    intros immédiatement après)
*)

Goal forall m, S (S n) = S m -> S n = m.
  intros.
  assert (H' := f_equal S H).
  injection H'.
  auto.
Qed.


(* auto

   Essaie de résoudre automatiquement le but courant en faisant une
   recherche élémentaire. Moralement, auto essaie de faire des apply,
   split, destruct et intros avec ce qu'il y a *dans le contexte* (on ne verra
   pas comment il rendre plus flexible ici).

   Si auto ne résoud pas le but courant, il ne fait rien en apparence.

   eauto est la même chose en plus puissant, dans le sens où il essaie de deviner
   des variables existentielles.
*)

Goal P 0 -> (forall k, P k -> P (S k)) -> P 3.
  auto.
Qed.

Goal P 0 -> (P 0 -> P 1) -> P 0 /\ P 1.
  auto.
Qed.

Goal A \/ B ->  (A -> B)  -> B.
  auto.
  eauto 15.
  intros [|]; auto.
Qed.

Goal P 0 -> exists x, P x.
  auto.
  eauto.
Qed.

Goal P 0 -> (forall k, P k -> P (S k)) -> P 40.
  auto.
  (* La recherche d'auto s'arrête avant de faire 40
     applications de l'hypothèse inductive... mais on peut
     le forcer à chercher plus. *)
  auto 70.
Qed.

(************************
 COMPOSITION DE TACTIQUES
*************************)


(* Éléments de Ltac si vous vous posez des questions sur les
   scripts ci-dessus

   tac1; tac2.

     Composition des tactiques: applique tac1, puis applique tac2
     à tous les sous-buts générés par tac1.

     Notez que la composition de tactiques n'est PAS associative.
     tac1;tac2;tac3 se lit (tac1;tac2);tac3

  tac; [tac1 | ... | tacn]

    Applique tac, puis taci au i-ème sous-but (échoue si n est 
    différent du nombre de sous-buts générés).

  fail

     Tactique qui échoue tout le temps

  progress tac

     Applique tac; si le but ne change pas, échoue

  try tac

     Si tac échoue, rattrape l'exception et ne fait rien

  repeat tac ≡ try (progress tac; repeat tac)
*)