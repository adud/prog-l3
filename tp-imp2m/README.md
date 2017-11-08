
# Une traduction du langage IMP (alias TOY, ...) dans le noyau fonctionnel de OCaml

Cette maquette vise à montrer 

1. que les traîts impératifs ne sont là que pour fournir une facilité syntaxique au programmeur.
2. sur quel noyau fonctionnel (ML pour Meta Language) s'appuit la **Sémantique Dénotationnelle**.

## Installation

Soit de manière standard, depuis la racine du dépôt (polluant) :

    make -C src depend
    make -C src all

Soit de manière propre, avec l'aide de `ocamlbuild` et de `menhir` :

    make
    
## Utilisation

    # Display Ocaml equivalent of IMP code from file <IMP>
    ./imp2ml <IMP> 

    # Generate standalone OCaml file from <IMP>
    ./imp2ml -standalone <IMP>
    # Play!
    ocaml <ML> -h
    
## Améliorations

La version **1** est basique, et fournit essentiellement la structure.
On pourra ajouter :

* Gestion des priorités dans l'affichage des expressions arithmétiques et booléennes.
* Extension de la syntaxe des expressions.
* D'autres optimisations syntaxiques du code engendré.

Le squelette de ce code peut aussi être utilisé pour étudier la **Sémantique Axiomatique**.
