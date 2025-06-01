# Résolution efficace, générique et validée expérimentalement de sudokus

Cette page donne les fichiers de mon TIPE (session 2024-2025). Notamment:

- Le [MCOT](Mcot.pdf) contient les références bibliographiques mentionnées ailleurs.

## Utilisation de mon programme OCaml

L'utilisation la plus simple est de lancer la commande:

    ocaml SUDOKU_MEL.ml

Le programme commence par un certain nombre de tests pour valider le bon fonctionnement de chaque méthode d'insertion:

- dénombrement de sudokus 4x4
- vérification de l'unicité de la solution à différents puzzles 9x9, 16x16, 25x25.

Pour éviter des temps de calculs trop longs, cette phase de validation met un "timeout" sur le nombre de "undos".

Ensuite, il mesure le temps d'exécution et le nombre de undos lors de la recherche d'une solution (pour chaque méthode d'insertion). Dans cette deuxième phase, il n'y a pas de "undos". Il faut faire "Ctrl-C" pour quitter.

## Pour une exécution plus rapide

Pour obtenir des résultats de mesures plus rapidement, j'effectue les commandes suivantes, pour exécuter le code machine de mon programme:

    ocamlopt -O3 SUDOKU_MEL.ml -o SUDOKU_MEL
    ./SUDOKU_MEL

