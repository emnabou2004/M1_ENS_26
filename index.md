---
layout: default
---

# Bienvenue

Ce site contient les informations concernant le Cours Avancé [Formalisation Mathématique](https://www.math.ens.psl.eu/formations/ca-formalisation-mathematique/) pour le M1 du Département de mathématiques et applications de l'ENS-Paris, qui a lieu au deuxième semestre 2025--26.

Le cours est assuré par [Filippo A. E. Nuccio](https://perso.univ-st-etienne.fr/nf51454h/). Le matériel est en anglais, le cours aura (probablement) lieu en français.

Chaque cours vient avec un fichier `.md` (exporté en `.pdf` aussi) que vous trouvez plus bas et qui contient le matériel discuté, ainsi qu'avec un fichier `.lean` à utiliser pendant le cours. Les solutions sont rajoutées le lendemain du cours, en général.

# Agenda
Les cours ont lieu de 13h30 à 16h30  selon le calendrier suivant:

| Date      | Cours         | Fichiers annexes | Notes
|-----------|---------------|---------------|---------------
| 3 février | Tactiques et Types | [Fichier Lean](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/1_Tactics%26Types.lean) et [MarkDown](https://github.com/faenuccio-teaching/M1_ENS_26/blob/master/M1ENS26/1_Tactics%26Types_lecture.md)|
| 5 février | Types (2) | |
| 10 février | Algèbre | |
| 17 février | Topologie | |
| 19 février | Analyse | |
| 10 mars | *à décider* | |
| 12 mars | **examen** | | Examen écrit de 2h
| 24 mars | séminaire étudiants | |
| 31 mars | séminaire étudiants | |
| 7 avril | séminaire étudiants | |
| 14 avril | séminaire étudiants | |


# Références 

Il n'y a pas (encore) beaucoup de livres qui parlent de `Lean`, mais le très beau
* [Mathematical Components](https://math-comp.github.io/mcb/), par A. Mahboubi et E. Tassi, bien que conçu pour l'assistant de preuve [`Rocq`](https://rocq-prover.org/), est une excellente présentation à ce qu'est la formalisation mathématique en général.

Pour tout ce qui concerne la "théorie des types" qu'on utilise, une jolie introduction est dans le premier chapitre "Type theory" de
* [Homotopy Type Theory (a.k.a. "HoTT book")](https://homotopytypetheory.org/book/)

Une source plus complète, très bien écrite et fort agréable à lire est
* [Lectures on the Curry–Howard Isomorphism](https://www.sciencedirect.com/bookseries/studies-in-logic-and-the-foundations-of-mathematics/vol/149/suppl/C), par M. H. Sørensen et P. Urzyczyn.

 Les deux références sont
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/), par J. Avigad, L. de Moura, S. Kong et S. Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), par J. Avigad et P. Massot
contiennent aussi beaucoup de matériel pertinent pour notre cours.

# Prérequis Lean et GitHub

Avant le début du cours (le mardi 3 février 2026), assurez-vous de:
* avoir accès à une connexion internet lorsque à l'ENS, idéalement via Eduroam;
* avoir configuré une installation `git`: si vous avez besoin d'aide, vous pouvez vous référer par exemple à la page <a href="https://www.imo.universite-paris-saclay.fr/~patrick.massot/misc/git.html">maintenue par Patrick Massot</a>;
* avoir créé un compte <a href="https://github.com">GitHub</a> pour pouvoir soumettre votre travail;
* installer Lean sur votre ordinateur, en suivant les [instructions officielles](https://lean-lang.org/install/): si vous rencontrez des difficultés, on en parlera lors du premier cours;
* d'avoir téléchargé (via `git clone`) le *repository* du cours à l'adresse https://github.com/faenuccio-teaching/ENS_26.git.

Autres informations et détails sont disponibles sur la [page officielle](https://faenuccio-teaching.github.io/ENS_26/) du cours.