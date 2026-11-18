# Equivalence of semi-simplicial and semi-cubical sets in fibred and indexed form in Agda

This repository contained an implementation of the construction of augmented
semi-simplicial sets and semi-cubical sets as a family of families of sets 
(called "indexed") as well as a proof of the equivalence of this construction
with the usual definition (contrastingly called "fibred").

The construction is directly based on a construction by Hugo Herbelin and
Ramkumar Ramachandra, presented in the following paper :\
[A Parametricity-Based Formalization of Semi-Simplicial and Semi-Cubical Sets](https://doi.org/10.1017/S096012952500009X)
([arXiv](https://arxiv.org/abs/2401.))
On the contrary of the Rocq proof associated to this paper, Agda mutual blocks
allow us to mirror more accurately the informal construction with a single large
mutual recursion.

The proof of equivalence between the two forms is original work (to the best of
our knowledge) developed as internship in Spring 2026.

This work was verified with Agda 2.8.0 and should work with Agda 2.9.0 as well.

## Postulates :

We postulate univalence and functional extensionality, additionally we add
the three following rewriting rules : `a + 0 = a` , `a + suc b = suc (a + b)` and
`recover-nat-eq x x p = refl` where `recover-nat-eq` is a function from equalities
of natural number in Prop to the usual propositional equality in Type.

Univalence is used to simplify the definition of bisimulation between two semi-cubical
sets and proving said bisimulation.

The rewrite rules allow us to compute irrelevant induction steps on inequalities and 
simplifying the use of a zipper-like structure to define presheaves.
