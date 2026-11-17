# Equivalence of semi-simplicial and semi-cubical sets in fibred and indexed form in Agda

This repository contained an implementation of the construction of augmented
semi-simplicial sets and semi-cubical sets as a family of families of sets as
well as a proof of the equivalence of this construction with the usual definition.

The construction is directly based on a construction by Hugo Herbelin and
Ramkumar Ramachandra, presented in the following paper :\
[A Parametricity-Based Formalization of Semi-Simplicial and Semi-Cubical Sets](https://doi.org/10.1017/S096012952500009X)
([arXiv](https://arxiv.org/abs/2401.))

## Postulates :

We postulate univalence and functional extensionality, additionally we add
the three following rewriting rules : `a + 0 = a` , `a + suc b = suc (a + b)` and
`recover-nat-eq x x p = refl` where `recover-nat-eq` is a function from equalities
of natural number in Prop to the usual propositional equality in Type.


