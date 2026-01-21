# Bonak-agda

Bonak-agda is an re-implementation of the project [Bonak](https://github.com/artagnon/bonak) in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php)

The usage of Agda allow induction-induction, which make it possible to directly implement equations from the original research paper :\
[arXiv:2401.00512](https://arxiv.org/abs/2401.00512) (pre-print) or [10.1017/S096012952500009X](https://doi.org/10.1017/S096012952500009X) (published version)

Additionaly by definiting inequalities `p <= n` as a number `δ` and an irrelevant equality `δ + p ≡ n`, it is possible to do recursion on those
inequalities while avoiding transport hell.

## Goal

The goal of this implementation is to show that the obtained data structure is isomorphic to the presheaf of the νCategory as defined in the original paper.