---
title: "On Well-Founded Induction"
author: Callan McGill
date: "Nov 23, 2025"
tags: [Agda, Induction, Well-Founded Relations]
description: Explorations into Well-Founded Relations in constructive mathematics
quote: Every reading of a classic is in fact a rereading.
quoteAuthor: Italo Calvino
agdaDevelopment: "Induction"
publish: true

---

One of the first things dependently typed progrmaming teaches is that thinking of induction as primarily about the natural numbers is an impoverished view. Instead, a system like `agda` encourages to think firstly that one can found mathematics on inductive structures as the raw prmitives, and secondly that  _every_ such structure -- the inductive collection of binary trees, for example -- comes with some means of proving properties about it. For instance, binary trees in `agda` might be defined as follows:

```Agda
data BinTree a where
  Leaf : a → BinTree a
  Bin : BinTree a → BinTree a → BinTree a
```

and these come with the following induction principle:
```Agda
bin-tree-induction : ∀ {a : Type} (P : (BinTree a) → Type) →
  ((l : a) → P (Leaf l)) →
  (∀ {lt rt : BinTree a} → (P[lt] : P lt) → (P[rt] : P rt) → P (Bin lt rt)) →
  (∀ (bin-tree : BinTree a) → P bin-tree)
bin-tree-induction P leaf-pf bin-pf (Leaf l) = leaf-pf l
bin-tree-induction P leaf-pf bin-pf (Bin ltree rtree) =
  bin-pf
    (bin-tree-induction P leaf-pf bin-pf ltree)
    (bin-tree-induction P leaf-pf bin-pf rtree)
```

This characterization focuses on an inductive set as a certain solution to a universal problem (an initial object in the category of `F-algebras`) and gives us an "immediate predecessor" method of proof. This does, however, come with a large downside: there are many natural results which we wish to prove by a more flexible method of induction. We may wish to do induction on a natural number via its set of prime factors, or prove something about an array by splitting it half.

One way to think about such problems is that we need not stick with the the given "immediate successor" relation, but instead we can develop other relations on a collection, which are appropriate for doing induction on. This is the theory of well-founded relations.


Classically there are various equivalent ways to think about the theory of well-founded relations, but as we wish to develop these ideas in `agda`, we should note that
these classically equivalent definitions split apart. Classically, we
have the following theorem giving us three different views on what a well-founded relation is:

**Theorem (Well-founded Relations)**:
$\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}} \def\x{\mathrm{x}}  \def\y{\mathrm{y}} $
$\def\x'{\mathrm{x'}}  \def\y'{\mathrm{y'}} \def\P{\mathrm{P}} $
Suppose $\X$ is a set with binary relation $\R$ on it, meaning $ \R \subset \X \times \X$. We write $\R$ infix --
  $ \x \R \y$ -- to mean that $(\x, \y) \in R$.

The following are equivalent:
- Every non-empty subset $\U \subset \X$ has an $\R$-least element i.e.
$$
  \exists \mathrm{u'} \in \U \ldot \forall u \in U \ldot u' \R u
$$
- Suppose $U$ is a subset of $X$. The following induction principle holds:
$$
  (\forall \x \x' \in X \ldot
$$
