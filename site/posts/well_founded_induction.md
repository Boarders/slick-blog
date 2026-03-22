---
title: "On Well-Founded Induction"
author: Callan McGill
date: "Nov 23, 2025"
tags: [Agda, Induction, Well-Founded Relations]
description: Explorations into Well-Founded Relations in constructive mathematics
quote: Every reading of a classic is in fact a rereading.
quoteAuthor: Italo Calvino
agdaDevelopment: "Inductive Relations"
publish: true

---

<div style="display:none">\(\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}} \def\x{\mathrm{x}}  \def\y{\mathrm{y}} \def\x'{\mathrm{x'}}  \def\y'{\mathrm{y'}} \def\P{\mathrm{P}}\)</div>


One of the first things dependently typed programming teaches is that thinking of induction as primarily about the natural numbers is an impoverished view. Instead, a system like `agda` encourages one firstly towards the idea that mathematics can be founded on inductive structures as the raw primitives, and secondly that  _every_ such structure comes with some given means of proving properties about it. For instance, binary trees in `agda` might be defined as follows:

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
The idea here is that if we can prove property about binary trees in the `Leaf` case, and in the `Bin` case (assuming it already holds for the child trees), then that property holds for all binary trees.

This characterization focuses on an inductive set as a certain solution to a universal problem (an initial object in the category of `F-algebras`) and gives us an "immediate predecessor" method of proof. This does, however, come with a large downside: there are many natural results which we wish to prove by a more flexible method of induction. For instance, we may wish to do _strong_ induction on the natural numbers, or induction via a numbers multi-set of prime factors, or to prove something about an array by dividing it in half.
n

One way to think about such problems is that we need not stick with the given "immpediate successor" relation, but instead we can develop other relations on a collection, which are appropriate for doing induction on. Moreover, if we have a theory of such inductive relations, we might be able then flexibly combine them together as components. This gives us the theory of well-founded relations.


Classically there are various equivalent ways to think about the theory of well-founded relations, but as we wish to develop these ideas in `agda`, we should note that
these classically equivalent definitions split apart. Classically, we have the following theorem giving us three different views on what a well-founded relation is:

**Theorem (Well-founded Relations)**:
Suppose $\X$ is a set with binary relation $\R$ on it, meaning $ \R \subset \X \times \X$. We write $\R$ infix --
  $ \x \R \y$ -- to mean that $(\x, \y) \in R$.

The following are equivalent:
- Every non-empty subset $\U \subset \X$ has an $\R$-least element i.e.
$$
  \exists \mathrm{u'} \in \U \ldot \forall u \in U \ldot u' \R u
$$
- Suppose $U$ is a subset of $X$. The following induction principle holds:
$$
  (\forall \x \in X, (\forall \x' \in X, \x' \R x, x' \in U) \Rightarrow \x \in U)
$$
