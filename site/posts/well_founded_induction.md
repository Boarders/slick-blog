---
title: "On Well-Founded Induction"
author: Callan McGill
date: "Mar 27, 2026"
tags: [Agda, Induction, Well-Founded Relations]
description: Explorations into Well-Founded Relations in constructive mathematics
quote: Every reading of a classic is in fact a rereading.
quoteAuthor: Italo Calvino
agdaDevelopment: "Inductive Relations"
publish: true

---

<div style="display:none">\(\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}} \def\x{\mathrm{x}}  \def\y{\mathrm{y}} \def\x'{\mathrm{x'}}  \def\y'{\mathrm{y'}} \def\P{\mathrm{P}}\)\def\i{\mathrm{i}}\def\j{\mathrm{j}}\def\x{\mathrm{x}}\def\y{\mathrm{y}}\def\m{\mathrm{m}}\def\n{\mathrm{n}}\def\u{\mathrm{u}}
</div>


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
Suppose $\X$ is a set with binary relation $\R$ on it, meaning $\R \subseteq \X \times \X$. We write $\R$ infix -- $\x \R \y$ -- to mean that $(\x, \y) \in R$.

The following are equivalent:

- [__Well-ordering principle__] For every non-empty subset $\U \subseteq \X$, there exists an $\R$-least element i.e.
$$
  \forall U\subseteq X, \exists \mathrm{m} \in \U, (\forall \u \in \U, \m \R \u)
$$
- [__R Inductive__] Suppose $U$ is a subset of $X$. The following induction principle holds:
$$
  (\forall \x \in X, (\forall \x' \in X, \x' \R x, x' \in U) \Rightarrow \x \in U)
$$
- [__Noetherian__] Say a sequence of elements $\{x_{\i}\}_{i \in \mathbb{N}}$ is $\R-\mathrm{descending}$ if for each $\j \in \mathbb{N}$ we have $\x_{\j+1} \R \x_{j}$. Any $\R-\mathrm{descending}$  sequence is eventually constant.


[explain why these are not equivalent constructively here]

## Agda Development

### Definitions

We will start with the definitions of relation, and property. In a constructive setting we are often better off working with "evidence-carrying" structures, and so a relation is not just a subset of the product $\A \times A$, but for each $\a, \b \in A$ we give back the type of proofs of how $\a$ is related to $\b$

```Agda
Rel :  ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Rel {ℓ = ℓ} A = A → A → Set ℓ
```

Similarly, rather than subsets, we work with evidence-carrying properties which say not just that
an element is in some particular subset, but give a proof for why a term is in the given set. If
one is already familiar with dependent type theory, we will note that a `Property`, in our sense,
is nothing other than a dependent type.

```
Property : ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Property {ℓ = ℓ} A = A → Set ℓ
```

The property we take as fundamental from the above theorem is that of an `inductive relation`. That is to say, we wish to characterize those relations upon which we can prove properties by an induction principle:
```
module InductiveDefs {ℓ : Level} (A : Set ℓ) where
  -- the induction principle for a given relation R and property P
  IndPrinciple : (R : Rel A) → (P : Property A) → Set ℓ
  IndPrinciple R P = ∀ (y : A) → ((∀ (x : A) → R x y → P x) → P y)

  -- A property is inductive with respect to R if we can prove it
  -- by induction on R
  InductiveP : (R : Rel A) → (P : Property A) → Set ℓ
  InductiveP R P =
    IndPrinciple R P →
    (∀ (x : A) → P x)

  -- A relation is inductive if every property
  -- is inductive with respect to it
  InductiveR : (R : Rel A) → Set (ℓsuc ℓ)
  InductiveR R = ∀ (P : Property A) → InductiveP R P
```

### Strong induction

```Agda
module InductiveTrans where
  -- _⁺ is the transitive closure of the relation
  data _⁺ (R : Rel A) : Rel A where
    gen⁺  : ∀ {x y : A} → R x y → (R ⁺) x y
    _⁺↦_  : ∀ {x y z : A} → (R ⁺) x y → R y z → (R ⁺) x z

  -- _* is the reflexive-transitive closure
  data _* (R : Rel A) : Rel A where
    gen*  : ∀ {x y : A} → R x y → (R *) x y
    id    : ∀ {x : A} → (R *) x x
```

```Agda
belowP : {R : Rel A} → Property A → Property A
belowP {R = R} P b = ∀ (a : A) → (((R ⁺) *) a b) → P a
```

```Agda
strong-induction-lemma
  : {R : Rel A} {P : Property A} →
  IndPrinciple (R ⁺) P → IndPrinciple R (belowP {R} P)
-- We are trying to prove P* c holds when we have (a ≤R c)
--
-- case 1: (id : c ≤R c), P* c
-- By R⁺ induction it is enough to show if we have
-- (p : a <R⁺ c) then we have P a

--   Case split on p:
--   ∙ If (p : a <R c) then we have to prove P a
--     which follows by the R induction step applied to p
--     as this gives us P* a which gives P a

--   ∙ If (p : a <R⁺ b <R c) holds then we have by R
--     induction that P* b holds and so we have that P a
--     holds by definition of P*
strong-induction-lemma R⁺ind c stepR-P* .c id =
  R⁺ind c λ {
    a (gen⁺ Rac) → stepR-P* a Rac a id ;
    a (_⁺↦_ {y = b} R⁺ab Rbc) → stepR-P* b Rbc a (gen* R⁺ab)}
-- In this case we have a single R step (p : b <R c)
-- and we have to show that P b holds
--
-- But, we have that P* b holds by R induction and so we have
-- P b
strong-induction-lemma R⁺ind c stepR-P* b (gen* (gen⁺ Rbc)) with stepR-P* b Rbc
... | P*b = P*b b id
-- Similarly, here we have a <R⁺ b <R c, and we want to show
-- P a holds
--
-- But, by R induction we have that P*b holds and so we have
-- that P a holds as a <R⁺ b

strong-induction-lemma indP c stepR-P* a (gen* (_⁺↦_ {y = b} R⁺ab Rbc)) with
  stepR-P* b Rbc
... | P*b = P*b a (gen* R⁺ab)
```

```Agda
-- By the lemma, we can prove (R ⁺) is inductive for any property
-- P if we assume that R is inductive for P*
liftInd
  : {R : Rel A} {P : Property A} →
    InductiveP R (belowP {R} P) →
    InductiveP (R ⁺) P
liftInd IndP* indR⁺ a =
  IndP* (strong-induction-lemma indR⁺) a a id

RtoR⁺-inductive : {R : Rel A} → InductiveR R → InductiveR (R ⁺)
RtoR⁺-inductive {R} IndR P = liftInd (IndR (belowP P))
```

-- Conversely, we can use R⁺ induction to prove R induction
-- by only using a <R b
RtoR⁺-principle : {P : Property A}{R : Rel A} → IndPrinciple R P → IndPrinciple (R ⁺) P
RtoR⁺-principle indR b R⁺step-ab =
  indR b (λ a Rab → R⁺step-ab a (gen⁺ Rab))

R⁺toR-inductive : {R : Rel A} → InductiveR (R ⁺) → InductiveR R
R⁺toR-inductive IndR⁺ P = λ indR a → IndR⁺ P (RtoR⁺-principle indR) a
```

```Agda
-- Therefore, a relation is inductive iff its transitive closure is inductive
⁺Inductive : {R : Rel A} → Equivalence (setoid (InductiveR R)) (setoid (InductiveR (R ⁺)))
⁺Inductive {R = R} = record {
     to = RtoR⁺-inductive {R = R} ;
     from =  R⁺toR-inductive {R = R} ;
     to-cong = cong RtoR⁺-inductive ;
     from-cong = cong R⁺toR-inductive
   }
```

### Pullback Relation

```Agda
module InductivePullback {ℓ : Level} (A B : Set ℓ) where
  open import Function
  open InductiveDefs
  open import Data.Product

  _←R_ : (f : A → B) → Rel B → Rel A
  f ←R R = λ a₀ a₁ → R (f a₀) (f a₁)

  _←P_ : (f : A → B) → Property B → Property A
  f ←P P = P ∘ f

  Π_∙_ : (f : A → B) → Property A → Property B
  Π f ∙ P = λ b → ∀ (a : A) → (f a ≡ b) → P a

  pullback-ind
      : {R : Rel B} {P : Property A}{f : A → B} →
      IndPrinciple A (f ←R R) P →
      IndPrinciple B R (Π f ∙ P )
  pullback-ind {f = f} indR← .(f a₁) indΣ a₁ refl =
    indR← a₁ (λ a₀ Ra₀₁ → indΣ (f a₀) Ra₀₁ a₀ refl)

  pullback-Ind : {R : Rel B}(f : A → B) →
    InductiveR B R →
    InductiveR A (f ←R R)
  pullback-Ind f IndR P indR← a = Π-aP a refl
    where
      Π-aP : (Π f ∙ P) (f a)
      Π-aP = IndR (Π f ∙ P) (pullback-ind indR←) (f a)
```


### Pointwise Product


```Agda
module InductivePWise {ℓ : Level} (A B : Set ℓ) where
  open import Data.Product
  open import Data.Sum
  open InductiveDefs

  data PWise (R₀ : Rel A) (R₁ : Rel B) : Rel (A × B) where
    PWise-R : ∀ {a₀ a₁ : A} {b₀ b₁ : B} →
      R₀ a₀ a₁ → R₁ b₀ b₁ → PWise R₀ R₁ (a₀ , b₀) (a₁ , b₁)

  FstP : Property (A × B) → Property A
  FstP P× = λ a → (b : B) → P× (a , b)

  SndP : Property (A × B) → Property B
  SndP P× = λ b → (a : A) → P× (a , b)

  pwise-ind :
    {R₀ : Rel A} {R₁ : Rel B}{P× : Property (A × B)} →
    IndPrinciple (A × B) (PWise R₀ R₁) P× →
    (IndPrinciple A R₀ (FstP P×)) × (IndPrinciple B R₁ (SndP P×))
  pwise-ind {R₀ = R₀}{R₁ = R₁} {P× = P×} indPW = indFst , indSnd
    where
      indFst : IndPrinciple A R₀ (FstP P×)
      indFst =
        λ a' indA b' → indPW (a' , b')
          (λ { .(_ , _) (PWise-R {a₀ = a'} {b₀ = b'} Ra'a Rb'b) →
            indA a' Ra'a b'})

      indSnd : IndPrinciple B R₁ (SndP P×)
      indSnd =
        λ b' indB a' → indPW (a' , b')
          (λ { .(_ , _) (PWise-R {a₀ = a'} {b₀ = b'} Ra'a Rb'b) →
            indB b' Rb'b a'})

  PWise-Ind :
    {R₀ : Rel A} {R₁ : Rel B} →
    InductiveR A R₀ ⊎ InductiveR B R₁ →
    InductiveR (A × B) (PWise R₀ R₁)
  PWise-Ind {R₀ = R₀} {R₁ = R₁} (inj₁ IndA) P× indPW (a , b) = Pa∀ b
    where
      Pa∀ : (b : B) → P× (a , b)
      Pa∀ = IndA (FstP P×) (proj₁ (pwise-ind indPW)) a
  PWise-Ind {R₀ = R₀} {R₁ = R₁} (inj₂ IndB) P× indPW (a , b) = P∀b a
    where
      P∀b : (a : A) → P× (a , b)
      P∀b = IndB (SndP P×) (proj₂ (pwise-ind indPW)) b
```


### Sum of Relations


```
module InductiveSum {ℓ : Level} (A B : Set ℓ) where
  open import Data.Product
  open import Data.Sum
  open InductiveDefs

  data SumR (R₀ : Rel A) (R₁ : Rel B) : Rel (A ⊎ B) where
    onL : ∀ {a₀ a₁ : A} →
      R₀ a₀ a₁ → SumR R₀ R₁ (inj₁ a₀) (inj₁ a₁)

    onR : ∀ {b₀ b₁ : B} →
      R₁ b₀ b₁ → SumR R₀ R₁ (inj₂ b₀) (inj₂ b₁)

    onLR : ∀{a : A} {b : B} → SumR R₀ R₁ (inj₁ a) (inj₂ b)

  inj₁P : Property (A ⊎ B) → Property A
  inj₁P P⊎ = λ a → P⊎ (inj₁ a)

  inj₂P : Property (A ⊎ B) → Property B
  inj₂P P⊎ = λ b → (∀ (a : A) → P⊎ (inj₁ a)) → P⊎ (inj₂ b)

  sum-ind :
    {R₀ : Rel A} {R₁ : Rel B}{P⊎ : Property (A ⊎ B)} →
    IndPrinciple (A ⊎ B) (SumR R₀ R₁) P⊎ →
    (IndPrinciple A R₀ (inj₁P P⊎)) × (IndPrinciple B R₁ (inj₂P P⊎))
  sum-ind {R₀ = R₀}{R₁ = R₁} {P⊎ = P⊎} ind⊎ = ind-inj₁ , ind-inj₂
    where
      ind-inj₁ : IndPrinciple A R₀ (inj₁P P⊎)
      ind-inj₁ =
        λ a indA → ind⊎ (inj₁ a)
          (λ { .(inj₁ _) (onL Ra'a) → indA _ Ra'a})

      ind-inj₂ : IndPrinciple B R₁ (inj₂P P⊎)
      ind-inj₂ =
        λ b indB Pinj₁ → ind⊎ (inj₂ b)
          (λ { .(inj₂ _) (onR Rb'b) → indB _ Rb'b Pinj₁ ;
               .(inj₁ _) onLR → Pinj₁ _}
          )

  SumR-Ind :
    {R₀ : Rel A} {R₁ : Rel B} →
    InductiveR A R₀ → InductiveR B R₁ →
    InductiveR (A ⊎ B) (SumR R₀ R₁)
  SumR-Ind {R₀ = R₀} {R₁ = R₁} IndA IndB P⊎ ind⊎ (inj₁ a) = Pinj₁a
    where
      Pinj₁a : P⊎ (inj₁ a)
      Pinj₁a = IndA (inj₁P P⊎) (proj₁ (sum-ind ind⊎)) a
  SumR-Ind {R₀ = R₀} {R₁ = R₁} IndA IndB P⊎ ind⊎ (inj₂ b) = Pinj₂b
    where
      Pinj₂b-step : ((a : A) → P⊎ (inj₁ a)) → P⊎ (inj₂ b)
      Pinj₂b-step =
        IndB (inj₂P P⊎) (proj₂ (sum-ind ind⊎)) b

      Pinj₂b : P⊎ (inj₂ b)
      Pinj₂b = Pinj₂b-step λ a → SumR-Ind IndA IndB P⊎ ind⊎ (inj₁ a)
```


### Descending

I learnt this formulation from the majestic 1lab

module Descending {ℓ : Level} {A : Set ℓ} where
  open import Data.Empty
  open import Data.Product
  open import Relation.Nullary
  open InductiveDefs

  data Desc (R : Rel A) (y : A) : Set ℓ where
    step : (∀ (x : A) → R x y → Desc R x) → Desc R y

  DescR : (R : Rel A) → Set ℓ
  DescR R = ∀ (x : A) → Desc R x

  descToInd : {R : Rel A} → DescR R → InductiveR A R
  descToInd {R = R} desc P indR b =  lemma b (desc b)
    where
      lemma : ∀ (b : A) → Desc R b → P b
      lemma b (step DaRb) = indR b (λ a Rab → lemma a (DaRb a Rab))

  indToDesc : {R : Rel A} → InductiveR A R → DescR R
  indToDesc {R = R} indR = indR (Desc R) λ _ → step

  -- Desc R x is equivalent to the standard library's accessibility predicate Acc R x,
  -- and DescR R to WellFounded R.
  open import Induction.WellFounded using (Acc; acc; WellFounded)

  descToAcc : {R : Rel A} {x : A} → Desc R x → Acc R x
  descToAcc (step f) = acc (λ {y} Ryx → descToAcc (f y Ryx))

  accToDesc : {R : Rel A} {x : A} → Acc R x → Desc R x
  accToDesc (acc f) = step (λ y Ryx → accToDesc (f Ryx))



### Lexicographic Ordering

The lexicographic ordering is a certain way of taking two sets with relations and giving an order to their product.

One thing that might bother us about this definition is that it is non-symmetric, treating the first variable as distinct from the second, and when such a situation arises we are well-placed to ask if this is better explained by a dependent pair. This is indeed the case and we can see that the nat

module InductiveLex {ℓ : Level} (A B : Set ℓ) where
  open import Data.Product
  open InductiveDefs
  open Descending

  data Lex (R₀ : Rel A) (R₁ : Rel B) : Rel (A × B) where
    FstR : ∀ {a₀ a₁ : A} {b₀ b₁ : B} → R₀ a₀ a₁ → Lex R₀ R₁ (a₀ , b₀) (a₁ , b₁)
    SndR  : ∀ {a : A} {b₀ b₁ : B} → R₁ b₀ b₁ → Lex R₀ R₁ (a , b₀) (a , b₁)

  desc-lem : {R₀ : Rel A} {R₁ : Rel B} →
    (a : A) (b : B) →
    Desc R₀ a →
    DescR R₁ →
    Desc R₁ b →
    Desc (Lex R₀ R₁) (a , b)
  desc-lem {R₀ = R₀} {R₁ = R₁} a b (step a-step) dB db = inner db
    where
      inner : ∀ {b' : B} → Desc R₁ b' → Desc (Lex R₀ R₁) (a , b')
      inner (step b-step) =
        step (λ {
          .(_ , _) (FstR Ra'a) →
            desc-lem _ _ (a-step _ Ra'a) dB (dB _) ;
          .(a , _) (SndR Rb'b) →
            inner (b-step _ Rb'b)}
            )

  Desc-Lex : {R₀ : Rel A} {R₁ : Rel B} →
    DescR R₀ →
    DescR R₁ →
    DescR (Lex R₀ R₁)
  Desc-Lex desc-R₀ desc-R₁ (a , b) =
    desc-lem a b (desc-R₀ a) desc-R₁ (desc-R₁ b)


### Natural Number Induction
module InductiveNat where
  open InductiveDefs
  open import Data.Product
  open import Data.Empty
  open import Data.Nat

  sucRel : Rel ℕ
  sucRel n m = m ≡ suc n

  module Proof(P : Property ℕ) where

    sucRel-0 : ∀ {n : ℕ} → sucRel n 0 → ⊥
    sucRel-0 ()

    indSplit : IndPrinciple ℕ sucRel P → (P 0 × (∀ (n : ℕ) → P n → P (suc n)))
    indSplit indP = P0 , Psuc
      where

      P0 : P 0
      P0 = indP zero (λ n suc0 → ⊥-elim (sucRel-0 suc0))

      Psuc :  (∀ (n : ℕ) → P n → P (suc n))
      Psuc n Pn = indP (suc n) λ { m refl → Pn}

    ℕ-ind : P 0 → (∀ (n : ℕ) → P n → P (suc n)) → (∀ (n : ℕ) → P n)
    ℕ-ind P0 Psuc zero = P0
    ℕ-ind P0 Psuc (suc n) = Psuc n (ℕ-ind P0 Psuc n)

  open Proof
  sucRelInductive : InductiveR ℕ sucRel
  sucRelInductive P indP with indSplit P indP
  ... | P0 , Psuc = ℕ-ind P P0 Psuc

### W-types

module Inductive-W-types {ℓ : Level} where
  open InductiveDefs
  open import Data.Product
  open import Data.Empty

  data W (A : Set ℓ) (P : A → Set ℓ) : Set ℓ where
    sup : (a : A) → (f : P a → W A P) → W A P

  module WType (A : Set ℓ) (P : A → Set ℓ) where
    Tree : Set ℓ
    Tree = W A P

    IndPrincipleT : (TrP : Property Tree) → Set ℓ
    IndPrincipleT TrP =
      (∀ (a : A) (f : P a → W A P) → (∀ (p : P a) → TrP (f p)) → TrP (sup a f))

    TreeInd :
      {TrP : Property Tree} →
      IndPrincipleT TrP →
      (∀ (t : Tree) → TrP t)
    TreeInd {TrP} indT (sup a f) = indT a f λ pa → TreeInd {TrP} indT (f pa)

    TreeRel : Rel Tree
    TreeRel subT (sup a f) = Σ[ pa ∈ P a ] subT ≡ f pa

    indSplit : {TrP : Property Tree} → IndPrinciple Tree TreeRel TrP → IndPrincipleT TrP
    indSplit indP = λ a f subT-P → indP (sup a f) (λ { .(f pa) (pa , refl) → subT-P pa})

    TreeRelInd : InductiveR Tree TreeRel
    TreeRelInd TrP indP with indSplit {TrP = TrP} indP
    ... | indP = TreeInd {TrP = TrP} indP

module WellOrdered where
  open import Data.Unit
  open import Data.Empty
  postulate
    P : Set

  dec-P : ℕ → Set
  dec-P zero = P
  dec-P (suc zero) = ⊤
  dec-P (suc (suc n)) = ⊥
```
