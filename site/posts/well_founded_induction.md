---
title: "On Well-Founded Induction"
author: Callan McGill
date: "Mar 24, 2026"
tags: [Agda, Induction, Well-Founded Relations]
description: Explorations into well-founded relations in constructive mathematics
quote: Every reading of a classic is in fact a rereading.
quoteAuthor: Italo Calvino
agdaDevelopment: "Inductive Relations"
publish: true

---

<div style="display:none">\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}} \def\x{\mathrm{x}}  \def\y{\mathrm{y}} \def\x'{\mathrm{x'}}  \def\y'{\mathrm{y'}} \def\P{\mathrm{P}}\def\i{\mathrm{i}}\def\j{\mathrm{j}}\def\x{\mathrm{x}}\def\y{\mathrm{y}}\def\m{\mathrm{m}}\def\n{\mathrm{n}}\def\u{\mathrm{u}}\def\A{\mathcal{A}}\def\a{\mathrm{a}}\def\b{\mathrm{b}}\def\p{\mathrm{p}}\def\B{\mathrm{B}}\def\f{\mathrm{f}}
</div>


One of the first things dependently typed programming teaches is that thinking of induction as primarily about the natural numbers is an impoverished view. Instead, a proof assistant like `agda` encourages one firstly towards the idea that mathematics can be founded on inductive structures as the raw primitives, and secondly that  _every_ such structure comes with some given means of proving properties about it. For instance, binary trees in `agda` might be defined as follows:

```Agda
data BinTree (a : Type) : Type where
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

The idea here is that if we can prove a property about binary trees in the `Leaf` case, and in the `Bin` case (assuming it already holds for the child trees), then that property holds for all binary trees.

This characterization focuses on an inductive set as a certain solution to a universal problem (an [initial object in the category of `F-algebras`](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)), and gives us an "immediate predecessor" method of inductive proof. This does, however, come with a downside: there are many natural results which we wish to prove by a more flexible method of induction. For instance, we may wish to do _strong_ induction on the natural numbers, or induction via a number's multi-set of prime factors, or to prove something about an array by iteratively dividing it in half.


One way to think about such problems is that we need not stick with the given "immediate predecessor" relation, but instead can develop other relations on a collection, which are appropriate for performing induction. Moreover, if we have an algebraic theory of such inductive relations, we might then be able to flexibly combine or alter the relations using some basic building blocks. This gives us the theory of well-founded relations.


Classically, there are various equivalent ways to think about the theory of well-founded relations, but as we wish to develop these ideas in `agda`, we should note that
these classically equivalent definitions come apart. Classically, we have the following theorem giving us three different views on what a well-founded relation is:

**Theorem (Well-founded Relations)**:
Suppose $\X$ is a set with a binary relation $\R$ on it, meaning $\R \subseteq \X \times \X$. We write $\R$ infix -- $\x \R \y$ -- to mean that $(\x, \y) \in \R$.

The following are equivalent:

- [__Well-ordering principle__] For every non-empty subset $\U \subseteq \X$, there exists an $\R$-minimal element, i.e. an element with nothing below it in $\U$:
$$
  \forall \U \subseteq \X,\, \U \neq \emptyset \Rightarrow \exists \m \in \U,\, \forall \u \in \U,\, \neg(\u \R \m)
$$
- [__R Inductive__] Suppose $\U$ is a subset of $\X$. The following induction principle holds:
$$
  (\forall \x \in \X, (\forall \x' \in \X, \x' \R \x \to \x' \in \U) \Rightarrow \x \in \U) \Rightarrow U = X
$$
- [__Artinian__\footnote{We use the name [_artinian_](https://en.wikipedia.org/wiki/Artinian_ring) as this is the term used in commutative algebra to describe a ring which satisfies the descending chain condition for ideals.}] Say a sequence of elements $\{\x_{\i}\}_{\i \in \mathbb{N}}$ is $\R$-descending if for each $\j \in \mathbb{N}$ we have $\x_{\j+1} \R \x_{\j}$. We then have that there do not exist any infinite $\R$-descending sequences.

Let us give some idea why the above theorem doesn't naively hold in a constructive setting. Suppose we have some property $\P$ (which may be undecidable or just not decidable by us) and define a subset
$\U \subseteq \mathbb{N}$ as follows:

$$
\U = \begin{cases} \{0, 1\} & \text{if } \P \\ \{1\} & \text{otherwise} \end{cases}
$$

Now, if we were to use the naive constructive version of the well-ordered principle, then this
would give us some way of constructing the least element of this set $\U$, and thus we would be
able to decide the proposition $\P$. Instead, let's take the second principle -- induction --
as the starting point of developing the notion of a well-founded relation in `Agda`.

## Agda Development

### Definitions

We will start with the definitions of relation and property. In a constructive setting we are often better off working with "evidence-carrying" structures, and so a relation is not just a subset of the product $\A \times \A$, but for each $\a, \b \in \A$ we give back the type of proofs of how $\a$ is related to $\b$.

```Agda
Rel :  ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Rel {ℓ = ℓ} A = A → A → Set ℓ
```

Similarly, rather than subsets, we work with evidence-carrying properties which say not just that
an element is in some particular subset, but give a proof for how it is in the given set. If
one is already familiar with dependent type theory, we will note that a `Property`, in our sense,
is nothing other than a dependent type.

```Agda
Property : ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Property {ℓ = ℓ} A = A → Set ℓ
```

The property we take as fundamental from the above theorem is that of an `inductive relation`. That is to say, we wish to characterize those relations upon which we can prove properties by an induction principle:

```Agda
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

We have then: `IndPrinciple R P` gives a general inductive step — to prove `P y` we may assume `P` holds for all `R`-predecessors of `y`; `InductiveP R P` says that P is provable by this method of induction; and `InductiveR R` says that _any_ property `P` can be proven by the induction principle for `R`.

### Strong induction

We would like to think of inductive relations as bonafide objects unto themselves.
A natural question when we start to think structurally in this way is how we can
combine or construct new inductive relations from existing ones.
In this regard, we will first aim at generalizing the notion of _strong induction_.
For the natural numbers, we have an inductive principle based on the immediate predecessor relation: to prove a property $\P$ holds for $\n$, we may assume it holds for the predecessor (remembering that $0$ has no predecessor) and then show it must hold for $\n$. Strong induction instead says that when we are proving $\P \; \n$, we may assume it holds for _all_ numbers less than $\n$. From our
vantage point, we can think of this as going from the predecessor relation $(\n, \operatorname{succ} \n)_{\n \in \mathbb{N}}$ to its transitive closure $\_<\_$. We prove, then, that this idea holds for _any_ inductive relation:

```Agda
module InductiveTrans where
  -- _⁺ is the transitive closure of R
  data _⁺ (R : Rel A) : Rel A where
    gen⁺  : ∀ {x y : A} → R x y → (R ⁺) x y
    _⁺↦_  : ∀ {x y z : A} → (R ⁺) x y → R y z → (R ⁺) x z

  -- _* is the reflexive closure of R
  data _* (R : Rel A) : Rel A where
    gen*  : ∀ {x y : A} → R x y → (R *) x y
    id    : ∀ {x : A} → (R *) x x
```

In the ordinary proof that weak induction gives strong induction, we usually try to package
up data of the strong induction into a different property which we can prove using
weak induction. If we prove $\P$ by strong induction, then we can transform
$\P$ to a new property $\P*$ where:
$$
  (\P*)(\n) = \forall \m < \n, \P \m
$$

We then have that weak induction on $\P*$ proves strong induction for $\P$.
Here is our equivalent of $\P*$:
```Agda
  belowP : {R : Rel A} → Property A → Property A
  belowP {R = R} P b = ∀ (a : A) → (((R ⁺) *) a b) → P a
```
We then use this to prove strong induction\footnote{This proof goes from `IndPrinciple R⁺ P` to `IndPrinciple R P*` and this looks suspiciously like it should be an adjunction of some kind, perhaps using the category of [Chu Spaces](https://en.wikipedia.org/wiki/Chu_space)}.
```Agda
  -- If we have the induction principle for R⁺ and P, then
  -- we get the induction principle for R with belowP P

  strong-induction-lemma
    : {R : Rel A} {P : Property A} →
    IndPrinciple (R ⁺) P → IndPrinciple R (belowP {R} P)
  -- We are trying to prove P* c holds whenever we have that it holds
  -- for all a with (a R c)
  --
  -- We do case analysis on the proof of (R+)* a b
  --
  -- case 1: (id : c ≤R c), we need to prove P c
  -- By R⁺ induction it is enough to show
  -- ∀ (p : a <R⁺ c), P a

  --   We then case split on p:
  --   ∙ If (p : a <R c) is a single step, then we have to
  --     prove P a which follows by the R induction step
  --     applied to p as this gives us P* a from which we get
  --     P a

  --   ∙ If (p : a <R⁺ b <R c) holds then we have by R
  --     induction that P* b holds and so we have that P a
  --     holds by definition of P*
  strong-induction-lemma R⁺ind c stepR-P* .c id =
    R⁺ind c λ {
      a (gen⁺ Rac) → stepR-P* a Rac a id ;
      a (_⁺↦_ {y = b} R⁺ab Rbc) → stepR-P* b Rbc a (gen* R⁺ab)}

  -- In the second case we have a single R step (p : b <R c)
  -- and we have to show that P b holds
  --
  -- But, we have that P* b holds by R induction and so we
  -- automatically have P b
  strong-induction-lemma R⁺ind c stepR-P* b (gen* (gen⁺ Rbc)) with stepR-P* b Rbc
  ... | P*b = P*b b id
  -- Similarly, in the third case we have a <R⁺ b <R c, and we want to show
  -- P a holds
  --
  -- But, by R induction we have that P*b holds and so we have
  -- that P a holds as a <R⁺ b
  strong-induction-lemma indP c stepR-P* a (gen* (_⁺↦_ {y = b} R⁺ab Rbc)) with
    stepR-P* b Rbc
  ... | P*b = P*b a (gen* R⁺ab)
```

We can then show that if ordinary induction holds for $\P*$, then strong induction holds for $\P$.
```Agda
-- By the lemma, we can prove (R ⁺) is inductive for any property
-- P if we assume that R is inductive for P*
liftInd
  : {R : Rel A} {P : Property A} →
    InductiveP R (belowP {R} P) →
    InductiveP (R ⁺) P
liftInd IndP* indR⁺ a =
  IndP* (strong-induction-lemma indR⁺) a a id
```

Finally, we get that if a relation is inductive, then its transitive closure is too:

```Agda
RtoR⁺-inductive : {R : Rel A} → InductiveR R → InductiveR (R ⁺)
RtoR⁺-inductive {R} IndR P = liftInd (IndR (belowP P))
```

Much easier, we can show that if we have strong induction then we have ordinary induction:

```Agda
-- use R induction to prove R⁺ induction by only using single steps a <R b
RtoR⁺-principle : {P : Property A}{R : Rel A} → IndPrinciple R P → IndPrinciple (R ⁺) P
RtoR⁺-principle indR b R⁺step-ab =
  indR b (λ a Rab → R⁺step-ab a (gen⁺ Rab))

R⁺toR-inductive : {R : Rel A} → InductiveR (R ⁺) → InductiveR R
R⁺toR-inductive IndR⁺ P = λ indR a → IndR⁺ P (RtoR⁺-principle indR) a
```

We therefore get that a relation is inductive if, and only if, its transitive closure is inductive:
```Agda
⁺Inductive : {R : Rel A} → Equivalence (setoid (InductiveR R)) (setoid (InductiveR (R ⁺)))
⁺Inductive {R = R} = record {
     to = RtoR⁺-inductive {R = R} ;
     from =  R⁺toR-inductive {R = R} ;
     to-cong = cong RtoR⁺-inductive ;
     from-cong = cong R⁺toR-inductive
   }
```

### Pullback Relation

Next up, we often want to do a "course-of-values" induction. For instance, we prove some property holds of binary trees by using induction on the height of a tree. The way we can think of this more abstractly is that we have a function `height : BinTree → ℕ` and use the _pullback_ of the immediate predecessor relation on `ℕ` to get an induction principle on `BinTree` for the height of sub-trees. We call this the pullback relation, because it is the ordinary pullback of a relation considered as a subset, in the sense that the following diagram is a pullback square:

$$
\begin{array}{ccc}
f^*S & \xrightarrow{\;f^*\;} & S \\
\Big\downarrow{\scriptstyle\subseteq} & & \Big\downarrow{\scriptstyle\subseteq} \\
A \times A & \xrightarrow{\;f \times f\;} & B \times B
\end{array}
$$

We give an explicit construction of the pullback, and also introduce
both the pullback and $\Pi$ type for properties as we use these to
transfer the induction principle from $\A$ to $\B$:
```Agda
module InductivePullback {ℓ : Level} (A B : Set ℓ) where
  open import Function
  open InductiveDefs
  open import Data.Product

  -- pullback relation
  _←R_ : (f : A → B) → Rel B → Rel A
  f ←R R = λ a₀ a₁ → R (f a₀) (f a₁)

  -- pullback of a property
  _←P_ : (f : A → B) → Property B → Property A
  f ←P P = P ∘ f

  --  Π-type: Π_f P b - right adjoint to above pullback/substitution
  Π_∙_ : (f : A → B) → Property A → Property B
  Π f ∙ P = λ b → ∀ (a : A) → (f a ≡ b) → P a

  -- If we have an induction principle for the pullback relation
  -- then we can prove an induction principle for the Π-type property
  pullback-ind
      : {R : Rel B} {P : Property A}{f : A → B} →
      IndPrinciple A (f ←R R) P →
      IndPrinciple B R (Π f ∙ P )
  pullback-ind {f = f} indR← .(f a₁) indΣ a₁ refl =
    indR← a₁ (λ a₀ Ra₀₁ → indΣ (f a₀) Ra₀₁ a₀ refl)

  -- If we have an inductive relation R on B, then
  -- the pullback relation is also inductive
  pullback-Ind : {R : Rel B}(f : A → B) →
    InductiveR B R →
    InductiveR A (f ←R R)
  pullback-Ind f IndR P indR← a = Π-aP a refl
    where
      Π-aP : (Π f ∙ P) (f a)
      Π-aP = IndR (Π f ∙ P) (pullback-ind indR←) (f a)
```
We note here that we make use of the right adjoint to pullback or substitution, and if $\P$ holds
inductively on our pullback relation, then we get exactly that $\Pi_{\f} P$ holds inductively
for our original relation.

### Pointwise Product

One elementary way we can build new inductive relations is to take the pointwise
product of two inductive relations on sets `A` and `B`.


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
            indB b' Rb'b a'}
)
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

We note that when proving this pointwise product induction principle, we only actually need
one of the two component relations to be inductive. This becomes most apparent once we have
introduced the equivalent formulation that a relation is Artinian, since any infinite descending
sequence of pairs will give an infinite descending sequence for each component.

### Sum of Relations

Similarly, if we have an inductive relation $\R_0$ on $\A$, and $\R_1$ on $\B$, then we
have an inductive relation $\R_0 \uplus \R_1$ on $\A \uplus \B$. For this, we make
everything in the first component $\R$-smaller than everything in the second component.
This is just like the usual ordinal sum\footnote{see [here](https://en.wikipedia.org/wiki/Ordinal_arithmetic) for more details}.

```Agda
module InductiveSum {ℓ : Level} (A B : Set ℓ) where
  open import Data.Product
  open import Data.Sum
  open InductiveDefs

  -- The sum relation says:
  --   • ∀ (a a' : A), aRa' gives (inj₁ a) R (inj₁ a')
  --   • ∀ (b b' : B), bRb' gives (inj₂ b) R (inj₂ b')
  --   • ∀ (a : A)(b : B), (inj₁ a) R (inj₂ b)
  data SumR (R₀ : Rel A) (R₁ : Rel B) : Rel (A ⊎ B) where
    onL : ∀ {a₀ a₁ : A} →
      R₀ a₀ a₁ → SumR R₀ R₁ (inj₁ a₀) (inj₁ a₁)

    onR : ∀ {b₀ b₁ : B} →
      R₁ b₀ b₁ → SumR R₀ R₁ (inj₂ b₀) (inj₂ b₁)

    onLR : ∀{a : A} {b : B} → SumR R₀ R₁ (inj₁ a) (inj₂ b)

  -- Given a property on the disjoint union, we can
  -- extract properties on each component
  inj₁P : Property (A ⊎ B) → Property A
  inj₁P P⊎ = λ a → P⊎ (inj₁ a)

  -- The induced property on B assumes we have already proven
  -- the property for all (a : A)
  inj₂P : Property (A ⊎ B) → Property B
  inj₂P P⊎ = λ b → (∀ (a : A) → P⊎ (inj₁ a)) → P⊎ (inj₂ b)

  -- If we have an induction principle for a property on the sum
  -- then we can extract the induced induction principles for
  -- each of the extracted properties:
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

  -- If we have that R₀ and R₁ are inductive, then the sum is inductive
  SumR-Ind :
    {R₀ : Rel A} {R₁ : Rel B} →
    InductiveR A R₀ → InductiveR B R₁ →
    InductiveR (A ⊎ B) (SumR R₀ R₁)
  -- If we are proving the property for a term of type (inj₁ a),
  -- then we can use induction for A and the induced property on A
  SumR-Ind {R₀ = R₀} {R₁ = R₁} IndA IndB P⊎ ind⊎ (inj₁ a) = Pinj₁a
    where
      Pinj₁a : P⊎ (inj₁ a)
      Pinj₁a = IndA (inj₁P P⊎) (proj₁ (sum-ind ind⊎)) a
  -- If we are proving the property for (inj₂ b) then
  -- we use B induction to prove the induced property
  -- holds assuming it holds for all (a : A)
  --
  -- We can then discharge this assumption by recursively calling
  -- SumR-Ind for the given a
  SumR-Ind {R₀ = R₀} {R₁ = R₁} IndA IndB P⊎ ind⊎ (inj₂ b) = Pinj₂b
    where
      Pinj₂b-step : ((a : A) → P⊎ (inj₁ a)) → P⊎ (inj₂ b)
      Pinj₂b-step =
        IndB (inj₂P P⊎) (proj₂ (sum-ind ind⊎)) b

      Pinj₂b : P⊎ (inj₂ b)
      Pinj₂b = Pinj₂b-step λ a → SumR-Ind IndA IndB P⊎ ind⊎ (inj₁ a)
```


### Artinian Condition

Let us think back to the various equivalent formulations of a well-founded relation.
We can think about what it means to say constructively that a relation doesn't have
an infinite chain.
One formulation\footnote{which I learned properly from the majestic [1lab](https://1lab.dev/Data.Wellfounded.Base.html#well-founded)} gives a kind of inductive description, which we call `FinDesc`, of those elements that not part of infinite descending chains:

- If an element has no element less than it, then it satisfies `FinDesc`
- If all of the elements immediately less than a given element already
satisfy `FinDesc`, then the given element satisfies `FinDesc`.

__Note__: As we show below, the much more standard way to refer to `FinDesc`
is as an accessibility predicate -- denoted `Acc` in `agda` -- and one usually calls
a relation that we refer to as `Artinian` just by the term `WellFounded` since this is the
most useful general formulation.

This can be encoded in the following definition:
```Agda
module Descending {ℓ : Level} {A : Set ℓ} where
  open import Data.Empty
  open import Data.Product
  open import Relation.Nullary
  open InductiveDefs

  data FinDesc (R : Rel A) (y : A) : Set ℓ where
    step : (∀ (x : A) → R x y → FinDesc R x) → FinDesc R y

  -- A relation is Artinian if all elements satisfy FinDesc
  Artinian : (R : Rel A) → Set ℓ
  Artinian R = ∀ (x : A) → FinDesc R x
```

We can then show that a relation is Artinian if, and only if, it is inductive:
```Agda
  ArtinianToInd : {R : Rel A} → Artinian R → InductiveR A R
  ArtinianToInd {R = R} fin-desc P indR b = lemma b (fin-desc b)
    where
	  -- We prove P b holds by induction,
	  -- if we have aRb, then because b satisfies FinDesc,
	  -- then so does a and so we apply the lemma recursively
	  -- to prove P a
      lemma : ∀ (b : A) → FinDesc R b → P b
      lemma b (step DaRb) = indR b (λ a Rab → lemma a (DaRb a Rab))

  -- If R is inductive, then we can prove it is Artinian
  -- by applying induction to the FinDesc property
  indToArtinian : {R : Rel A} → InductiveR A R → Artinian R
  indToArtinian {R = R} indR = indR (FinDesc R) λ _ → step
```

Finally, as we mentioned we note that our concept `FinDesc` is equivalent to one already in `Agda`'s `stdlib` called `Acc`:

```Agda
  open import Induction.WellFounded using (Acc; acc; WellFounded)

  descToAcc : {R : Rel A} {x : A} → FinDesc R x → Acc R x
  descToAcc (step f) = acc (λ {y} Ryx → descToAcc (f y Ryx))

  accToFinDesc : {R : Rel A} {x : A} → Acc R x → FinDesc R x
  accToFinDesc (acc f) = step (λ y Ryx → accToFinDesc (f Ryx))
```

### Lexicographic Ordering

A different way of giving a well-ordering to a product than the pointwise order is the
lexicographic ordering. For this, we have two relations $\R_0$ on $\A$, $\R_1$ on $\B$,
and then we define a new relation $\R$ on pairs, where we say $(\a, \b) \; \R \; (\a', \b')$
in just the cases when either:

- We have that $\a \; \R_0\; \a'$
- We have that $\a = \a'$ and also that $\b\; \R_1\; \b'$

One thing that might bother us about this definition is that it is very non-symmetric, treating the first variable as somehow distinguished. When such a situation arises, one is often well-placed to ask if this can be better explained by using a dependent pair instead of a product. This is indeed the case, and so we will work in the generality that we have not just
two types $\A$ and $\B$, but that $\B$ is a dependent type over $\A$:

```Agda
module InductiveLex {ℓ : Level} (A : Set ℓ) (B : A → Set ℓ) where
  open import Data.Product
  open InductiveDefs
  open Descending

  data Lex (R₀ : Rel A) (R₁ : (a : A) → Rel (B a)) : Rel (Σ A B) where
    FstR : ∀ {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁} → R₀ a₀ a₁ → Lex R₀ R₁ (a₀ , b₀) (a₁ , b₁)
    SndR : ∀ {a : A} {b₀ b₁ : B a} → R₁ a b₀ b₁ → Lex R₀ R₁ (a , b₀) (a , b₁)
```

Ordinarily, when we want to prove lexicographic ordering is a well-ordering, we want
to use our descending sequence condition. Imagine we have a descending sequence in
`Σ A B`: $\p_0,\; \p_1,\; \ldots$ and suppose $\p_0 = (\x, \y)$. We then have that there
can only exist a finite number of terms in our sequence with $\x$ as their first term
since $\B\; \x$ satisfies the descending sequence condition. But then, because $\A$
also satisfies the descending sequence condition, we see that this jump in the first term of the sequence can only happen a finite number of times and thus that overall such a sequence cannot be infinite. Because this argument seems much more natural than arguing directly with the
induction principle, we use the Artinian/Accessibility characterization from the previous
section to show that the lexicographic ordering is Artinian:

```Agda

  -- We fix a given a and b and want to show that if a satisfies FinDesc
  -- and the relation on B is pointwise Artinian, then (a, b) satisfies
  -- FinDesc for the lex relation
  desc-lem : {R₀ : Rel A} {R₁ : (a : A) → Rel (B a)} →
    (a : A) (b : B a) →
    FinDesc R₀ a →
    ((a : A) → Artinian (R₁ a)) →
    FinDesc (R₁ a) b →
    FinDesc (Lex R₀ R₁) (a , b)
  -- We here case on the proof that a satisfies FinDesc
  desc-lem {R₀ = R₀} {R₁ = R₁} a b (step a-step) dB db = inner db
    where
	  -- For this fixed a, we then split on the proof that b is artinian
	  -- where:
	  --   - in the case that we descend on the first component, we use
	  --     that a satisfies FinDesc and recurse with a'
	  --   - in the case that we recurse on the second component, then
	  --     we recurse on inner which descends on b
      inner : ∀ {b' : B a} → FinDesc (R₁ a) b' → FinDesc (Lex R₀ R₁) (a , b')
      inner (step b-step) =
        step (λ {
          .(_ , _) (FstR Ra'a) →
            desc-lem _ _ (a-step _ Ra'a) dB (dB _ _) ;
          .(a , _) (SndR Rb'b) →
            inner (b-step _ Rb'b)}
            )
```

We can then show that the lexicographic ordering is Artinian (and therefore inductive):
```Agda
  Desc-Lex : {R₀ : Rel A} {R₁ : (a : A) → Rel (B a)} →
    Artinian R₀ →
    ((a : A) → Artinian (R₁ a)) →
    Artinian (Lex R₀ R₁)
  Desc-Lex desc-R₀ desc-R₁ (a , b) =
    desc-lem a b (desc-R₀ a) desc-R₁ (desc-R₁ a b)
```

### Natural Number Induction

Given that we are talking about _induction_, we'd be remiss if we didn't demonstrate how
natural number induction fits into our scheme. Let's define the ordinary predecessor relation, and show that this is nothing but the ordinary induction principle for the natural numbers:

```Agda
module InductiveNat where
  open InductiveDefs
  open import Data.Product
  open import Data.Empty
  open import Data.Nat

  predRel : Rel ℕ
  predRel n m = m ≡ suc n
```

We then show that if something satisfies the induction principle for `predRel`, then
we can extract from it the ordinary inputs for natural number induction:

```Agda
  module Proof(P : Property ℕ) where

    -- We need to use that 0 has no predecessor
    predRel-0 : ∀ {n : ℕ} → predRel n 0 → ⊥
    predRel-0 ()

    indSplit : IndPrinciple ℕ predRel P → (P 0 × (∀ (n : ℕ) → P n → P (suc n)))
    indSplit indP = P0 , Psuc
      where
      P0 : P 0
      P0 = indP zero (λ n suc0 → ⊥-elim (predRel-0 suc0))

      Psuc :  (∀ (n : ℕ) → P n → P (suc n))
      Psuc n Pn = indP (suc n) λ { m refl → Pn}

    ℕ-ind : P 0 → (∀ (n : ℕ) → P n → P (suc n)) → (∀ (n : ℕ) → P n)
    ℕ-ind P0 Psuc zero = P0
    ℕ-ind P0 Psuc (suc n) = Psuc n (ℕ-ind P0 Psuc n)
```

We can therefore show that `predRel` is an inductive relation:
```Agda
  predRelInductive : InductiveR ℕ predRel
  predRelInductive P indP with indSplit P indP
  ... | P0 , Psuc = ℕ-ind P P0 Psuc
```

Thus we re-capture the familiar principle of mathematical induction as a special case using
the immediate predecessor relation.

### W-types

Another very general way type theorists have of talking about induction is via [W-types](https://ncatlab.org/nlab/show/W-type), that is, the type of well-founded trees.
The idea of a `W-type` is that we have a type $\A$ of "shapes" and a dependent type $\P : \A \rightarrow \mathrm{Type}$ of "positions", corresponding to a type of indices where we can place a recursive sub-tree\footnote{This terminology comes from the theory of [containers](https://en.wikipedia.org/wiki/Polynomial_functor_(type_theory)), where a `W-type` is a
fixed point for the functor associated with a container}.

For instance, we can encode the natural numbers by taking $\A = \mathbb{2}$ corresponding to the constructors `Zero` and `Succ`, and where we define the "positions" for each constructor as
$$
\P(\b) = \begin{cases} \bot & \text{if } \b = 0 \\ \top & \text{if } \b = 1 \end{cases}
$$

```Agda
module Inductive-W-types {ℓ : Level} where
  open InductiveDefs
  open import Data.Product
  open import Data.Empty

  data W (A : Set ℓ) (P : A → Set ℓ) : Set ℓ where
    sup : (a : A) → (f : P a → W A P) → W A P
```
This has the following primitive induction principle:
```Agda
  module WType (A : Set ℓ) (P : A → Set ℓ) where
    Tree : Set ℓ
    Tree = W A P

    -- For each constructor a with argument p : P a
    -- we assume that the property holds for each subtree f p
    -- and then have that it holds for each tree constructor from
    -- p and f p
    IndPrincipleTree : (Q : Property Tree) → Set ℓ
    IndPrincipleTree Q =
      (∀ (a : A) (f : P a → W A P) →
      (∀ (p : P a) → Q (f p)) →
      Q (sup a f))

    -- We can then use this induction principle to prove a property holds
    -- for all W-types
    TreeInd :
      {Q : Property Tree} →
      IndPrincipleTree Q →
      (∀ (t : Tree) → Q t)
    TreeInd {Q} indT (sup a f) = indT a f λ pa → TreeInd {Q} indT (f pa)
```

As with $\mathbb{N}$, we can show that induction for the immediate sub-term relation
gives us back this same induction principle:
```Agda
    -- The relation we take is essentially the immediate sub-tree relation
    -- so we say sub R (sup a f) just in the case that there exists some
    -- position pa : P a s.t. sub is propositionally equal to the tree f pa
    TreeRel : Rel Tree
    TreeRel sub (sup a f) = Σ[ pa ∈ P a ] sub ≡ f pa

    -- If we have the induction principle for this relation then
    -- we get the above W-tree induction principle
    indSplit : {Q : Property Tree} → IndPrinciple Tree TreeRel Q → IndPrincipleTree Q
    indSplit indP = λ a f subT-P → indP (sup a f) (λ { .(f pa) (pa , refl) → subT-P pa})

    -- We therefore have that the immediate subtree relation is inductive
    TreeRelInd : InductiveR Tree TreeRel
    TreeRelInd Q indP with indSplit {Q = Q} indP
    ... | indP = TreeInd {Q = Q} indP
```

### Automorphisms of relations

To give some flavour of further ideas we could explore, note that lots of what we
have developed is very closely aligned with the theory of [ordinals](https://ncatlab.org/nlab/show/ordinal+number). This suggests not only
developing new ways to construct inductive relations, but also thinking about the
category of such relations and what properties it has. For instance, it is an
important and well-known fact about ordinals that any automorphism of an ordinal must be the
identity. As we might imagine, something similar is true for our well-founded relations.

Let's first set up what a homomorphism between two relations is:
```Agda
module WellOrderedAuto where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
  open import Relation.Binary using (Trichotomous; Tri)
  open Descending

  record RelHom {ℓ : Level} {A B : Set ℓ} (R₁ : Rel A) (R₂ : Rel B) : Set ℓ where
    field
      fn : A → B
      rel-preserve : ∀ {x y} → R₁ x y → R₂ (fn x) (fn y)
```

This gives us a notion of isomorphism between relations:

```Agda
  record Iso {ℓ : Level} {A B : Set ℓ} (R₁ : Rel A) (R₂ : Rel B) : Set ℓ where
    field
      to-hom : RelHom R₁ R₂
      from-hom : RelHom R₂ R₁
    module T = RelHom to-hom
    module F = RelHom from-hom
    field
      to∘from : ∀ (b : B) → T.fn (F.fn b) ≡ b
      from∘to : ∀ (a : A) → F.fn (T.fn a) ≡ a
```

We can then show (by induction) that no automorphism of an inductive relation can send an element to one that is
$\R$-smaller than it:
```Agda
  open RelHom
  open Iso
  open InductiveDefs
  open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
  open import Data.Product

  ind-auto-no-regress : {ℓ : Level} {A : Set ℓ} {R : Rel A} (IndR : InductiveR A R) → (iso-R : Iso R R) → ∀ (a : A) → R (fn (to-hom iso-R) a) a → ⊥
  ind-auto-no-regress {ℓ = ℓ} {A = A} {R = R} IndR iso-R = R-sep-holds
    where
    module I = Iso iso-R
    fwd = I.T.fn
    R-hom = I.T.rel-preserve

    R-sep : Property A
    R-sep a = R (fn (to-hom iso-R) a) a → ⊥ {ℓ}

    R-sep-holds : ∀ (a : A) → R-sep a
    R-sep-holds a = IndR R-sep (λ a' inda'' a'Ra → inda'' (fwd a') a'Ra (R-hom a'Ra)) a
```

This shows that no automorphism $f$ satisfies $\f(\a)\; \R \; \a$. But then, applying
this to the inverse automorphism $\f^{-1}$ at $\f(\a)$, we get that no automorphism satisfies
$\f^{-1}(\f(\a))\; \R \; \f(\a)$, i.e., $\a \R \f(\a)$, so automorphisms also don't send elements to those that are $\R$-larger than them:
```Agda
  ind-auto-no-progress
    : {ℓ : Level} {A : Set ℓ} {R : Rel A} →
      InductiveR A R →
      (iso-R : Iso R R) →
      ∀ (a : A) → R a (fn (to-hom iso-R) a) → ⊥
  ind-auto-no-progress {A = A} {R = R} IndR iso-R a Rafa =
    ind-auto-no-regress IndR iso-R⁻¹ (fn (to-hom iso-R) a)
      (subst (λ x → R x (fn (to-hom iso-R) a)) (sym (from∘to iso-R a)) Rafa)
      -- Rewrite
      --   Rafa : R a (f a)) ↦
      --        : R (f⁻¹ (f a)) (f a)
      -- so we can use ind-auto-no-regress with iso-R⁻¹ at value f a
    where
      -- if f is an iso then f⁻¹ is also
      iso-R⁻¹ : Iso R R
      iso-R⁻¹ = record
        { to-hom   = from-hom iso-R
        ; from-hom = to-hom iso-R
        ; to∘from  = from∘to iso-R
        ; from∘to  = to∘from iso-R
        }
```

Finally, if our relation is a total order, so that each pair of elements is $\R$-comparable, we get that
any automorphism is extensionally equal to the identity:
```Agda
  -- For a totally ordered inductive relation any automorphism must be
  -- extensionally equal to the identity.
  auto-is-identity
    : {ℓ : Level} {A : Set ℓ} {R : Rel A} →
      InductiveR A R →
      Trichotomous _≡_ R →
      (iso-R : Iso R R) →
      ∀ (a : A) → fn (to-hom iso-R) a ≡ a
  auto-is-identity {R = R} IndR triR iso-R a with triR a (fn (to-hom iso-R) a)
  ... | Tri.tri< Rafa  _  _  = ⊥-elim (ind-auto-no-progress IndR iso-R a Rafa)
  ... | Tri.tri≈ _  a≡fa  _  = sym a≡fa
  ... | Tri.tri> _  _  Rfaa  = ⊥-elim (ind-auto-no-regress  IndR iso-R a Rfaa)
```

The ideas in this post -- especially using the accessibility predicate associated to a relation -- are exactly what systems like `lean` and `rocq` use to compile recursive definitions using eliminators. They are also the foundation of systems like `rocq`'s [equations library](https://mattam82.github.io/Coq-Equations/). There is far more to be said beyond our introduction for constructively developing the theory of well-founded relations, and relatedly the theory of ordinals. For more on this topic from the point of view of constructive mathematics, I would recommend looking at [TypeTopology](https://github.com/martinescardo/TypeTopology), as well as other works by [Martin Escardo](https://martinescardo.github.io/) and his collaborators.
