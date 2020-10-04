---
title: "Peano Axioms (Draft)"
author: Callan McGill
date: "Sep 27, 2020"
tags: [Agda, Natural Numbers]
description: Explorations into the natural numbers
quote: If there is one thing in mathematics that fascinates me more than anything else (and doubtless always has), it is neither 'number' nor 'size,' but always form.
quoteAuthor: Grothendieck

---


  The 19th century brought about an unprecedented revolution in the foundations of mathematics culminating in the Zermelo--Frankel (ZF) axioms.
The ZF axioms gave a logical basis to Cantor's _set theory_ as a foundational theory
, in which the main branches of mathematics (analysis, topology, geometry and number theory) could be encoded and thusly understood.
It was through this newly-systematized approach that the axiomatic method was born.
This is of historical and philosophical interest as it marks a decisive structuralist turn
in mathematical thought. It is at this time that mathematical objects begin to be characterized
not by any particular construction, but by the collection of axioms (or laws) an object satisfies.
$\def\N{\mathsf{N}}$

Consider a paradigmatic case; characterizing the natural numbers. In this post we will explore two
different formulations of the natural numbers, the first given by Peano in the late 19th century, the
second, a more categorical approach inspired by Lawvere.
This will provide us a springboard upon which to explore _how_ we can formulate and reason about
mathematical structures in Agda. Since Agda is based on dependent type theory our formulations will be
[_constructive_](https://en.wikipedia.org/wiki/Constructivism_(philosophy_of_mathematics)).
This means our constructions will be _proof relevant_. In this setting, proofs are first-class entities
and as such our algebraic structures will encode both the operations a structure has along with
proofs of the properties that it satisfies.


We will assume the reader has some familiarity with Agda (with reminders sprinkled in throughout) and has an interest in formalizing mathematics.


Let us begin with Peano's axioms. A set $\N$ satisfies Peano's axioms if the following properties hold:


 -  There exist terms $0 \in \N$ and $\mathrm{s} : \N \rightarrow \N$.
 - $\N$ carries an equivalence relation $\simeq\;\subset\N \times\N$ (to be explained below).
 - $\mathrm{s}$ reflects $\simeq$-equivalence:
$$ \forall \; \mathrm{n}, \mathrm{m} \in \N \; . \; \mathrm{s} (\mathrm{n}) \simeq \mathrm{s} (\mathrm{m}) \Rightarrow \mathrm{m} \simeq \mathrm{n} $$
 - $0$ is never (equivalent to) the successor of any number:
 $$ \nexists \; \mathrm{n} \in \mathbb{N} \; . \; \mathrm{s}(n) \simeq 0 $$
  - $\N$ satisfies induction: if $\phi : \N \rightarrow \mathbb{B}$ is a predicate and the following conditions hold:
    - $\phi(0)$ is true.
    - $\forall \; \mathrm{n} \in \mathbb{N} \; . \; \phi(n) \Rightarrow \phi(\mathrm{s}(\mathrm{n}))$

    then $\phi$ is true for all $\mathrm{n} \in \N$.

How can we prove that this uniquely determines the natural numbers? Our strategy would roughly go as follows:

  - Give a particular construction of $\mathbb{N}$ showing it satisfies the axioms.
  - For any set $\N$ satisfying the axioms, construct maps:
  $$\begin{aligned}
      \mathrm{from} &: \mathbb{N} \rightarrow \mathsf{N} \\
      \mathrm{to}   &: \mathsf{N} \rightarrow \mathbb{N} \\
    \end{aligned}$$
  - Use induction with the following predicates:
  $$\begin{aligned}
      \phi_{\mathbb{N}}(n) &= n \simeq_\mathbb{N} \mathrm{to} \circ \mathrm{from}(n) \\
      \phi_{\mathsf{N}}(n) &= n \simeq_\mathsf{N} \mathrm{to} \circ \mathrm{from} (n)
    \end{aligned}$$
    to show the these maps form an equivalence.


  Let's try to formalise this constructively in Agda. We start with a few imports we will need later:

```agda
module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)
open import Function
  using (_∘_)
```

Typically, we define the (unary) natural numbers as follows:

```agda
data ℕ : Set where
  Zero : ℕ
  Succ : ℕ -> ℕ

-- This allows us to use numeric literals.
{-# BUILTIN NATURAL ℕ #-}
```

Our first port of call is to formulate equivalence relations. In Agda we usually encode
algebraic structures as [records](https://agda.readthedocs.io/en/v2.6.1.1/language/record-types.html).
As mentioned in the introduction, since proofs are first-class, we carry around not just the
structure of the binary relation but also the properties it satisfies:

```agda
record EqRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    reflexivity  : ∀ {a : A}     → a ≃ a
    symmetry     : ∀ {a b : A}   → a ≃ b → b ≃ a
    transitivity : ∀ {a b c : A} → a ≃ b → b ≃ c → a ≃ c
```

We note that this definition is slightly different from what is typical in mathematics.
Rather than a _subset_ of the diagonal we make use of a two-argument dependent type $\_ \simeq \_$. Given $\mathrm{a}, \mathrm{b} : \mathrm{A}$,
the type $\mathrm{a}\;\simeq\;\mathrm{b}$ gives the collection of  _evidence_ that $\mathrm{a}$ and $\mathrm{b}$ are equal.
The axioms this satisfies are reflexivity (that any element is equal to itself) symmetry
(that we can freely reverse equalities) and transitivity (that we can compose equalities).

Let's show that Agda's built-in equality type, $\equiv$, is an equivalence relation on $\mathbb{N}$. As a brief reminder, here is how the equality type is defined, if we ignore 
[level polymorphism](https://agda.readthedocs.io/en/v2.6.1.1/language/universe-levels.html):
```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```
That is to say, we can give a term $\mathrm{refl}$ of type $\mathrm{a} \equiv \mathrm{b}$
so long as Agda can directly compute that $\mathrm{a}$ and $\mathrm{b}$ are equal within
the particular context. For example, if we define addition:
```agda
_+_ : ℕ -> ℕ -> ℕ
_+_ Zero     m = m
_+_ (Succ n) m = Succ (n + m)
```
then we can give the following (unnamed) definition:

```agda
_ : 2 + 2 ≡ 4
_ = refl
```
as Agda can compute that both sides are equal.

Coming back to $\mathbb{N}$, let's show how $\equiv$ satisfies the properties of an equivalence
relation:

```agda
ℕ-refl : ∀ {n : ℕ} → n ≡ n
ℕ-refl = refl

ℕ-symm : ∀ {n m : ℕ} → n ≡ m → m ≡ n
ℕ-symm eq rewrite eq = refl

ℕ-trans : ∀ {m n r : ℕ} → m ≡ n → n ≡ r → m ≡ r
ℕ-trans  m≡n n≡r rewrite m≡n | n≡r = refl
```
Here we make use of Agda's
[rewrite construction](https://agda.readthedocs.io/en/v2.6.1/language/with-abstraction.html#with-rewrite). By providing an equality proof of the form
$\mathrm{a} \equiv \mathrm{b}$, the rewrite construction will replace subexpressions in the goal of the
form $\mathrm{a}$ with $\mathrm{b}$. For example, in $\mathbb{N}\mathrm{-symm}$, we use
the equality term we are given as an argument to rewrite so that each appearance of
$\mathrm{n}$ is replaced with $\mathrm{m}$. At this point we may fill the hole with
$\mathrm{refl} : \mathrm{m} \equiv \mathrm{m}$.

It is worth noting that we haven't used anything special about $\mathbb{N}$ and these
same definitions would work to prove that _any_ set forms an equivalence relation under $\equiv$.

Now we can write an instance of EqRel for $\mathbb{N}$:

```agda
open EqRel {{...}} public

instance
  ≡-Nat : EqRel ℕ
  ≡-Nat =
    record
    { _≃_          = _≡_
    ; reflexivity  = ℕ-refl
    ; symmetry     = ℕ-symm
    ; transitivity = ℕ-trans
    }
```

Here we use Agda's 
[instance arguments](https://agda.readthedocs.io/en/v2.6.1.1/language/instance-arguments.html) 
mechanism, the analog to Haskell's typeclass instances.
We start by bringing the fields of EqRel into scope for those instances which can be resolved.
This is essentially equivalent to us defining top-level functions of the form:
```agda
_≃_         : ∀ {A : Set} {{_ : EqRel A}} → A → A → Set
reflexivity : ∀ {A : Set} {{_ : EqRel A}} {a b : A} → (a ≃ a)
-- etc.
```
Implicit arguments $\{\{\_ : \mathrm{EqRel}\; \mathrm{A}\}\}$ are resolved by searching
for instances we have available in scope. In particular, we define an instance of EqRel
for $\mathbb{N}$ which means that we may use these methods on $\mathbb{N}$ and Agda
will infer the instance we have provided.

Now we are in a position to formalise the Peano axioms. In much the same way as we have done with equivalence relations we again use records to encode algebraic structure:

```agda
record Peano (N : Set) {{rel : EqRel N}} : Set₁ where
  field
    zero        : N
    succ        : N → N
    s-injective : ∀ {a b : N} → (succ a) ≃ (succ b) → a ≃ b
    zero≠succ   : ∀ (a : N) → zero ≃ (succ a) → ⊥
    induction   :
       ∀ (P : N → Set) (a : N)
       → (z : P zero)
       → (s : ∀ {b : N} → P b → P (succ b))
       → P a
    induction-zero :
       ∀ (P : N → Set)
       → (z : P zero)
       → (s : ∀ {b : N} → P b → P (succ b))
       → (induction P zero z s ≡ z)
    induction-succ :
       ∀ (P : N → Set) (a : N)
       → (z : (P zero))
       → (s : ∀ {b : N} → P b → P (succ b))
       → (induction P (succ a) z s ≡ s (induction P a z s))
```

Several things are worth noting about this defintion:

  - We again make use of instance arguments so that the input type $\N$ has the structure
    of an equivalence relation. This is somewhat similar to a typeclass extension definition
    in Haskell:
```haskell
    class Eq a => Ord a
```
  - We upgrade induction from a unary predicate $\phi : \N \rightarrow \mathbb{B}$ to a dependent type
    $\mathrm{P} : \N \rightarrow \mathrm{Set}$.
  - As we will see later, we would like this upgraded principle to be able to _compute_. As such
    we add two laws that dictate how computation should unfold.

Let's now prove that $\mathbb{N}$ satisfies induction and injectivity of $\mathrm{Succ}$:
```agda
ℕ-induction :
  ∀ (P : ℕ → Set) (a : ℕ)
  → (P Zero)
  → (∀ {b : ℕ} → (P b) → (P (Succ b)))
  → (P a)
ℕ-induction P Zero p[zero] p[succ] = p[zero]
ℕ-induction P (Succ n) p[zero] p[succ]
  = p[succ] (ℕ-induction P n p[zero] p[succ])

Succ-inj : ∀ {n m : ℕ} → (Succ n) ≡ (Succ m) → n ≡ m
Succ-inj refl = refl
```

This is much as we might expect, induction is identical to the recursion principle
for $\mathbb{N}$ and $\mathrm{Succ}$-$\mathrm{inj}$ follows definitionally after we
case match on equality. We can now make $\mathbb{N}$ an instance of $\mathrm{Peano}$:

```
instance
  ℕ-Peano : Peano ℕ
  ℕ-Peano =
    record
      { zero           = Zero
      ; succ           = Succ
      ; s-injective    = Succ-inj
      ; zero≠succ      = λ n ()
      ; induction      = ℕ-induction
      ; induction-zero = λ P z s   → refl
      ; induction-succ = λ P a z s → refl
      }
```

In the last two cases the $\mathrm{induction}$ laws hold definitionally from how
we have defined $\mathbb{N}$-$\mathrm{induction}$.

  Now, given any set $\mathsf{N}$ satisfying the Peano axioms we want to define
functions to and from $\mathbb{N}$:
```agda

from-ℕ : ∀ {N : Set} {{_ : EqRel N}} → {{ _ : Peano N}} → ℕ → N
from-ℕ {N} n = induction (λ _ -> N) n zero succ

to-ℕ : ∀ {N : Set} {{_ : EqRel N}} → {{_ : Peano N}} → N → ℕ
to-ℕ n = induction (λ _ → ℕ) n zero succ
```

Pleasantly both definitions are essentially identical, using instance resolution to
determine the relevant induction principle and values to use. Here we see the power
of constructive induction. We don't use induction to prove a _property_ per se, but
to compute. Since the dependent types in question are constant induction simply _is_ recursion!


Now we can show these maps form equivalences. To get a flavour let
us step through the development for the first equality:
```agda
to∘from :
  ∀ {N : Set} {{ _ : EqRel N }} → {{peano : Peano N}}
  → (n : ℕ) → to-ℕ {N} (from-ℕ n) ≡ n
to∘from n = {!!}
```

Asking Agda for the goal gives us:

```terminal
Goal: Peano.induction peano (λ _ → ℕ)
      (ℕ-induction (λ _ → N) n (Peano.zero peano) (Peano.succ peano)) 0
      Succ
      ≡ n
————————————————————————————————————————————————————————————
n     : ℕ
peano : Peano N  (not in scope, instance)
_     : EqRel N    (instance)
N     : Set      (not in scope)

```

We can see that in order for $\mathbb{N}$-$\mathrm{induction}$ to make progress we need to split
on $\mathrm{n}$:
```agda
to∘from :
  ∀ {N : Set} {{ _ : EqRel N }} → {{peano : Peano N}}
  → (n : ℕ) → to-ℕ {N} (from-ℕ n) ≡ n
to∘from Zero     = {!!}
to∘from (Succ n) = {!!}
```

The new goal for $\mathrm{Zero}$ is:
```terminal
Goal: Peano.induction peano (λ _ → ℕ) (Peano.zero peano) 0 Succ ≡ 0
```
But this is precisely our $\mathrm{induction}$-$\mathrm{zero}$ principle! Similarly we can
now use the $\mathrm{induction}$-$\mathrm{succ}$ principle in the second case and then recurse
giving us:
```agda
to∘from :
  ∀ {N : Set} {{ _ : EqRel N }} → {{peano : Peano N}}
  → (n : ℕ) → to-ℕ {N} (from-ℕ n) ≡ n
to∘from Zero =  (induction-zero (λ _ → ℕ) Zero Succ)
to∘from {N} {{_}} {{peano}} (Succ n)
  rewrite
    (induction-succ
      (λ _ → ℕ)
      (ℕ-induction (λ _ → N) n (Peano.zero peano) (Peano.succ peano))
      Zero
      Succ)
  | to∘from {N} n
  = refl
```

The slightly gnarly explicit arguments in the second case are to help along the rewrite
construction as it didn't seem to cooperate with a less verbose alternative.

The other proof is similarly a case of following our nose (or rather following the
typechecker). We first remind ourselves of some equality principles we have imported
above (again simplifying away level polymorphism):
```agda
-- Funtions preserve equality:
cong
  : {A : Set} {B : Set} (f : A → B) {x y : A}
  → x ≡ y → f x ≡ f y

-- The transitivity principle for ≡
trans : ∀ {a b c : A} → a ≡ b → b ≡ c → a ≡ c
```
We also will need the fact that we can lift any propositional equality into an equivalence relation:
```agda
liftEq : ∀ {A : Set}  {{r : EqRel A}} → {a b : A} → a ≡ b → (a ≃ b)
liftEq refl = reflexivity
```

With these can now give the proof:
```agda

from∘to :
  ∀ {N : Set}{{ rel : EqRel N}} → {{peano : Peano N}} → (n : N) →
  from-ℕ (to-ℕ n) ≃ n
from∘to {N} n = liftEq (prop-eq {N})
             -- We make use of liftEq as we prove the
             -- stronger claim that from-ℕ (to-ℕ n) ≡ n
  where
  -- In the zero case we apply induction-zero underneath from-ℕ
  -- and then use the definition of from-ℕ.
  zero-lem
    : ∀ {N} {{_ : EqRel N}} {{peano : Peano N}}
    → from-ℕ {N} (induction {N} (λ _ → ℕ) zero Zero Succ) ≡ zero
  zero-lem {N} =
    let
      pf1 : from-ℕ (induction {N} (λ _ → ℕ) zero Zero Succ) ≡ from-ℕ Zero
      pf1 = cong from-ℕ (induction-zero (λ _ → ℕ) Zero Succ)

      pf2 : from-ℕ  Zero ≡ zero
      pf2 = refl
    in
      trans pf1 pf2
  -- In the successor case we similarly apply induction-succ
  -- underneath from-ℕ and then recurse on the previous proof.
  succ-lem
    : ∀ {N} {{_ : EqRel N}} {{peano : Peano N}} (prev : N)
    → from-ℕ (induction (λ _ → ℕ) prev Zero Succ) ≡ prev
    → from-ℕ (induction (λ _ → ℕ) (succ prev) Zero Succ) ≡ succ prev
  succ-lem prev pf =
    let
      pf1 : from-ℕ (induction (λ _ → ℕ) (succ prev) Zero Succ)
          ≡ from-ℕ (Succ (induction (λ _ → ℕ) prev Zero Succ))
      pf1 = cong from-ℕ (induction-succ (λ _ → ℕ) prev Zero Succ)

      pf2 : from-ℕ (Succ (induction (λ _ → ℕ) prev Zero Succ)) ≡ (succ prev)
      pf2 = cong succ pf
    in
      trans pf1 pf2

  prop-eq
    : ∀ {N} {{_ : EqRel N}} {{peano : Peano N}}
    → from-ℕ (to-ℕ n) ≡ n
  prop-eq =
      induction
     -- we use induction on the principle
     -- we are trying to show with the above
     -- lemmas.
        (λ n → from-ℕ (to-ℕ  n) ≡ n)
        n
        zero-lem
        (λ {prev} → succ-lem prev)
```

This shows that any two types which satisfy the Peano axioms are equivalent in
the sense that there are maps between them which form an isomorphism up to equivalence.

This is quite interesting as it stands but we might wonder if there is a more direct
characterization of the natural numbers? After all, our original definition as a
recursive algebraic data type seems to give a perfectly good specification of what
the natural numbers _are_. Let us turn to a characterization of $\mathbb{N}$ given
by Lawvere.

We define the category of discrete dynamical systems, whose:

  - Objects are sets $X$ equipped with a starting point $x_0 \in X$ and a
    self-map $f : X \rightarrow X$.
  - Morphisms are functions $\phi : X \rightarrow Y$ which take basepoint to basepoint
    and which commute with the self-map:
    $$
\begin{array}{lll}
X          & \xrightarrow{\phi} & Y      \\
\downarrow &             & \downarrow    \\
X          & \xrightarrow{\phi} & Y      \\
\end{array}
$$


  Lawvere then observed that the natural numbers are the initial object in the category
of discrete dynamical systems. In other words, every other dynamical system receives
a _unique_ map from the discrete dynamical system
$\left( \mathbb{N}\; , \; 0 : \mathbb{N}\; ,\; \mathrm{s}\; : \; \mathbb{N} \rightarrow \mathbb{N}\right)$.

Let us phrase this idea in terms of language more familiar to functional programmers. First define a "pattern functor" for $\mathbb{N}$:
```agda
data NatP (r : Set) : Set where
  ZeroP : NatP r
  SuccP : r → NatP r
```
This has the same shape as $\mathbb{N}$ but we leave the recursion open (this same pattern
of open recursion is the animating idea behind [recursion schemes](https://hackage.haskell.org/package/recursion-schemes)).
We can show that this is a functor (we don't worry about the functor laws):
```agda
record Functor (F : Set → Set) : Set₁ where
  constructor Func
  field
    Arr : ∀ {A B : Set} → (f : A → B) → F A → F B

open Functor {{...}} public

instance
  NatP-Functor : Functor NatP
  NatP-Functor = Func map
    where
    map : ∀ {A} {B} → (A → B) → NatP A → NatP B
    map f ZeroP     = ZeroP
    map f (SuccP x) = SuccP (f x)
```

Functional programmers might recognise that the discrete dynamical systems discussed above are
in fact $\mathrm{F}$-algebras for this pattern functor, which we define as follows:
```agda
record Alg (F : Set → Set) (A : Set) : Set where
  field
    μ : F A → A
open Alg {{...}} public
```
In particular if we define discrete dynamical systems:
```agda
record Dyn (A : Set) : Set where
  constructor D
  field
    basepoint : A
    self-map  : A → A
```
then we can show then any dynamical system gives rise to an algebra:
```agda
from-Dyn : ∀ {A : Set} → Dyn A → Alg NatP A
from-Dyn {A} (D basepoint self-map) = record { μ = alg }
  where
  alg : NatP A → A
  alg ZeroP     = basepoint
  alg (SuccP a) = self-map a
```

and we leave as an exercise to show that there is an isomorphism between $\mathrm{NatP}$
algebra structures on $\mathrm{A}$ and discrete dynamical system structures (an observation
we can upgrade to an isomorphism between the respective categories).

Let's give the algebra structure for $\mathbb{N}$:
```agda
instance
  ℕ-Alg : Alg NatP ℕ
  ℕ-Alg = record { μ = alg }
    where
    alg : NatP ℕ → ℕ
    alg ZeroP     = Zero
    alg (SuccP x) = Succ x
```

Just as in Lawvere's characterization, we now wish to show that this algebra is initial.
For that, we first have to define maps between algebras. Suppose $\mathrm{A}$ and $\mathrm{B}$ are
$\mathrm{F}$-algebras. We then say a map $m : \mathrm{A} \rightarrow \mathrm{B}$ is an
$\mathrm{F}$-algebra homomorphism when the following diagram commutes (where the downward
arrows are the algebra maps):

$$
\begin{array}{lll}
F A          & \xrightarrow{F m} & F B  \\
\downarrow &             & \downarrow   \\
A          & \xrightarrow{m} & B        \\
\end{array}
$$

In other words the algebra map commutes with the map in question, or in equations:
$$
f \circ \mu_{A} \equiv \mu_{B} \circ (F f)
$$

```agda
record Alg-Homo (A B : Set) {F : Set → Set} {{f : Functor F}}
  (FA : Alg F A) (FB : Alg F B) : Set₁ where
  constructor AlgHom
  field
    →-fun  : A → B
    μ-comm
      : ∀ (fa : F A)
      → →-fun (Alg.μ FA fa) ≡ (Alg.μ FB) (Arr →-fun fa)
```

Now we can try to prove that the algebra structure on $\mathbb{N}$ is initial. We first show there
is an induced map to every other $\mathrm{F}$-$\mathrm{algebra}$:
```agda
ℕ-weakly-initial
  : ∀ {A : Set}
  → {{FA : Alg NatP A}}
  → Alg-Homo ℕ A ℕ-Alg FA
ℕ-weakly-initial {A} = AlgH init-ℕ law
  where
  init-ℕ : ℕ → A
  init-ℕ Zero     = μ ZeroP
  init-ℕ (Succ n) = μ (SuccP (init-ℕ n))

  law : (nP : NatP ℕ) → init-ℕ (μ nP) ≡ μ (Arr init-ℕ nP)
  law ZeroP     = refl
  law (SuccP x) = refl
```

We define the map via the structure of the algebra. $\mathrm{Zero}$ maps to the basepoint of $\mathrm{A}$
and for the successor we apply the self-map and then recurse. For the $\mu$-$\mathrm{law}$ we
first case split as this is how $\mathrm{init}$-$\mathbb{N}$ is defined. At this point we
can see that the laws hold definitionally from how we have defined the map.

We can then show uniqueness:
```agda
ℕ-init-uniq :
  ∀ {A : Set}
  → {{FA : Alg NatP A}}
  → (alg-hom : Alg-Homo ℕ A ℕ-Alg FA)
  → ∀ (n : ℕ)
  → (Alg-Homo.→-fun alg-hom n)
  ≡ (Alg-Homo.→-fun (ℕ-weakly-initial {{FA}}) n)
ℕ-init-uniq alg-hom Zero = μ-comm ZeroP
  where
    open Alg-Homo alg-hom public
ℕ-init-uniq {{FA}} alg-hom (Succ n) =
  let
    pf1 :  →-fun (Succ n) ≡ μ (SuccP (→-fun n))
    pf1 = μ-comm (SuccP n)

    pf2 :  μ (SuccP (→-fun n)) ≡ μ (SuccP (Alg-Homo.→-fun ℕ-weakly-initial n))
    pf2 = cong (μ ∘ SuccP) (ℕ-init-uniq alg-hom n)
  in
    trans pf1 pf2
  where
    open Alg-Homo alg-hom public
```

We don't infer algebra homomorphisms and so we need to pass them as arguments and
open the various records to bring their fields into scope.
In the first case we have the following goal:
```agda
→-fun 0 ≡ μ ZeroP
```
We note that this is definitionally equivalent to showing:
```agda
→-fun (μ ZeroP) ≡ μ (Arr →-fun ZeroP)
```
and this is the $\mu$-$\mathrm{comm}$ law!

In the successor case we have to prove:
```agda
→-fun (Succ n) ≡ μ (SuccP (Alg-Homo.→-fun ℕ-weakly-initial n))
```

We use a similar observation as above to first rewrite the left-hand-side using the
$\mu$-$\mathrm{comm}$ law. At that point (as before) we can rewrite the inner part by recursion.

One nice thing about this characterization (beyond being much simpler to reason about!) is that
the same idea of initial algebra semantics works just as well for any algebraic data type.
For example we can do exactly the same for lists as we have for $\mathbb{N}$:
```agda
data ListP (A : Set) (r : Set) : Set where
  NilP  : ListP A r
  ConsP : A → r → ListP A r

data List (A : Set) : Set where
  Nil  : List A
  Cons : A → List A → List A

instance
  ListP-Functor : ∀ {A} →  Functor (ListP A)
  ListP-Functor {A} = Func map-L
    where
    map-L : ∀ {B} {C} → (B → C) → ListP A B → ListP A C
    map-L f NilP = NilP
    map-L f (ConsP a b) = ConsP a (f b)


record HasFold (A : Set) (B : Set) : Set₁ where
  constructor F
  field
    initial  : B
    operator : A → B → B

fromHasFold : ∀ {A B : Set} →  HasFold A B → Alg (ListP A) B
fromHasFold {A} {B} (F initial operator) = record { μ = alg }
  where
  alg : ListP A B → B
  alg NilP = initial
  alg (ConsP a b) = operator a b

toHasFold : ∀ {A B : Set} → Alg (ListP A) B → HasFold A B
toHasFold {A} {B} record { μ = μ } = F init op
  where
  init : B
  init = μ NilP

  op : A → B → B
  op a b = μ (ConsP a b)

instance
  List-Alg : ∀ {A} → Alg (ListP A) (List A)
  List-Alg {A} = record { μ = alg }
    where
    alg : ListP A (List A) → List A
    alg NilP = Nil
    alg (ConsP a as) = Cons a as

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr op init Nil         = init
foldr op init (Cons a as) = op a (foldr op init as)

foldr-Alg : ∀ {A B : Set}
  → {{FA : Alg (ListP A) B}}
  → List A → B
foldr-Alg = foldr (λ a b → μ (ConsP a b)) (μ NilP)

List-weakly-initial
  : ∀ {A B : Set}
  → {{FA : Alg (ListP A) B}}
  → Alg-Homo (List A) B (List-Alg {A}) FA
List-weakly-initial {A} {B} = AlgHom foldr-Alg law
  where

  law : (fa : ListP A (List A)) →
    foldr (λ a b → μ (ConsP a b)) (μ NilP) (μ fa)
      ≡
    μ (Arr (foldr (λ a b → μ (ConsP a b)) (μ NilP)) fa)
  law NilP         = refl
  law (ConsP a as) = refl
```
and we see that out of initiality naturally comes $\mathrm{foldr}$!
$\mathrm{F}$-algebra semantics give rise to _recursion principles_!
The essence of $\mathbb{N}$, from this point of view,
lies in its recursive structure. After all, in a dependently-typed setting recursion and induction are
really two sides of the same coin.


Thank you for reading! The full code for these examples is available
[here](https://github.com/Boarders/agda-peano/blob/master/Peano.agda). Hopefully
this has given some ideas for how we can explore mathematical ideas in Agda leveraging
the typechecker to guide our proofs. Feel free to contact me
[here](mailto:callan.mcgill@gmail.com) with questions, thoughts, ideas, or all of the above.

<i>With warmest thanks to Sam Derbyshire, Reed Mullanix, Alixandra Prybyla and Shon Feder for their valuable feedback.</i>
