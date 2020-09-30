---
title: "Peano Axioms"
author: Callan McGill
date: "Sep 27, 2020"
tags: [Agda, Natural Numbers]
description: Explorations into the natural numbers
quote: "God made the integers; all else is the work of man."

---


  The 19th century brought about a revolution in the foundations of mathematics culminating in the Zermelo--Frankel axioms. 
This gave a foundational theory, _set theory_, within which the typical objects of mathematics could be encoded. 
Within this mileux more generally arose the axiomatic method whereby mathematical objects came to be characterized not by any particular construction one could give but by the set of axioms (or laws) which an object should satisfy. This eventually gave rise to the development of category theory as a foundational theory of mathematics characterizing objects via their universal properties.
Let us turn then to the question of characterizing the natural numbers not as a particular set but by the properties it (hopefully uniquely) satisfies. Peano gave an axiomatization stating that a set of natural numbers $\def\N{\mathsf{N}}$ $\N$ is characterized by the following:


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
    
  Let's try to formalise (with necessary adjustments along the way) this in Agda and show that any such structure is isomorphic to the natural numbers as we know them. 
We start with a few imports we will need later:

```agda
module Peano where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)
open import Function
  using (_∘_)
```

Typically in Agda (or Haskell) we define the (unary) natural numbers as follows:

```agda
data ℕ : Set where
  Zero : ℕ
  Succ : ℕ -> ℕ
```

Now out first port of call towards Peano's axioms is to formulate equivalence relations in Agda:

```agda
record Rel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    reflexivity  : ∀ {a : A} → a ≃ a
    symmetry     : ∀ {a b : A} → a ≃ b → b ≃ a
    transitivity : ∀ {a b c : A} → a ≃ b → b ≃ c → a ≃ c
```

We note that the Agda definition is slightly different from what is typical in mathematics. Rather than a (mere) subset of the diagonal we use a dependent type taking two arguments and returning what we can think of the _evidence_ that the two values are equal. The axioms this satisfies are reflexivity (that we any element is equal with itself), symmetry (that we can freely flip equalities) and transitivity (that we can compose equalities). Let us start by showing that $\mathbb{N}$, under Agda's built-in equality type $\equiv$, forms an equivalence relation. As a brief reminder let us recall how this equality type is defined for any Set:
```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```
That is to say that we can give a term $\mathrm{refl} of type $\mathrm{a} \equiv \mathrm{b}$ so long as Agda can directly compute that $\mathrm{a}$ and $\mathrm{b}$ are equal within the particular context. For example if we define addition then we can write:
```agda
_+_ : ℕ -> ℕ -> ℕ
_+_ Zero m = m
_+_ (Succ n) m = Succ (n + m)

-- allowing us to use numeric literals
{-# BUILTIN NATURAL ℕ #-} 

_ : 2 + 2 ≡ 4
_ = refl
```
and Agda can definitionally compute that these are both equal and so we can use $\mathrm{refl}$.

Let's see then that $\mathbb{N}$ is an equivlence relation under this notion of equality:

```agda
ℕ-refl : ∀ {n : ℕ} → n ≡ n
ℕ-refl = refl

ℕ-symm : ∀ {n m : ℕ} → n ≡ m → m ≡ n
ℕ-symm eq rewrite eq = refl

ℕ-trans : ∀ {m n r : ℕ} → m ≡ n → n ≡ r → m ≡ r
ℕ-trans  m≡n n≡r rewrite m≡n | n≡r = refl
```
Here we make use of Agda's rewrite mechanism. By providing an equality proof of the form $\mathrm{a} \equiv \mathrm{b}$ we can re-write all instances of the term $\mathrm{a}$ in the goal to the term $\mathrm{b}$. For example, in $\mathbb{N}\mathrm{-symm}$, we use the equality we are given as an argument to rewrite so that each appearance of $\mathrm{n}$ is replaced with $\mathrm{m}$ at which point we may provide $\mathrm{refl} : \mathrm{m} \equiv \mathrm{m}$. It is worth saying that we haven't used anything special about $\mathbb{N}$ and these same definitions would work to prove that _any_ set forms an equivalence relation under $\equiv$. We can then write an instance of Rel for $\mathbb{N}$:

```agda
open Rel {{...}} public


instance
  ≡-Nat : Rel ℕ
  _≃_          {{≡-Nat}} = _≡_
  reflexivity  {{≡-Nat}} = ℕ-refl
  symmetry     {{≡-Nat}} = ℕ-symm
  transitivity {{≡-Nat}} = ℕ-trans
```

Here we use Agda's instance arguments mechanism. We start by bringing the fields of Rel into scope for those instances which can resolved. This is essentially the equivalent to us defining functions of the form:
```agda
_≃_         : {A : Set} {{_ : Rel A}} → A → A → Set
reflexivity : {A : Set} {{_ : Rel A}} {a b : A} → (a ≃ a)
-- etc.
```
We then resolve implicit arguments ${{_ : Rel A}}$ by searching for instances we have available in scope. In particular we define an instance of Rel for $\mathbb{N}$ which means that we may use these on $\mathbb{N}$ and Agda will infer the definition we have given.

Now we can move towards giving the Peano axioms. In much the same way as equivalence relations we make use of records to encode algebraic structures and we again make necessary adjustments to account for our constructive setting:

```agda
record Peano (N : Set) {{rel : Rel N}} : Set₁ where
  field
    zero        : N
    succ        : N → N
    s-injective : forall {a b : N} → (succ a) ≃ (succ b) → a ≃ b
    zero≠succ   : forall (a : N) → zero ≃ (succ a) → ⊥
    induction   :
       ∀ (P : N → Set) (a : N)
       → (z : (P zero))
       → (s : ∀ {b : N} → P b → P (succ b))
       → P a
    induction-zero :
       ∀ (P : N → Set)
       → (z : (P zero))
       → (s : ∀ {b : N} → P b → P (succ b))
       → ((induction P zero z s) ≡ z)
    induction-succ :
       ∀ (P : N → Set) (a : N)
       → (z : (P zero))
       → (s : ∀ {b : N} → P b → P (succ b))
       → ((induction P (succ a) z s)) ≡ s (induction P a z s)
```

Several things are worth noting:

  - As indicated above we make Peano rely on an implicit instance argument so that 
    the argument $\N$ has the structure of an equivalence relation.
  - We upgrade induction from a unary predicate $\phi : \N -> \mathbb{B}$ to a dependent type
    $\mathrm{P} : \N \rightarrow \mathrm{Set}$.
  - As we will see later, we would like this upgraded principle to be able to _compute_. As such 
    we add two laws that dictate how this computation should go.
    
Let's start by proving that $\mathbb{N}$ satisfies induction:
```agda
ℕ-induction :
  ∀ (P : ℕ → Set) (a : ℕ)
  → (P Zero)
  → (∀ {b : ℕ} → (P b) → (P (Succ b)))
  → (P a)
ℕ-induction P Zero p[zero] p[succ] = p[zero]
ℕ-induction P (Succ n) p[zero] p[succ] 
  = p[succ] (ℕ-induction P n p[zero] p[succ])
```

This is much as we might expect and we can now show that $\mathbb{N}$ satisfies the Peano axioms:

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

We note in the last two cases that these rules hold by definition from how we have defined $\mathbb{N}$-$\mathrm{induction}$.

  Now, given any set satisfying the Peano axioms we would like for it to be the case that there is an isomorphism (or more precisely an _equivalence_) with $\mathbb{N}$ (as sets with equivalence relations) and so let's start by defining functions to and from $\mathbb{N}$:
  
```agda
ℕ-dep : ∀ {N : Set} → N → Set
ℕ-dep _ = ℕ

from-ℕ : ∀ {N : Set} {{_ : Rel N}} → {{ _ : Peano N }} → ℕ → N
from-ℕ {N} n = induction (λ _ -> N ) n zero succ

to-ℕ : ∀ {N : Set} {{_ : Rel N}} → {{_ : Peano N}} → N → ℕ
to-ℕ n = induction ℕ-dep n zero succ
```

Pleasantly both definitions are essentially identical using instance resolution to determine the relevant inducton principle. We provide ourselves with $\mathbb{N}$-$\mathrm{dep}$ as this will save us some time in the proofs to follow. Let us see how to prove that these form equivalences:
```agda
to∘from : 
  ∀ {N : Set} {{ _ : Rel N }} → {{peano : Peano N}} → (n : ℕ) →
    to-ℕ {N} (from-ℕ n) ≡ n
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
peano : Peano N   (not in scope, instance)
_     : Rel N   (instance)
N     : Set   (not in scope)

```

We can see that in order for $\mathbb{N}$-$\mathrm{induction}$ to make progress we need to split
on $\mathrm{n}$:
```agda
to∘from : 
  ∀ {N : Set} {{ _ : Rel N }} → {{peano : Peano N}} → (n : ℕ) →
    to-ℕ {N} (from-ℕ n) ≡ n
to∘from Zero = {!!}
to∘from (Succ n) = {!!}
```

The new goal for $\mathrm{Zero}$ is:
```terminal
Goal: Peano.induction peano (λ _ → ℕ) (Peano.zero peano) 0 Succ ≡ 0
```
This is precisely our $\mathrm{induction}$-$\mathrm{zero}$ principle! Similarly we can
now use the $\mathrm{induction}$-$\mathrm{succ}$ principle in the second case and then recurse giving us:
```agda
to∘from : 
  ∀ {N : Set} {{ _ : Rel N }} → {{peano : Peano N}} → (n : ℕ) →
    to-ℕ {N} (from-ℕ n) ≡ n
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

The slightly gnarly explicit arguments in the second case's rewrite clause are to help along the rewrite mechanism as it didn't seem to work with the less verbose alternative.

The other case (which we will not explain in the same step-by-step detail) is similarly a case of following our nose (or rather the typechecker). We first remind ourselves of some equality principles we
have imported (simplifying away level polymorphism):
```agda
-- Funtions preserve equality:
cong : {A : Set} {B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y

-- The transitivity principle for ≡
transitivity : ∀ {a b c : A} → a ≡ b → b ≡ c → a ≡ c
```

We can now give the proof:
```agda
-- We can lift any propositional equality into an equivalence relation
liftEq : ∀ {A : Set}  {{r : Rel A}} → {a b : A} → a ≡ b → (a ≃ b)
liftEq refl = reflexivity

-- We make use of the above principle as we prove the stronger claim
-- that from-ℕ (to-ℕ n) ≡ n
from∘to : 
  ∀ {N : Set}{{ rel : Rel N}} → {{peano : Peano N}} → (n : N) →
  from-ℕ (to-ℕ n) ≃ n
from∘to n = 
  let
    prop-eq : from-ℕ (to-ℕ n) ≡ n
    prop-eq =
      induction
     -- we use induction on the claim we are trying to prove.
        (λ n → from-ℕ (to-ℕ  n) ≡ n)
        n 
        zero-lem
        (λ {prev} → succ-lem prev )
  in
 -- We then lift the equality from ≡ to ≃
    liftEq prop-eq
  where
  -- In the zero case we apply inducton-zero underneath from from-ℕ
  zero-lem 
    : ∀ {N} {{_ : Rel N}} {{peano : Peano N}}
    → from-ℕ {{_}} {{peano}} (induction (ℕ-dep {N}) zero Zero Succ)
        ≡ zero
  zero-lem {N} =
    let
      pf1 : from-ℕ (induction (ℕ-dep {N}) zero Zero Succ) ≡ from-ℕ Zero
      pf1 = cong from-ℕ (induction-zero ℕ-dep Zero Succ)

      pf2 : from-ℕ  Zero ≡ zero
      pf2 = refl
    in
      trans pf1 pf2
  -- In the successor case we similarly inducton-succ underneath from from-ℕ
  -- and then recursely use the previous proof.
  succ-lem 
    : ∀ {N} {{_ : Rel N}} {{peano : Peano N}} (prev : N)
    → from-ℕ (induction ℕ-dep prev Zero Succ) ≡ prev 
    → from-ℕ (induction (ℕ-dep {N}) (succ prev) Zero Succ) ≡ succ prev
  succ-lem prev pf = 
    let
      pf1 : from-ℕ (induction ℕ-dep (succ prev) Zero Succ)
          ≡ from-ℕ (Succ (induction ℕ-dep prev Zero Succ))
      pf1 = cong (from-ℕ) (induction-succ ℕ-dep prev Zero Succ)

      pf2 : from-ℕ (Succ (induction ℕ-dep prev Zero Succ)) ≡ (succ prev)
      pf2 = cong succ pf
    in 
      trans pf1 pf2
```

This shows that any two types which satisfy the Peano axioms are equivalent as setoids (sets carrying equivalence relation).

This is quite interesting as it stands but is there a more direct characterization of the natural numbers? After all, our original definition as a recursive algebraic data type seems to give a perfectly good specification of what the natural numbers are and how they can be built. Let us turn to a characterization that Lawvere gave. We define the category of dynamical systems with:
  
  - Objects given by set $X$ along with a starting point $x_0 \in X$ and a 
    self-map $f : X \rightarrow X$.
  - Morphisms are those set maps $\phi : X \rightarrow Y$ which take basepoint to basepoint
    and which commute with the self-map.
    
    
  Lawvere then characterized the natural numbers as the initial object in the category of dynamical systems. In other words every other dynamical system receives a unique map from $\(\mathbb{N}, \mathrm{z} : \mathbb{N}, \,mathrm{s}\;\; \mathbb{N} \rigtharrow \mathbb{N}$. Let us phrase things in terms of language more familiar to functional programmers. Let us define a "pattern functor":
```agda
data NatP (r : Set) : Set where
  ZeroP : NatP r
  SuccP : r → NatP r
```
and show that this is indeed a functor (we don't worry here about the functor laws):
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
    map f ZeroP = ZeroP
    map f (SuccP x) = SuccP (f x)
```

Functional programmers might recognise that the dynamical systems above are in fact 
$\mathrm{F}$-algebras for this pattern functor $\mathrm{F}$ which we can define as follows:
```agda
record Alg (F : Set → Set) (A : Set) : Set where
  constructor AlgCon
  field
    μ : F A → A
open Alg {{...}} public    
```

It is then easy for us to check that $\mathbb{N}$ is indeed an algebra for this functor:
```agda
instance
  ℕ-Alg : Alg NatP ℕ
  ℕ-Alg = record { μ = alg }
    where
    alg : NatP ℕ → ℕ
    alg ZeroP     = Zero
    alg (SuccP x) = Succ x
```

Just as in Lawvere's argument we now wish to show that this algebra is initial. First we have to define
maps between algebras. Suppose $\mathrm{A}$ and $\mathrm{B}$ are $\mathrm{F}$ algebras. We then say a map $f : \mathrm{A} \rightarrow \mathrm{B}$ is an $\mathrm{F}$-algeba homomorphism when the following diagram commutes:

$$
\begin{array}{lll}
F A          & \xrightarrow{F f} & F B  \\ 
\downarrow &             & \downarrow   \\ 
A          & \xrightarrow{f} & B         \\ 
\end{array}
$$

In other words the algebra map commutes with the map in question or in equations:

$$
f \circ \mu_{A} \equiv \mu_{B} \circ (F f)
$$

Let's define that in Agda:
```agda
record Alg-Homo 
  (A B : Set) {F : Set → Set} {{f : Functor F}} (FA : Alg F A) (FB : Alg F B) : Set₁ where
  constructor AlgH
  field
    ↓-map  : A → B
    μ-comm : ∀ (fa : F A) → ↓-map (Alg.μ FA fa) ≡ (Alg.μ FB) (Arr ↓-map fa)
```

Now we can try to prove that the algebra structure on $\mathbb{N}$ is initial. We first show there
is an induced map to every other $\mathrm{F}-algebra$:
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

  law : (na : NatP ℕ) → init-ℕ (μ na) ≡ μ (Arr init-ℕ na)
  law ZeroP     = refl
  law (SuccP x) = refl
```

We define the map via the structure of the algebra. $\mathrm{Zero}$ maps to the basepoint of $\mathrm{A}$ 
and for the successor we apply the self-map and then recurse. For the $\mu$-$\mathrm{law}$ we 
first case split as this is how $\mathrm{init}$-$\mathbb{N}$ is defined. At this point we
can see that the laws hold definitionally as this is how we have defined the map.

We can then show uniqueness:
```agda
ℕ-init-uniq : 
  ∀ {A : Set} 
  → {{FA : Alg NatP A}}
  → (alg-hom : Alg-Homo ℕ A ℕ-Alg FA)
  → ∀ (n : ℕ) 
  → (Alg-Homo.↓-map alg-hom n) ≡ (Alg-Homo.↓-map (ℕ-weakly-initial {{FA}}) n)
ℕ-init-uniq alg-hom Zero = μ-comm ZeroP
  where
    open Alg-Homo alg-hom public
ℕ-init-uniq {{FA}} alg-hom (Succ n) = 
  let
    pf1 :  ↓-map (Succ n) ≡ μ (SuccP (↓-map n))
    pf1 = μ-comm (SuccP n)

    pf2 :  μ (SuccP (↓-map n)) ≡ μ (SuccP (Alg-Homo.↓-map ℕ-weakly-initial n))
    pf2 = cong (μ ∘ SuccP) (ℕ-init-uniq alg-hom n)
  in
    trans pf1 pf2
  where
    open Alg-Homo alg-hom public
```

We don't infer algebra homomorphisms and so we need to pass each argument separately.
We note that in the first case we have the following goal:
```agda
↓-map 0 ≡ μ ZeroP
```
We note that this is definitionall equivlent to showing:
```agda
↓-map (μ ZeroP) ≡ μ (Arr ↓-map ZeroP)
```
and so this is the algebra law.

In the successor case we have to prove:
```agda
↓-map (Succ n) ≡ μ (SuccP (Alg-Homo.↓-map ℕ-weakly-initial n))
```

We use a similar observation above to first rewrite the first equaton using commutativity.
After that point we can rewrite the inner part by recursion showing the result.

One nice thing about this characterization is that initial algebra semantics works
just as well for any algebraic data type. Moreover this definition is much nicer categorically
 and allows us to define natural number objects in any cartesian closed category.


Thank you for reading! Feel free to contact me [here](mailto:callan.mcgill@gmail.com) with questions, thoughts, ideas, or all of the above. Thanks to [DRAFT READERS HERE] for providing valuable feedback.





