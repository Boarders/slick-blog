---
title: "The Halting Problem (part 2)"
author: Callan McGill
date: "Oct 10, 2020"
tags: [Halting Problem, Agda]
description: Exploring the Halting problem in Agda
quote: Everything is vague to a degree you do not realize till you have tried to make it precise.
quoteAuthor: Bertrand Russell

---

In this post we are going to take the argument from [last time]( TO DO ) and formalise it in Agda.
As always, let's grab some imports:

```agda
module Halt where

open import Data.List
  using (List; []; _∷_)
open import Relation.Nullary
   using (¬_)
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Product
  using (Σ-syntax; _×_) renaming (_,_ to Sg)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
```

For this development we will use a typed lambda calculus essentially identical to
[PCF](https://en.wikipedia.org/wiki/Programming_Computable_Functions) (only with booleans over
natural numbers), as this makes the
formalisation quite tidy. In order to get
the basic semantics of the language we will closely follow the
[DeBruijn](https://plfa.github.io/DeBruijn/)
chapter from the fantastic [Programming Language Foundations in Agda](https://plfa.github.io/).

Our language will be simply-typed, having just booleans, $\mathbb{B}$, and function types:
```agda
data Type : Set where
  𝔹  :  Type
  _⇒_ : Type → Type → Type
```

We make use of intrinsically well-scoped, well-typed terms and so we use proof-carrying
de-bruijn indices for variables.
In this set-up indices act both as an index into a typing context and as a _proof_ that
the variable is well-typed in the current context.

```agda
-- A typing context is a represented as a list of types.
Con : Set
Con = List Type

-- We use nil for the empty context.
nil : Con
nil = []

-- _,_ extends contexts to the right.
infixl 6 _,_
_,_ : Con → Type → Con
_,_ con ty = ty ∷ con

-- A type for de-bruijn indices into a context. The index represents
-- a pointer into a context along with a proof that the
-- context contains the given type at that position.
-- For example given the context:
--
--   Γ = 𝔹, 𝔹 ⇒ 𝔹
--
-- we have:
--   - z   : 𝔹 ⇒ 𝔹 ∈ Γ
--   - s z : 𝔹 ∈ Γ
infix 4 _∈_
data _∈_  (t : Type) : Con → Set where
  z : ∀ {ts} → t ∈ (t ∷ ts)
  s : ∀ {r} {ts} → (t ∈ ts) → t ∈ (r ∷ ts)
```

We can now define the terms of our language. Here $\mathrm{Expr}\;\Gamma\; \mathrm{a}$ denotes a term of type $\mathrm{a}$ in the typing context $\Gamma$:
```agda
data Expr (Γ : Con) : Type → Set where
  var  : ∀ {a : Type} → a ∈ Γ → Expr Γ a
  app  : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  lam  : ∀ {a b} → Expr (Γ, a) b → Expr Γ (a ⇒ b)
  tt   : Expr Γ 𝔹
  ff   : Expr Γ 𝔹
  bool : ∀ {a} → Expr Γ 𝔹 → Expr Γ a → Expr Γ a → Expr Γ a
  fix  : ∀ {a} → Expr (Γ , a) a → Expr Γ a
```

The names are largely self-explanatory but we explicitly note that we are
using $\mathrm{bool}$ for the conditional. It is also worth pointing out that
as both $\mathrm{lam}$ and $\mathrm{fix}$ are binding forms, they take arguments
with contexts extended by the type of the bound variable.


We give an identical approach to variable substitution as in PLFA by first defining context
extension and variable renaming:

```agda
ext : ∀ {Γ Δ : Con}
  → (∀ {ty : Type} → ty ∈ Γ → ty ∈ Δ)
  → (∀ {ty tyB : Type} → ty ∈ Γ , tyB → ty ∈ Δ , tyB)
ext ρ z = z             -- if it is the newly bound variable
                        -- we simply return it.
ext ρ (s x) = s (ρ x)   -- otherwise we perform the substitution 
                        -- and take successor.

-- rename is defined by structural recursion, extending the renaming
-- at binding sites and applying it when we reach variables.
rename : ∀ {Γ Δ}
  → (∀ {ty} → ty ∈ Γ → ty ∈ Δ)
  → (∀ {ty} → Expr Γ ty → Expr Δ ty)
rename ρ (var x) = var (ρ x)
rename ρ (app rator rand) = app (rename ρ rator) (rename ρ rand)
rename ρ (lam body) = lam (rename (ext ρ) body)
rename ρ tt = tt
rename ρ ff = ff
rename ρ (bool b th el) = bool (rename ρ b) (rename ρ th) (rename ρ el)
rename ρ (fix body) = fix (rename (ext ρ) body)
```

We then extend this from variable renamings to arbitrary context morphisms:

```agda
-- extend a context morphism to a context with another variable
-- bound.
exts : ∀ {Γ Δ}
  → (∀ {ty} →       ty ∈ Γ →     Expr Δ ty)
    ---------------------------------
  → (∀ {ty tyB} → ty ∈ (Γ , tyB) → Expr (Δ , tyB) ty)
exts ρ z     = var z
exts ρ (s x) = rename s (ρ x)

-- Perform structural recursion, extending the context morphism at
-- binding sites and applying it when we reach variables.
subst : ∀ {Γ Δ}
  → (∀ {ty} → ty ∈ Γ → Expr Δ ty)
  → (∀ {ty} → Expr Γ ty → Expr Δ ty)
subst ρ (var x) = ρ x
subst ρ (app rator rand) = app (subst ρ rator) (subst ρ rand)
subst ρ (lam body) = lam (subst (exts ρ) body)
subst ρ tt = tt
subst ρ ff = ff
subst ρ (bool b th el) = bool (subst ρ b) (subst ρ th) (subst ρ el)
subst ρ (fix body) = fix (subst (exts ρ) body)
```

This gives parallel substitution across an entire context $\Gamma$. From parallel
substitution it is easy for us to define ordinary
substitution of a single variable by defining a context morphism which is the
identity on $\Gamma$ and returns the term we are substituting for the first variable:
```agda
sub : ∀ {Γ} {ty tyB} → Expr Γ tyB → ty ∈ (Γ , tyB) → Expr Γ ty
sub term z   = term
sub _ (s pf) = var pf

_[_] : ∀ {Γ ty tyB}
        → Expr (Γ , tyB) ty
        → Expr Γ tyB
        → Expr Γ ty
_[_] {Γ} {ty} {tyB} body term = subst {Γ , tyB} {Γ} (sub term) body
```

Next we can define the values of our language, that is those terms which a program should
return if it terminates. Along with values we give the small-step operational semantics,
giving each possible choice of reduction that can take place within a term:
```agda
data Value : ∀ {Γ} {ty} → Expr Γ ty → Set where
  V-↦ : ∀ {Γ } {ty tyB} {body : Expr (Γ , tyB) ty }
    → Value (lam body)
  V-tt : ∀ {Γ} → Value {Γ} {𝔹} tt
  V-ff : ∀ {Γ} → Value {Γ} {𝔹} ff

data _↓_ : ∀ {Γ} {ty} → Expr Γ ty -> Expr Γ ty -> Set where

  l-↓ : ∀ {Γ ty tyB} {L L' : Expr Γ (ty ⇒ tyB)} {R : Expr Γ ty}
    -> L ↓ L'
    -> app L R ↓ app L' R

  r-↓ : ∀ {Γ ty tyB} {VL : Expr Γ (ty ⇒ tyB)} { R R' : Expr Γ ty}
    -> (Value VL)
    -> R ↓ R'
    -> app VL R ↓ app VL R'


  β-↓ : ∀ {Γ} {ty tyB} {N : Expr (Γ , tyB) ty} {V : Expr Γ tyB}
    -> (app (lam N) V) ↓ (N [ V ])

  if-↓ : ∀ {Γ} {ty} {b b' : Expr Γ 𝔹} {th el : Expr Γ ty}
    -> b ↓ b'
    -> (bool b th el) ↓ (bool b' th el)

  if-tt-↓ : ∀ {Γ} {ty} {th el : Expr Γ ty}
    -> (bool tt th el) ↓ th

  if-ff-↓ : ∀ {Γ} {ty} {th el : Expr Γ ty}
    -> (bool ff th el) ↓ el


  fix-↓ : ∀ {Γ ty} {expr : Expr (Γ , ty) ty}
    -> fix expr ↓ (expr [ fix expr ])
```
Here we a use call-by-value semantics and so we reduce arguments to values
before performing $\beta$-reduction. We also fix a leftmost evaluation order
for applications. We then extend this relation to its reflective, transitive closure
to denote the stepping relation that one expression can step to another.

```agda
data _⇓_ : ∀ {Γ ty} → Expr Γ ty → Expr Γ ty → Set where

  _∎ : ∀ {Γ ty} (M : Expr Γ ty)
    → M ⇓ M

  _→⟨_⟩_ : ∀ {Γ ty} (L : Expr Γ ty) {M N : Expr Γ ty}
    → L ↓ M
    → M ⇓ N
    → L ⇓ N
```

Now let us think about our $\mathbf{Halt}$ term from last time. We define the notion of
halting by saying an expression halts when there exists a value that it steps to.
We then postulate the existence of a $\mathrm{halt}$ function with the expected properties.

```agda
data Halt {Γ a} (e :  Expr Γ a) : Set where
  halts : ∀ {v : Expr Γ a} → (Value v) → (e ⇓ v) → Halt e

postulate
  halt     : ∀ {Γ} {a} → Expr Γ (a ⇒ 𝔹)
  halt-sub :
    ∀ {Γ Δ} {a}
    →(ρ : ∀ {ty} → ty ∈ Γ → Expr Δ ty)
    → subst {Γ} {Δ} ρ (halt {Γ} {a}) ≡ (halt {Δ})
  halt-ret : ∀ {Γ} {ty} (e : Expr Γ ty) → ((app halt e) ⇓ tt) ⊎ (app halt e ⇓ ff)
  halt-tt  : ∀ {Γ ty} (e : Expr Γ ty)   → ((app halt e) ⇓ tt) →    Halt e
  halt-ff  : ∀ {Γ ty} (e : Expr Γ ty)   → ((app halt e) ⇓ ff) → ¬ (Halt e)
```

Here we assume we have a term $\mathrm{halt}$ which has the type of a function
that takes an argument of any type and returns a bool. We assume that it is decidable that halt always
returns $\mathrm{tt}$ or $\mathrm{ff}$. Furthermore, the terms $\mathrm{halt-tt}$ and
$\mathrm{halt-ff}$ encode that if $\mathrm{halt}$ returns $\mathrm{tt}$, then the term is normalizing
and conversely, if it returns $\mathrm{ff}$, then it is non-normalizing.


We will also define our three terms from last time:

```agda
-- Since fix takes a binding term we write fix (var z)
-- instead of the term fix (lam z) we used last time.
bot : ∀ {ty Γ} → Expr Γ ty
bot = fix (var z)

problem : ∀ {Γ} → Expr (Γ , 𝔹) 𝔹
problem = bool (app halt (var z)) bot tt

fix-problem : ∀ {Γ} → Expr Γ 𝔹
fix-problem = fix problem
```

At this piont we would like to use $\mathrm{halt-ret}






Thank you for reading! The full code for these examples is available
[here](https://github.com/Boarders/agda-peano/blob/master/Peano.agda).
