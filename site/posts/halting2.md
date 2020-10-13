---
title: "The Halting Problem (part 2)"
author: Callan McGill
date: "Oct 06, 2020"
tags: [Halting Problem, Agda]
description: Exploring the Halting problem in Agda
quote: Everything is vague to a degree you do not realize till you have tried to make it precise. 
quoteAuthor: Bertrand Russell

---

Let's take the argument from [last time]( TO DO ) and formalise it in Agda. As always let's grab some imports:

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

For this development we will use a typed lambda calculus very much like [PCF](https://en.wikipedia.org/wiki/Programming_Computable_Functions) as this makes the formalisation quite tidy. In order to get
the basic properties of the language we need we will closely the 
[DeBruijn](https://plfa.github.io/DeBruijn/) 
chapter from the fantastic [Programming Language Foundations in Agda](https://plfa.github.io/).

Our language will have just $\mathbb{Booleans}$ and function types:
```agda
data Type : Set where
  𝔹  :  Type
  _⇒_ : Type → Type → Type
```

We make use of intrinsically well-scoped terms and so we use de-bruijn indices for variables
which provide a _proof_ that the variable points at some particular type:

```
-- A context is a list of types
Con = List Type

-- We use nil for the empty context
nil : Con
nil = []

infixl 6 _,_
_,_ : Con → Type → Con
_,_ con ty = ty ∷ con

-- A de-bruijn index into a context representing a proof that the context contains a given type
infix 4 _∈_
data _∈_  (t : Type) : Con → Set where
  z : ∀ {ts} → t ∈ (t ∷ ts)
  s : ∀ {r} {ts} → (t ∈ ts) → t ∈ (r ∷ ts)
```

We can now define our expression langauge:
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

We use $\mathrm{bool}$ to denote the condintional and everything else is as expected. Note
that both $\mathrm{lam}$ and $\mathrm{fix}$ bind variables and so they take an argument with
an extended context. Our terms are intrinsically well-scoped and so variables need a proof
that a type is defined in a context.



Thank you for reading! The full code for these examples is available
[here](https://github.com/Boarders/agda-peano/blob/master/Peano.agda).
