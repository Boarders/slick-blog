---
title: "The Halting Problem (part 2)"
author: Callan McGill
date: "Dec 7, 2020"
tags: [Halting Problem, Agda]
description: Exploring the Halting problem in Agda
quote: Everything is vague to a degree you do not realize till you have tried to make it precise.
quoteAuthor: Bertrand Russell

---

[Last time](https://boarders.github.io/posts/halting1.html), we showed the undecidability of the
halting problem using the lambda calculus as our model of computation.
In this post, we are going to take that argument and formalise it in Agda.
To begin, let's grab some imports:

```agda
module Halt where

open import Data.List
  using (List; []; _∷_)
open import Relation.Nullary
   using (¬_)
open import Data.Empty
  using (⊥; ⊥-elim)\
open import Data.Product
  using (Σ-syntax; _×_) renaming (_,_ to Sg)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
```

For this development we will use a typed lambda calculus essentially identical to
[PCF](https://en.wikipedia.org/wiki/Programming_Computable_Functions) (only with booleans instead
of natural numbers), as this makes the
formalisation quite tidy. In order to get
the basic semantics of the language we will closely follow the
[DeBruijn](https://plfa.github.io/DeBruijn/)
chapter from the fantastic [Programming Language Foundations in Agda](https://plfa.github.io/).

Our language will be simply-typed, having only booleans, $\mathbb{B}$, and function types:
```agda
data Type : Set where
  𝔹  :  Type
  _⇒_ : Type → Type → Type
```

We make use of intrinsically well-scoped, well-typed terms and so we use 'proof-carrying'
de-bruijn indices for variables.
In this set-up indices act both as an index into a typing context and as a _proof_ that
the variable is well-typed in the current context.

```agda
-- A typing context is represented as a list of types.
Con : Set
Con = List Type

-- We use ∙ for the empty context.
∙ : Con
∙ = []

-- _,_ extends contexts to the right as is typical in type theory
-- and so we use a view the list in reverse order.
infixl 6 _,_
_,_ : Con → Type → Con
_,_ con ty = ty ∷ con

-- A type for de-bruijn indices into a context. The index represents
-- a pointer into a context along with a proof that the
-- context contains the given type at that position.
-- For example, given the context:
--
--   Γ = 𝔹, 𝔹 ⇒ 𝔹
--
-- we have:
--    z   : 𝔹 ⇒ 𝔹 ∈ Γ
--    s z : 𝔹 ∈ Γ
infix 4 _∈_
data _∈_  (t : Type) : Con → Set where
  z : ∀ {ts} → t ∈ (t ∷ ts)
  s : ∀ {r} {ts} → (t ∈ ts) → t ∈ (r ∷ ts)
```

We can now define the terms of our language. Here `Expr Γ ty` denotes a term of type `ty` in the typing context `Γ`:
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

The names are largely self-explanatory but we observe that we use `bool`
for the conditional instead of `if`. It is also worth noting that
as `lam` and `fix` are binding forms, they take arguments
with contexts extended by the type of the bound variable.


We give an identical approach to variable substitution as in [PLFA](https://plfa.github.io/)
by first defining context extension and variable renaming:

```agda
ext : ∀ {Γ Δ : Con}
  → (∀ {ty : Type} → ty ∈ Γ → ty ∈ Δ)
  → (∀ {ty tyB : Type} → ty ∈ Γ , tyB → ty ∈ Δ , tyB)
ext ρ z = z             -- if it is the newly bound variable
                        -- we simply return it.
ext ρ (s x) = s (ρ x)   -- otherwise we perform the substitution
                        -- and take successor.

-- rename is defined by structural recursion, extending the renaming
-- at binding sites and applying it to variables.
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

Here,  a variable renaming, `(∀ {ty} → ty ∈ Γ → ty ∈ Δ)`, simply takes an index
into one context of a particular type and gives an index into a different
context of the same type.

We extend this from variable renaming to arbitrary context morphisms:

```agda
-- extend a context morphism with a new bound variable.
exts : ∀ {Γ Δ}
  → (∀ {ty} →  ty ∈ Γ → Expr Δ ty)
  → (∀ {ty tyB} → ty ∈ (Γ , tyB) → Expr (Δ , tyB) ty)
exts ρ z     = var z
exts ρ (s x) = rename s (ρ x)

-- Perform structural recursion, extending the context morphism at
-- binding sites and applying it to variables.
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

This gives parallel substitution across an entire context `Γ` to 
another context `Δ`. Intuitively we take an open term with variables
of type `Γ` and replace them with terms of type `Δ`. To make
this clearer let us give an example:
```
-- Our example context has three 𝔹 variables. 
con₁ : Con
con₁ = ∙ , 𝔹 , 𝔹 , 𝔹

-- Our open term is then, roughly, "if x then y else z" where
-- x : 𝔹, y : 𝔹 and z : 𝔹
term₁ : Expr con₁ 𝔹
term₁ = bool (var z) (var (s z)) (var (s (s z)))

-- For those variables we can then substitute closed terms:
sub₁ : ∀ {ty} → ty ∈ con₁ → Expr ∙ ty
sub₁ z = tt
sub₁ (s z) = ff
sub₁ (s (s z)) = tt

-- Our parallel substitution then works as expected:
subst-term₁ : subst sub₁ term₁ ≡ bool tt ff tt
subst-term₁ = refl
```

From parallel substitution, it is easy for us to define ordinary substitution 
of a single binding variable. We define the context morphism that decrements all
variables in $\Gamma$ and returns the substituting term for the initial variable:

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

Again, let's give a simple example:
```agda
-- This time our context has n : 𝔹 ⇒ 𝔹 and b : 𝔹
con₂  : Con
con₂  = ∙ , 𝔹 ⇒ 𝔹 , 𝔹

-- Our open term is n applied to b:
term₂  : Expr con₂ 𝔹
term₂  = app (var (s z)) (var z)

-- Once we substitute b ↦ tt we have the smaller typing
-- context: 
--   ∙ , 𝔹 ⇒ 𝔹 
-- and so we decrement the n variable.
subst-term₂ : term₂ [ tt ] ≡ app (var z) tt
subst-term₂ = refl
```

Next we can define the values of our language - that is, those terms which terminating programs
return. Along with values we define the small-step operational semantics of the language, showing
how reduction takes place:
```agda
data Value : ∀ {Γ} {ty} → Expr Γ ty → Set where
-- lambdas are values
  V-↦ : ∀ {Γ } {ty tyB} {body : Expr (Γ , tyB) ty}
    → Value (lam body)
-- tt is a value
  V-tt : ∀ {Γ} → Value {Γ} {𝔹} tt
-- ff is a value
  V-ff : ∀ {Γ} → Value {Γ} {𝔹} ff

data _↓_ : ∀ {Γ} {ty} → Expr Γ ty -> Expr Γ ty -> Set where
-- reduce on the left in an application.
  l-↓ : ∀ {Γ ty tyB} {L L' : Expr Γ (ty ⇒ tyB)} {R : Expr Γ ty}
    -> L ↓ L'
    -> app L R ↓ app L' R
-- reduce on the right so long as we have already reduced the left
-- argument to a value.
  r-↓ : ∀ {Γ ty tyB} {VL : Expr Γ (ty ⇒ tyB)} { R R' : Expr Γ ty}
    -> (Value VL)
    -> R ↓ R'
    -> app VL R ↓ app VL R'

-- Perform beta-reduction.
  β-↓ : ∀ {Γ} {ty tyB} {N : Expr (Γ , tyB) ty} {V : Expr Γ tyB}
    -> (app (lam N) V) ↓ (N [ V ])

-- reduce boolean in a conditional.
  if-↓ : ∀ {Γ} {ty} {b b' : Expr Γ 𝔹} {th el : Expr Γ ty}
    -> b ↓ b'
    -> (bool b th el) ↓ (bool b' th el)

-- reduce conditional to true branch.
  if-tt-↓ : ∀ {Γ} {ty} {th el : Expr Γ ty}
    -> (bool tt th el) ↓ th

-- reduce conditional to false branch.
  if-ff-↓ : ∀ {Γ} {ty} {th el : Expr Γ ty}
    -> (bool ff th el) ↓ el

-- recursively substitute fix expression.
  fix-↓ : ∀ {Γ ty} {expr : Expr (Γ , ty) ty}
    -> fix expr ↓ (expr [ fix expr ])
```
We use (something close to) a call-by-name semantics and so don't necessarily
reduce arguments to values before performing $\beta$-reduction.
We also fix a leftmost evaluation order
for applications reducing the left argument to a value before the right argument.
We extend this relation to its reflective, transitive closure - the stepping relation -
that one expression reduces, in some number of steps, to another.

```agda
data _⇓_ : ∀ {Γ ty} → Expr Γ ty → Expr Γ ty → Set where
-- reflexivity
  _∎ : ∀ {Γ ty} (M : Expr Γ ty)
    → M ⇓ M
-- transitivity
  _→⟨_⟩_ : ∀ {Γ ty} (L : Expr Γ ty) {M N : Expr Γ ty}
    → L ↓ M
    → M ⇓ N
    → L ⇓ N
```
For later use we note, as one might expect, that values,
as we have defined them, only reduce to themselves:
```agda
⇓-val : ∀ {Γ a} {e e' : Expr Γ a} → Value e → e ⇓ e' → e' ≡ e
⇓-val val   (_ ∎) = refl
-- In the cases where we have a transitive step Agda will
-- produce an absurd pattern as none of the reduction
-- rules apply.
⇓-val V-↦  (_ →⟨ () ⟩ st)
⇓-val V-tt (_ →⟨ () ⟩ st)
⇓-val V-ff (_ →⟨ () ⟩ st)
```

Now let us think about our $\mathbf{HALT}$ term from last time. We define the notion of
halting by stating the existence of both a value and a series of reduction steps to that value.
We encode that as follows:

```agda
data Halt {Γ a} (e :  Expr Γ a) : Set where
  halts : ∀ {v : Expr Γ a} → (Value v) → (e ⇓ v) → Halt e
```

We are now in the position to postulate the existence of a `halt`
function with the expected properties:
```
postulate
  halt     : ∀ {Γ} {a} → Expr Γ (a ⇒ 𝔹)
-- halt is a closed term
  halt-sub :
    ∀ {Γ Δ} {a}
    → (ρ : ∀ {ty} → ty ∈ Γ → Expr Δ ty)
    → subst {Γ} {Δ} ρ (halt {Γ} {a}) ≡ halt {Δ}
  halt-ret :
    ∀ {Γ} {ty}
    (e : Expr Γ ty) → app halt e ⇓ tt ⊎ app halt e ⇓ ff
  halt-tt  :
    ∀ {Γ ty}
    (e : Expr Γ ty) → app halt e ⇓ tt → Halt e
  halt-ff :
    ∀ {Γ ty}
    (e : Expr Γ ty) → app halt e ⇓ ff → ¬ Halt e
```

We assume we have a function `halt` that takes an argument of any type
(in the meta-language, agda, since our language doesn't itself have polymorphism) and returns a bool.
That this function applies to terms of any type is irrelevant to the argument we give here.
This would work just as well were we to simply use `𝔹`.

We also assume that it is decidable that halt always
returns `tt` or `ff`. Furthermore, the terms `halt-tt` and
`halt-ff` encode our assumptions regarding applying the `halt` function -
if it returns `tt`, then the term is normalizing
and conversely, if it returns `ff`, then it is non-normalizing.


We can now define our three terms from last time:

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

At this point we would like to use `halt-ret` on `fix-problem` but upon reflection we
see that last time's argument was a little loose. We showed that if
`halt fix-problem` is `true` then `fix-problem` reduces to `bot` but this actually isn't
enough, by itself, to get a contradiction. What we need to know is that if a term reduces
to `bot` then no other reduction sequence halts.

Stated as a general lemma:
```agda
halt-⊥ :
  ∀ {Γ ty} {e1 e2 : Expr Γ ty}
  → e1 ⇓ e2 → ¬ (Halt e2) → ¬ (Halt e1)
```
In order to prove this, we would like to use the following: if `e1` steps to a value
then there exists some reduction sequence where `e2` also steps to that same value.
This follows from the more general property of confluence:

**Definition [Confluence]**: A reduction relation $\rightarrow$ on a set $\mathcal{T}$ is confluent
if for any $e1, e2, e3 \in \mathcal{T}$ there exists an $e4$ such that the following diagram
commutes:
    $$
    \require{AMScd}
    \begin{CD}
    e1     @>>>  e2\\
    @VVV        @VV*V\\
    e3     @>*>>  e4
    \end{CD}
$$
Here $\xrightarrow{*}$ denotes the reflective, transitive closure of $\rightarrow$.

It would be outside of the scope of this post to prove confluence but it is a well-known
result (and one which I will blog about in the future) that the lambda calculus is
confluent. As such, we allow ourselves to assume it as a postulate:
```agda
postulate
  confluence
    : ∀ {Γ} {a}
    → {e e1 e2 : Expr Γ a}
    → e ⇓ e1 → e ⇓ e2
    → Σ[ e3 ∈ Expr Γ a ] (e1 ⇓ e3) × (e2 ⇓ e3)
```

In the above we make use of Agda's sigma syntax. A term of the form
`Σ[ x ∈ A ] P` is a convenient syntax agda offers for the dependent sum,
traditionally written something like $\Sigma_{x \in A} P$.
Using confluence, it is now easy to prove that if a term
halts at a value then no matter which reduction steps we take to some other
term we will still be able to reduce to the same value:
```agda
⇓-val-uniq
  : ∀ {Γ ty} {e e' v : Expr Γ ty}
  → Value v → e ⇓ v → e ⇓ e' → e' ⇓ v
⇓-val-uniq pf e⇓v e⇓e' with confluence e⇓v e⇓e'
... | Sg e3 (Sg v⇓e3 e'⇓e3) with ⇓-val pf v⇓e3
... | refl = e'⇓e3
```
From this, we can conclude the "head-expansion" property we wanted of non-termination:
```agda
halt-⊥
  : ∀ {Γ ty} {e1 e2 : Expr Γ ty}
  → e1 ⇓ e2 → ¬ (Halt e2) → ¬ (Halt e1)
halt-⊥ e1⇓e2 e2-⊥ (halts v-e1 st) with ⇓-val-uniq v-e1 st e1⇓e2
... | e2⇓v = e2-⊥ (halts v-e1 e2⇓v)
```

First, it is easy for us to show (recursively) that `bot` does not halt:
```agda
bot-non-term : ∀ {Γ ty} →  ¬ (Halt {Γ} {ty} bot)
bot-non-term (halts v (.(fix (var z)) →⟨ fix-↓ ⟩ st))
  = bot-non-term (halts v st)
```
We can then put together `halt-⊥` and `bot-non-term` to show that any term that steps to
`bot` cannot terminate:
```agda
⇓-bot-⊥ : ∀ {Γ ty} → (e : Expr Γ ty) → e ⇓ bot → ¬ Halt e
⇓-bot-⊥ e st = halt-⊥ st bot-non-term
```

Now, we are better placed to show that if `halt fix-problem` reduces to `tt`
then `fix-problem` reduces to `bot` and thus we get a contradiction. The final general
result we will need is one that connects the big step operational semantics of Booleans
to that of our conditional function, `bool`. 

```agda
-- In both cases if there is no reduction then we directly step.
-- Otherwise we reduce the conditional and recurse on the result.
bool-stepper-tt
  : ∀ {Γ} {th el} (b : Expr Γ 𝔹)
  → b ⇓ tt → (bool {Γ} {𝔹} b th el) ⇓ th
bool-stepper-tt {_} {th} {el} .tt (.tt ∎)
  = bool tt th el →⟨ if-tt-↓ ⟩ (th ∎)
bool-stepper-tt {_} {th} {el} b (_→⟨_⟩_ .b {M} x st)
  = _→⟨_⟩_ (bool b th el) (if-↓ x) (bool-stepper-tt M st)

bool-stepper-ff
  : ∀ {Γ} {th el} (b : Expr Γ 𝔹)
  → b ⇓ ff → (bool {Γ} {𝔹} b th el) ⇓ el
bool-stepper-ff {_} {th} {el} .ff (.ff ∎)
  = bool ff th el →⟨ if-ff-↓ ⟩ (el ∎)
bool-stepper-ff {_} {th} {el} b (_→⟨_⟩_ .b {M} x st)
  = _→⟨_⟩_ (bool b th el) (if-↓ x) (bool-stepper-ff M st)
```

We are now in a position to show that `halt (fix-problem) ⇓ tt` gives rise to a
contradiction which we do in a number of simple steps:
```agda
-- First, we show that there is only a single way to reduce
-- fix-problem since only the fix rule applies.
-- In order to reduce fix-problem to what we want
-- we have to know that:
--
--   problem [ fix-problem ] ≡ bool (app halt fix-problem) bot tt
--
-- In order for this to be the case we need that:
--
--     app (halt [ fix-problem ]) (sub fix-problem z)
--   ≡ app halt fix-problem
--
-- and so we need that halt is a closed term. That is precisely what
-- halt-sub gives us:
fp-step1
   : ∀ {Γ} {e : Expr Γ 𝔹}
   → (fix-problem {Γ}) ↓ e
   → e ≡ bool (app halt fix-problem) bot tt
fp-step1 {Γ} fix-↓
  rewrite (halt-sub {Γ , 𝔹} {Γ} {𝔹} (sub {Γ} fix-problem))
  = refl

-- Here we have a small lemma that we can replace
-- equal values in the stepping relation
≡-↓
  : ∀ {Γ} {e e' e'' : Expr Γ 𝔹}
  → e ↓ e'
  → e' ≡ e''
  → e ↓ e''
≡-↓ e↓e' refl = e↓e'

-- We then make use of this fact and step 1 to show
-- that fix-problem steps as we expect:
fp-step2
   : ∀ {Γ}
   → (fix-problem {Γ}) ↓ (bool (app halt (fix-problem)) bot tt)
fp-step2 {Γ} =
  ≡-↓ (fix-↓ {Γ} {𝔹} {problem}) (fp-step1 (fix-↓ {Γ} {𝔹} {problem}))

-- In the next two steps we then use our assumption and the
-- big step lemma to derive a contradiction:
fp-step3
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ tt
   → (bool (app (halt {Γ}) fix-problem) bot tt) ⇓ bot
fp-step3 ⇓-tt = bool-stepper-tt _  ⇓-tt

fp-step4
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ tt
   → (fix-problem {Γ}) ⇓ bot
fp-step4 {Γ} ⇓-tt = fix-problem →⟨ fp-step2 ⟩ fp-step3 ⇓-tt
```
The other half of the argument, assuming `halt (fix-problem) ⇓ ff`, is quite a bit simpler.
To prove halting, we only need to exhibit some particular sequence of reductions:
```agda
fp-step5
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ ff
   → (bool (app (halt {Γ}) fix-problem) bot tt) ⇓ tt
fp-step5 ⇓-ff = bool-stepper-ff _ ⇓-ff

-- We make use of our substition lemma (fp-step2) to
-- show under this assumption that fix-problem big
-- steps to tt.
fp-step6
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ ff
   → fix-problem ⇓ tt
fp-step6 ⇓-ff = fix-problem →⟨ fp-step2 ⟩ fp-step5 ⇓-ff
```

Finally, let's package up these results into their respective contradictions:

```agda
fix-problem-tt
  : ∀ {Γ}
  → (app (halt {Γ}) fix-problem) ⇓ tt
  → Halt {Γ} fix-problem → ⊥
fix-problem-tt ⇓-tt h = ⇓-bot-⊥ _ (fp-step4 ⇓-tt) h

fix-problem-ff
  : ∀ {Γ}
    → (app (halt {Γ}) fix-problem) ⇓ ff
    → (¬ Halt {Γ} fix-problem) → ⊥
fix-problem-ff ⇓-ff ¬h = ¬h (halts V-tt (fp-step6 ⇓-ff))
```

and put everything together:
```agda
halting : ⊥
halting with halt-ret {nil} fix-problem
halting | inj₁ ⇓tt  = fix-problem-tt ⇓tt (halt-tt fix-problem ⇓tt)
halting | inj₂ ⇓ff  = fix-problem-ff ⇓ff (halt-ff fix-problem ⇓ff)
```


Hopefully this post has given an approachable account of formalising one of the
central results in computability theory. We hope to have also demonstrated, from
a programming language theory perspective, some of the advantages of the lambda calculus
as a foundational theory of computation (over, for example, Turing machines). 
Thank you for reading! The full code for this proof
 is available [here](https://github.com/Boarders/agda-halting).

<i>With warmest thanks to Alixandra Prybyla and Sam Derbyshire for their valuable feedback.</i>
