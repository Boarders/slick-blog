---
title: "Semantics of STLC in Agda"
author: Callan McGill
date: "Mar 20, 2026"
tags: [Agda, CCC, STLC, Category-Theory]
description: An excursion into the semantics of STLC formalized in agda
quote: The sentence 'snow is white' is true if, and only if, snow is white.
quoteAuthor: Alfred Tarski
agdaDevelopment: "STLC semantics"
publish: true

---

<div style="display:none">\(\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}}\def\a{\mathrm{a}}\def\d{\mathrm{d}}\def\f{\mathrm{f}}\def\i{\mathrm{i}} \def\w{\mathrm{w}} \def\x{\mathrm{x}} \def\y{\mathrm{y}} \def\z{\mathrm{z}} \def\n{\mathrm{n}} \def\m{\mathrm{m}} \def\p{\mathrm{p}} \def\t{\mathrm{t}} \def\a{\mathrm{a}} \def\b{\mathrm{b}} \def\c{\mathrm{c}} \def\i{\mathrm{i}} \def\j{\mathrm{j}} \def\k{\mathrm{k}} \def\A{\mathcal{A}}\def\B{\mathcal{B}}\def\C{\mathcal{C}} \def\D{\mathcal{D}}\def\E{\mathcal{E}}\def\F{\mathcal{F}} \def\G{\mathcal{G}}\def\H{\mathcal{H}} \def\Fr{\mathcal{Fr}} \def\Set{\mathcal{Set}} \def\var{\mathrm{var}}\def\proj{\operatorname{proj}}\def\lsem{\text{⟦}}\def\rsem{\text{⟧}}\newcommand{\sem}[1]{\text{⟦}#1\text{⟧}}\def\ty{\mathrel{:}}\def\defeq{\mathrel{\mathop{:}}=}\def\eval{\operatorname{eval}}\)</div>

## Motivation

In the study of formal languages (or other types of syntactical gadgets) we face two fundamental questions:

1. What, if any, is the intended or conventional _meaning_ of the language in question?
2. What general class of mathematical or formal objects does the language seek to describe?

Formal languages, in this sense, arguably first arose with Frege's work and later that of Hilbert, Russell and Whitehead etc. Hilbert was the first to define a formal language legible as what we would today call first-order Peano arithmetic.

For such a language, the intended model is, of course, the natural numbers; the language is precisely constructed to capture the essential logical principles for all arithmetical truths. The second question, that of the general class of models of first-order Peano arithmetic seems to have been a later historical consideration.
It was perhaps thought, though unstated, that such a language is _categorical_, that is to say: the language has a unique model up to (model) isomorphism. Later work of Gödel, and especially Skolem, emphasized the folly of this idea, typifying expressive first-order theories of arithmetic as necessarily giving rise to a panoply of non-standard models of arithmetic.

Whilst non-standard models in this case might strike us as especially peculiar -- models, for instance, which have some non-standard number with Gödel
number equal to a Gödel sentence of the system -- they seem much tamer to contemplate when we change our perspective to a more modern algebraic one.
For instance, let us imagine a formal language for an algebraic theory -- let us say, the language of groups -- with the intended models of the theory
precisely capturing the correct algebraic structures -- the class of all groups. An impressionistic version of such a formal language might be a kind of
type theory with judgments of the following form:

$$
   \x \ty \G , \y \ty \G  \vdash \x \cdot \y \ty \G
$$
$$
   \x \ty \G  \vdash \x^{-1} \ty \G
$$
$$
     \vdash e \ty \G
$$

Such a language would also need to have an equality judgment capturing the equational theory of groups:

$$
\frac{}{\x \ty \G \vdash \x \cdot e \equiv \x}
$$

$$
\frac{}{\x \ty \G \vdash e \cdot \x \equiv \x}
$$

$$
\frac{}{\x \ty \G \vdash \x \cdot \x^{-1} \equiv e}
$$

$$
\frac{}{\x \ty \G \vdash \x^{-1} \cdot \x \equiv e}
$$

$$
\frac{}{\x \ty \G, \y \ty \G, \z \ty \G \vdash (\x \cdot \y) \cdot \z \equiv \x \cdot (\y \cdot \z)}
$$

$$
\frac{\x \ty \G, \y \ty \G \vdash \x \equiv \y \quad \z \ty \G}{\x \ty \G, \y \ty \G, \z \ty \G \vdash \x \cdot \z \equiv \y \cdot \z}
$$

$$
\frac{\z \ty \G \quad \x \ty \G, \y \ty \G \vdash \x \equiv \y}{\x \ty \G, \y \ty \G, \z \ty \G \vdash \z \cdot \x \equiv \z \cdot \y}
$$

$$
\frac{\x \ty \G, \y \ty \G \vdash \x \equiv \y}{\x \ty \G, \y \ty \G \vdash \x^{-1} \equiv \y^{-1}}
$$

Now, in order for us to interpret this theory we need not just to interpret the symbols of the theory, but to give a semantics of each judgment, and thus
to give meaning first to contexts, and then to judgments. Here is an idea for how we might do so -- given a judgment of this form:

$$
   \x \ty \G , \y \ty \G  \vdash \x \cdot \y \ty \G
$$
which we are trying to interpret in some set $\X$, we naively interpret this as some function:
$$
  \X \times \X \rightarrow \X
$$

Similarly, given a term judgment like:

$$
   \x \ty \G , \y \ty \G, \z \ty \G  \vdash (\x \cdot \y) \cdot \z \ty \G
$$

we want to interpret this semantically as a function of the form:

$$
  \X \times \X \times \X \rightarrow \X
$$

Not wishing to get too into the weeds on this particular example, we make two observations about where such thinking leads. Firstly, this is essentially how one might arrive at the notion of a [Lawvere Theory](https://ncatlab.org/nlab/show/Lawvere+theory) -- Lawvere's abstraction of the notion of syntax and semantics. What this means in this case, roughly, is that given any word on $\n$ variables in the free group $\Fr\langle\x\_1,\ldots,x\_n\rangle$, the semantics of our theory gives an interpretation of such a word as a morphism:
$$
  \underbrace{\X \times \cdots \times \X}_{n} \rightarrow \X
$$

We can package this observation up algebraically by constructing a certain syntactic category $\mathbb{T}_{\mathrm{Grp}}$ with objects given by sets of variables, $\Gamma = \{\x\_1, \ldots, \x\_\n\}$, and morphisms between contexts $\{\x\_1, \ldots, \x\_\n\} \rightarrow \{\y\_1, \ldots, \y\_m\}$ given by an m-tuple of words in the free group on $\Gamma$: $\y_\j = \w_\j\left[x\_1,\ldots,\x_{\n}\right]$. This category has products given by the disjoint union of contexts. Condensing the above then, a model of our theory (in $\Set$) is nothing but a product-preserving functor from this _syntactic category_:
$$
  \mathrm{M} : \underbrace{\mathbb{T}_{\mathrm{Grp}} \rightarrow \Set }_{\mathrm{product\ preserving}}
$$

Secondly, we note that, in a certain sense, our theory gives rise to a _canonical model_ where we take as our set of elements in context $\Gamma = \{\x\_1, \ldots, \x\_\n\}$, precisely the equivalence class of judgments for the theory and, we take for morphisms, equivalence classes of substitutions. We won't spell out this example here as we do something similar for simply typed lambda calculus, but we will keep in mind the following takeaways:

- A semantics of a type theory might be thought of as a certain kind of algebraic theory
- This semantics comes with a canonical syntactical model of the theory which should, in some sense, be the free theory.
- Our semantics should be _sound_ for the type theory -- anything we prove in the type theory should be true for all algebraic models.
- Ideally, our semantics should also be _complete_ for the theory -- If we can prove some judgment is true for all models, then it should be true for the theory. More is true: if something is true across all models, then it is true of the canonical model, and thus syntactically true. Thus, we see that providing a canonical model is fundamentally connected to the idea of completeness.


## Semantics of Simply Typed Lambda Calculus

It is an oft-repeated (perhaps more than understood) fact  that the simply typed lambda calculus (STLC) is a kind of "internal language" or "syntax" for the theory of Cartesian Closed Categories (CCC's). As such, in the paradigm we have been sketching, we can think of Cartesian closed categories as semantic models of the theory of the type theory described by STLC. What does this intuitively mean? Consider a prototypical term formation judgment in STLC:

$$
\begin{array}{@{}c@{\quad}l@{}}
\vcenter{\hbox{$
  \dfrac{x_{\i} : a_{\i} \in \Gamma}{\Gamma \vdash \var(x_{\i}) : a_{\i}}
$}}
& \text{(Var)}
\end{array}
$$

Semantically, this is pleasantly simple: assuming we have a natural interpretation for each of the simple types, then if we are given some context $\Gamma = \x\_1 \ty \a_1, \cdots, \x\_\n \ty \a_\n$, we interpret this as a product (in some ambient category $\C$): $\sem{a_1} \;\times\; \cdots \;\times\; \lsem a_{\n} \rsem$. This term is interpreted as nothing other than a projection from an iterated product:
$$
\sem{\var(x_{\i})} \defeq \proj_{\i} : \sem{\a_1} \;\times\; \cdots \;\times\; \sem{\a_{\n}} \rightarrow \sem{\a_{\i}}
$$

Similarly, suppose we have the following application typing judgment:

$$
\f : \a \Rightarrow b,  \x : \a \vdash \f \cdot \x
$$

This should correspond to taking a function object i.e. an abstract collection where each of the (generalized) elements correspond to a function
(in $\C$), and an element of the domain of the function and "evaluating" the function on that argument:

$$
\sem{\f \cdot \x} \defeq \eval : (\sem{\f} : \sem{\b}^{\sem{a}}) \;\times\; (\sem{x} : \sem{a}) \rightarrow \sem{\b}
$$

The evaluation map is precisely one of the defining features of an [exponential object](https://ncatlab.org/nlab/show/exponential+object#definition)
which is one of the defining structures in a Cartesian closed category. More generally then, we will see how each of the terms in STLC precisely corresponds to a feature in a CCC. In the above terminology then, we can think of the STLC as a syntax for the algebraic theory of CCC's. Moreover, from the STLC we should be able to construct a syntactical category which is a _canonical_ model for the type theory. Let us see then how we can begin to develop such a semantics in `agda`.

## Agda Development

### Contexts, Renamings and Substitution

We use intrinsically well-scoped, well-typed syntax throughout, defining single-variable substitution as a special case of parallel substitution. In order to get off the ground, we first define a subcategory of substitutions called renamings. A renaming from one context $\Gamma$ to another $\Delta$ gives us a way of taking any
typed variable $(\x \ty \t)  \in \Gamma$ and giving back a variable in $\Delta$ of the same type. Here is the syntax we will use for types, terms, and contexts:
```Agda
pattern _▸_ as a = a ∷ as
pattern ∅ = []

-- `typed` de bruijn indices
infix 4 _∈_
data _∈_ {A : Type} : (a : A) → List A -> Type where
  Z : ∀ {Γ : List A}{n : A} -> n ∈ Γ ▸ n

  S : ∀ {Γ n m} -> n ∈ Γ -> n ∈ Γ ▸ m
```

```Agda
-- We add two primitive types to our theory:
--  - 𝟙 corresponding to the terminal object
--  - 𝕆 corresponding to any object
--    [suggestively named as it could be empty]
data Ty : Type where
  𝕆 : Ty
  𝟙 : Ty
  _⇒_ : Ty → Ty → Ty

Ctxt : Set
Ctxt = List Ty

-- Intrinsically well-typed well-scoped terms
data Tm : Ctxt → Ty → Type where
  var : ∀ {Γ ty} → ty ∈ Γ → Tm Γ ty
  _∙_ : ∀ {Γ dom cod} → Tm Γ (dom ⇒ cod) → Tm Γ dom → Tm Γ cod
  fun : ∀ {Γ dom cod} → Tm (Γ ▸ dom) cod → Tm Γ (dom ⇒ cod)
  tt  : ∀ {Γ} → Tm Γ 𝟙
```

From here, there are two ways one can define renamings, the first, which we will not use, is as an inductive type:
```Agda
data IndRen (Δ : Ctxt) : (Γ : Ctxt) → Set where
  ε   : IndRen Δ ∅
  _,_ : ∀ {Γ a} (ρ : IndRen Δ Γ) (x : a ∈ Δ) → IndRen Δ (Γ ▸ a)
```

This approach is nice, and comes with a reasonable built-in notion of equality of renamings. A second approach, and the one
we follow in this development, is the more naive definition in terms of functions:

```Agda
Ren : Ctxt → Ctxt → Set
Ren Γ Δ = ∀ {ty} → ty ∈ Δ → ty ∈ Γ
```
This says exactly that if we are given any variable in `Δ`, we get a corresponding variable (of the same type) in `Γ`. In order for this definition to have
a reasonable notion of equality, we will assume function extensionality throughout and so postulate the following two extensionality variants from the `agda` std-lib:

```Agda
postulate
  fun-ext : Extensionality ℓzero ℓzero
  fun-ext-imp : ExtensionalityImplicit ℓzero ℓzero
```

We then have the following notion of renaming equivalence:
```Agda
_≡Ren_ : ∀ {Γ Δ} → (ρ σ : Ren Γ Δ) → Type
_≡Ren_ {Δ = Δ} ρ σ = ∀ {ty} → ∀ (v : ty ∈ Δ) → ρ v ≡ σ v
```

For our purposes, perhaps the most salient observation about renamings is that the collection of all contexts with
renamings\footnote{This is not precisely correct, as we will see below, we should in fact take _equivalence classes_ of renamings with respect to their equational theory}
between them, which we denote `Ren`, forms a category with the following identity and composition:

```Agda
id-Ren : ∀ {Γ} → Ren Γ Γ
id-Ren = λ v → v
```
```Agda
_∘R_ : ∀ {Ξ Δ Γ} → Ren Γ Δ → Ren Ξ Γ → Ren Ξ Δ
_∘R_ ρ σ = λ v → σ (ρ v)
```

We then note that we can perform an operation of weakening (called `ext`) on renamings, that they are a congruence with respect to weakening, and that weakening distributes over composition:
```Agda
-- weaken a renaming by adding the same type to each context
ext : ∀ {Γ Δ ty} → Ren Γ Δ → Ren (Γ ▸ ty) (Δ ▸ ty)
ext ρ Z = Z
ext ρ (S pf) = S (ρ pf)

-- weakening preserves equality of renamings:
ext-≡ : ∀ {Γ Δ ty} → {ρ σ : Ren Δ Γ} → ρ ≡Ren σ → ext {ty = ty} ρ ≡Ren ext σ
ext-≡ eq Z = refl
ext-≡ eq (S v) = cong S (eq v)

ext-∘R : ∀ {Ξ Γ Δ ty} → (σ : Ren Δ Γ) → (τ : Ren Ξ Δ)  →
  ext {ty = ty} (σ ∘R τ) ≡Ren (ext σ ∘R ext τ)
ext-∘R σ τ Z = refl
ext-∘R σ τ (S v) = refl
```

We then have that renaming acts to perform parallel renaming of variables on terms, as we would hope:
```Agda
rename : ∀ {Γ Δ t} → Tm Γ t → Ren Δ Γ → Tm Δ t
rename (var v) ρ = var (ρ v)
rename (rator ∙ rand) ρ = (rename rator ρ) ∙ (rename rand ρ)
rename (fun body) ρ = fun (rename body (ext ρ))
rename tt ρ = tt
```

Given the above, that renamings are the morphisms in a category `Ren`, and that these morphisms act _contravariantly_ on terms (of a fixed type), we might suspect that we should think of `Tm _  t` as a [presheaf](https://ncatlab.org/nlab/show/presheaf) on `Ren`. Before we show that this is indeed the case, we must first develop some of the basic equational theory, in our set-up, proving that renaming preserves Ren-equality:

```Agda
rename-≡ : ∀ {Γ Δ t} → {ρ σ : Ren Δ Γ} → ρ ≡Ren σ → (tm : Tm Γ t) → rename tm ρ ≡ rename tm σ
rename-≡ eq (var v) = cong (λ v → var v ) (eq v)
rename-≡ eq (rator ∙ rand) = cong₂ (λ rator rand → rator ∙ rand ) (rename-≡ eq rator) (rename-≡ eq rand)
rename-≡ eq (fun body) = cong fun (rename-≡ (ext-≡ eq) body)
rename-≡ eq tt = refl
```

We can then show that the renaming action respects composition of renamings (functoriality):
```Agda
open ≡-Reasoning
rename-∘R : ∀ { Ξ Γ Δ ty} → (tm : Tm Γ ty) → (σ : Ren Δ Γ) → (τ : Ren Ξ Δ)  →
  (rename tm (σ ∘R τ)) ≡ rename (rename tm σ) τ
rename-∘R (var v) σ τ = refl
rename-∘R (rator ∙ rand) σ τ
  rewrite rename-∘R rator σ τ
  rewrite rename-∘R rand σ τ
  = refl
rename-∘R {ty = ty} (fun body) σ τ =
  begin
    (fun (rename body (ext (σ ∘R τ))))
      -- Use ext-∘R to distribute ext over composition
      ≡⟨ cong fun (rename-≡ (ext-∘R σ τ) _) ⟩
    (fun (rename body ((ext σ) ∘R (ext τ))))
      -- Apply rename-∘R inductively to the body
      ≡⟨ cong fun (rename-∘R body (ext σ) (ext τ)) ⟩
    (fun (rename (rename body (ext σ)) (ext τ))) ∎
rename-∘R tt σ τ = refl
```

Similarly, after we observe that weakening of the identity is Ren-equivalent to the identity,
we can show that renaming also preserves the identity up to propositional equality of terms:
```Agda
ext-id : ∀ {ty Γ} → ext {Γ = Γ} {ty = ty} id-Ren ≡Ren id-Ren
ext-id Z = refl
ext-id (S v) = refl

id-Ren-≡ : ∀ {Γ t} → ∀ (tm : Tm Γ t) → rename tm id-Ren ≡ tm
id-Ren-≡ (var v) = refl
id-Ren-≡ (rator ∙ rand) = cong₂ (λ f x → f ∙ x) (id-Ren-≡ rator) (id-Ren-≡ rand)
id-Ren-≡ (fun body) = cong (λ a → fun a) eq-lem
   where
     eq-lem : _
     eq-lem = begin
       rename body (ext id-Ren)
         -- ext id-Ren = id-Ren
         ≡⟨ rename-≡ ext-id body ⟩
       rename body id-Ren
         -- Apply id-Ren-≡ inductively
         ≡⟨ id-Ren-≡ body ⟩
       body ∎
id-Ren-≡ tt = refl
```

Together, `rename-∘R` and `id-Ren-≡` give us the data of a presheaf: `Tm _ t` is contravariant and functorial in the renaming action.


Finally, we use renamings to define term weakening, by noting that the de Bruijn increment operator -- `S` -- defines a weakening from `Γ` to `Γ ▸ ty`:
```Agda
wk-Tm tm = rename tm S
```

With renamings in hand, we can develop the full theory of substitutions. Just as a renaming takes a (typed) variable from context `\Gamma` and gives
a (typed) variable in a context `Δ`, a substitution takes a (typed) variable from `Γ` and gives back a term in context `Δ`:
```Agda
Sub : Ctxt → Ctxt → Type
Sub Δ Γ = ∀ {ty} → ty ∈ Γ → Tm Δ ty
```

In order to properly describe the equational theory of such substitutions, we would first need to have the correct equational theory of terms (which would require already having defined substitution of terms), and so, for now, we have a notion of "raw equality" of substitutions:
```Agda
_≣Sub_ : ∀ {Δ Γ} → (ρ σ : Sub Δ Γ) → Type
_≣Sub_ {Γ = Γ} ρ σ =  ∀ {ty} → ∀ (v : ty ∈ Γ) → ρ v ≡ σ v
```

Just as `Ren` formed a category with objects given by contexts, we have a category `Sub` where the morphisms are now substitutions with the following identity and
composition:
```Agda
Sub-id : ∀ {Γ} → Sub Γ Γ
Sub-id v = var v

_∘𝕊_ : ∀ {Ξ Δ Γ} → Sub Γ Δ → Sub Ξ Γ → Sub Ξ Δ
_∘𝕊_ ρ σ v = subst σ (ρ v)
```

We again have a notion of weakening for a substitution:
```Agda
ext : ∀ {Γ Δ ty} → Sub Γ Δ → Sub (Γ ▸ ty) (Δ ▸ ty)
ext σ Z = var Z
-- Here we perform substitution under a binder and so also need to weaken
-- the term we give back
ext σ (S pf) = Ren.wk-Tm (σ pf)
```

and we again have a contravariant action of substitutions on terms:
```Agda
subst : ∀ {Γ Δ t} → Sub Δ Γ → Tm Γ t → Tm Δ t
subst σ (var v) = σ v
subst σ (rator ∙ rand) = (subst σ rator) ∙ (subst σ rand)
subst σ (fun body) = fun (subst (ext σ) body)
subst σ tt = tt
```

As before, we have that this action is functorial (preserves identity and composition up to propositional equality):
```Agda
Sub-id-≣ : ∀ {Γ t} → ∀ (tm : Tm Γ t) → subst Sub-id tm ≡ tm

∘Sub-≡ :
  ∀ {Γ Δ Θ ty} (tm : Tm Δ ty) →
  (ρ : Sub Γ Δ) (ρ' : Sub Θ Γ) →
  subst ρ' (subst ρ tm) ≡ subst (ρ ∘𝕊 ρ') tm
```

We leave the laborious details, regarding the mechanics of substitution, of these lemmas to the proof development for those interested\footnote{To be found [here for Sub-id](agda-link: Sub-id)
and [here for ∘Sub-≡](agda-link: ∘Sub-≡)}.

Finally, we have what we need to define single variable substitution which we will need for the equational theory:
```Agda
-- substitution of a single variable
sub/ : ∀ {Γ ty} → Tm Γ ty → Sub Γ (Γ ▸ ty)
sub/ arg Z = arg
sub/ _   (S v) = var v

-- substitute for the `topmost` variable in a term
_/[_] : ∀ {Γ ty₁ ty₂} → Tm (Γ ▸ ty₁) ty₂ → Tm Γ ty₁ → Tm Γ ty₂
_/[_] {Γ = Γ} {ty₁ = ty₁} sub-tm arg = subst (sub/ arg) sub-tm
```

### Equational Theory of STLC

With substitution in hand, we can define an inductive type to capture the judgments in the equational theory of terms as follows:
```Agda
data _≡Tm_ : {Γ : Ctxt} {t : Ty} → Tm Γ t → Tm Γ t → Type where
  reflexivity :
    ∀ {Γ ty} (tm : Tm Γ ty) →
      tm ≡Tm tm
  symmetry :
    ∀ {Γ ty} {t1 t2 : Tm Γ ty} → t1 ≡Tm t2 →
      t2 ≡Tm t1
  transitivity :
    ∀ {Γ ty} {t1 t2 t3 : Tm Γ ty} → t1 ≡Tm t2 → t2 ≡Tm t3 →
      t1 ≡Tm t3
  β-red :
    ∀ {dom cod Γ} → (body : Tm (Γ ▸ dom) cod)(arg : Tm Γ dom) →
      ((fun body) ∙ arg) ≡Tm (body /[ arg ])
  η-fn :
    ∀{dom cod Γ}(fn-tm : Tm Γ (dom ⇒ cod)) →
      (fun ((Ren.wk-Tm fn-tm) ∙ (var Z))) ≡Tm fn-tm
  var-cong :
    ∀ {Γ ty} {v v' : ty ∈ Γ} →
    v ≡ v' →
    var v ≡Tm var v'
  ∙-cong :
    ∀{dom cod Γ}(fn₁ fn₂ : Tm Γ (dom ⇒ cod)) (arg₁ arg₂ : Tm Γ dom) →
      fn₁ ≡Tm fn₂ → arg₁ ≡Tm arg₂ →
      fn₁ ∙ arg₁ ≡Tm fn₂ ∙ arg₂
  fun-cong :
    ∀{dom cod Γ}(bd₁ bd₂ : Tm (Γ ▸ dom) cod) →
      bd₁ ≡Tm bd₂ → (fun bd₁) ≡Tm (fun bd₂)
  𝟙-η : {Γ : Ctxt} → (tm-𝟙 : Tm Γ 𝟙) → tm-𝟙 ≡Tm tt
```
We note the following:

- We make equality automatically an equivalence relation, corresponding to the usual rules:

$$
\dfrac{}{\Gamma \vdash \t \equiv \t \ty \a} \quad \text{(Refl)}
\qquad
\dfrac{\Gamma \vdash \t_1 \equiv \t_2 \ty \a}{\Gamma \vdash \t_2 \equiv \t_1 \ty \a} \quad \text{(Sym)}
$$
$$
\dfrac{\Gamma \vdash \t_1 \equiv \t_2 \ty \a \quad \Gamma \vdash \t_2 \equiv \t_3 \ty \a}{\Gamma \vdash \t_1 \equiv \t_3 \ty \a} \quad \text{(Trans)}
$$

- The β-rule -- `β-red` corresponds exactly to the usual rule of applying a lambda term to an argument reducing via substitution:

$$
\dfrac{\Gamma,\, \x \ty \a \vdash \t \ty \b \quad \Gamma \vdash s \ty \a}
      {\Gamma \vdash (\lambda\, \x \ty \a .\; \t)\; s \equiv \t[s/\x] \ty \b}
\quad \text{(β)}
$$

- Similarly, the η rule, `η-fn`, is the standard rule that gives us a way of writing any term of a function type as a lambda term:

$$
\dfrac{\Gamma \vdash \f \ty \a \Rightarrow \b}
      {\Gamma \vdash \lambda\, \x .\; \f\; \x \equiv \f \ty \a \Rightarrow \b}
\quad \text{(η-fn)}
\qquad
\dfrac{\Gamma \vdash \t \ty \mathbf{1}}
      {\Gamma \vdash \t \equiv \mathtt{tt} \ty \mathbf{1}}
\quad \text{(η-\(\mathbf{1}\))}
$$

- Lastly, we want the equality relation to be a congruence with respect to the term formation rules:

$$
\dfrac{\Gamma \vdash \f_1 \equiv \f_2 \ty \a \Rightarrow \b \quad \Gamma \vdash s_1 \equiv s_2 \ty \a}
      {\Gamma \vdash \f_1\; s_1 \equiv \f_2\; s_2 \ty \b}
\quad \text{(Cong-App)}
$$
$$
\dfrac{\Gamma,\, \x \ty \a \vdash \t_1 \equiv \t_2 \ty \b}
      {\Gamma \vdash \lambda\, \x \ty \a .\; \t_1 \equiv \lambda\, \x \ty \a .\; \t_2 \ty \a \Rightarrow \b}
\quad \text{(Cong-Lam)}
$$

Using the notion of equivalence relation (and setoid -- a type carrying some chosen equivalence relation) from the standard library, we can then register that equality gives
an equivalence relation (with associated setoid):
```Agda
≡Tm-Equality : {Γ : Ctxt}{ty : Ty} → IsEquivalence {A = Tm Γ ty} _≡Tm_
≡Tm-Equality =
  record {
    refl = λ {x} → reflexivity x ;
    sym = symmetry ;
    trans = λ eq₁ eq₂ → transitivity eq₁ eq₂
    }

≡Tm-setoid : (Γ : Ctxt) (ty : Ty) → Setoid ℓzero ℓzero
≡Tm-setoid Γ ty =
  record
    { Carrier       = Tm Γ ty
    ; _≈_           = _≡Tm_
    ; isEquivalence = ≡Tm-Equality
    }
```

This also, finally, gives us a proper equational theory of substitutions:
```Agda
_≡Sub_ : ∀ {Δ Γ} → (ρ σ : Sub Δ Γ) → Type
_≡Sub_ {Γ = Γ} ρ σ =  ∀ {ty} → ∀ (v : ty ∈ Γ) → ρ v ≡Tm σ v
```

### A Set-Theoretic Model

We finally then have enough of the basic theory developed to construct a particular model of the theory. As mentioned in the introduction, our model will take each term judgment $\Gamma \vdash \mathtt{tm} \ty \t$ to be interpreted as a function from the interpretation of the context $\sem{\Gamma}$ to the interpretation of the type $\sem{\t}$. As before, each context is semantically just the product of the interpretation of each type. We interpret variables as projections, `tt` as the unique term in `⊤`, function terms as terms in
a set-theoretic function type, and function application as the composition of function evaluation, and the fork of the semantics of each component of application:

```Agda
⟦_⟧𝕋 : Ty → Set
⟦ 𝕆 ⟧𝕋 = ⊥
⟦ 𝟙 ⟧𝕋 = ⊤
⟦ dom ⇒ cod ⟧𝕋 = ⟦ dom ⟧𝕋  → ⟦ cod ⟧𝕋

⟦_⟧ℂ : Ctxt → Set
⟦ [] ⟧ℂ = ⊤
⟦ (Γ ▸ t) ⟧ℂ = ⟦ Γ ⟧ℂ × ⟦ t ⟧𝕋

⟦var⟧ : ∀ {ty Γ} → ty ∈ Γ → (⟦ Γ ⟧ℂ → ⟦ ty ⟧𝕋)
⟦var⟧ Z Γ = proj₂ Γ
⟦var⟧ (S pf) Γ = ⟦var⟧ pf (proj₁ Γ)

-- We define and use an explicit eval function
-- to more cleanly generalize to a CCC
eval : ∀ {a b : Type} → (a → b) × a → b
eval (f , a ) = f a

⟦_⟧ : ∀ {Γ t} → Tm Γ t → (⟦ Γ ⟧ℂ → ⟦ t ⟧𝕋)
⟦ var v ⟧ = ⟦var⟧ v
⟦ rator ∙ rand ⟧ = λ ρ → eval (⟦ rator ⟧ ρ , ⟦ rand ⟧ ρ)
⟦ fun f ⟧ = λ ρ a → ⟦ f ⟧ (ρ , a)
⟦ tt ⟧ = λ _ → tt
```

There is a sense in which this model allows us to show the consistency of our raw theory:
```Agda
consistent : Tm ∅ 𝕆 → ⊥
consistent t = ⟦ t ⟧ tt
```

However, this is a somewhat empty sort of consistency. In this model we map $\mathcal{O}$ to $\bot$, and this shows that we can't directly construct a term in the possibly empty type, as we would then be able to directly construct a term of type $\bot$. In order for this to _really_ capture the consistency of STLC, we require not just a way to interpret term judgments, but that our interpretation also respects the equational judgments. That our semantics respects the equations or the proof theory of our system is usually known as _soundness_. As we will do this in greater generality, and the proof involves developing various of the kinds of finicky manipulations associated with substitutions that typify this kind of result, we only note the importance of the substitution lemma which we state without proof\footnote{see [here](agda-link: Semantics.SetModel.sub-lem) for exploring the substitution lemma and [here](agda-link: ⟦⟧-Soundness) for the proof of soundness}:
```Agda
-- the semantics of a substituted term is a composition
-- of a composition followed by the semantics of the
-- term morphism:
--
-- So we can think semantically about a substitution as:
-- ⟦ Δ ⟧ -- σ --> ⟦ Γ ⟧ -- ⟦ tm ⟧ --> ⟦ t ⟧
sub-lem : ∀ {Γ Δ t} → (σ : Sub Δ Γ) → (tm : Tm Γ t)
  → (∀ (δ : ⟦ Δ ⟧ℂ) → ⟦ subst σ tm  ⟧ δ ≡ (⟦ tm ⟧ (⟦ σ ⟧𝕊 δ)))
```

```Agda
-- Our set-theoretical model respects our equality judgment
⟦⟧-Soundness : {Γ : Ctxt} {t : Ty} → {lhs rhs : Tm Γ t}
  → (lhs ≡Tm rhs) → (⟦ lhs ⟧) ≡ (⟦ rhs ⟧)
⟦⟧-Soundness (reflexivity tm) = refl
⟦⟧-Soundness (symmetry eq) with ⟦⟧-Soundness eq
... | rhs≡lhs = sym rhs≡lhs
⟦⟧-Soundness (transitivity eq1 eq2) with ⟦⟧-Soundness eq1 , ⟦⟧-Soundness eq2
... | t1≡t2 , t2≡t3 = trans t1≡t2 t2≡t3
⟦⟧-Soundness (β-red body arg) =
   begin
     (λ ρ → eval ((λ a → ⟦ body ⟧ (ρ , a)) , ⟦ arg ⟧ ρ))
       ≡⟨ refl ⟩
     (λ ρ → ⟦ body ⟧ (ρ , ⟦ arg ⟧ ρ))
       -- cong tetris using that ⟦ Sub.Sub-id ⟧𝕊 ρ ≡ ρ
       ≡⟨ fun-ext (λ ρ → cong (λ f → ⟦ body ⟧ (f , ⟦ arg ⟧ ρ)) (sym (⟦⟧-Sub-id ρ)) ) ⟩
     (λ ρ → ⟦ body ⟧ (⟦ Sub.Sub-id ⟧𝕊 ρ , ⟦ arg ⟧ ρ))
       ≡⟨ refl ⟩
     (λ ρ → ⟦ body ⟧ (⟦ Sub.sub/ arg ⟧𝕊 ρ))
       ≡⟨ sym (fun-ext (λ δ → sub-lem (Sub.sub/ arg) body δ)) ⟩
     ⟦ body Sub./[ arg ] ⟧ ∎
⟦⟧-Soundness (η-fn fn-tm)
   =
   begin
     (λ ρ a → eval (⟦ Ren.wk-Tm fn-tm ⟧ (ρ , a) , a))
     -- using ⟦ Ren.wk-Tm fn-tm ⟧ ≡ ⟦ tm ⟧ ∘ proj₁
       ≡⟨ fun-ext (λ ρ →
            fun-ext (λ a →
              cong₂ (λ f a → eval (f , a))
              (cong (λ fn → fn (ρ , a)) (⟦⟧-Wk-Tm fn-tm)) refl)) ⟩
     ⟦ fn-tm ⟧ ∎
⟦⟧-Soundness (𝟙-η tm-𝟙)
   = refl
⟦⟧-Soundness (var-cong v≡v') = cong ⟦var⟧ v≡v'
⟦⟧-Soundness (∙-cong fn₁ fn₂ arg₁ arg₂ eq₁ eq₂)
   with ⟦⟧-Soundness eq₁ , ⟦⟧-Soundness eq₂
... |  ⟦eq₁⟧ , ⟦eq₂⟧ =
    begin
      (λ ρ → eval (⟦ fn₁ ⟧ ρ , ⟦ arg₁ ⟧ ρ))
        -- We use fun-ext and then inductively use equalities on each component
        ≡⟨ fun-ext (λ ρ →
          cong eval (≡-× (cong (λ f → f ρ) ⟦eq₁⟧) (cong (λ a → a ρ) ⟦eq₂⟧))) ⟩
      (λ ρ → eval (⟦ fn₂ ⟧ ρ , ⟦ arg₂ ⟧ ρ)) ∎
⟦⟧-Soundness (fun-cong bd₁ bd₂ eq)
  with ⟦⟧-Soundness eq
... | ⟦eq⟧ =
  begin
      (λ ρ a → ⟦ bd₁ ⟧ (ρ , a))
        -- We use fun-ext and then inductively use the equality on the body
        ≡⟨ fun-ext (λ ρ → fun-ext (λ a → cong (λ f → f (ρ , a)) ⟦eq⟧))   ⟩
      (λ ρ a → ⟦ bd₂ ⟧ (ρ , a)) ∎

```

### Models in Cartesian Closed Categories

We have then a particular model using the ambient type theory (which we think of, for the purposes here, as `Set`). More generally, as we mentioned, this relies on nothing
more than capabilities offered by any CCC. Let us then generalize the above model in this setting.
For that purpose, we will use the rather excellent [agda-categories library](https://github.com/agda/agda-categories).
We start with these imports we need from the library\footnote{the full development for this section can be followed starting [here](agda-link: CCC)}:
```Agda
open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Object.Product.Core using (Product)
open import Categories.Object.Exponential
open import Categories.Object.Terminal
open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Object.Product.Morphisms 𝒞 using ([_⇒_]_×id)
```

We assume throughout that we have a given Cartesian closed category with object $\mathcal{O}$ and so our development is
a parameterized module fixing a particular Cartesian closed category along with an object of the category:

```Agda
module CCCSemantics
  {o ℓ e}
  (𝒞 : Category o ℓ e)
  (CC-𝒞 : CartesianClosed 𝒞)
  (𝒪 : Category.Obj 𝒞)
```

We then introduce these various shortenings for the various bits of categorical structure that $\C$ has:
```Agda
module 𝒞 = Category 𝒞
module CC-𝒞 = CartesianClosed CC-𝒞
module Cart = Cartesian CC-𝒞.cartesian
module 𝒞-× = BinaryProducts Cart.products
module 𝒞-Pr (A B : 𝒞.Obj) = Product (𝒞-×.product {A} {B})
module 𝒞-𝟙 = Terminal Cart.terminal
module exp (A B : 𝒞.Obj) =  Exponential (CC-𝒞.exp {A} {B})
module Exp = CC-𝒞.exp
open import Categories.Object.Product.Morphisms 𝒞 using ([_⇒_]_×id)

CC-Pr : {A B : 𝒞.Obj} → Product 𝒞 A B
CC-Pr = 𝒞-×.product

Exp-Pr : {A B : 𝒞.Obj} → Product 𝒞 (CC-𝒞.exp.B^A {A} {B}) A
Exp-Pr = Exp.product

_𝒞⇒_ : (A : 𝒞.Obj) → (B : 𝒞.Obj) → 𝒞.Obj
_𝒞⇒_ A B = E.B^A
  where
  module E = exp A B

𝒞Hom : Rel 𝒞.Obj ℓ
𝒞Hom = 𝒞._⇒_
```

We can then start to give our generalization of the set-theoretic semantics. Firstly, types are interpreted inductively
on their structure as we would expect:
```Agda
⟦_⟧𝕋 : Ty → 𝒞.Obj
⟦ 𝕆 ⟧𝕋 = 𝒪
-- 𝟙 is interpreted as the terminal object
⟦ 𝟙 ⟧𝕋 = 𝒞-𝟙.⊤
-- Function types are interpreted as function objects
⟦ dom 𝕋⇒ cod ⟧𝕋 = ⟦ dom ⟧𝕋 𝒞⇒ ⟦ cod ⟧𝕋
```

Similarly, contexts are again interpreted as products, where an n-arity product: $\X_1 \times \cdots \times \X_{\n}$ is defined to be the left-parenthesized iterated
binary product $\X_1 \times \cdots \times \X_{\n} := (\cdots(\X_1 \times \X_2) \times \X_3)\times \ldots \times \X_{\n - 1} )\times \X_{\n}$
```Agda
⟦_⟧ℂ : Ctxt → 𝒞.Obj
⟦ [] ⟧ℂ = 𝒞-𝟙.⊤
⟦ (Γ ▸ t) ⟧ℂ = ⟦ Γ ⟧ℂ × ⟦ t ⟧𝕋
  where
  open 𝒞-×
```

Variables are then once again iterated projections, only this time the projection morphisms are generalized to those that exist in any CCC. As before,
we define this inductively based on the debruijn index, using the current top type if the variable is `Z`, and otherwise compose with $\pi_1$ and recurse:
```Agda
⟦var⟧ : ∀ {ty Γ} → ty ∈ Γ → (𝒞Hom ⟦ Γ ⟧ℂ ⟦ ty ⟧𝕋)
⟦var⟧ Z = 𝒞-×.π₂
⟦var⟧ (S pf) = ⟦var⟧ pf 𝒞.∘ 𝒞-×.π₁
  where
  open 𝒞
  open 𝒞-×
```

We then get to our generalization of the interpretation of terms we hinted at in the beginning:
```Agda
⟦_⟧ : ∀ {Γ t} → Tm Γ t → (𝒞Hom ⟦ Γ ⟧ℂ ⟦ t ⟧𝕋)
⟦ var v ⟧ = ⟦var⟧ v
⟦ _∙_ {dom = d} {cod = c} rator rand ⟧ =
  E.eval 𝒞.∘ E.product.⟨  ⟦ rator ⟧ ,  ⟦ rand ⟧ ⟩
  where
  open 𝒞
  module E = exp ⟦ d ⟧𝕋 ⟦ c ⟧𝕋
⟦ fun {dom = d} {cod = c} body ⟧ = E.λg 𝒞-×.product ⟦ body ⟧
  where
  module E = exp ⟦ d ⟧𝕋 ⟦ c ⟧𝕋
⟦ tt ⟧ = 𝒞-𝟙.!
```

We note several things:
- In the semantics for function application we take a composition of the fork `⟨  ⟦ rator ⟧ ,  ⟦ rand ⟧ ⟩` with the function `E.eval`, this is the universal function that any function object in a CCC has with type signature:
```Agda
eval : B^A×A ⇒ B
```
- Similarly, functions are interpreted using the function $\lambda\mathrm{g}$. This is one of the fields an Exponential object (as defined in `agda-categories`) has, and has
type:
```Agda
λg : ∀ (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ B^A)
```
In more conventional notation this is a function $\operatorname{Hom}(\X \times \A, B) \rightarrow \operatorname{Hom}(X, B^A)$. This is the usual operation of currying, or said
another way, this is the universal arrow distinguishing the function object, wherein we can also recover the original arrow by pairing with this arrow and using `eval`.
- The arrow `𝒞-𝟙.!` is just the universal arrow to the terminal object.

We again have a substitution lemma, saying just the same as before. We give the proof, to give the flavour that proving things
in a CCC is just the same sort of equational reasoning we would do when reasoning about the set theoretical model:

```Agda
sub-lem : ∀ {Γ Δ t} → (σ : Sub Δ Γ) → (tm : Tm Γ t)
      → ⟦ subst σ tm  ⟧ 𝒞.≈ (⟦ tm ⟧ 𝒞.∘ ⟦ σ ⟧𝕊)

sub-lem σ (var v) = ⟦var⟧-Sub σ v
sub-lem σ (rator ∙ rand) =
      begin
        CC-𝒞.exp.eval 𝒞.∘ Pr.⟨ ⟦ subst σ rator ⟧ , ⟦ subst σ rand ⟧ ⟩
          -- Use lemma to factor out ⟦ σ ⟧𝕊 from product
          ≈⟨ ∘-resp-≈ Equiv.refl lemma ⟩
        CC-𝒞.exp.eval 𝒞.∘ (Pr.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧𝕊)
          -- Reassociate
          ≈⟨ sym-assoc ⟩
        (CC-𝒞.exp.eval 𝒞.∘ Pr.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩) 𝒞.∘ ⟦ σ ⟧𝕊 ∎
      where
        module Pr = CC-𝒞.exp.product
        open Categories.Category.Category.HomReasoning 𝒞
        lemma :
          (Pr.⟨ ⟦ subst σ rator ⟧ , ⟦ subst σ rand ⟧ ⟩)
            𝒞.≈
          (Pr.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧𝕊)
        lemma =
          begin
            (Pr.⟨ ⟦ subst σ rator ⟧ , ⟦ subst σ rand ⟧ ⟩)
              -- Apply sub-lem inductively to both components
              ≈⟨ Pr.⟨⟩-cong₂ (sub-lem σ rator) (sub-lem σ rand) ⟩
            (Pr.⟨ ⟦ rator ⟧ 𝒞.∘ ⟦ σ ⟧𝕊 , ⟦ rand ⟧ 𝒞.∘ ⟦ σ ⟧𝕊 ⟩)
              -- Factor out common ⟦ σ ⟧𝕊 from product
              ≈⟨ Equiv.sym Pr.∘-distribʳ-⟨⟩ ⟩
            (Pr.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧𝕊) ∎
sub-lem σ (fun {dom = d} tm) =
      begin
        Exp.λg CC-Pr ⟦ subst (Sub.ext σ) tm ⟧
          ≈⟨ Exp.λ-cong CC-Pr (sub-lem (Sub.ext σ) tm) ⟩
          -- inductively rewrite subst (Sub.ext σ) tm
        CC-𝒞.exp.λg CC-Pr (⟦ tm ⟧ 𝒞.∘ ⟦ Sub.ext {ty = d} σ ⟧𝕊)
          ≈⟨ Exp.λ-cong CC-Pr (∘-resp-≈ Equiv.refl (⟦sub⟧-Wk σ)) ⟩
          -- use ⟦sub⟧-Wk to rewrite ⟦ Sub.ext σ ⟧𝕊
        Exp.λg CC-Pr (⟦ tm ⟧ 𝒞.∘ [ CC-Pr ⇒ CC-Pr ] ⟦ σ ⟧𝕊 ×id)
          ≈⟨ Equiv.sym (CC-𝒞.exp.subst CC-Pr CC-Pr) ⟩
          -- factor out component in λg
        Exp.λg CC-Pr ⟦ tm ⟧ 𝒞.∘ ⟦ σ ⟧𝕊 ∎
      where
        open Categories.Category.Category.HomReasoning 𝒞
    sub-lem {Γ = Γ} {Δ = Δ} σ tt =
      𝒞-𝟙.!-unique (𝒞._∘_ {B = ⟦ Γ ⟧ℂ} (⟦_⟧ {Γ = Γ} tt) ⟦ σ ⟧𝕊)
```

We rely on two lemmas, the first is just the specialized version for the variable case\footnote{see [here](agda-link: ⟦var⟧-Sub) to explore all the details on proving soundness in the variable case}:
```Agda
⟦var⟧-Sub :  ∀ {Γ Ξ ty} → (τ : Sub Ξ Γ) →
  (v : ty ∈ Γ) →
  ⟦ τ v ⟧ 𝒞.≈ (⟦var⟧ v 𝒞.∘ ⟦ τ ⟧𝕊)
```

The second is a weakening lemma \footnote{See [here](agda-link: ⟦sub⟧-Wk) for details}:
```Agda
⟦sub⟧-Wk : ∀ {Γ Δ : Ctxt}{ty : Ty} → (σ : Sub Δ Γ) →
  ⟦ Sub.ext {ty = ty} σ ⟧𝕊 𝒞.≈ ([ CC-Pr ⇒ CC-Pr ] ⟦ σ ⟧𝕊 ×id)
```
This says that a weakened extension $\sigma$ acts on a product as the product map $⟦ \sigma ⟧ \times  ⟦ id ⟧$, in other words, it semantically doesn't affect the topmost
weakened variable, and acts the same as $\sigma$ on all other variables.

This is again the key lemma we need to prove soundness. Here is the shape of the proof:
```Agda
⟦⟧-Soundness :
      {Γ : Ctxt} {t : Ty} → {lhs rhs : Tm Γ t} →
      (lhs ≡Tm rhs) → (⟦ lhs ⟧) 𝒞.≈ (⟦ rhs ⟧)
⟦⟧-Soundness (reflexivity tm) = Equiv.refl
⟦⟧-Soundness (symmetry eq) = Equiv.sym (⟦⟧-Soundness eq)
⟦⟧-Soundness (transitivity eq₁ eq₂) = Equiv.trans (⟦⟧-Soundness eq₁) (⟦⟧-Soundness eq₂)
⟦⟧-Soundness (β-red body arg) = Equiv.sym (β-lemma body arg)
⟦⟧-Soundness (η-fn fn-tm) = η-lemma fn-tm
⟦⟧-Soundness (𝟙-η tm-𝟙) = Equiv.sym (𝒞-𝟙.!-unique ⟦ tm-𝟙 ⟧)
⟦⟧-Soundness (var-cong {v = v} {v' = v'} v≡v') = var-lemma v v' v≡v'
⟦⟧-Soundness (∙-cong fn₁ fn₂ arg₁ arg₂ eq₁ eq₂) =
  begin
    CC-𝒞.exp.eval 𝒞.∘ CC-𝒞.exp.product.⟨ ⟦ fn₁ ⟧ , ⟦ arg₁ ⟧ ⟩
      -- Apply ⟦⟧-Soundness inductively to both components
      ≈⟨ ∘-resp-≈
               Equiv.refl
               (Exp.product.⟨⟩-cong₂ (⟦⟧-Soundness eq₁) (⟦⟧-Soundness eq₂))
       ⟩
    CC-𝒞.exp.eval 𝒞.∘ CC-𝒞.exp.product.⟨ ⟦ fn₂ ⟧ , ⟦ arg₂ ⟧ ⟩ ∎
      where
        open Categories.Category.Category.HomReasoning 𝒞
⟦⟧-Soundness (fun-cong bd₁ bd₂ eq) = Exp.λ-cong 𝒞-×.product (⟦⟧-Soundness eq)
```

Here we dispatch each non-trivial case to some specialized lemma. For instance here is how the proof for `β-red` looks:
```Agda
β-lemma :
  {Γ : Ctxt} {d c : Ty} → (body : Tm (Γ ▸ d) c) (arg : Tm Γ d) →
  ⟦ body /[ arg ] ⟧ 𝒞.≈
  Exp.eval 𝒞.∘ Exp.product.⟨ Exp.λg 𝒞-×.product ⟦ body ⟧ , ⟦ arg ⟧ ⟩
β-lemma {Γ}{d}{c} body arg =
  begin
     ⟦ body /[ arg ] ⟧
         -- def of /[_]
         ≈⟨ Equiv.refl ⟩
     ⟦ Sub.subst (sub/ arg) body ⟧
         -- rewrite using substitution lemma
         ≈⟨ sub-lem (sub/ arg) body ⟩
     ⟦ body ⟧ 𝒞.∘ ⟦ sub/ arg ⟧𝕊
         -- definition of sub/
         ≈⟨ Equiv.refl ⟩
         -- definition of sub/
     ⟦ body ⟧ 𝒞.∘ ⟨ ⟦ (var {Γ = Γ}) ⟧𝕊 , ⟦ arg ⟧ ⟩
         -- definition of Sub-id
         ≈⟨ Equiv.refl ⟩
     ⟦ body ⟧ 𝒞.∘ ⟨ ⟦ (Sub-id {Γ = Γ}) ⟧𝕊 , ⟦ arg ⟧ ⟩
         -- rewrite ⟦ Sub-id ⟧ as 𝒞.id
         ≈⟨ ∘-resp-≈ Equiv.refl (⟨⟩-congʳ (⟦⟧-Sub-id {Γ = Γ})) ⟩
     ⟦ body ⟧ 𝒞.∘ ⟨ 𝒞.id , ⟦ arg ⟧ ⟩
         -- inverse β for function objects:
         --   rewrite ⟦ body ⟧ to Exp.eval ∘ λ ⟦ body ⟧ × id
         -- In more detail, we have:
         --   g : A × B → C ≈
         --     A × B -- ĝ × id --> C^B × B -- eval --> C
         ≈⟨ ∘-resp-≈ (Equiv.sym (Exp.β 𝒞-×.product)) Equiv.refl ⟩
     (Exp.eval 𝒞.∘ ([ 𝒞-×.product ⇒ Prod ] Exp.λg 𝒞-×.product ⟦ body ⟧ ×id)) 𝒞.∘ ⟨ 𝒞.id , ⟦ arg ⟧ ⟩
         -- reassociate
         ≈⟨ assoc ⟩
     Exp.eval 𝒞.∘ (([ 𝒞-×.product ⇒ Prod ] Exp.λg 𝒞-×.product ⟦ body ⟧ ×id) 𝒞.∘ ⟨ 𝒞.id , ⟦ arg ⟧ ⟩)
         -- definition of [_]_×id in terms of [_]_×_
         ≈⟨ Equiv.refl ⟩
     Exp.eval 𝒞.∘ ((𝒫𝓇.[ 𝒞-×.product ⇒ Prod ] (Exp.λg 𝒞-×.product ⟦ body ⟧) × 𝒞.id) 𝒞.∘ ⟨ 𝒞.id , ⟦ arg ⟧ ⟩)
         -- rewrite using ×∘⟨⟩ i.e.
         -- f×g∘⟨h₁,h₂⟩ ≈ ⟨f ∘ h₁, g ∘ h₂⟩
         ≈⟨ ∘-resp-≈ Equiv.refl [ 𝒞-×.product ⇒ Prod ]×∘⟨⟩ ⟩
     Exp.eval 𝒞.∘ Exp.product.⟨ (Exp.λg 𝒞-×.product ⟦ body ⟧) 𝒞.∘ 𝒞.id , 𝒞.id 𝒞.∘ ⟦ arg ⟧ ⟩
         -- Remove composition with 𝒞.id
         ≈⟨ ∘-resp-≈ Equiv.refl (Exp.product.⟨⟩-cong₂ identityʳ identityˡ) ⟩
      Exp.eval 𝒞.∘ Exp.product.⟨ Exp.λg 𝒞-×.product ⟦ body ⟧ , ⟦ arg ⟧ ⟩ ∎
     where
          open import Categories.Object.Product.Morphisms 𝒞 as 𝒫𝓇
            using ([_⇒_]_×_; [_⇒_]×∘⟨⟩)
          Prod = Exp.product
          open Categories.Category.Category.HomReasoning 𝒞
```
The main thing to appreciate about this proof is that we are just doing equational reasoning in a Cartesian closed category. Although it may be
the case that the details are quite gnarly and unnecessarily low-level for how we usually reason about morphisms in a CCC, none of this is anything out
of the ordinary. It is also worth saying that the heart of the proof -- which `agda-categories` calls `Exp.β` -- explicitly says how the semantic $\beta$
reduction works, which is nothing other than the universal property of an exponential object. Precisely the same holds true of the η-law\footnote{The full proof of the `η-lemma` [here](agda-link: η-lemma)} where we use the uniqueness of the associated curried function to show the semantic $\eta$ law holds.


### The Syntactic Category

Finally, we don't give the full development of the syntactic category -- we don't prove that this category is indeed Cartesian closed -- but just some flavour of how the category looks. Before we get to the full syntactic category, we give the category of renamings that was mentioned previously:
```Agda
  Ren-Cat : Category ℓzero ℓzero ℓzero
  Ren-Cat = record
    { Obj = Ctxt
    ; _⇒_ = Ren
    ; _≈_ = _≡Ren_
    ; id = id-Ren
    ; _∘_ = _∘R_
    ; assoc = λ _ → refl
    ; sym-assoc = λ _ → refl
    ; identityˡ = λ _ → refl
    ; identityʳ = λ _ → refl
    ; identity² = λ _ → refl
    ; equiv = λ {A} {B} → ≡Ren-equiv {A} {B}
    ; ∘-resp-≈ = ∘R-resp-≈
    }
```

In `agda-categories` we define a category by giving the objects, the morphisms and an equivalence relation on the collection of morphisms. We then have the various category laws\footnote{Anyone familiar with the typical axioms of a category will notice that there are more laws than might be typical, this is a trade-off we face when designing an algebraic interface in a dependent type theory. Some of the design decisions for this interface are explained in the [agda-categories source](agda-link: Category)}, along with a proof that the relation is a congruence with respect to composition.
For renamings we have to prove that equality of renamings is an equivalence relation:
```Agda
≡Ren-equiv : {Γ Δ : Ctxt} → IsEquivalence (_≡Ren_ {Γ = Γ} {Δ = Δ})
≡Ren-equiv =
 record {
   refl = λ _ → refl ;
   sym = sym-R ;
   trans = λ {r₁} {r₂} {r₃} eq₁ eq₂ v → trans (eq₁ v) (eq₂ v)
   }
```

We then also need to show that this relation is a congruence for composition of renamings:
```Agda
∘R-resp-≈ : {A B C : Ctxt} {f h : Ren B C} {g i : Ren A B} →
   f ≡Ren h → g ≡Ren i → (f ∘R g) ≡Ren (h ∘R i)
∘R-resp-≈ {f = f}{h = h}{g = g}{i = i} f≡Rh g≡Ri v =
 begin
   (f ∘R g) v
     -- Rewrite f to h using f≡Rh
     ≡⟨ cong g (f≡Rh v) ⟩
   (h ∘R g) v
     -- Rewrite g to i using g≡Ri
     ≡⟨ g≡Ri (h v) ⟩
   (h ∘R i) v ∎
 where
 open ≡-Reasoning
```

Since equality of renamings only involves point-wise propositional equality of functions,
this proof is just the same as showing that if we compose propositionally equal functions, then they
are equal pointwise.

The full syntactic category corresponds to the free cartesian closed category (in our case on a single object $\mathcal{O})$, but also has a concrete description as what we called `Sub`, where the objects of the category are the contexts,
and the morphisms are equivalence classes of substitutions. Here is how that looks:
```Agda
Sub-Cat : Category ℓzero ℓzero ℓzero
Sub-Cat = record
  { Obj = Ctxt
  ; _⇒_ = Sub
  ; _≈_ = _≡Sub_
  ; id = Sub-id
  ; _∘_ = _∘𝕊_
  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → assoc-proof {A} {B} {C} {D} {f} {g} {h}
  ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h} → sym-assoc-proof {A} {B} {C} {D} {f} {g} {h}
  ; identityˡ = λ {A} {B} {f} → identityˡ-proof {A} {B} {f}
  ; identityʳ = λ {A} {B} {f} → identityʳ-proof {A} {B} {f}
  ; identity² = identity²-proof
  ; equiv = ≡Sub-equiv
  ; ∘-resp-≈ = ∘𝕊-resp-≈
  }
  where
  assoc-proof : {A B C D : Ctxt} {h : Sub A B} {g : Sub B C} {f : Sub C D} →
                ((f ∘𝕊 g) ∘𝕊 h) ≡Sub (f ∘𝕊 (g ∘𝕊 h))
  assoc-proof {A} {B} {C} {D} {h} {g} {f} v =
    begin
      ((f ∘𝕊 g) ∘𝕊 h) v
        -- Associativity of _∘𝕊_
        ≈⟨ ∘Sub-≡Tm (f v) g h ⟩
      (f ∘𝕊 (g ∘𝕊 h)) v ∎
    where open Reasoning (≡Tm-setoid A (type-of v))

  sym-assoc-proof : {A B C D : Ctxt} {h : Sub A B} {g : Sub B C} {f : Sub C D} →
                    (f ∘𝕊 (g ∘𝕊 h)) ≡Sub ((f ∘𝕊 g) ∘𝕊 h)
  sym-assoc-proof {A} {B} {C} {D} {h} {g} {f} v =
    begin
      (f ∘𝕊 (g ∘𝕊 h)) v
        -- Associativity⁻¹ of _∘𝕊_
        ≈⟨ symmetry (∘Sub-≡Tm (f v) g h) ⟩
      ((f ∘𝕊 g) ∘𝕊 h) v ∎
    where open Reasoning (≡Tm-setoid A (type-of v))

  identityˡ-proof : {A B : Ctxt} {f : Sub A B} →
                     (Sub-id ∘𝕊 f) ≡Sub f
   identityˡ-proof {A} {B} {f} v =
     begin
       (Sub-id ∘𝕊 f) v
         -- Definition of ∘𝕊
         ≈⟨ reflexivity ((Sub-id ∘𝕊 f) v) ⟩
       subst f (var v)
         -- Definition of Sub-id
         ≈⟨ reflexivity (f v) ⟩
       f v ∎
     where open Reasoning (≡Tm-setoid A (type-of v))

  identityʳ-proof : {A B : Ctxt} {f : Sub A B} →
                     (f ∘𝕊 Sub-id) ≡Sub f
  identityʳ-proof {A} {B} {f} v =
    begin
      (f ∘𝕊 Sub-id) v
        -- Definition of ∘𝕊
        ≈⟨ reflexivity ((f ∘𝕊 Sub-id) v) ⟩
      subst Sub-id (f v)
        -- Sub-id is identity for substitution
        ≈⟨ subst-id (f v) ⟩
      f v ∎
    where open Reasoning (≡Tm-setoid A (type-of v))

  identity²-proof : {A : Ctxt} →
    (Sub-id ∘𝕊 Sub-id) ≡Sub Sub-id {A}
  identity²-proof {A} v =
    begin
      (Sub-id ∘𝕊 Sub-id) v
        -- Definition of ∘𝕊
        ≈⟨ reflexivity ((Sub-id ∘𝕊 Sub-id) v) ⟩
      subst Sub-id (var v)
        -- Definition of subst for var
        ≈⟨ reflexivity (var v) ⟩
      var v
        -- Definition of Sub-id
        ≈⟨ reflexivity (Sub-id v) ⟩
      Sub-id v ∎
    where open Reasoning (≡Tm-setoid A (type-of v))
```

As for `Ren`, the objects are contexts and the morphisms are substitutions. We then have to give an equivalence relation on morphisms. In our case, equivalence is equality of substitutions:
```Agda
≡Sub-equiv : {Γ Δ : Ctxt} → IsEquivalence (_≡Sub_ {Δ = Δ} {Γ = Γ})
≡Sub-equiv {Γ} {Δ} =
  record {
    refl = λ _ → E.refl ≡Tm-Equality
    ; sym = λ {r₁} {r₂} eq v → E.sym ≡Tm-Equality (eq v)
    ; trans = λ {r₁} {r₂} {r₃} eq₁ eq₂ v → E.trans ≡Tm-Equality (eq₁ v) (eq₂ v)
    }
    where
    module E = IsEquivalence
```

Our proof that composition of substitutions is a congruence is structurally the same, relying
on analogous equational properties of term equality, e.g. [subst-cong](agda-link: subst-cong):
```Agda

∘𝕊-resp-≈ : {A B C : Ctxt} {f h : Sub B C} {g i : Sub A B} →
  f ≡Sub h → g ≡Sub i → (f ∘𝕊 g) ≡Sub (h ∘𝕊 i)
∘𝕊-resp-≈ {A} {B} {C} {f = f}{h = h}{g = g}{i = i} f≡𝕊h g≡𝕊i v =
  begin
    (f ∘𝕊 g) v
      -- Rewrite f to h using subst-cong
      ≈⟨ subst-cong g (f v) (h v) (f≡𝕊h v) ⟩
    (h ∘𝕊 g) v
      -- Rewrite g to i using subst-≣𝕊
      ≈⟨ subst-≣𝕊 (h v) g≡𝕊i ⟩
    (h ∘𝕊 i) v ∎
    where
    open Reasoning (≡Tm-setoid A (type-of v))
```

From here we would want to show that this category is Cartesian closed, and this would be the path towards showing CCCs are complete with respect to the equational theory of STLC. What would this categorical structure look like? The product of contexts $\Gamma$ and $\Delta$ is their concatenation $\Gamma, \Delta$ (this is similar to the Lawvere category of an algebraic theory). The unit for this category is given by the empty context $\emptyset$. A function object must be an adjoint to the product, and
so would satisfy:
$$
\mathrm{Sub}(X, \Delta^\Gamma) \cong \mathrm{Sub}(X \times \Gamma, \Delta)
$$

Suppose $\X = \x\_1, \ldots , \x_{\n}$, $\Gamma = \y\_1, \ldots, \y_{\m}$, and $\Delta = \d_1, \ldots, \d_{\k}$. This means that a substitution from $\X$ into context $\Delta^\Gamma$ should be given by a sequence of terms $\t_{\i}$ of type $\d_{\i}$, for each $\i$, in context $\X , \Gamma$. By repeated lambda abstraction (the inverse of what logicians call the Deduction theorem), we can think of giving terms of the form $\X , \Gamma \vdash \t_{\i} : \d_{\i}$, as equivalently giving terms $\X \vdash \tilde{\t_{\i}} : \Gamma \Rightarrow \d_{\i}$. Here $\Gamma \Rightarrow \d$ is notation for:

$$
\Gamma \Rightarrow \d := \y_1 \Rightarrow (\y_2 \Rightarrow \ldots \Rightarrow (\y_{\m} \Rightarrow \d)\ldots)
$$

We can thus _define_ the exponential as the pointwise exponential:
$$
\Delta^\Gamma := \Gamma \Rightarrow \d_1, \ldots, \Gamma \Rightarrow \d_{\k}
$$

In other words, a substitution $\X \rightarrow \Delta^\Gamma$ is nothing other than a sequence of
curried terms for each type in $\Delta$. In order to complete the development, we would need to show
this has an `evaluation` morphism, which would be a substitution of the form:
$$
\Delta^\Gamma \times \Gamma \rightarrow \Delta
$$

If we mediate on this then we see the evaluation map will apply each variable in $\Delta^\Gamma$ to each of the variables in $\Gamma$ giving back a term of type $\d_{\i} \in \Delta$.

That is a sketch of the Cartesian closed structure, but we leave its full development to a future version of this post. Once we prove that it is a CCC, then this would give us completeness: since the syntactic category is itself a CCC model, any equality that holds in all CCC models must already hold in the equational theory.
We also note that while we have established the necessary components for `Tm _ t` being a presheaf on `Ren-Cat` -- `rename-∘R` and `id-Ren-≡` provide the functoriality and identity -- we have not packaged this up formally as a presheaf on the above `Ren-Cat`, nor have we shown the analogous result for `Sub-Cat`.

For more information about these ideas, Lambek and Scott's *Introduction to Higher-Order Categorical Logic* is an essential resource. They vastly generalize the above by considering $\lambda$-theories -- type theories extending STLC with specified equations -- and CCCs satisfying those equations. They show that the syntactic category construction gives a functor from $\lambda$-theories to CCCs, the internal language of a CCC gives a functor in the other direction, and that these two functors give an equivalence of categories.
