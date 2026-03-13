---
title: "Semantics of STLC in Agda"
author: Callan McGill
date: "Dec 29, 2025"
tags: [Agda, CCC, STLC, Category-Theory]
description: An excursion into the semantics of STLC formalized in agda
quote: The sentence 'snow is white' is true if, and only if, snow is white.
quoteAuthor: Alfred Tarski
agdaDevelopment: "STLC semantics"
publish: true

---

<p class="no-dropcap"><em>Note</em>: <em>The opening section is intended only as motivation for the kinds of semantics we are going to consider, and can be skipped if you are already quite motivated enough.</em></p>

$\def\X{\mathrm{X}} \def\R{\mathcal{R}} \def\U{\mathcal{U}}\def\a{\mathrm{a}}\def\f{\mathrm{f}}\def\i{\mathrm{i}} \def\w{\mathrm{w}} \def\x{\mathrm{x}} \def\y{\mathrm{y}} \def\z{\mathrm{z}} \def\n{\mathrm{n}} \def\m{\mathrm{m}} \def\p{\mathrm{p}} \def\t{\mathrm{t}} \def\a{\mathrm{a}} \def\b{\mathrm{b}} \def\c{\mathrm{c}} \def\i{\mathrm{i}} \def\j{\mathrm{j}} \def\A{\mathcal{A}}\def\B{\mathcal{B}}\def\C{\mathcal{C}} \def\D{\mathcal{D}}\def\E{\mathcal{E}}\def\F{\mathcal{F}} \def\G{\mathcal{G}}\def\H{\mathcal{H}} \def\Fr{\mathcal{Fr}} \def\Set{\mathcal{Set}} \def\var{\mathrm{var}}\def\proj{\operatorname{proj}}\def\lsem{\text{⟦}}\def\rsem{\text{⟧}}\newcommand{\sem}[1]{\text{⟦}#1\text{⟧}}\def\ty{\mathrel{:}}\def\defeq{\mathrel{\mathop{:}}=}\def\eval{\operatorname{eval}}$

## Motivation

In the study of formal languages (or other types of syntactical gadgets) we face two fundamental questions:

1. What, if any, is the intended or conventional _meaning_ of the language in question?
2. What general class of mathematical or formal objects does the language seek to describe?

Formal languages, in this sense, arguably first arose, with Frege's work and later that of Hilbert, Russell and Whitehead etc. Hilbert was the first to define a formal language like what we would know as first-order Peano arithhmetic.

For such a language, the intended model is, of course, the natural numbers; the language is precisely consructed intending to capture the essential logical principles for all arithmetical truths. The second question, that of the general class of models of first-order Peano airthmetic, seems to have been a later historical consideration.
It was perhaps thought, though unstated, that such a language is _categorical_, that is to say: the language has a unique model up to (model) isomorphism. Later work of Gödel, and especially Skolem, emphasized the folly of this idea, typifying expressive first-order theories of arithemtic as necessarily giving rise to a panoply of non-standard models of arithmetic.

Whilst non-standard models in this case might strike us as especially peculiar -- models, for instance, which have some non-standard number with Gödel
number equal to a Gödel sentence of the system -- they seem much more tame to contemplate when we change our perspective to a more modern algebraic one. For instance, let us imagine
a formal language for an algebraic theory -- let us say, the language of groups -- with the intended models of the theory precisely capturing the correct algebraic structures -- the class of all groups. An impressionistic version of such a formal language might be a kind of type theory with judgments of the following form:

$$
   \x \ty \G , \y \ty \G  \vdash \x \cdot \y \ty \G
$$
$$
   \x \ty \G  \vdash \x^{-1} \ty \G
$$
$$
     \vdash e \ty \G
$$
Such a language would aso need to have an equality judgment capturing the equational theory of groups:

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

Now, in order for us to interpret this theory we need not just to interpret the symbols of the theory, but to interpret the semantics of each judgment, and thus
to give a semantics to context, and then to judgments. Here is an idea for how we might do so, given a judgment of this form:
$$
   \x \ty \G , \y \ty \G  \vdash \x \cdot \y \ty \G
$$
which we are trying to interpret in some set $\X$, we naively interpret this as some function:
$$
  \X \times X \rightarrow X
$$

Similarly, given a term judgment like:
$$
   \x \ty \G , \y \ty \G, \z \ty \G  \vdash (\x \cdot \y) \cdot \z \ty \G
$$

we want to interpret this semantically as some function:
$$
  \X \times X \times X \rightarrow X
$$

Not wishing to get too into the weeds on this particular example, we make two observations about where this path leads. Firstly, this leads us to the notion of a [Lawvere Theory](https://ncatlab.org/nlab/show/Lawvere+theory): what this means, essentially, is that given any word on $\n$ variables in the free group $\Fr\langle\x\_1,\ldots,x\_n\rangle$, the semantics of our theory gives an interpretation of such a word as a morphism:
$$
  \underbrace{\X \times \cdots \times \X}_{n} \rightarrow \X
$$

We can package this observation up by constructing  a certain syntactical category $\mathbb{T}_{\mathrm{Grp}}$ with objects given by sets of variables, $\Gamma = \{\x\_1, \ldots, \x\_\n\}$, morphisms between contexts $\{\x\_1, \ldots, \x\_\n\} \rightarrow \{\y\_1, \ldots, \y\_m\}$ given by an m-tuple of words in the free group on $\Gamma$: $\y_\j = \w_\j\left[x\_1,\ldots,\x\n\right]$, and products in the category given by the disjoint union of contexts. Then, packaging up the above remark, a model of our theory (in $\Set$) is nothing but a product-preserving functor from this _syntactic category_:
$$
  \mathrm{M} : \underbrace{\mathbb{T}_{\mathrm{Grp}} \rightarrow \Set }_{\mathrm{product\ preserving}}
$$


Secondly, we note that, in a certain sense, our theory gives rise to a _canonical model_ where we take as our set of elements in context $\Gamma = \{\x\_1, \ldots, \x\_\n\}$, precisely the equivalence class of judgments for the theory and, we take for morphisms, equivalence classes of substitutions. We won't spell out this example here, but take inspiration in the rest of this post that the semantics of a type theory is a certain kind of algebraic theory, and that the type theory itself gives rise to a canonical syntactical model of the theory which should, in some sense, be the free theory.


## Semantics of Simply Typed Lambda Calculus

It is a perhaps more often repeated than understood fact that the simply typed lambda caluclus is a kind of "internal language" or "syntax" for the theory of Cartesian Closed Categories (CCC's). As such, in our above paradigm, we can think of Cartesian closed categories as semantical models of the theory of the type theory described by STLC. Let us think intuitively
about what this means. Consider a prototypical term formation judgment in STLC:

$$
\begin{array}{@{}c@{\quad}l@{}}
\vcenter{\hbox{$
  \dfrac{x_{\i} : a_{\i} \in \Gamma}{\Gamma \vdash \var(x_{\i}) : a_{\i}}
$}}
& \text{(Var)}
\end{array}
$$


Semantically, this is delightfully simple: assuming we have an interpretion for each of the simple types, then given some context $\Gamma = \x\_1 \ty \a_1, \cdots,x \ty \a_\n$, we interpret this as a product (in some ambient category $\C$): $\sem{a_1} \;\times\; \cdots \;\times\; \lsem a_{\n} \rsem$. This term is interpreted as nothing other than a projection:
$$
\sem{\var(x_{\i})} \defeq \proj_{\i} : \sem{\a_1} \;\times\; \cdots \;\times\; \sem{\a_{\n}} \rightarrow \a_{\i}
$$

Similarly, suppose we have the following typing judgment:

$$
\f : \a \Rightarrow b,  \x : \a \vdash \f \cdot \x
$$

This should correspond to taking a function object i.e. an abstract collection where each of the (generalized) elements correspond to functions
(in \C) and an element of the domain of the function and "evaluating" the function on that argument:

$$
\sem{\f \cdot \x} \defeq \eval : \sem{\b}^{\sem{a}} \;\times\; \sem{a} \rightarrow \sem{\b}
$$

Such a function is precisely one of the defining features of an [exponential object](https://ncatlab.org/nlab/show/exponential+object#definition)
which is one of the defining structures in a cartesian closed category. Let us see how to develop such a semantics in `agda`.

## Agda Development

### Contexts, Renamings and Substitions

We use a standard approach with intrinsically well-scoped, well-typed syntax defining single variable substition via parallel substition. In order to get going with this we first define a subcategory of substitutions called renamings. A renaming from one context $\Gamma$ to another $\Delta$ gives a way of taking any
typed variable $(\x \ty \t)  \in \Gamma$ and giving a variable in $\Delta$ of the same type. First, let us get our syntax for types, terms, and contexts out of the way:
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
-- We add two primitive types to our theory with 𝟙 corresponding to the terminal object
-- and 𝕆 corresponding to any object (suggesting named as it could be empty)
data Ty : Type where
  𝕆 : Ty
  𝟙 : Ty
  _⇒_ : Ty → Ty → Ty

Ctxt : Set
Ctxt = List Ty

data Tm : Ctxt → Ty → Type where
  var : ∀ {Γ ty} → ty ∈ Γ → Tm Γ ty
  _∙_ : ∀ {Γ dom cod} → Tm Γ (dom ⇒ cod) → Tm Γ dom → Tm Γ cod
  fun : ∀ {Γ dom cod} → Tm (Γ ▸ dom) cod → Tm Γ (dom ⇒ cod)
  tt  : ∀ {Γ} → Tm Γ 𝟙
```

From here, there are two ways one can define renamings, the first is as an inductive type:
```Agda
data IndRen (Δ : Ctxt) : (Γ : Ctxt) → Set where
  ε   : IndRen Δ ∅
  _,_ : ∀ {Γ a} (ρ : IndRen Δ Γ) (x : a ∈ Δ) → IndRen Δ (Γ ▸ a)
```

This approach is nice, and comes with a reasonable built-in notion of equality of renamings. A second approach, and the one
we follow in this development, is the naive definition in terms of functions:

```Agda
Ren : Ctxt → Ctxt → Set
Ren Γ Δ = ∀ {ty} → ty ∈ Δ → ty ∈ Γ
```
This says exactly that if we are given any variable in `Δ`, we get a corresponding variable (of the same type) in `Γ`. In order for this definition to have
a reasonable notion of equality, we will need to assume function extensionality, and we will postulate the following two extensionality variants from
the `agda` std-lib:

```Agda
postulate
  fun-ext : Extensionality ℓzero ℓzero
  fun-ext-imp : ExtensionalityImplicit ℓzero ℓzero
```

For our purposes, perhaps the most salient observation about renamings is that the collection -- denoted `Ren` -- consisting of the collection of all contexts
with renamings\footnote{This is not quite correct, as we will see below, we should in fact take equivalence classes of renamings with respect to their equational theory}
between them, forms a category with the following identity and compostion\footnote{This `doesn't` work}:

```Agda
id-Ren : ∀ {Γ} → Ren Γ Γ
id-Ren = λ v → v
```
```Agda
_∘R_ : ∀ {Ξ Δ Γ} → Ren Γ Δ → Ren Ξ Γ → Ren Ξ Δ
_∘R_ ρ σ = λ v → σ (ρ v)
```

We then note that we can perform weakening (called `ext`) on renamings, that they are a congruence, and that weakening distributes over composition:
```Agda
ext : ∀ {Γ Δ ty} → Ren Γ Δ → Ren (Γ ▸ ty) (Δ ▸ ty)
ext ρ Z = Z
ext ρ (S pf) = S (ρ pf)

ext-≡ : ∀ {Γ Δ ty} → {ρ σ : Ren Δ Γ} → ρ ≡Ren σ → ext {ty = ty} ρ ≡Ren ext σ
ext-≡ eq Z = refl
ext-≡ eq (S v) = cong S (eq v)

ext-∘R : ∀ {Ξ Γ Δ ty} → (σ : Ren Δ Γ) → (τ : Ren Ξ Δ)  →
  ext {ty = ty} (σ ∘R τ) ≡Ren (ext σ ∘R ext τ)
ext-∘R σ τ Z = refl
ext-∘R σ τ (S v) = refl
```

We then have that renaming acts on terms as we would expect:
```Agda
rename : ∀ {Γ Δ t} → Tm Γ t → Ren Δ Γ → Tm Δ t
rename (var v) ρ = var (ρ v)
rename (rator ∙ rand) ρ = (rename rator ρ) ∙ (rename rand ρ)
rename (fun body) ρ = fun (rename body (ext ρ))
rename tt ρ = tt
```

Given the above, that renamings are the morphisms in a category `Ren`, and that these morphisms act _contravariantly_ on terms (of a fixed type), we might then suspect that we should think of `Tm _  t` as a presheaf on `Ren`. Before we show that this indeed the case, we must first develop the basic equational theory, in our set-up, for when two renamings are equal, and prove that renaming preserves this equality. We note that when we say there is a category called `Ren`:

```Agda
_≡Ren_ : ∀ {Γ Δ} → (ρ σ : Ren Γ Δ) → Type
_≡Ren_ {Δ = Δ} ρ σ = ∀ {ty} → ∀ (v : ty ∈ Δ) → ρ v ≡ σ v

rename-≡ : ∀ {Γ Δ t} → {ρ σ : Ren Δ Γ} → ρ ≡Ren σ → (tm : Tm Γ t) → rename tm ρ ≡ rename tm σ
rename-≡ eq (var v) = cong (λ v → var v ) (eq v)
rename-≡ eq (rator ∙ rand) = cong₂ (λ rator rand → rator ∙ rand ) (rename-≡ eq rator) (rename-≡ eq rand)
rename-≡ eq (fun body) = cong fun (rename-≡ (ext-≡ eq) body)
rename-≡ eq tt = refl
```

We can then show that the action respects composition of renamings:
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

Similarly, after we observe that weakening of the identity gives the identity, we can show that renaming preserves the identity:
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

Finally, we can use renamings to define term weakening, by noting that `S` defines a weakening from `\Gamma` to `\Γ ▸ \ty`:
```Agda
wk-Tm tm = rename tm S
```

Now that we have renamings, we can develop the full theory of substitutions. Just as a renaming takes a (typed) variable from context `\Gamma` and gives a (typed) variable in a context `\Delta`, a substitution takes a (typed) variable from `\Gamma` and gives back a term in context `Delta`:
```Agda
Sub : Ctxt → Ctxt → Type
Sub Δ Γ = ∀ {ty} → ty ∈ Γ → Tm Δ ty
```

In order to property describe the equational theory of such substitutions, we would need to have the equational theory of terms (which would require having defined substitution), and so for now we have a notion of "raw equality" of substitutions:
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

As before, we have that this action is functorial:
```Agda
Sub-id-≣ : ∀ {Γ t} → ∀ (tm : Tm Γ t) → subst Sub-id tm ≡ tm

∘Sub-≡ :
  ∀ {Γ Δ Θ ty} (tm : Tm Δ ty) →
  (ρ : Sub Γ Δ) (ρ' : Sub Θ Γ) →
  subst ρ' (subst ρ tm) ≡ subst (ρ ∘𝕊 ρ') tm
```

We leave the laborious details of these lemmas to the proof development\footnote{To be found [here for Sub-id](agda-link: Sub-id)
and [here for ∘Sub-≡](agda-link: ∘Sub-≡)}.

This finally gives us what we need to define single variable substitution:
```Agda
sub/ : ∀ {Γ ty} → Tm Γ ty → Sub Γ (Γ ▸ ty)
sub/ arg Z = arg
sub/ _   (S v) = var v

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

Using the notion of equivalence relation and setoid from the standard library, it follows (by construction) that this gives
an equivalence relation:
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

This also allows us to give a proper equational theory of substitutions:
```Agda
_≡Sub_ : ∀ {Δ Γ} → (ρ σ : Sub Δ Γ) → Type
_≡Sub_ {Γ = Γ} ρ σ =  ∀ {ty} → ∀ (v : ty ∈ Γ) → ρ v ≡Tm σ v
```

### A Set-Theoretic Model

We finally then have enough of the basic theory developed to construct a model. As mentioned in the introduction, our model takes it that each term judgment `\Gamma \vdash \tm \ty \t` is interpretted as a function from the interpretation of the context `\Gamma` to the interpretation of the type `\t`. As mentioned previously, each context is semantically just the product of the interpretation of each type. We then interpret variables as projections, `tt` as the unique term in `⊤`, function terms as terms in
a set-theoretic function object, and function application as the composition of function evaluation, and the fork of the semantics of each component:

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

-- We define this explicitly to more cleanly generalize to a CCC
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

However, in order for this to _really_ capture the sematnics of STLC, we require not just a way to interpret term judgments, but that our interpretation respects the equational judgments also. That our semantics respects the equations or proofs of our theory is usually known as soundness. As we will do this in more generality, and the proof involves developing various of the kinds of finnicky manipulations with substitutions that typify this kind of result, we only note the importance of the substitution lemma which we also state but without proof\footnote{see what is needed in the substitution lemma [here] and explore the proof of soundness [here]}:
```Agda
sub-lem : ∀ {Γ Δ t} → (σ : Sub Δ Γ) → (tm : Tm Γ t)
  → (∀ (δ : ⟦ Δ ⟧ℂ) → ⟦ subst σ tm  ⟧ δ ≡ (⟦ tm ⟧ (⟦ σ ⟧𝕊 δ)))
```

```Agda
⟦⟧-Soundness : {Γ : Ctxt} {t : Ty} → {lhs rhs : Tm Γ t} → (lhs ≡Tm rhs) → (⟦ lhs ⟧) ≡ (⟦ rhs ⟧)
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

That means we have a particular model using the ambient type theory (which we think of, for our purposes, as `Set`). More generally, we would like to develop a soundness theorem for interpreting STLC in any CCC. For this, we will use the [agda-categories library](here). We start then with these imports:
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

We assume throughout that we have a given Cartesian closed category with object $\mathcal{O}$

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

To wit, our semantics is a parameterized module parameterized by a Cartesian closed category $\C$, and we give specialized names to the various bits of structure, e.g. the category having a choice of global products which we write as `\C-]times`, a choice of exponential object etc.XS

We can then start to give semantics sketched above as follows. Firstly, types are interpretted semantically as we would expect:
```Agda
⟦_⟧𝕋 : Ty → 𝒞.Obj
⟦ 𝕆 ⟧𝕋 = 𝒪
-- 𝟙 is interpreted as the terminal object
⟦ 𝟙 ⟧𝕋 = 𝒞-𝟙.⊤
-- Function types are interpretted as function objects
⟦ dom 𝕋⇒ cod ⟧𝕋 = ⟦ dom ⟧𝕋 𝒞⇒ ⟦ cod ⟧𝕋
```

Contexts are interrpretted as products, where a n-arity product: $\X_1 \times \cdots \times \X_{\n}$ is defined as the left-parenthesized iterated
binary product $\X_1 \times \cdots \times \X_{\n} := (\cdots(\X_1 \times \X_2) \times X_3)\times \ldots \times \X_{\n - 1} )\times \X_{\n}$
```Agda
⟦_⟧ℂ : Ctxt → 𝒞.Obj
⟦ [] ⟧ℂ = 𝒞-𝟙.⊤
⟦ (Γ ▸ t) ⟧ℂ = ⟦ Γ ⟧ℂ × ⟦ t ⟧𝕋
  where
  open 𝒞-×
```

Variables will then need to be interpretted as projections which we can define inductively based on the debruijn index:
```Agda
⟦var⟧ : ∀ {ty Γ} → ty ∈ Γ → (𝒞Hom ⟦ Γ ⟧ℂ ⟦ ty ⟧𝕋)
⟦var⟧ Z = 𝒞-×.π₂
⟦var⟧ (S pf) = ⟦var⟧ pf 𝒞.∘ 𝒞-×.π₁
  where
  open 𝒞
  open 𝒞-×
```

We can then give an interpretation of terms:
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
- In the semantics for function application we write take a composition of the fork `⟨  ⟦ rator ⟧ ,  ⟦ rand ⟧ ⟩`




Soundness


### The Syntactic Category


Completeness
