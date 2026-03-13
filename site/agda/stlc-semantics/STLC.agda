{-# OPTIONS --without-K #-}

module STLC where

open import Relation.Binary using (Rel; IsPartialOrder; IsPreorder; IsEquivalence)
open import Level renaming (suc to ℓsuc; zero to ℓzero)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; cong-app; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Agda.Primitive renaming (Set to Type ; Setω to Typeω)
open import Relation.Binary.Bundles renaming (Poset to Posetℓ)
open import Data.List
open import Function.Base using (_∘_; _$_; id; const)
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Data.Maybe

postulate
  fun-ext : Extensionality ℓzero ℓzero
  fun-ext-imp : ExtensionalityImplicit ℓzero ℓzero

-- Basic utilities and helpers
module Base where
  open import Data.Product using (_×_; proj₁; proj₂; _,_)
  ≡-× : ∀ {A B : Set}{a a' : A}{b b' : B} → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
  ≡-× refl refl = refl

  ≡₁ :  ∀ {A B : Set}{a a' : A}{b : B} → a ≡ a' → (a , b) ≡ (a' , b)
  ≡₁ refl = refl

  ≡₂ :  ∀ {A B : Set}{a : A}{b b' : B} → b ≡ b' → (a , b) ≡ (a , b')
  ≡₂ refl = refl

  pattern _▸_ as a = a ∷ as
  pattern ∅ = []

  infix 4 _∈_

  data _∈_ {A : Type} : (a : A) → List A -> Type where
    Z : ∀ {Γ : List A}{n : A} -> n ∈ Γ ▸ n

    S : ∀ {Γ n m}
     -> n ∈ Γ
     -> n ∈ Γ ▸ m

  type-of : {A : Type}{a : A}{as : List A} → (v : a ∈ as) -> A
  type-of  {a = a} v = a

  pred-∈ : ∀ {A : Type} {a a' : A}{Γ} → (v : a ∈ (Γ ▸ a')) → Maybe (a ∈ Γ)
  pred-∈ Z = nothing
  pred-∈ (S v) = just v

  just-inj : ∀ {A : Type} {x y : A} → (just x ≡ just y) → x ≡ y
  just-inj refl = refl

  S-inj : ∀ {A : Type} {a a' : A}{Γ} → {v v' : a ∈ Γ} →  (S {m = a'} v ≡ S v') → v ≡ v'
  S-inj eq = just-inj (cong pred-∈ eq)

-- Intrinsically-typed STLC syntax
module Syntax where
  open Base
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

-- Variable renamings
module Ren where
  open Base
  open Syntax

  Ren : Ctxt → Ctxt → Set
  Ren Γ Δ = ∀ {ty} → ty ∈ Δ → ty ∈ Γ

  wk-Ren : ∀ {Γ Δ t} → Ren Γ (Δ ▸ t) → Ren Γ Δ
  wk-Ren ρ v = ρ (S v)

  _≡Ren_ : ∀ {Γ Δ} → (ρ σ : Ren Γ Δ) → Type
  _≡Ren_ {Δ = Δ} ρ σ = ∀ {ty} → ∀ (v : ty ∈ Δ) → ρ v ≡ σ v

  sym-R :  ∀ {Γ Δ} → {ρ σ : Ren Γ Δ} → ρ ≡Ren σ → σ ≡Ren ρ
  sym-R eq v = sym (eq v)

  id-Ren : ∀ {Γ} → Ren Γ Γ
  id-Ren = λ v → v

  _∘R_ : ∀ {Ξ Δ Γ} → Ren Γ Δ → Ren Ξ Γ → Ren Ξ Δ
  _∘R_ ρ σ = λ v → σ (ρ v)

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

  ext-S∘ext : ∀ {Γ Δ ty} → (σ : Ren Δ Γ) →
    (S ∘R ext {ty = ty} σ) ≡Ren (σ ∘R S)
  ext-S∘ext σ Z = refl
  ext-S∘ext σ (S v) = refl

  rename : ∀ {Γ Δ t} → Tm Γ t → Ren Δ Γ → Tm Δ t
  rename (var v) ρ = var (ρ v)
  rename (rator ∙ rand) ρ = (rename rator ρ) ∙ (rename rand ρ)
  rename (fun body) ρ = fun (rename body (ext ρ))
  rename tt ρ = tt

  rename-≡ : ∀ {Γ Δ t} → {ρ σ : Ren Δ Γ} → ρ ≡Ren σ → (tm : Tm Γ t) → rename tm ρ ≡ rename tm σ
  rename-≡ eq (var v) = cong (λ v → var v ) (eq v)
  rename-≡ eq (rator ∙ rand) = cong₂ (λ rator rand → rator ∙ rand ) (rename-≡ eq rator) (rename-≡ eq rand)
  rename-≡ eq (fun body) = cong fun (rename-≡ (ext-≡ eq) body)
  rename-≡ eq tt = refl

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

  wk-Tm : ∀ {Γ ty t} → Tm Γ t → Tm (Γ ▸ ty) t
  wk-Tm tm = rename tm S

-- Substitutions
module Sub where
  open Base
  open Syntax
  open Ren using (_∘R_; wk-Tm; sym-R; ext-S∘ext; rename)

  Sub : Ctxt → Ctxt → Type
  Sub Δ Γ = ∀ {ty} → ty ∈ Γ → Tm Δ ty

  -- This type of extensional propositonal equality is not really
  -- what we want for equality of substituions
  _≣Sub_ : ∀ {Δ Γ} → (ρ σ : Sub Δ Γ) → Type
  _≣Sub_ {Γ = Γ} ρ σ =  ∀ {ty} → ∀ (v : ty ∈ Γ) → ρ v ≡ σ v

  ≣Sub-sym : ∀ {Δ Γ} → {ρ σ : Sub Δ Γ} → ρ ≣Sub σ → σ ≣Sub ρ
  ≣Sub-sym eq v = sym (eq v)

  Sub-id : ∀ {Γ} → Sub Γ Γ
  Sub-id v = var v

  wk-Sub : ∀ {Γ Δ t} → Sub Γ (Δ ▸ t) → Sub Γ Δ
  wk-Sub ρ v = ρ (S v)

  ext : ∀ {Γ Δ ty} → Sub Γ Δ → Sub (Γ ▸ ty) (Δ ▸ ty)
  ext σ Z = var Z
  -- Here we perform substitution under a binder and so also need to weaken
  ext σ (S pf) = Ren.wk-Tm (σ pf)

  ext-≡ : ∀ {Γ Δ ty} → {ρ σ : Sub Δ Γ} → ρ ≣Sub σ → ext {ty = ty} ρ ≣Sub ext σ
  ext-≡ eq Z = refl
  ext-≡ eq (S v) = cong Ren.wk-Tm (eq v)

  ext-id : ∀ {ty Γ} → ext {Γ = Γ} {ty = ty} Sub-id ≣Sub Sub-id
  ext-id Z = refl
  ext-id (S v) = refl

  subst : ∀ {Γ Δ t} → Sub Δ Γ → Tm Γ t → Tm Δ t
  subst σ (var v) = σ v
  subst σ (rator ∙ rand) = (subst σ rator) ∙ (subst σ rand)
  subst σ (fun body) = fun (subst (ext σ) body)
  subst σ tt = tt

  subst-≣ : ∀ {Γ Δ t} → {ρ σ : Sub Δ Γ} → ρ ≣Sub σ → (tm : Tm Γ t) → subst ρ tm ≡ subst σ tm
  subst-≣ eq (var v) = eq v
  subst-≣ eq (rator ∙ rand) = cong₂ (λ f x → f ∙ x) (subst-≣ eq rator) (subst-≣ eq rand)
  subst-≣ eq (fun body) = cong fun (subst-≣ (ext-≡ eq) body)
  subst-≣ eq tt = refl

  sub-wk :  ∀ {Γ Δ ty} → ∀ (σ : Sub Δ Γ) →  (Ren.wk-Tm ∘ σ) ≣Sub (ext {ty = ty} σ ∘ S)
  sub-wk σ Z = refl
  sub-wk σ (S v) = refl

  Sub-id-≣ : ∀ {Γ t} → ∀ (tm : Tm Γ t) → subst Sub-id tm ≡ tm
  Sub-id-≣ (var v) = refl
  Sub-id-≣ (rator ∙ rand) = cong₂ (λ f x → f ∙ x) (Sub-id-≣ rator) (Sub-id-≣ rand)
  Sub-id-≣ (fun body) = cong (λ a → fun a) eq-lem
    where
      open ≡-Reasoning
      eq-lem : _
      eq-lem = begin
        subst (ext Sub-id) body
          -- ext Sub-id = Sub-id
          ≡⟨ subst-≣ ext-id body ⟩
        subst Sub-id body
          -- Apply Sub-id-≣ inductively
          ≡⟨ Sub-id-≣ body ⟩
        body ∎
  Sub-id-≣ tt = refl

  _∘𝕊_ : ∀ {Ξ Δ Γ} → Sub Γ Δ → Sub Ξ Γ → Sub Ξ Δ
  _∘𝕊_ ρ σ v = subst σ (ρ v)

  -- Apply renaming to a substitution (rename all terms in the substitution)
  sub-ren-∘ : ∀ {Γ Δ Ξ} → Sub Δ Γ → Ren.Ren Ξ Δ → Sub Ξ Γ
  sub-ren-∘ σ ρ v = Ren.rename (σ v) ρ
  -- Compose substitution with renaming: (σ ∘ ρ) v = σ (ρ v)
  ren-sub-∘ : ∀ {Γ Δ Ξ} → Ren.Ren Δ Γ → Sub Ξ Δ → Sub Ξ Γ
  ren-sub-∘ ρ σ v = σ (ρ v)

  ext-sub-ren-∘≣ : ∀ {Γ Δ Ξ ty} (σ : Sub Δ Γ) (ρ : Ren.Ren Ξ Δ) →
    ext {ty = ty} (sub-ren-∘ σ ρ) ≣Sub sub-ren-∘ (ext σ) (Ren.ext ρ)
  ext-sub-ren-∘≣ σ ρ Z = refl
  ext-sub-ren-∘≣ σ ρ (S v) =
    begin
      Ren.rename (Ren.rename (σ v) ρ) S
        -- Unfold composition of renamings
        ≡⟨ sym (Ren.rename-∘R (σ v) ρ S) ⟩
      Ren.rename (σ v) (ρ ∘R S)
        -- Rewrite using S ∘R ext ρ = ext ρ ∘R S
        ≡⟨ Ren.rename-≡ (sym-R (ext-S∘ext ρ)) (σ v) ⟩
      Ren.rename (σ v) (S ∘R Ren.ext ρ)
        -- Fold composition back
        ≡⟨ Ren.rename-∘R (σ v) S (Ren.ext ρ) ⟩
      Ren.rename (Ren.rename (σ v) S) (Ren.ext ρ)
        -- Definition of wk-Tm
        ≡⟨ refl ⟩
      Ren.rename (wk-Tm (σ v)) (Ren.ext ρ) ∎
    where
      open ≡-Reasoning

  -- Propositional version: renaming after substitution
  sub-ren-∘-≡ : ∀ {Γ Δ Ξ ty} (σ : Sub Δ Γ) (tm : Tm Γ ty) (ρ : Ren.Ren Ξ Δ) →
    Ren.rename (subst σ tm) ρ ≡ subst (sub-ren-∘ σ ρ) tm
  sub-ren-∘-≡ σ (var v) ρ = refl
  sub-ren-∘-≡ σ (rator ∙ rand) ρ =
    cong₂ _∙_ (sub-ren-∘-≡ σ rator ρ) (sub-ren-∘-≡ σ rand ρ)
  sub-ren-∘-≡ σ (fun body) ρ =
    begin
      fun (Ren.rename (subst (ext σ) body) (Ren.ext ρ))
        -- Apply sub-ren-∘-≡ inductively to the body
        ≡⟨ cong fun (sub-ren-∘-≡ (ext σ) body (Ren.ext ρ)) ⟩
      fun (subst (sub-ren-∘ (ext σ) (Ren.ext ρ)) body)
        -- Use ext-sub-ren-∘≣ to move ext outside
        ≡⟨ cong fun (subst-≣ (≣Sub-sym (ext-sub-ren-∘≣ σ ρ)) body) ⟩
      fun (subst (ext (sub-ren-∘ σ ρ)) body) ∎
    where open ≡-Reasoning
  sub-ren-∘-≡ σ tt ρ = refl

  -- Helper: ren-sub-∘ S (ext τ) is the same as sub-ren-∘ τ S
  ren-sub-ext-S : ∀ {Γ Δ ty} (τ : Sub Δ Γ) →
    ren-sub-∘ S (ext {ty = ty} τ) ≣Sub sub-ren-∘ τ S
  ren-sub-ext-S τ v = refl

  ext-ren-sub-∘≣ : ∀ {Γ Δ Ξ ty} (σ : Sub Ξ Δ) (ρ : Ren.Ren Δ Γ) →
    ext {ty = ty} (ren-sub-∘ ρ σ) ≣Sub ren-sub-∘ (Ren.ext ρ) (ext σ)
  ext-ren-sub-∘≣ σ ρ Z = refl
  ext-ren-sub-∘≣ σ ρ (S v) = refl

  -- syntactic equality of substitution after renaming
  subst-rename-≡ : ∀ {Γ Δ Ξ ty} (σ : Sub Ξ Δ) (ρ : Ren.Ren Δ Γ) (tm : Tm Γ ty) →
    subst σ (Ren.rename tm ρ) ≡ subst (ren-sub-∘ ρ σ) tm
  subst-rename-≡ σ ρ (var v) = refl
  subst-rename-≡ σ ρ (rator ∙ rand) =
    cong₂ _∙_ (subst-rename-≡ σ ρ rator) (subst-rename-≡ σ ρ rand)
  subst-rename-≡ σ ρ (fun body) =
    begin
      fun (subst (ext σ) (Ren.rename body (Ren.ext ρ)))
        -- Apply subst-rename-≡ inductively to the body
        ≡⟨ cong fun (subst-rename-≡ (ext σ) (Ren.ext ρ) body) ⟩
      fun (subst (ren-sub-∘ (Ren.ext ρ) (ext σ)) body)
        -- Use ext-ren-sub-∘≣ to move ext outside
        ≡⟨ cong fun (subst-≣ (≣Sub-sym  (ext-ren-sub-∘≣ σ ρ) ) body) ⟩
      fun (subst (ext (ren-sub-∘ ρ σ)) body) ∎
    where open ≡-Reasoning
  subst-rename-≡ σ ρ tt = refl

  -- Special case for S
  -- TODO: this should be one liner?
  subst-wk : ∀ {Γ Δ ty wk-ty} (τ : Sub Δ Γ) (tm : Tm Γ ty) →
    subst (ext {ty = wk-ty} τ) (Ren.rename tm S) ≡ Ren.rename (subst τ tm) S
  subst-wk τ (var v) = refl
  subst-wk τ (rator ∙ rand) =
    begin
      (subst (ext τ) (Ren.rename rator S) ∙ subst (ext τ) (Ren.rename rand S))
        -- rewrite inductively on both sides of _∙_
        ≡⟨ cong₂ (λ fn arg → fn ∙ arg) (subst-wk τ rator) (subst-wk τ rand) ⟩
      (Ren.rename (subst τ rator) S ∙ Ren.rename (subst τ rand) S) ∎
      where
      open ≡-Reasoning
  subst-wk τ (fun body) =
    begin
      fun (subst (ext (ext τ)) (Ren.rename body (Ren.ext S)))
        -- Use subst-rename-≡ to rewrite substitution of renamed term
        ≡⟨ cong fun (subst-rename-≡ (ext (ext τ)) (Ren.ext S) body) ⟩
      fun (subst (ren-sub-∘ (Ren.ext S) (ext (ext τ))) body)
        -- Use ext-ren-sub-∘ in reverse to move ext inside
        ≡⟨ cong fun (subst-≣ (≣Sub-sym (ext-ren-sub-∘≣ (ext τ) S)) body)
        ⟩
      fun (subst (ext (ren-sub-∘ S (ext τ))) body)
        -- Use ren-sub-ext-S to simplify
        ≡⟨ cong fun (subst-≣ (ext-≡ (ren-sub-ext-S τ)) body) ⟩
      fun (subst (ext (sub-ren-∘ τ S)) body)
        -- Use ext-sub-ren-∘≣ to relate ext (sub-ren-∘ τ S) to sub-ren-∘ (ext τ) (Ren.ext S)
        ≡⟨ cong fun (subst-≣ (ext-sub-ren-∘≣ τ S) body) ⟩
      fun (subst (sub-ren-∘ (ext τ) (Ren.ext S)) body)
        -- Use sub-ren-∘-≡ in reverse
        ≡⟨ cong fun (sym (sub-ren-∘-≡ (ext τ) body (Ren.ext S))) ⟩
      fun (Ren.rename (subst (ext τ) body) (Ren.ext S)) ∎
    where
      open ≡-Reasoning
  subst-wk τ tt = refl

  ext-∘𝕊 : ∀ {Ξ Γ Δ ty} → (σ : Sub Δ Γ) → (τ : Sub Ξ Δ)  →
    ext {ty = ty} (σ ∘𝕊 τ) ≣Sub (ext σ ∘𝕊 ext τ)
  ext-∘𝕊 σ τ Z = refl
  ext-∘𝕊 σ τ (S v) =
    Ren.wk-Tm ((σ ∘𝕊 τ) v)
      -- definition of wk-Tm
      ≡⟨ refl ⟩
    Ren.rename ((σ ∘𝕊 τ) v) S
      -- (σ ∘𝕊 τ) v = subst τ (σ v)
      ≡⟨ refl ⟩
    Ren.rename (subst τ (σ v)) S
      -- Use subst-wk in reverse: rename (subst τ tm) S = subst (ext τ) (rename tm S)
      ≡⟨ sym (subst-wk τ (σ v)) ⟩
    subst (ext τ) (Ren.rename (σ v) S)
      -- definition of wk-Tm
      ≡⟨ refl ⟩
    subst (ext τ) (Ren.wk-Tm (σ v))
      ≡⟨ refl ⟩
    subst (ext τ) ((ext σ) (S v))
      ≡⟨ refl ⟩
    (ext σ ∘𝕊 ext τ) (S v) ∎
    where
    open ≡-Reasoning

  ∘Sub-≡ :
      ∀ {Γ Δ Θ ty} (tm : Tm Δ ty) →
      (ρ : Sub Γ Δ) (ρ' : Sub Θ Γ) →
      subst ρ' (subst ρ tm) ≡ subst (ρ ∘𝕊 ρ') tm
  ∘Sub-≡ (var v) ρ ρ' = refl
  ∘Sub-≡ {Θ = Θ} {ty = ty} (rator ∙ rand) ρ ρ' =
    begin
      (subst ρ' (subst ρ rator) ∙ subst ρ' (subst ρ rand))
        -- rewrite inductively on both sides of _∙_
        ≡⟨ cong₂ (λ fn arg → fn ∙ arg) (∘Sub-≡ rator ρ ρ') (∘Sub-≡ rand ρ ρ') ⟩
      (subst (ρ ∘𝕊 ρ') rator ∙ subst (ρ ∘𝕊 ρ') rand) ∎
      where
      open ≡-Reasoning
  ∘Sub-≡ (fun body) ρ ρ' =
    begin
      fun (subst (ext ρ') (subst (ext ρ) body))
        -- Apply ∘Sub-≡ inductively to the body
        ≡⟨ cong fun (∘Sub-≡ body (ext ρ) (ext ρ')) ⟩
      fun (subst (ext ρ ∘𝕊 ext ρ') body)
        -- Use ext-∘𝕊 to move ext outside composition
        ≡⟨ cong fun (subst-≣ (≣Sub-sym (ext-∘𝕊 ρ ρ')) body) ⟩
      fun (subst (ext (ρ ∘𝕊 ρ')) body) ∎
      where
      open ≡-Reasoning
  ∘Sub-≡ tt ρ ρ' = refl

  sub/ : ∀ {Γ ty} → Tm Γ ty → Sub Γ (Γ ▸ ty)
  sub/ arg Z = arg
  sub/ _   (S v) = var v

  _/[_] : ∀ {Γ ty₁ ty₂} → Tm (Γ ▸ ty₁) ty₂ → Tm Γ ty₁ → Tm Γ ty₂
  _/[_] {Γ = Γ} {ty₁ = ty₁} sub-tm arg = subst (sub/ arg) sub-tm

  ext-S∘𝕊ext-/[] : ∀ {Γ ty wk-ty} (t : Tm Γ wk-ty) →
    ren-sub-∘ (Ren.ext {ty = ty} S) (ext (sub/ t)) ≣Sub Sub-id
  ext-S∘𝕊ext-/[] t Z = refl
  ext-S∘𝕊ext-/[] t (S v) = refl

  sub/-wk : ∀ {Γ ty wk-ty} (arg : Tm Γ wk-ty) (tm : Tm Γ ty) →
    subst (sub/ arg) (rename tm S) ≡ tm
  sub/-wk arg (var v) = refl
  sub/-wk arg (rator ∙ rand) =
    begin
      (subst (sub/ arg) (rename rator S) ∙ subst (sub/ arg) (rename rand S))
        -- Apply sub/-wk inductively on both sides
        ≡⟨ cong₂ _∙_ (sub/-wk arg rator) (sub/-wk arg rand) ⟩
      (rator ∙ rand) ∎
    where
    open ≡-Reasoning
  sub/-wk arg (fun body) =
    begin
      fun (subst (ext (sub/ arg)) (rename body (Ren.ext S)))
        -- rewrite using subst of rename
        ≡⟨ cong fun (subst-rename-≡ (ext (sub/ arg)) (Ren.ext S) body) ⟩
      fun (subst (ren-sub-∘ (Ren.ext S) (ext (sub/ arg))) body)
        -- ext S ∘ ext sub/ ≡Sub id
        ≡⟨ cong fun (subst-≣ (ext-S∘𝕊ext-/[] arg) body) ⟩
      fun (subst Sub-id body)
        -- substitution by id is id
        ≡⟨ cong fun (Sub-id-≣ body) ⟩
      fun body ∎
    where
    open ≡-Reasoning
  sub/-wk arg tt = refl

  -- single substituiton after parallel substitution
  -- similar to usual commutation of single substitution rules
  ext∘𝕊/[] :
    ∀ {Γ Δ ty₂} → (arg : Tm Δ ty₂) → (σ : Sub Γ Δ) →
      (ext σ ∘𝕊 (sub/ (subst σ arg))) ≣Sub ((sub/ arg) ∘𝕊 σ)
  ext∘𝕊/[] arg σ Z = refl
  ext∘𝕊/[] arg σ (S v) =
    begin
      (ext σ ∘𝕊 sub/ (subst σ arg)) (S v)
        -- definition
        ≡⟨ refl ⟩
      subst (sub/ (subst σ arg)) (rename (σ v) S)
        -- substituion into weakened term is the identity
        ≡⟨ sub/-wk (subst σ arg) (σ v) ⟩
      σ v
        ≡⟨ refl ⟩
      (sub/ arg ∘𝕊 σ) (S v) ∎
    where
    open ≡-Reasoning

  wk-/[] : ∀ {Γ ty} (arg : Tm Γ ty) → ren-sub-∘ S (sub/ arg) ≣Sub Sub-id
  wk-/[] arg Z = refl
  wk-/[] arg (S v) = refl

-- Equational theory (β, η)
module Equational where
  open Base
  open Syntax
  open Sub

  infix 4 _≡Tm_
  -- Note: As we are using intrinsically well-typed terms, we only can compare terms
  -- which are already of the same type
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

  ≡Tm-Equality : {Γ : Ctxt}{ty : Ty} → IsEquivalence {A = Tm Γ ty} _≡Tm_
  ≡Tm-Equality =
    record {
      refl = λ {x} → reflexivity x ;
      sym = symmetry ;
      trans = λ eq₁ eq₂ → transitivity eq₁ eq₂
      }

  ≡Tm-setoid : (Γ : Ctxt) (ty : Ty) → Setoid ℓzero ℓzero
  ≡Tm-setoid Γ ty =  record
    { Carrier       = Tm Γ ty
    ; _≈_           = _≡Tm_
    ; isEquivalence = ≡Tm-Equality
    }

  _≡Sub_ : ∀ {Δ Γ} → (ρ σ : Sub Δ Γ) → Type
  _≡Sub_ {Γ = Γ} ρ σ =  ∀ {ty} → ∀ (v : ty ∈ Γ) → ρ v ≡Tm σ v

-- Set-theoretic semantics
module Semantics where
  open Syntax
  open import Data.Product
  open import Data.Unit

  eval : ∀ {a b : Type} → (a → b) × a → b
  eval (f , a ) = f a

  module SetModel where
    open Base
    open import Data.Empty

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

    ⟦_⟧ : ∀ {Γ t} → Tm Γ t → (⟦ Γ ⟧ℂ → ⟦ t ⟧𝕋)
    ⟦ var v ⟧ = ⟦var⟧ v
    ⟦ rator ∙ rand ⟧ = λ ρ → eval (⟦ rator ⟧ ρ , ⟦ rand ⟧ ρ)
    ⟦ fun f ⟧ = λ ρ a → ⟦ f ⟧ (ρ , a)
    ⟦ tt ⟧ = λ _ → tt

    consistent : Tm ∅ 𝕆 → ⊥
    consistent t = ⟦ t ⟧ tt

    open Ren
    open ≡-Reasoning
    ⟦_⟧Ren : ∀ {Γ Δ} → Ren Δ Γ → (⟦ Δ ⟧ℂ → ⟦ Γ ⟧ℂ)
    ⟦_⟧Ren {Γ = []} ρ ⟦Δ⟧ = tt
    ⟦_⟧Ren {Γ = Γ ▸ t} {Δ = Δ} ρ ⟦Δ⟧ = ⟦ ρ ∘ S ⟧Ren ⟦Δ⟧ , ⟦var⟧ (ρ Z) ⟦Δ⟧

    ⟦⟧Ren≡ : ∀ {Γ Δ} → (σ τ : Ren Δ Γ) → (E : ⟦ Δ ⟧ℂ) → σ ≡Ren τ → ⟦ σ ⟧Ren E ≡ ⟦ τ ⟧Ren E
    ⟦⟧Ren≡ {∅} σ τ E eq = refl
    ⟦⟧Ren≡ {Γ ▸ ty} σ τ E eq =
      begin
         (⟦ σ ∘ S ⟧Ren E , ⟦ var (σ Z) ⟧ E)
           -- rewrite σ Z to τ Z using rename equality
           ≡⟨ ≡₂ (cong (λ tm → ⟦ tm ⟧ E ) (cong var (eq Z) )) ⟩
         (⟦ σ ∘ S ⟧Ren E , ⟦ var (τ Z) ⟧ E)
           -- inductively rewrite (σ ∘ S) to (τ ∘ S) using cong of Ren≡
           ≡⟨ ≡₁ (⟦⟧Ren≡ (σ ∘ S) (τ ∘ S) E λ v → eq (S v)) ⟩
         (⟦ τ ∘ S ⟧Ren E , ⟦ var (τ Z) ⟧ E) ∎
       where
       open ≡-Reasoning

    ⟦var⟧-Ren :  ∀ {Γ Ξ d} → (τ : Ren Ξ Γ) → (δ : ⟦ Ξ ⟧ℂ) → (v : d ∈ Γ)
      → ⟦var⟧ (τ v) δ ≡ ⟦var⟧ v (⟦ τ ⟧Ren δ)
    ⟦var⟧-Ren τ δ Z = refl
    ⟦var⟧-Ren τ δ (S v)
      rewrite ⟦var⟧-Ren (S ∘R τ) δ v
      = refl

    ⟦⟧-∘Ren :  ∀ {Γ Δ Ξ} → (σ : Ren Γ Δ) (τ : Ren Ξ Γ) → (δ : ⟦ Ξ ⟧ℂ) →
      (⟦ σ ∘R τ ⟧Ren δ) ≡ (⟦ σ ⟧Ren (⟦ τ ⟧Ren δ))
    ⟦⟧-∘Ren {Δ = ∅} σ τ δ = refl
    ⟦⟧-∘Ren {Δ = Δ ▸ d} σ τ δ
      rewrite ⟦⟧-∘Ren {Δ = Δ} (S ∘R σ) τ δ = ≡-× refl (⟦var⟧-Ren τ δ (σ Z))

    ⟦⟧-Ren-S : ∀ {Γ Δ ty} → (τ : Ren Δ Γ) → (ρ : ⟦ Δ ⟧ℂ)(a : ⟦ ty ⟧𝕋) →
      ⟦ S ∘ τ ⟧Ren (ρ , a) ≡ ⟦ τ ⟧Ren ρ
    ⟦⟧-Ren-S {∅} τ ρ a = refl
    ⟦⟧-Ren-S {Γ ▸ t} τ ρ a rewrite ⟦⟧-Ren-S {Γ} (τ ∘ S) ρ a = refl

    ⟦⟧-Ren-var : ∀ {Γ Δ ty} → (σ : Ren Δ Γ) → (v : ty ∈ Γ)
      → ⟦var⟧ (σ v) ≡ ⟦var⟧ v ∘ ⟦ σ ⟧Ren
    ⟦⟧-Ren-var σ Z = refl
    ⟦⟧-Ren-var σ (S v) rewrite ⟦⟧-Ren-var (σ ∘ S) v = refl

    ⟦S⟧Ren-proj₁ : ∀ {Γ ty} → (ρ : ⟦ Γ ⟧ℂ)(a : ⟦ ty ⟧𝕋) →
      ⟦ S {Γ = Γ} {m = ty} ⟧Ren (ρ , a) ≡ ρ
    ⟦S⟧Ren-proj₁ {∅} ρ a = refl
    ⟦S⟧Ren-proj₁ {Γ ▸ t} ρ@(f , s) a
      rewrite ⟦⟧-Ren-S S ρ a
      rewrite ⟦S⟧Ren-proj₁ {Γ} f s
      = refl

    ⟦⟧-Ren : ∀ {Γ Δ ty} → (tm : Tm Γ ty) → (σ : Ren Δ Γ) →
        ⟦ Ren.rename tm σ ⟧ ≡ (⟦ tm ⟧ ∘ ⟦ σ ⟧Ren)
    ⟦⟧-Ren  (var v) σ = ⟦⟧-Ren-var σ v
    ⟦⟧-Ren (rand ∙ rator) σ
      rewrite ⟦⟧-Ren rator σ
      rewrite ⟦⟧-Ren rand  σ = refl
    ⟦⟧-Ren {∅} (fun tm) σ
      rewrite ⟦⟧-Ren tm (ext σ) = refl
    ⟦⟧-Ren {Γ ▸ ty} (fun tm) σ
      rewrite ⟦⟧-Ren tm (ext σ)  =
        begin
          (λ ρ a → ⟦ tm ⟧ ((⟦ S ∘ (σ ∘ S) ⟧Ren (ρ , a) , ⟦var⟧ (σ Z) ρ) , a))
            -- Simplify ⟦ S ∘ (σ ∘ S) ⟧Ren using ⟦⟧-Ren-S
            ≡⟨ fun-ext (λ ρ → fun-ext λ a →
               cong ⟦ tm ⟧ (≡-× (≡-× (⟦⟧-Ren-S (σ ∘ S) ρ a) refl) refl))
             ⟩
          (λ ρ a → ⟦ tm ⟧ ((⟦ (σ ∘ S) ⟧Ren ρ , ⟦var⟧ (σ Z) ρ) , a)) ∎
    ⟦⟧-Ren tt σ = refl

    ⟦⟧-Wk-Tm : ∀ {Γ ty wk} → (tm : Tm Γ ty) →
        ⟦ Ren.wk-Tm {ty = wk} tm ⟧ ≡ (⟦ tm ⟧ ∘ proj₁)
    ⟦⟧-Wk-Tm {wk = wk} tm =
        begin
          ⟦ Ren.wk-Tm {ty = wk} tm ⟧
            -- Definition of wk-Tm
            ≡⟨ refl ⟩
          ⟦ rename tm S ⟧
            -- Semantics of rename
            ≡⟨ ⟦⟧-Ren tm S ⟩
          ⟦ tm ⟧ ∘ ⟦ S ⟧Ren
            -- Simplify ⟦ S ⟧Ren to proj₁
            ≡⟨ (fun-ext λ tup →
               cong (λ a → ⟦ tm ⟧ a) (⟦S⟧Ren-proj₁ (proj₁ tup) (proj₂ tup)))
             ⟩
          ⟦ tm ⟧ ∘ proj₁ ∎

    open Sub
    ⟦_⟧𝕊 :  ∀ {Γ Δ} → Sub Δ Γ → (⟦ Δ ⟧ℂ → ⟦ Γ ⟧ℂ)
    ⟦_⟧𝕊 {Γ = []} ρ ⟦Δ⟧ = tt
    ⟦_⟧𝕊 {Γ = Γ ▸ t} {Δ = Δ} ρ ⟦Δ⟧ = ⟦ ρ ∘ S ⟧𝕊 ⟦Δ⟧ , ⟦ ρ Z ⟧ ⟦Δ⟧

    ⟦⟧𝕊≡ : ∀ {Γ Δ} → {σ τ : Sub Δ Γ} → (E : ⟦ Δ ⟧ℂ) → σ ≣Sub τ → ⟦ σ ⟧𝕊 E ≡ ⟦ τ ⟧𝕊 E
    ⟦⟧𝕊≡ {∅} E eq = refl
    ⟦⟧𝕊≡ {Γ ▸ ty} {σ = σ} {τ = τ} E eq =
      begin
         (⟦ σ ∘ S ⟧𝕊 E , ⟦ σ Z ⟧ E)
           -- Use soundness on σ Z ≡ τ Z
           ≡⟨ ≡₂ (cong (λ tm → ⟦ tm ⟧ E ) (eq Z)) ⟩
         (⟦ σ ∘ S ⟧𝕊 E , ⟦ τ Z ⟧ E)
           -- Apply ⟦⟧𝕊≡ inductively on ⟦ Γ ⟧
           ≡⟨ ≡₁ (⟦⟧𝕊≡ {σ = (σ ∘ S)} {τ = (τ ∘ S)} E λ v → eq (S v)) ⟩
         (⟦ τ ∘ S ⟧𝕊 E , ⟦ τ Z ⟧ E) ∎
       where
       open ≡-Reasoning

    ⟦⟧-Tm-Wk  : ∀ {Γ : Ctxt}{wk-ty ty : Ty} → (tm : Tm Γ ty) →
      (∀ (δ : ⟦ Γ  ⟧ℂ) (d : ⟦ wk-ty ⟧𝕋) →
         (⟦ rename tm S ⟧ (δ , d)) ≡ (⟦ tm ⟧ δ))
    ⟦⟧-Tm-Wk (var v) δ d = refl
    ⟦⟧-Tm-Wk (rator ∙ rand) δ d
      rewrite ⟦⟧-Tm-Wk rator δ d
      rewrite ⟦⟧-Tm-Wk rand δ d = refl
    ⟦⟧-Tm-Wk {Γ = Γ} {wk-ty = wk-ty} (fun {dom = dom} tm) δ d
      with ⟦⟧-Ren tm (Ren.ext {ty = dom} (S {m = wk-ty}))
    ... | wkBody-lem =
      begin
         (λ a → ⟦ rename tm (Ren.ext S) ⟧ ((δ , d) , a))
           -- Use semantics of rename
           ≡⟨ fun-ext (λ a → cong (λ f → f ((δ , d) , a)) wkBody-lem ) ⟩
         (λ a → (⟦ tm ⟧ ∘ ⟦ (Ren.ext S) ⟧Ren) ((δ , d) , a))
           -- Definition of ⟦ Ren.ext S ⟧Ren
           ≡⟨ refl ⟩
         (λ a → (⟦ tm ⟧ (⟦ S ∘R S ⟧Ren ((δ , d) , a), a)))
           -- Simplify ⟦ S ∘R S ⟧Ren to δ using rw-S∘S
           ≡⟨ fun-ext (λ a → cong (λ arg → ⟦ tm ⟧ arg) (≡-× (rw-S∘S δ d a) refl)) ⟩
         (λ a → ⟦ tm ⟧ (δ , a)) ∎
      where
      rw-S∘S : ∀ (δ : ⟦ Γ  ⟧ℂ) (d : ⟦ wk-ty ⟧𝕋) (a : ⟦ dom ⟧𝕋) →
        (⟦ S ∘R S ⟧Ren ((δ , d) , a)) ≡ δ
      rw-S∘S δ d a =
        begin
           (⟦ S ∘R S ⟧Ren ((δ , d) , a))
             -- Unfold composition of renamings
             ≡⟨ ⟦⟧-∘Ren S S _ ⟩
            ⟦ S ⟧Ren (⟦ S ⟧Ren ((δ , d) , a))
             -- Apply ⟦S⟧Ren-proj₁ to inner S
             ≡⟨ cong (λ x → ⟦ S ⟧Ren x) (⟦S⟧Ren-proj₁ (δ , d) a) ⟩
            ⟦ S ⟧Ren (δ , d)
             -- Apply ⟦S⟧Ren-proj₁ to outer S
             ≡⟨ ⟦S⟧Ren-proj₁ δ d  ⟩
            δ  ∎
    ⟦⟧-Tm-Wk tt δ d = refl

    ⟦sub⟧-Rn-Wk : ∀ {Γ Δ : Ctxt}{ty : Ty} → (σ : Sub Δ Γ) →
      (∀ (δ : ⟦ Δ  ⟧ℂ) (d : ⟦ ty ⟧𝕋) →
        (⟦ Sub.ext σ ∘ S ⟧𝕊 ( δ , d )) ≡ (⟦ σ ⟧𝕊 δ))
    ⟦sub⟧-Rn-Wk {∅} σ δ d = refl
    ⟦sub⟧-Rn-Wk {Γ = Δ ▸ ty} {ty = ty'} σ δ d = ≡-× (⟦sub⟧-Rn-Wk (σ ∘ S) δ d) (lem σ δ d)
      where
        lem : ∀ {ty ty'} {Γ Δ} →
           (σ : Sub Δ (Γ ▸ ty)) (δ : ⟦ Δ ⟧ℂ) (d : ⟦ ty' ⟧𝕋) →
           ⟦ (Sub.ext σ ∘ S) Z ⟧ (δ , d) ≡ ⟦ σ Z ⟧ δ
        lem σ δ d = begin
           ⟦ (Sub.ext σ ∘ S) Z ⟧ (δ , d)
             -- Definition of Sub.ext σ (S Z)
             ≡⟨ refl  ⟩
            ⟦ wk-Tm (σ Z) ⟧ (δ , d)
             -- Definition of wk-Tm
             ≡⟨ refl  ⟩
            ⟦ rename (σ Z) S ⟧ (δ , d)
             -- Semantics of rename
             ≡⟨ cong (λ f → f (δ , d)) (⟦⟧-Ren (σ Z) S)  ⟩
            ⟦ (σ Z) ⟧ (⟦ S ⟧Ren (δ , d))
             -- Simplify ⟦ S ⟧Ren to proj₁
             ≡⟨ cong (λ a → ⟦ (σ Z) ⟧ a) (⟦S⟧Ren-proj₁ δ d)  ⟩
            ⟦ σ Z ⟧ δ  ∎

         where
         open ≡-Reasoning

    ⟦sub⟧-Wk : ∀ {Γ Δ : Ctxt}{ty : Ty} → (σ : Sub Δ Γ) →
      (∀ (δ : ⟦ Δ  ⟧ℂ) (d : ⟦ ty ⟧𝕋) →
        (⟦ Sub.ext {ty = ty} σ ⟧𝕊 ( δ , d )) ≡ (⟦ σ ⟧𝕊 δ , d))
    ⟦sub⟧-Wk {Γ} {Δ} σ δ d = ≡-× pf refl
      where

      pf : ∀ {Γ} {Δ} {ty} {σ : Sub Δ Γ} {δ : ⟦ Δ ⟧ℂ} {d : ⟦ ty ⟧𝕋 } ->
        ⟦ Sub.ext σ ∘ S ⟧𝕊 (δ , d) ≡ ⟦ σ ⟧𝕊 δ
      pf {Γ = Γ} {Δ = Δ} {σ = σ} {δ = δ} {d = d} = begin
          ⟦ Sub.ext σ ∘ S ⟧𝕊 (δ , d)
            -- Definition of Sub.ext σ ∘ S
            ≡⟨ refl ⟩
          ⟦ Ren.wk-Tm ∘ σ ⟧𝕊 (δ , d)
            -- Apply ⟦sub⟧-Rn-Wk
            ≡⟨ ⟦sub⟧-Rn-Wk {Γ = Γ} σ δ d ⟩
          ⟦ σ ⟧𝕊 δ ∎
        where
        open ≡-Reasoning

    open ≡-Reasoning
    sub-lem : ∀ {Γ Δ t} → (σ : Sub Δ Γ) → (tm : Tm Γ t)
      → (∀ (δ : ⟦ Δ ⟧ℂ) → ⟦ subst σ tm  ⟧ δ ≡ (⟦ tm ⟧ (⟦ σ ⟧𝕊 δ)))
    sub-lem σ (var Z) δ = refl
    sub-lem σ (var (S v)) δ = sub-lem (wk-Sub σ) (var v) δ
    sub-lem σ (rator ∙ rand) δ with sub-lem σ rator δ , sub-lem σ rand δ
    ... | rator-≡ , rand-≡ =
      begin
        ⟦ subst σ rator ⟧ δ (⟦ subst σ rand ⟧ δ)
          -- Apply sub-lem inductively to both rator and rand
          ≡⟨ cong₂ (λ f x → f x) rator-≡ rand-≡ ⟩
        ⟦ rator ⟧ (⟦ σ ⟧𝕊 δ) (⟦ rand ⟧ (⟦ σ ⟧𝕊 δ)) ∎
    sub-lem σ (fun {dom = dom} body) δ = fun-ext (λ ⟦d⟧ →
        begin
          ⟦ subst σ[dom] body ⟧ (δ , ⟦d⟧)
            -- Apply sub-lem inductively to the body
            ≡⟨  sub-lem σ[dom] body (δ , ⟦d⟧) ⟩
          ⟦ body ⟧ (⟦ σ[dom] ⟧𝕊 (δ , ⟦d⟧))
            -- Use ⟦sub⟧-Wk to simplify extended substitution semantics
            ≡⟨ cong (λ a → ⟦ body ⟧ a) (⟦sub⟧-Wk {ty = dom} σ δ ⟦d⟧)  ⟩
          ⟦ body ⟧ (⟦ σ ⟧𝕊 δ , ⟦d⟧) ∎
       )
      where
        σ[dom] = Sub.ext {ty = dom} σ
    sub-lem σ tt δ = refl

    ⟦⟧-Sub-id : ∀ {Γ} → (ρ : ⟦ Γ ⟧ℂ) → ⟦ Sub-id ⟧𝕊 ρ ≡ ρ
    ⟦⟧-Sub-id {∅} ρ = refl
    ⟦⟧-Sub-id {Γ'@(Γ ▸ ty)} ρ@(f , s) = ≡-× eq refl
      where
      lem : ∀ {Γ ty} → (Sub-id {Γ = (Γ ▸ ty)}) ≣Sub Sub.ext Sub-id
      lem = ≣Sub-sym Sub.ext-id

      eq : ⟦ (Sub-id ∘ S) ⟧𝕊 (f , s) ≡ f
      eq  =
        begin
          ⟦ (Sub-id ∘ S) ⟧𝕊 (f , s)
          -- lift equality on substitution to semantics
            ≡⟨ ⟦⟧𝕊≡ {Δ = Γ'} ((f , s)) (λ {v-ty} v → lem (S v)) ⟩
          ⟦ (Sub.ext Sub-id) ∘ S ⟧𝕊 (f , s)
            ≡⟨ ⟦sub⟧-Rn-Wk var f s ⟩
          ⟦ Sub-id ⟧𝕊 f
            ≡⟨ ⟦⟧-Sub-id f  ⟩
          f ∎

-- Soundness of equational theory
module Soundness where
  open import Data.Product using (_×_; proj₁; proj₂; _,_)
  open Base
  open Syntax
  open Equational
  open Semantics
  open SetModel
  open ≡-Reasoning

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

-- Cartesian closed category semantics
module CCC where
  open Function.Base renaming (_∘_ to _Fn∘_)

  open import Data.Product renaming (_×_ to _×'_)
  open import Categories.Category using (Category)
  open import Categories.Category.BinaryProducts using (BinaryProducts)
  open import Categories.Object.Product.Core using (Product)
  open import Categories.Object.Exponential
  open import Categories.Object.Terminal
  open import Categories.Category.CartesianClosed
  open import Categories.Category.Cartesian

  module CCCSemantics
    {o ℓ e}
    (𝒞 : Category o ℓ e)
    (CC-𝒞 : CartesianClosed 𝒞)
    (𝒪 : Category.Obj 𝒞)
    where
    open Base
    open Syntax renaming (_⇒_ to _𝕋⇒_)
    open Ren
    open Sub

    module 𝒞 = Category 𝒞
    module CC-𝒞 = CartesianClosed CC-𝒞
    module Cart = Cartesian CC-𝒞.cartesian
    module 𝒞-× = BinaryProducts Cart.products
    module 𝒞-Pr (A B : 𝒞.Obj) = Product (𝒞-×.product {A} {B})
    module 𝒞-𝟙 = Terminal Cart.terminal
    module exp (A B : 𝒞.Obj) =  Exponential (CC-𝒞.exp {A} {B})
    module Exp = CC-𝒞.exp
    module ExpProd = Exp.product
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
    module GlobalProducts where
      open 𝒞
      open 𝒞-×
      proj₂-β :
        ∀ {X A B : 𝒞.Obj} {h :  𝒞Hom X A} {i : 𝒞Hom X B} →  (π₂ 𝒞.∘ ⟨ h , i ⟩) 𝒞.≈ i
      proj₂-β = project₂

    ⟦_⟧𝕋 : Ty → 𝒞.Obj
    ⟦ 𝕆 ⟧𝕋 = 𝒪
    ⟦ 𝟙 ⟧𝕋 = 𝒞-𝟙.⊤
    ⟦ dom 𝕋⇒ cod ⟧𝕋 = ⟦ dom ⟧𝕋 𝒞⇒ ⟦ cod ⟧𝕋

    ⟦_⟧ℂ : Ctxt → 𝒞.Obj
    ⟦ [] ⟧ℂ = 𝒞-𝟙.⊤
    ⟦ (Γ ▸ t) ⟧ℂ = ⟦ Γ ⟧ℂ × ⟦ t ⟧𝕋
      where
        open 𝒞-×

    ⟦var⟧ : ∀ {ty Γ} → ty ∈ Γ → (𝒞Hom ⟦ Γ ⟧ℂ ⟦ ty ⟧𝕋)
    ⟦var⟧ Z = 𝒞-×.π₂
    ⟦var⟧ (S pf) = ⟦var⟧ pf 𝒞.∘ 𝒞-×.π₁
      where
        open 𝒞
        open 𝒞-×

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

    ⟦_⟧Ren : ∀ {Γ Δ} → Ren Δ Γ → (𝒞Hom ⟦ Δ ⟧ℂ ⟦ Γ ⟧ℂ)
    ⟦_⟧Ren {Γ = []} ρ = 𝒞-𝟙.!
    ⟦_⟧Ren {Γ = Γ ▸ t} {Δ = Δ} ρ = ⟨  ⟦ ρ ∘ S  ⟧Ren , ⟦var⟧ (ρ Z) ⟩
      where
        open 𝒞-× using (⟨_,_⟩)
    ⟦_⟧𝕊 :  ∀ {Γ Δ} → Sub Δ Γ → (𝒞Hom ⟦ Δ ⟧ℂ ⟦ Γ ⟧ℂ)
    ⟦_⟧𝕊 {Γ = []} ρ = 𝒞-𝟙.!
    ⟦_⟧𝕊 {Γ = Γ ▸ t} ρ = ⟨ ⟦ ρ ∘ S ⟧𝕊 , ⟦ (ρ Z) ⟧ ⟩
      where
        open 𝒞-× using (⟨_,_⟩)

    module SubstitutionLemma where
      open 𝒞
      open 𝒞-×
      ⟦var⟧-Ren :  ∀ {Γ Ξ ty} → (τ : Ren Ξ Γ) →
        (v : ty ∈ Γ) →
        ⟦var⟧ (τ v) 𝒞.≈ (⟦var⟧ v 𝒞.∘ ⟦ τ ⟧Ren)
      ⟦var⟧-Ren τ Z = Equiv.sym project₂
      ⟦var⟧-Ren {ty = ty} τ (S {m = wk} v) =
        begin
          ⟦var⟧ (τ (S v))
            ≈⟨ ⟦var⟧-Ren (S ∘R τ) v ⟩
          ⟦var⟧ v 𝒞.∘ ⟦ S ∘R τ ⟧Ren
            ≈⟨ ∘-resp-≈ Equiv.refl (Equiv.sym project₁) ⟩
          (⟦var⟧ v 𝒞.∘ (π₁ 𝒞.∘ ⟨ ⟦ (S ∘R τ) ⟧Ren , ⟦var⟧ (τ Z) ⟩))
            ≈⟨ sym-assoc ⟩
          (⟦var⟧ v 𝒞.∘ π₁) 𝒞.∘ ⟨ ⟦ (S ∘R τ) ⟧Ren , ⟦var⟧ (τ Z) ⟩
            ≈⟨ Equiv.refl ⟩
            -- def of ⟦var⟧ S v
            -- def of ⟦ τ ⟧Ren for Δ = Δ' ▸ ty
          (⟦var⟧ (S {m = wk} v) 𝒞.∘ ⟦ τ ⟧Ren) ∎
        where
          open Equiv
          open Categories.Category.Category.HomReasoning 𝒞

      ⟦⟧-∘Ren :  ∀ {Γ Δ Ξ} → (σ : Ren Γ Δ) (τ : Ren Ξ Γ) →
        (⟦ σ ∘R τ ⟧Ren) 𝒞.≈ (⟦ σ ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren)
      ⟦⟧-∘Ren {Δ = ∅} σ τ = 𝒞-𝟙.!-unique (⟦ σ ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren)
      ⟦⟧-∘Ren {Γ = Γ} {Δ = (Δ' ▸ ty)}  {Ξ = Ξ} σ τ
        =
        begin
            -- def of Ren for Δ = Δ' ▸ ty
          ⟨ ⟦ (λ x → (σ ∘R τ) (S x)) ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            -- rewrite
            ≈⟨ Equiv.refl ⟩
          ⟨ ⟦ ((S ∘R σ) ∘R τ) ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            -- inductively apply lemma on left
            ≈⟨ ⟨⟩-congʳ (⟦⟧-∘Ren ((S ∘R σ)) τ) ⟩
          ⟨ ⟦ (S ∘R σ) ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            ≈⟨ Equiv.refl ⟩
            -- def of _∘R_
          ⟨ ⟦ (S ∘R σ) ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren , ⟦var⟧ (τ (σ Z)) ⟩
            -- apply ⟦var⟧-Ren lemma
            ≈⟨ ⟨⟩-congˡ (⟦var⟧-Ren τ (σ Z)) ⟩
          ⟨ ⟦ (S ∘R σ) ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren , ⟦var⟧ (σ Z) 𝒞.∘ ⟦ τ ⟧Ren ⟩
            -- ⟨ f ∘ h , g ∘ h ⟩ ≈ ⟨ f , g ⟩ ∘ h
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
          ⟨ ⟦ (S ∘R σ) ⟧Ren , ⟦var⟧ (σ Z) ⟩ 𝒞.∘ ⟦ τ ⟧Ren ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞 {A = ⟦ Ξ ⟧ℂ} {B = ⟦ Δ' ▸ ty ⟧ℂ}

      ⟦⟧-Rn-∘ : ∀ {Γ Δ Ξ : Ctxt} → (σ : Ren Γ Δ) → (τ : Ren Ξ Γ) →
        ⟦ σ ∘R τ ⟧Ren 𝒞.≈ ⟦ σ ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren
      ⟦⟧-Rn-∘ {Δ = ∅} σ τ = 𝒞-𝟙.!-unique (⟦ σ ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren)
      ⟦⟧-Rn-∘ {Γ = Γ}  {Δ = Δ₁ ▸ t} {Ξ = Ξ} σ τ =
        begin
          ⟨ ⟦ (σ ∘R τ) Fn∘ S ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            ≈⟨ Equiv.refl ⟩
            -- def of _∘R_
            -- definitional fn associativity
          ⟨ ⟦ (S ∘R σ) ∘R τ ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Rn-∘ (S ∘R σ) τ) ⟩
            -- inductively apply theorem on left
          ⟨ ⟦ (S ∘R σ) ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren , ⟦var⟧ ((σ ∘R τ) Z) ⟩
            ≈⟨ ⟨⟩-congˡ (⟦var⟧-Ren τ (σ Z)) ⟩
            -- use ⟦var⟧ lemma on right
          ⟨ ⟦ (S ∘R σ) ⟧Ren 𝒞.∘ ⟦ τ ⟧Ren , (⟦var⟧ (σ Z)) 𝒞.∘ ⟦ τ ⟧Ren ⟩
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
          ⟨ ⟦ σ Fn∘ S ⟧Ren , ⟦var⟧ (σ Z) ⟩ 𝒞.∘ ⟦ τ ⟧Ren  ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
          module Pr = CC-𝒞.exp.product

      ⟦⟧-Ren-S : ∀ {Γ Δ t} → (σ : Ren Δ Γ) →
        ⟦ σ ∘R (S {m = t}) ⟧Ren 𝒞.≈  ⟦ σ ⟧Ren 𝒞.∘ π₁
      ⟦⟧-Ren-S {∅} σ = 𝒞-𝟙.!-unique (⟦ σ ⟧Ren 𝒞.∘ π₁)
      ⟦⟧-Ren-S {Γ ▸ t} σ =
        begin
          ⟨ ⟦ S ∘R (σ ∘R S) ⟧Ren , ⟦var⟧ (σ Z) 𝒞.∘ π₁ ⟩
            -- Reassociate renaming composition
            ≈⟨ Equiv.refl ⟩
          ⟨ ⟦ ((S ∘R σ) ∘R S) ⟧Ren  , ⟦var⟧ (σ Z) 𝒞.∘ π₁ ⟩
            -- Apply ⟦⟧-Ren-S inductively
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Ren-S ((S ∘R σ))) ⟩
          ⟨ ⟦ S ∘R σ ⟧Ren 𝒞.∘ π₁  , ⟦var⟧ (σ Z) 𝒞.∘ π₁ ⟩
            -- Factor out common π₁
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
          ⟨ ⟦ S ∘R σ ⟧Ren , ⟦var⟧ (σ Z) ⟩ 𝒞.∘ π₁ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
          module Pr = CC-𝒞.exp.product

      ⟦⟧-S : ∀ {Γ : Ctxt} {ty} →
        ⟦ S {Γ = Γ} {m = ty} ⟧Ren 𝒞.≈ π₁
      ⟦⟧-S {∅} = 𝒞-𝟙.!-unique π₁
      ⟦⟧-S {Γ ▸ t} =
        begin
          ⟨ ⟦ (S {Γ = Γ}) ∘R S ⟧Ren , π₂ 𝒞.∘ π₁ ⟩
            -- Apply ⟦⟧-Ren-S to simplify S ∘R S
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Ren-S (S {Γ = Γ})) ⟩
         ⟨ ⟦ S {Γ = Γ} ⟧Ren 𝒞.∘ π₁ , π₂ 𝒞.∘ π₁ ⟩
            -- Apply ⟦⟧-S inductively to rewrite S to π₁
            ≈⟨ ⟨⟩-congʳ (∘-resp-≈ (⟦⟧-S {Γ = Γ}) Equiv.refl) ⟩
         ⟨ π₁ 𝒞.∘ π₁ , π₂ 𝒞.∘ π₁ ⟩
            -- Factor out common π₁
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
         ⟨ π₁ , π₂ ⟩ 𝒞.∘ π₁
            -- η for products: ⟨ π₁ , π₂ ⟩ ≈ id
            ≈⟨ ∘-resp-≈ (unique identityʳ identityʳ) Equiv.refl ⟩
         𝒞.id 𝒞.∘ π₁
            -- Left identity
            ≈⟨ identityˡ ⟩
          π₁ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
      ⟦⟧-Ren : ∀ {Γ Δ ty} → (tm : Tm Γ ty) → (σ : Ren Δ Γ) →
          ⟦ Ren.rename tm σ ⟧ 𝒞.≈ (⟦ tm ⟧ 𝒞.∘ ⟦ σ ⟧Ren)
      ⟦⟧-Ren (var v) σ = ⟦var⟧-Ren σ v
      ⟦⟧-Ren (rator ∙ rand) σ =
        begin
          -- rename and semantics for _∙_
          CC-𝒞.exp.eval 𝒞.∘
            CC-𝒞.exp.product.⟨ ⟦ rename rator σ ⟧ , ⟦ rename rand σ ⟧ ⟩
            -- rewrite inner term using inductive lemma
            ≈⟨ ∘-resp-≈ Equiv.refl lemma ⟩
          CC-𝒞.exp.eval 𝒞.∘
            (CC-𝒞.exp.product.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧Ren)
            -- reassociate
            ≈⟨ sym-assoc ⟩
          (CC-𝒞.exp.eval 𝒞.∘ CC-𝒞.exp.product.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩) 𝒞.∘ ⟦ σ ⟧Ren ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
          module Pr = CC-𝒞.exp.product
          lemma :
            CC-𝒞.exp.product.⟨ ⟦ rename rator σ ⟧ , ⟦ rename rand σ ⟧ ⟩
            𝒞.≈  CC-𝒞.exp.product.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧Ren
          lemma =
            begin
              CC-𝒞.exp.product.⟨ ⟦ rename rator σ ⟧ , ⟦ rename rand σ ⟧ ⟩
                -- inductively rewrite inner terms
                ≈⟨ Pr.⟨⟩-cong₂ (⟦⟧-Ren rator σ ) (⟦⟧-Ren rand σ) ⟩
              CC-𝒞.exp.product.⟨ ⟦ rator ⟧ 𝒞.∘ ⟦ σ ⟧Ren , ⟦ rand ⟧ 𝒞.∘ ⟦ σ ⟧Ren ⟩
                -- factor our ⟦ σ ⟧ from product
                ≈⟨ Equiv.sym Pr.∘-distribʳ-⟨⟩ ⟩
              CC-𝒞.exp.product.⟨ ⟦ rator ⟧ , ⟦ rand ⟧ ⟩ 𝒞.∘ ⟦ σ ⟧Ren ∎
      ⟦⟧-Ren (fun {dom = d} body) σ =
            begin
              CC-𝒞.exp.λg 𝒞-×.product ⟦ rename body (Ren.ext σ) ⟧
                -- Apply ⟦⟧-Ren inductively to the body
                ≈⟨ λ-cong 𝒞-×.product (⟦⟧-Ren body (Ren.ext σ)) ⟩
              CC-𝒞.exp.λg 𝒞-×.product (⟦ body ⟧ 𝒞.∘ ⟦ (Ren.ext {ty = d} σ) ⟧Ren)
                -- Rewrite ⟦ Ren.ext σ ⟧Ren using lemma
                ≈⟨ λ-cong 𝒞-×.product (∘-resp-≈ Equiv.refl lemma) ⟩
              CC-𝒞.exp.λg 𝒞-×.product (⟦ body ⟧ 𝒞.∘ [ Prod ⇒ Prod ] ⟦ σ ⟧Ren ×id)
                -- Apply exponential substitution law in reverse
                ≈⟨ Equiv.sym (CC-𝒞.exp.subst 𝒞-×.product 𝒞-×.product) ⟩
              CC-𝒞.exp.λg 𝒞-×.product ⟦ body ⟧ 𝒞.∘ ⟦ σ ⟧Ren ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
          open CC-𝒞.exp
          Prod = 𝒞-×.product

          lemma : ⟨ ⟦ σ ∘R (S {m = d})⟧Ren , π₂ ⟩ 𝒞.≈ [ Prod ⇒ Prod ] ⟦ σ ⟧Ren ×id
          lemma =
            begin
              ⟨ ⟦ σ ∘R (S {m = d})⟧Ren , π₂ ⟩
                -- Apply ⟦⟧-Ren-S to simplify σ ∘R S
                ≈⟨ ⟨⟩-congʳ (⟦⟧-Ren-S σ) ⟩
              ⟨ ⟦ σ ⟧Ren 𝒞.∘ π₁ , π₂ ⟩
                -- Insert identity before π₂
                ≈⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
              ⟨ ⟦ σ ⟧Ren 𝒞.∘ π₁ , 𝒞.id 𝒞.∘ π₂ ⟩
                -- Definition of [_]_×id
                ≈⟨ Equiv.refl ⟩
              ([ Prod ⇒ Prod ] ⟦ σ ⟧Ren ×id) ∎

      ⟦⟧-Ren {Γ = Γ} {Δ = Δ} tt σ =
        -- Need to supply implicit args to ⟦ tt ⟧ 𝒞.∘ ⟦ σ ⟧Ren
        𝒞-𝟙.!-unique (𝒞._∘_ {B = ⟦ Γ ⟧ℂ} (⟦_⟧ {Γ = Γ} tt) ⟦ σ ⟧Ren)

      ⟦⟧-id-Ren : ∀ {Γ} → ⟦ Ren.id-Ren {Γ = Γ} ⟧Ren 𝒞.≈ 𝒞.id
      ⟦⟧-id-Ren {Γ = ∅} = 𝒞-𝟙.!-unique 𝒞.id
      ⟦⟧-id-Ren {Γ = Γ ▸ t} =
        begin
          -- def of ⟦_⟧Ren
          ⟨ ⟦ (S {m = t}) ∘R (Ren.id-Ren {Γ = Γ ▸ t}) ⟧Ren , π₂ ⟩
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Ren-S {Γ = Γ} Ren.id-Ren) ⟩
            -- rewrite ⟦ S ∘ τ ⟧ = ⟦ τ ⟧ ∘ π₁
          ⟨ ⟦ Ren.id-Ren {Γ = Γ} ⟧Ren 𝒞.∘ π₁ , π₂ ⟩
            ≈⟨ ⟨⟩-congʳ (∘-resp-≈ (⟦⟧-id-Ren {Γ = Γ}) Equiv.refl ) ⟩
            -- rewrite ⟦ id-Ren ⟧ inductively
          ⟨ 𝒞.id 𝒞.∘ π₁ , π₂ ⟩
            -- identity law
            ≈⟨ ⟨⟩-congʳ identityˡ ⟩
          ⟨ π₁ , π₂ ⟩
            -- η for products: ⟨ π₁ , π₂ ⟩ ≈ id
            ≈⟨ unique identityʳ identityʳ ⟩
          𝒞.id ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

      ⟦⟧-Wk-Tm : ∀ {Γ ty wk} → (tm : Tm Γ ty) →
        ⟦ Ren.wk-Tm {ty = wk} tm ⟧ 𝒞.≈ (⟦ tm ⟧ 𝒞.∘ π₁)
      ⟦⟧-Wk-Tm {Γ = Γ} {ty = ty} {wk = wk} tm =
        begin
          ⟦ wk-Tm tm ⟧
            ≈⟨ Equiv.refl ⟩
            -- def of wk-Tm
          ⟦ rename tm (S {m = wk}) ⟧
            ≈⟨ ⟦⟧-Ren tm (S {m = wk}) ⟩
          ⟦ tm ⟧ 𝒞.∘ ⟦ (S {Γ = Γ} {m = wk}) ⟧Ren
            ≈⟨ Equiv.refl ⟩
            -- id-Ren satisfies defintional identity laws
          ⟦ tm ⟧ 𝒞.∘ ⟦ Ren.id-Ren ∘R (S {Γ = Γ} {m = wk}) ⟧Ren
            ≈⟨ ∘-resp-≈ Equiv.refl (⟦⟧-Ren-S {Γ = Γ} Ren.id-Ren) ⟩
          ⟦ tm ⟧ 𝒞.∘ (⟦ Ren.id-Ren {Γ = Γ} ⟧Ren 𝒞.∘ π₁)
            ≈⟨ ∘-resp-≈ Equiv.refl (∘-resp-≈ (⟦⟧-id-Ren {Γ = Γ}) Equiv.refl) ⟩
          ⟦ tm ⟧ 𝒞.∘ (𝒞.id 𝒞.∘ π₁)
            ≈⟨ ∘-resp-≈ Equiv.refl identityˡ ⟩
          ⟦ tm ⟧ 𝒞.∘ π₁ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
      ⟦var⟧-Sub :  ∀ {Γ Ξ ty} → (τ : Sub Ξ Γ) →
         (v : ty ∈ Γ) →
         ⟦ τ v ⟧ 𝒞.≈ (⟦var⟧ v 𝒞.∘ ⟦ τ ⟧𝕊)
      ⟦var⟧-Sub τ Z =
        begin
          ⟦ τ Z ⟧
            -- π₂ ∘ ⟨ f , g ⟩ ≈ g
            ≈⟨ Equiv.sym project₂ ⟩
          π₂ 𝒞.∘ ⟨ ⟦ (τ Fn∘ S) ⟧𝕊 , ⟦ τ Z ⟧ ⟩ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
      ⟦var⟧-Sub τ (S v) =
        begin
          ⟦ τ (S v) ⟧
            ≈⟨ Equiv.refl ⟩
            -- re-associate
          ⟦ (τ Fn∘ S) v ⟧
            ≈⟨ ⟦var⟧-Sub (τ Fn∘ S) v ⟩
            -- apply induction
          ⟦var⟧ v 𝒞.∘ ⟦ τ Fn∘ S ⟧𝕊
            ≈⟨ Equiv.sym (∘-resp-≈ Equiv.refl project₁) ⟩
            -- expand to fit definition of ⟦ τ ⟧𝕊
          ⟦var⟧ v 𝒞.∘ (π₁ 𝒞.∘ ⟨ ⟦ τ Fn∘ S ⟧𝕊 , ⟦ τ Z ⟧ ⟩)
            ≈⟨ sym-assoc ⟩
            -- by def: var (S v) := (⟦var⟧ v 𝒞.∘ π₁)
            -- by def: ⟦ τ ⟧𝕊 := ⟨ ⟦ τ Fn∘ S ⟧𝕊 , ⟦ τ Z ⟧ ⟩
            --   for Γ = Γ ▸ ty, which must be the case for (S v) branch
          (⟦var⟧ v 𝒞.∘ π₁) 𝒞.∘ ⟨ ⟦ τ Fn∘ S ⟧𝕊 , ⟦ τ Z ⟧ ⟩ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

      ⟦sub⟧-Rn-Wk : ∀ {Γ Δ : Ctxt}{ty : Ty} → (σ : Sub Δ Γ) →
        ⟦ Sub.ext {ty = ty} σ Fn∘ S ⟧𝕊 𝒞.≈ ⟦ σ ⟧𝕊 𝒞.∘ π₁
      ⟦sub⟧-Rn-Wk {Γ = ∅} σ = 𝒞-𝟙.!-unique (⟦ σ ⟧𝕊 𝒞.∘ π₁)
      ⟦sub⟧-Rn-Wk {Γ = Γ ▸ t} {Δ} {ty = ty} σ =
        begin
          ⟨ ⟦ ((Sub.ext σ Fn∘ S) Fn∘ S) ⟧𝕊 , ⟦ (Sub.ext {ty = ty} σ Fn∘ S) Z ⟧ ⟩
            ≈⟨ Equiv.refl ⟩
            -- definition of Sub.ext σ (S v)
          ⟨ ⟦ (Sub.ext {ty = ty} (σ Fn∘ S) Fn∘ S) ⟧𝕊
          , ⟦ rename {Γ = Δ} (σ Z) (S {m = ty}) ⟧ ⟩
            ≈⟨ ⟨⟩-congʳ (⟦sub⟧-Rn-Wk (σ Fn∘ S)) ⟩
            -- inductively apply to first component
          ⟨ ⟦ σ Fn∘ S ⟧𝕊 𝒞.∘ π₁
          , ⟦ rename {Γ = Δ} (σ Z) (S {m = ty}) ⟧ ⟩
            ≈⟨ ⟨⟩-congˡ (⟦⟧-Wk-Tm ((σ Z))) ⟩
            -- rename tm S := Wk-Tm tm
            -- Now use Wk-Tm lemma
          ⟨ ⟦ σ Fn∘ S ⟧𝕊 𝒞.∘ π₁
          , ⟦ (σ Z) ⟧ 𝒞.∘ π₁ ⟩
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            -- factor out common π₁
          ⟨ ⟦ (σ Fn∘ S) ⟧𝕊 , ⟦ σ Z ⟧ ⟩ 𝒞.∘ π₁ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
      ⟦sub⟧-Wk : ∀ {Γ Δ : Ctxt}{ty : Ty} → (σ : Sub Δ Γ) →
          ⟦ Sub.ext {ty = ty} σ ⟧𝕊 𝒞.≈ ([ CC-Pr ⇒ CC-Pr ] ⟦ σ ⟧𝕊 ×id)
      ⟦sub⟧-Wk {Γ} {Δ} {ty} σ =
        begin
          ⟦ Sub.ext {ty = ty} σ ⟧𝕊
            ≈⟨ Equiv.refl ⟩
            -- Sub.ext σ := ⟨ ⟦ Sub.ext ∘ S ⟧𝕊 , ⟦ (Sub.ext σ) Z ⟧ ⟩
            -- ⟦ (Sub.ext σ) Z ⟧ := ⟦ var Z ⟧
            -- ⟦ var Z ⟧ := π₂
          ⟨ ⟦ wk-Tm {ty = ty} Fn∘ σ ⟧𝕊 , π₂ ⟩
            ≈⟨ ⟨⟩-congʳ (⟦sub⟧-Rn-Wk σ) ⟩
            -- apply ⟦sub⟧-Rn-Wk
          ⟨ ⟦ σ ⟧𝕊 𝒞.∘ π₁ , π₂ ⟩
            ≈⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
          ⟨ ⟦ σ ⟧𝕊 𝒞.∘ π₁ , 𝒞.id 𝒞.∘ π₂ ⟩
            ≈⟨ Equiv.refl ⟩
          [ CC-Pr ⇒ CC-Pr ] ⟦ σ ⟧𝕊 ×id ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
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

      ⟦⟧-Sub-S : ∀ {Γ Δ}{t : Ty} → (σ : Sub Δ (Γ ▸ t)) →
        ⟦ σ Fn∘ S ⟧𝕊 𝒞.≈ π₁ 𝒞.∘ ⟦ σ ⟧𝕊
      ⟦⟧-Sub-S {Γ = ∅} σ = 𝒞-𝟙.!-unique (π₁ 𝒞.∘ ⟦ σ ⟧𝕊)
      ⟦⟧-Sub-S {Γ = Γ ▸ t'} σ =
        begin
          ⟨ ⟦ (σ Fn∘ S) Fn∘ S ⟧𝕊 , ⟦ σ (S Z) ⟧ ⟩
            -- π₁ ∘ ⟨ f , g ⟩ ≈ f
            ≈⟨ Equiv.sym project₁ ⟩
          π₁ 𝒞.∘ ⟨ ⟨ ⟦ (σ Fn∘ S) Fn∘ S ⟧𝕊 , ⟦ σ (S Z) ⟧ ⟩ , ⟦ σ Z ⟧ ⟩ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

      ⟦⟧-Sub-id-∘ : ∀ {Ξ Γ} → (σ : Ren Ξ Γ) →
        ⟦ Sub-id {Γ = Ξ} Fn∘ σ  ⟧𝕊 𝒞.≈ ⟦ σ ⟧Ren
      ⟦⟧-Sub-id-∘ {Γ = ∅} σ = Equiv.refl
      ⟦⟧-Sub-id-∘ {Ξ = Ξ} {Γ = Γ ▸ t} σ =
        begin
          -- TODO: explain this proof
          ⟨ ⟦ (Sub-id {Γ = Ξ} Fn∘ σ) Fn∘ S ⟧𝕊 , ⟦var⟧ (σ Z) ⟩
            ≈⟨ Equiv.refl ⟩
          ⟨ ⟦ (Sub-id {Γ = Ξ} Fn∘ ( σ Fn∘ S)) ⟧𝕊 , ⟦var⟧ (σ Z)  ⟩
            ≈⟨ ⟨⟩-congˡ (⟦var⟧-Ren σ Z) ⟩
          ⟨ ⟦ (Sub-id Fn∘ (σ Fn∘ S)) ⟧𝕊 , (⟦var⟧ {Γ = Γ ▸ t} Z) 𝒞.∘ ⟦ σ ⟧Ren ⟩
            ≈⟨ Equiv.refl ⟩
          ⟨ ⟦ (Sub-id Fn∘ (σ Fn∘ S)) ⟧𝕊 , π₂ 𝒞.∘ ⟦ σ ⟧Ren ⟩
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Sub-id-∘ (σ Fn∘ S)) ⟩
          ⟨ ⟦ ( σ Fn∘ S) ⟧Ren , π₂ 𝒞.∘ ⟦ σ ⟧Ren ⟩
            ≈⟨ Equiv.refl ⟩
          ⟨ ⟦ (S ∘R σ) ⟧Ren , π₂ 𝒞.∘ ⟦ σ ⟧Ren ⟩
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Rn-∘ S σ) ⟩
          ⟨ ⟦ S {Γ = Γ} ⟧Ren 𝒞.∘ ⟦ σ ⟧Ren , π₂ 𝒞.∘ ⟦ σ ⟧Ren ⟩
            ≈⟨ Equiv.sym ⟨⟩∘ ⟩
          ⟨ ⟦ S {Γ = Γ} ⟧Ren , π₂  ⟩ 𝒞.∘ ⟦ σ ⟧Ren
            ≈⟨ ∘-resp-≈ (⟨⟩-congʳ (⟦⟧-S {Γ = Γ})) Equiv.refl ⟩
          ⟨ π₁ , π₂ ⟩ 𝒞.∘ ⟦ σ ⟧Ren
            ≈⟨ ∘-resp-≈ (unique identityʳ identityʳ) Equiv.refl ⟩
          𝒞.id 𝒞.∘ ⟦ σ ⟧Ren
            ≈⟨ identityˡ ⟩
          ⟦ σ ⟧Ren  ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

      ⟦⟧-Sub-id : ∀ {Γ} →
        ⟦ Sub-id {Γ = Γ}  ⟧𝕊 𝒞.≈ 𝒞.id
      ⟦⟧-Sub-id {Γ = ∅} = 𝒞-𝟙.!-unique 𝒞.id
      ⟦⟧-Sub-id {Γ = Γ ▸ t} =
        begin
          ⟨ ⟦ (Sub-id {Γ ▸ t}) Fn∘ S ⟧𝕊 , π₂ ⟩
            -- Rewrite Sub-id Fn∘ S to ⟦ S ⟧Ren
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Sub-id-∘ {Ξ = Γ ▸ t} S) ⟩
          ⟨ ⟦ S {Γ = Γ} ⟧Ren , π₂ ⟩
            -- Rewrite ⟦ S ⟧Ren to π₁
            ≈⟨ ⟨⟩-congʳ (⟦⟧-S {Γ = Γ}) ⟩
          ⟨ π₁ , π₂ ⟩
            -- η for products: ⟨ π₁ , π₂ ⟩ ≈ id
            ≈⟨ unique identityʳ identityʳ ⟩
          𝒞.id ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

      module CCCSoundness where
      open Equational

      sub/-lemma :
        {Γ : Ctxt} {d c : Ty} → (body : Tm (Γ ▸ d) c) (arg : Tm Γ d) →
        ⟦ sub/ arg ⟧𝕊 𝒞.≈ ⟨ 𝒞.id , ⟦ arg ⟧ ⟩
      sub/-lemma {Γ = ∅} body arg = ⟨⟩-cong₂ (𝒞-𝟙.!-unique 𝒞.id) Equiv.refl
      sub/-lemma {Γ = Γ ▸ t} body arg =
        begin
          ⟨ ⟨ ⟦ var {Γ = Γ ▸ t} Fn∘ S ⟧𝕊 , π₂ ⟩ , ⟦ arg ⟧ ⟩
            -- Apply ⟦⟧-Sub-S to simplify var Fn∘ S
            ≈⟨ ⟨⟩-congʳ (⟨⟩-congʳ (⟦⟧-Sub-S {Γ = Γ} var)) ⟩
          ⟨ ⟨ π₁ 𝒞.∘ ⟦ var {Γ ▸ t} ⟧𝕊 , π₂ ⟩ , ⟦ arg ⟧ ⟩
            -- Rewrite ⟦ var ⟧𝕊 to 𝒞.id
            ≈⟨ ⟨⟩-congʳ (⟨⟩-congʳ (∘-resp-≈ Equiv.refl (⟦⟧-Sub-id {Γ = Γ ▸ t}))) ⟩
          ⟨ ⟨ π₁ 𝒞.∘ 𝒞.id , π₂ ⟩ , ⟦ arg ⟧ ⟩
            -- Right identity
            ≈⟨ ⟨⟩-congʳ (⟨⟩-congʳ identityʳ) ⟩
          ⟨ ⟨ π₁ , π₂ ⟩ , ⟦ arg ⟧ ⟩
            -- η for products: ⟨ π₁ , π₂ ⟩ ≈ id
            ≈⟨ ⟨⟩-congʳ (unique identityʳ identityʳ) ⟩
          ⟨ 𝒞.id , ⟦ arg ⟧ ⟩ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞
      var-lemma :
        {Γ : Ctxt} {t : Ty} → (v v' : t ∈ Γ) → v ≡ v' →
        ⟦var⟧ v ≈ ⟦var⟧ v'
      var-lemma Z .Z refl = Equiv.refl
      var-lemma (S v) (S v') eq =
        begin
          ⟦var⟧ v 𝒞.∘ π₁
            -- Apply var-lemma inductively using S-inj
            ≈⟨ ∘-resp-≈ (var-lemma v v' (S-inj eq)) Equiv.refl ⟩
          ⟦var⟧ v' 𝒞.∘ π₁ ∎
        where
        open Categories.Category.Category.HomReasoning 𝒞
      β-lemma :
        {Γ : Ctxt} {d c : Ty} → (body : Tm (Γ ▸ d) c) (arg : Tm Γ d) →
        ⟦ body /[ arg ] ⟧
          𝒞.≈
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
            -- rewrite ⟦ body ⟧ to Exp.eval ∘ λ ⟦ body ⟧ × id
            -- In more detail, we have:
            --   g : A × B → C ≈
            --   A × B -- ĝ × id --> C^B × B -- eval --> C
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
      η-lemma :
        {Γ : Ctxt} {d c : Ty} → (fn-tm : Tm Γ (d Ty.⇒ c)) →
          Exp.λg 𝒞-×.product
        (Exp.eval 𝒞.∘ Exp.product.⟨ ⟦ wk-Tm {ty = d} fn-tm ⟧ , π₂ ⟩)
          ≈
        ⟦ fn-tm ⟧
      η-lemma fn-tm =
        begin
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ℰ-Prod.⟨ ⟦ wk-Tm fn-tm ⟧ , π₂ ⟩)
            -- semantics of wk i.e.
            -- ⟦ wk-Tm fn-tm ⟧ ≈ ⟦ fn-tm ⟧ 𝒞.∘ π₁
            ≈⟨ Exp.λ-cong 𝒞-prod (∘-resp-≈ Equiv.refl (ℰ-Prod.⟨⟩-cong₂ (⟦⟧-Wk-Tm fn-tm) Equiv.refl)) ⟩
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ℰ-Prod.⟨ ⟦ fn-tm ⟧ 𝒞.∘ π₁ , π₂ ⟩)
            -- rewrite π₂ to 𝒞.id 𝒞.∘ π₂ to factor out ⟨ π₁ , π₂ ⟩
            ≈⟨ Exp.λ-cong 𝒞-prod (∘-resp-≈ Equiv.refl (ℰ-Prod.⟨⟩-cong₂ Equiv.refl (Equiv.sym identityˡ))) ⟩
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ℰ-Prod.⟨ ⟦ fn-tm ⟧ 𝒞.∘ π₁ , 𝒞.id 𝒞.∘ π₂ ⟩)
            -- rewrite using inverse of ×∘⟨⟩ i.e.
            -- ⟨f ∘ h₁, g ∘ h₂⟩ ≈ f×g∘⟨h₁,h₂⟩
            ≈⟨ Exp.λ-cong 𝒞-prod (∘-resp-≈ Equiv.refl (Equiv.sym [ 𝒞-prod ⇒ ℰ-prod ]×∘⟨⟩)) ⟩
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ((𝒫𝓇.[ 𝒞-prod ⇒ ℰ-prod ]  (⟦ fn-tm ⟧) × 𝒞.id) 𝒞.∘ ⟨ π₁ , π₂ ⟩))
            -- η for products: ⟨ π₁ , π₂ ⟩ ≈ id
            ≈⟨ Exp.λ-cong 𝒞-prod (∘-resp-≈ Equiv.refl (∘-resp-≈ Equiv.refl (unique identityʳ identityʳ))) ⟩
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ((𝒫𝓇.[ 𝒞-prod ⇒ ℰ-prod ]  (⟦ fn-tm ⟧) × 𝒞.id) 𝒞.∘ 𝒞.id))
            -- Remove composition with 𝒞.id
            ≈⟨ Exp.λ-cong 𝒞-prod (∘-resp-≈ Equiv.refl identityʳ) ⟩
          Exp.λg 𝒞-prod (Exp.eval 𝒞.∘ ((𝒫𝓇.[ 𝒞-prod ⇒ ℰ-prod ]  (⟦ fn-tm ⟧) × 𝒞.id)))
            -- apply η for function objects:
            -- rewrite λ (eval ∘ ⟦ fn-tm ⟧) ≈ ⟦ fn-tm ⟧
            -- In more detail, we have:
            -- g : A → C^B ≈
            -- adjoint of: A × B -- g × id --> C^B × B -- eval --> C
            ≈⟨ Exp.η 𝒞-prod ⟩
          ⟦ fn-tm ⟧ ∎
        where
          𝒞-prod = 𝒞-×.product
          module ℰ-Prod = Exp.product
          ℰ-prod = Exp.product
          open import Categories.Object.Product.Morphisms 𝒞 as 𝒫𝓇
            using ([_⇒_]_×_; [_⇒_]×∘⟨⟩)
          open Categories.Category.Category.HomReasoning 𝒞
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

      ⟦⟧-Sub-≡ : ∀ {Γ Δ} → (σ τ : Sub Δ Γ) → σ ≡Sub τ →  ⟦ σ ⟧𝕊 𝒞.≈ ⟦ τ ⟧𝕊
      ⟦⟧-Sub-≡ {Γ = ∅} σ τ eq = Equiv.refl
      ⟦⟧-Sub-≡ {Γ = Γ ▸ t} σ τ eq =
        begin
          ⟨ ⟦ (σ Fn∘ S) ⟧𝕊 , ⟦ σ Z ⟧ ⟩
            -- Apply ⟦⟧-Sub-≡ inductively for ⟦ Γ ⟧
            ≈⟨ ⟨⟩-congʳ (⟦⟧-Sub-≡ ((σ Fn∘ S)) (τ Fn∘ S) λ v → eq (S v)) ⟩
          ⟨ ⟦ (τ Fn∘ S) ⟧𝕊 , ⟦ σ Z ⟧ ⟩
            -- Use soundness on σ Z ≡Tm τ Z
            ≈⟨ ⟨⟩-congˡ (⟦⟧-Soundness (eq Z)) ⟩
          ⟨ ⟦ (τ Fn∘ S) ⟧𝕊 , ⟦ τ Z ⟧ ⟩ ∎
        where
          open Categories.Category.Category.HomReasoning 𝒞

-- Syntactic categories from renamings and substitutions
module SyntacticCategories where
  module Ren-Cat where
  open Base
  open Syntax
  open Ren
  open Equational
  open import Categories.Category using (Category)

  ≡Ren-equiv : {Γ Δ : Ctxt} → IsEquivalence (_≡Ren_ {Γ = Γ} {Δ = Δ})
  ≡Ren-equiv =
    record {
      refl = λ _ → refl ;
      sym = sym-R ;
      trans = λ {r₁} {r₂} {r₃} eq₁ eq₂ v → trans (eq₁ v) (eq₂ v)
      }

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

  module Sub-Cat where
  open Base
  open Syntax
  open Ren
  open Sub
  open Equational
  open import Categories.Category using (Category)
  import Relation.Binary.Reasoning.Setoid as Reasoning

  rename-≡Ren : ∀ {Δ Γ} {ty} → (σ ρ : Ren Δ Γ) → (tm  : Tm Γ ty) → σ ≡Ren ρ →
    rename tm σ ≡Tm rename tm ρ
  rename-≡Ren σ ρ (var v) eq = var-cong (eq v)
  rename-≡Ren σ ρ (rator ∙ rand) eq =
    ∙-cong
      (rename rator σ)
      (rename rator ρ)
      (rename rand σ)
      (rename rand ρ)
      (rename-≡Ren σ ρ rator eq)
      (rename-≡Ren σ ρ rand eq)
  rename-≡Ren σ ρ (fun tm) eq =
    fun-cong
      (rename tm (Ren.ext σ))
      (rename tm (Ren.ext ρ))
      (rename-≡Ren (Ren.ext σ) (Ren.ext ρ) tm (Ren.ext-≡ eq))
  rename-≡Ren σ ρ tt eq = reflexivity (rename tt σ)

  ∘R-≡Tm :
      ∀ {Γ Δ Θ t} (tm : Tm Δ t) →
      (ρ  : Ren Γ Δ) (ρ' : Ren Θ Γ) →
      rename (rename tm ρ) ρ' ≡Tm rename tm (ρ ∘R ρ')
  ∘R-≡Tm (var v) ρ ρ' = reflexivity (rename (rename (var v) ρ) ρ')
  ∘R-≡Tm {Θ = Θ} {t = ty} (rator ∙ rand) ρ ρ' =
    begin
      (rename (rename rator ρ) ρ' ∙ rename (rename rand ρ) ρ')
        -- Apply ∘R-≡Tm inductively to both rator and rand
        ≈⟨
          ∙-cong
            (rename (rename rator ρ) ρ')
            (rename rator (ρ ∘R ρ'))
            (rename (rename rand ρ) ρ')
            (rename rand (ρ ∘R ρ'))
            (∘R-≡Tm rator ρ ρ')
            (∘R-≡Tm rand ρ ρ')
         ⟩
      (rename rator (ρ ∘R ρ') ∙ rename rand (ρ ∘R ρ')) ∎
    where
    open Reasoning (≡Tm-setoid Θ ty)
  ∘R-≡Tm {Δ = Δ} {Θ = Θ} {t = ty} (fun {dom = d} {cod = c} body) ρ ρ' =
    begin
      fun (rename (rename body (Ren.ext ρ)) (Ren.ext ρ'))
        -- inductively rewrite the body as a composition
        ≈⟨
          fun-cong
            (rename (rename body (Ren.ext ρ)) (Ren.ext ρ'))
            (rename body (Ren.ext ρ ∘R Ren.ext ρ'))
            (∘R-≡Tm body (Ren.ext ρ) (Ren.ext ρ'))
         ⟩
      fun (rename body ((Ren.ext ρ) ∘R (Ren.ext ρ')))
        -- Now use that ext (ρ ∘R ρ') ≡Ren (ext ρ ∘R ext ρ')
        ≈⟨
          fun-cong
            (rename body (Ren.ext ρ ∘R Ren.ext ρ'))
            (rename body (Ren.ext (ρ ∘R ρ')))
            (rename-≡Ren
              (Ren.ext ρ ∘R Ren.ext ρ')
              (Ren.ext (ρ ∘R ρ'))
              body
              (sym-R (ext-∘R ρ ρ')))
          ⟩
      fun (rename body (Ren.ext (ρ ∘R ρ'))) ∎
    where
    open Reasoning (≡Tm-setoid Θ ty)
  ∘R-≡Tm tt ρ ρ' = reflexivity (rename (rename tt ρ) ρ')

  ≡→≡Tm : ∀ {Γ ty} {tm₁ tm₂ : Tm Γ ty} → tm₁ ≡ tm₂ → tm₁ ≡Tm tm₂
  ≡→≡Tm refl = reflexivity _

  ≣→≡Sub : ∀ {Γ Δ} {σ₁ σ₂ : Sub Γ Δ} → σ₁ ≣Sub σ₂ → σ₁ ≡Sub σ₂
  ≣→≡Sub {σ₂ = σ₂} eq v rewrite eq v = reflexivity (σ₂ v)

  ext-ren-sub-∘ : ∀ {Γ Δ Ξ ty} (σ : Sub Ξ Δ) (ρ : Ren Δ Γ) →
    Sub.ext {ty = ty} (ren-sub-∘ ρ σ) ≡Sub ren-sub-∘ (Ren.ext ρ) (Sub.ext σ)
  ext-ren-sub-∘ σ ρ = ≣→≡Sub (ext-ren-sub-∘≣ σ ρ)

  ext-sub-ren-∘ : ∀ {Γ Δ Ξ ty} (σ : Sub Δ Γ) (ρ : Ren Ξ Δ) →
    Sub.ext {ty = ty} (sub-ren-∘ σ ρ) ≡Sub sub-ren-∘ (Sub.ext σ) (Ren.ext ρ)
  ext-sub-ren-∘ σ ρ = ≣→≡Sub (ext-sub-ren-∘≣ σ ρ)

  subst-id : ∀ {Γ t} → ∀ (tm : Tm Γ t) → subst Sub-id tm ≡Tm tm
  subst-id tm = ≡→≡Tm (Sub-id-≣ tm)

  -- Lemma: sub/ commutes with renaming in a specific way
  sub/-ren-comm : ∀ {Γ Δ wk-ty ty} (arg : Tm Γ ty) (ρ : Ren Δ Γ) →
    sub-ren-∘ (Sub.ext {ty = wk-ty} (sub/ arg)) (Ren.ext ρ) ≣Sub
    ren-sub-∘ (Ren.ext (Ren.ext ρ)) (Sub.ext (sub/ (rename arg ρ)))
  sub/-ren-comm arg ρ Z = refl
  sub/-ren-comm arg ρ (S Z) =
    begin
      rename (wk-Tm arg) (Ren.ext ρ)
        ≡⟨ refl ⟩
      rename (rename arg S) (Ren.ext ρ)
        ≡⟨ sym (rename-∘R arg S (Ren.ext ρ)) ⟩
      rename arg (S ∘R Ren.ext ρ)
        ≡⟨ rename-≡ (ext-S∘ext ρ) arg ⟩
      rename arg (ρ ∘R S)
        ≡⟨ rename-∘R arg ρ S ⟩
      rename (rename arg ρ) S
        -- definition of wk-Tm
        ≡⟨ refl ⟩
      wk-Tm (rename arg ρ) ∎
    where open ≡-Reasoning
  sub/-ren-comm arg ρ (S (S v)) = refl

  -- rename (subst σ t) ρ  =  subst (rename each term in σ by ρ) t
  sub-ren-∘st : ∀ {Γ Δ Ξ ty}
    (σ : Sub Δ Γ) (tm : Tm Γ ty) (ρ : Ren Ξ Δ) →
    rename (subst σ tm) ρ ≡Tm subst (sub-ren-∘ σ ρ) tm
  sub-ren-∘st σ (var v) ρ = reflexivity (rename (subst σ (var v)) ρ)
  sub-ren-∘st σ (rator ∙ rand) ρ =
    ∙-cong
      (rename (subst σ rator) ρ)
      (subst (sub-ren-∘ σ ρ) rator)
      (rename (subst σ rand) ρ) (subst (sub-ren-∘ σ ρ) rand)
      (sub-ren-∘st σ rator ρ) (sub-ren-∘st σ rand ρ)
  sub-ren-∘st {Ξ = Ξ} {ty = ty} σ (fun body) ρ =
    begin
      rename (subst σ (fun body)) ρ
        -- Definition of subst for fun
        ≈⟨ reflexivity _ ⟩
      rename (fun (subst (Sub.ext σ) body)) ρ
        -- Definition of rename for fun
        ≈⟨ reflexivity _ ⟩
      fun (rename (subst (Sub.ext σ) body) (Ren.ext ρ))
        -- Apply sub-ren-∘st inductively to the body
        ≈⟨ fun-cong _ _ (sub-ren-∘st (Sub.ext σ) body (Ren.ext ρ)) ⟩
      fun (subst (sub-ren-∘ (Sub.ext σ) (Ren.ext ρ)) body)
        -- Use ext-sub-ren-∘≣ to move ext outside
        ≈⟨ fun-cong _ _ (≡→≡Tm (subst-≣ (≣Sub-sym (ext-sub-ren-∘≣ σ ρ)) body)) ⟩
      fun (subst (Sub.ext (sub-ren-∘ σ ρ)) body) ∎
    where
      open Reasoning (≡Tm-setoid Ξ ty)
  sub-ren-∘st σ tt ρ = reflexivity (rename (subst σ tt) ρ)

  -- subst σ (rename ρ t)  =  subst (σ ∘ ρ) t
  subst-rename : ∀ {Γ Δ Ξ ty}
    (σ : Sub Ξ Δ) (ρ : Ren Δ Γ) (tm : Tm Γ ty) →
    subst σ (rename tm ρ) ≡Tm subst (ren-sub-∘ ρ σ) tm
  subst-rename σ ρ (var v) = reflexivity (subst σ (rename (var v) ρ))
  subst-rename {Ξ = Ξ} {ty = ty} σ ρ (rator ∙ rand) =
    begin
      subst σ (rename rator ρ ∙ rename rand ρ)
        -- Definition of subst for ∙
        ≈⟨ reflexivity _ ⟩
      (subst σ (rename rator ρ) ∙ subst σ (rename rand ρ))
        -- Apply subst-rename inductively to both sides
        ≈⟨ ∙-cong _ _ _ _
             (subst-rename σ ρ rator)
             (subst-rename σ ρ rand) ⟩
      (subst (ren-sub-∘ ρ σ) rator ∙ subst (ren-sub-∘ ρ σ) rand) ∎
    where
      open Reasoning (≡Tm-setoid Ξ ty)
  subst-rename {Ξ = Ξ} {ty = ty} σ ρ (fun body) =
    begin
      subst σ (fun (rename body (Ren.ext ρ)))
        -- Definition of subst for fun
        ≈⟨ reflexivity _ ⟩
      fun (subst (Sub.ext σ) (rename body (Ren.ext ρ)))
        -- Apply subst-rename inductively to the body
        ≈⟨ fun-cong _ _ (subst-rename (Sub.ext σ) (Ren.ext ρ) body) ⟩
      fun (subst (ren-sub-∘ (Ren.ext ρ) (Sub.ext σ)) body)
        -- Use ext-ren-sub-∘≣ to move ext outside
        ≈⟨ fun-cong _ _ (symmetry (≡→≡Tm (subst-≣ (ext-ren-sub-∘≣ σ ρ) body))) ⟩
      fun (subst (Sub.ext (ren-sub-∘ ρ σ)) body) ∎
    where
      open Reasoning (≡Tm-setoid Ξ ty)
  subst-rename σ ρ tt = reflexivity (subst σ (rename tt ρ))

  rename/[] :
      ∀ {Γ Δ ty v-ty} (tm : Tm (Δ ▸ v-ty) ty) → (arg : Tm Δ v-ty) →
      (ρ  : Ren Γ Δ) →
      rename tm (Ren.ext ρ) /[ rename arg ρ ] ≡Tm
      rename (tm /[ arg ]) ρ
  rename/[] (var Z) arg ρ =
    reflexivity (rename (var Z) (Ren.ext ρ) /[ rename arg ρ ])
  rename/[] (var (S v)) arg ρ =
    reflexivity (rename (var (S v)) (Ren.ext ρ) /[ rename arg ρ ])
  rename/[] {Γ = Γ} {ty = ty} (rator ∙ rand) arg ρ =
    begin
      ((rename rator (Ren.ext ρ) ∙ rename rand (Ren.ext ρ)) /[ rename arg ρ ])
        -- Definition of /[_] for ∙
        ≈⟨ reflexivity _ ⟩
      (subst (sub/ (rename arg ρ)) (rename rator (Ren.ext ρ)) ∙
       subst (sub/ (rename arg ρ)) (rename rand (Ren.ext ρ)))
        -- Apply rename/[] inductively to both sides
        ≈⟨ ∙-cong _ _ _ _
             (rename/[] rator arg ρ)
             (rename/[] rand arg ρ) ⟩
      (rename (subst (sub/ arg) rator) ρ ∙ rename (subst (sub/ arg) rand) ρ) ∎
    where
    open Reasoning (≡Tm-setoid Γ ty)
  rename/[] {Γ = Γ} {ty = ty} (fun tm) arg ρ =
    begin
      (fun (rename tm (Ren.ext (Ren.ext ρ))) /[ rename arg ρ ])
        ≈⟨ reflexivity _ ⟩
      fun (subst (Sub.ext (sub/ (rename arg ρ))) (rename tm (Ren.ext (Ren.ext ρ))))
        -- Apply subst-rename to rewrite subst of rename
        ≈⟨ fun-cong _ _ (subst-rename (Sub.ext (sub/ (rename arg ρ))) (Ren.ext (Ren.ext ρ)) tm) ⟩
      fun (subst (ren-sub-∘ (Ren.ext (Ren.ext ρ)) (Sub.ext (sub/ (rename arg ρ)))) tm)
        -- Use sub/-ren-comm to show substitutions are equal
        ≈⟨ fun-cong _ _ (≡→≡Tm (subst-≣ (≣Sub-sym (sub/-ren-comm arg ρ)) tm)) ⟩
      fun (subst (sub-ren-∘ (Sub.ext (sub/ arg)) (Ren.ext ρ)) tm)
        -- Apply sub-ren-∘st in reverse to get rename of subst
        ≈⟨ fun-cong _ _ (symmetry (sub-ren-∘st (Sub.ext (sub/ arg)) tm (Ren.ext ρ))) ⟩
      fun (rename (subst (Sub.ext (sub/ arg)) tm) (Ren.ext ρ))
        ≈⟨ reflexivity _ ⟩
      rename (fun (subst (Sub.ext (sub/ arg)) tm)) ρ
        ≈⟨ reflexivity _ ⟩
      rename (fun tm /[ arg ]) ρ ∎
    where
    open Reasoning (≡Tm-setoid Γ ty)
  rename/[] tt arg ρ = reflexivity (rename tt (Ren.ext ρ) /[ rename arg ρ ])

  rename-wk-≡Tm : ∀ {Δ Γ} {wk-ty ty} → (σ : Ren Δ Γ) → (tm : Tm Γ ty) →
    rename (wk-Tm {ty = wk-ty} tm) (Ren.ext σ) ≡Tm wk-Tm (rename tm σ)
  rename-wk-≡Tm {Δ = Δ} {wk-ty = wk-ty} {ty = ty} σ tm =
    begin
      rename (wk-Tm {ty = wk-ty} tm) (Ren.ext σ)
        -- defintion of wk-Tm
        ≈⟨ reflexivity (rename (wk-Tm tm) (Ren.ext σ)) ⟩
      rename (rename tm S) (Ren.ext σ)
        ≈⟨ ∘R-≡Tm tm S (Ren.ext σ) ⟩
      rename tm (S ∘R Ren.ext σ)
        ≈⟨ rename-≡Ren (S ∘R Ren.ext σ) (σ ∘R S) tm (ext-S∘ext σ) ⟩
      rename tm (σ ∘R S)
        ≈⟨ symmetry (∘R-≡Tm tm σ S) ⟩
      rename (rename tm σ) S
        -- defintion of wk-Tm
        ≈⟨ reflexivity (rename (rename tm σ) S) ⟩
      wk-Tm (rename tm σ) ∎
    where
    open Reasoning (≡Tm-setoid (Δ ▸ wk-ty) ty)

  rename-≡Tm : ∀ {Δ Γ} {ty} → (σ : Ren Δ Γ) → (tm₁ tm₂ : Tm Γ ty) → tm₁ ≡Tm tm₂ →
    rename tm₁ σ ≡Tm rename tm₂ σ
  rename-≡Tm σ tm₁ tm₂ (reflexivity tm) = reflexivity (rename tm₁ σ)
  rename-≡Tm σ tm₁ tm₂ (symmetry eq) = symmetry (rename-≡Tm σ tm₂ tm₁ eq)
  rename-≡Tm σ tm₁ tm₂ (transitivity eq eq₁) = transitivity (rename-≡Tm σ tm₁ _ eq) (rename-≡Tm σ _ tm₂ eq₁)
  rename-≡Tm {Δ = Δ} {ty = ty} σ tm₁ tm₂ (β-red body arg) =
    begin
      (fun (rename body (Ren.ext σ)) ∙ rename arg σ)
        -- Apply β-reduction
        ≈⟨ β-red (rename body (Ren.ext σ)) (rename arg σ) ⟩
      rename body (Ren.ext σ) /[ rename arg σ ]
        -- Use rename/[] to commute rename and /[_]
        ≈⟨ rename/[] body arg σ ⟩
      rename (body /[ arg ]) σ ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
  rename-≡Tm {Δ = Δ} {ty = ty} σ tm₁ tm₂ (η-fn fn-tm) =
    begin
      fun (rename (wk-Tm tm₂) (Ren.ext σ) ∙ var Z)
        -- Use rename-wk-≡Tm to commute rename and wk-Tm
        ≈⟨
          fun-cong _ _
            (∙-cong _ _ _ _
              (rename-wk-≡Tm σ fn-tm)
              (reflexivity (var Z)))
          ⟩
      fun (wk-Tm (rename fn-tm σ) ∙ var Z)
        -- Apply η-reduction
        ≈⟨ η-fn (rename tm₂ σ) ⟩
      rename tm₂ σ ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
  rename-≡Tm σ (var v) (var v') (var-cong v-eq) = var-cong (cong σ v-eq)
  rename-≡Tm σ tm₁ tm₂ (∙-cong fn₁ fn₂ arg₁ arg₂ eq eq₁) =
    ∙-cong
      (rename fn₁ σ)
      (rename fn₂ σ)
      (rename arg₁ σ)
      (rename arg₂ σ)
      (rename-≡Tm σ fn₁ fn₂ eq)
      (rename-≡Tm σ arg₁ arg₂ eq₁)
  rename-≡Tm σ (fun bd₁) (fun bd₂) (fun-cong .bd₁ .bd₂ eq) =
    fun-cong
      (rename bd₁ (Ren.ext σ))
      (rename bd₂ (Ren.ext σ))
      (rename-≡Tm (Ren.ext σ) bd₁ bd₂ eq)
  rename-≡Tm {ty = ty} σ tm₁ tm₂ (𝟙-η tm-𝟙) = 𝟙-η (rename tm₁ σ)

  ext-≡Sub : ∀ {Δ Γ} {ty} → (ρ σ : Sub Δ Γ) → ρ ≡Sub σ → Sub.ext {ty = ty} ρ ≡Sub Sub.ext σ
  ext-≡Sub ρ σ ρ≡𝕊σ Z = reflexivity (Sub.ext ρ Z)
  ext-≡Sub ρ σ ρ≡𝕊σ (S v) = rename-≡Tm S (ρ v) (σ v) (ρ≡𝕊σ v)

  subst-≣Sub : ∀ {Δ Γ} {ty} → (σ ρ : Sub Δ Γ) → (tm  : Tm Γ ty) → σ ≡Sub ρ →
    subst σ tm ≡Tm subst ρ tm
  subst-≣Sub σ ρ (var v) s-eq = s-eq v
  subst-≣Sub σ ρ (rator ∙ rand) s-eq =
    ∙-cong
      (subst σ rator)
      (subst ρ rator)
      (subst σ rand)
      (subst ρ rand)
      (subst-≣Sub σ ρ rator s-eq)
      (subst-≣Sub σ ρ rand s-eq)
  subst-≣Sub σ ρ (fun body) s-eq =
    fun-cong
      (subst (Sub.ext σ) body)
      (subst (Sub.ext ρ) body)
      (subst-≣Sub (Sub.ext σ) (Sub.ext ρ) body (ext-≡Sub σ ρ s-eq))
  subst-≣Sub σ ρ tt s-eq = reflexivity (subst σ tt)

  wk-Tm/[tm] :
    ∀ {Γ ty sub-ty} → (body : Tm Γ ty) → (arg : Tm Γ sub-ty) →
      (wk-Tm body) /[ arg ] ≡Tm
      body
  wk-Tm/[tm] (var v) arg = reflexivity (wk-Tm (var v) /[ arg ])
  wk-Tm/[tm] (rator ∙ rand) arg =
    ∙-cong
      (subst (sub/ arg) (rename rator S)) rator
      (subst (sub/ arg) (rename rand S)) rand
      (wk-Tm/[tm] rator arg) (wk-Tm/[tm] rand arg)
  wk-Tm/[tm] {Γ = Γ} {ty = ty} (fun body) arg =
    begin
      (wk-Tm (fun body) /[ arg ])
        -- definition of wk-Tm
        ≈⟨ reflexivity (wk-Tm (fun body) /[ arg ]) ⟩
      (rename (fun body) S /[ arg ])
        -- definition of single substitution /[_]
        ≈⟨ reflexivity (rename (fun body) S /[ arg ]) ⟩
      (subst (sub/ arg) (rename (fun body) S))
        ≈⟨ subst-rename (sub/ arg) S (fun body) ⟩
      (subst (ren-sub-∘ S (sub/ arg)) (fun body))
        ≈⟨ subst-≣Sub _ _ (fun body) (≣→≡Sub (wk-/[] arg)) ⟩
      (subst Sub-id (fun body))
        ≈⟨ subst-id (fun body) ⟩
      fun body ∎
    where
    open Reasoning (≡Tm-setoid Γ ty)
  wk-Tm/[tm] tt arg = reflexivity (wk-Tm tt /[ arg ])

  ∘Sub-≡Tm :
      ∀ {Γ Δ Θ t} (tm : Tm Δ t) →
      (ρ : Sub Γ Δ) (ρ' : Sub Θ Γ) →
      subst ρ' (subst ρ tm) ≡Tm subst (ρ ∘𝕊 ρ') tm
  ∘Sub-≡Tm tm ρ ρ' = ≡→≡Tm (∘Sub-≡ tm ρ ρ')

  var≡-lemma : ∀ {ty Γ Δ} → (v v' : ty ∈ Γ) (σ : Sub Δ Γ) → v ≡ v' → σ v ≡Tm σ v'
  var≡-lemma v v' σ refl = reflexivity (σ v)

  subst-cong : ∀ {Γ Δ ty} → (σ : Sub Δ Γ) → (tm₁ tm₂ : Tm Γ ty) →
    (eq : tm₁ ≡Tm tm₂) → subst σ tm₁ ≡Tm subst σ tm₂
  subst-cong σ tm₁ tm₂ (reflexivity tm) = reflexivity (subst σ tm₁)
  subst-cong σ tm₁ tm₂ (symmetry eq) = symmetry (subst-cong σ tm₂ tm₁ eq)
  subst-cong {Δ = Δ} {ty = ty} σ tm₁ tm₃ (transitivity {t2 = tm₂} eq₁ eq₂) =
    begin
      subst σ tm₁
        -- Apply subst-cong with first equality
        ≈⟨ subst-cong σ tm₁ tm₂ eq₁ ⟩
      subst σ tm₂
        -- Apply subst-cong with second equality
        ≈⟨ subst-cong σ tm₂ tm₃ eq₂ ⟩
      subst σ tm₃ ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
  subst-cong {Δ = Δ} {ty = ty} σ tm₁ tm₂ (β-red body arg) =
     begin
      (fun (subst (Sub.ext σ) body) ∙ subst σ arg)
        ≈⟨ β-red (subst (Sub.ext σ) body) (subst σ arg) ⟩
      (subst (Sub.ext σ) body) /[ subst σ arg ]
        ≈⟨ reflexivity (subst (Sub.ext σ) body /[ subst σ arg ]) ⟩
      (subst (Sub.ext σ) body) /[ subst σ arg ]
        -- by definition of single subst /[]
        ≈⟨ reflexivity (subst (Sub.ext σ) body /[ subst σ arg ]) ⟩
      (subst (sub/ (subst σ arg)) (subst (Sub.ext σ) body))
        ≈⟨ ∘Sub-≡Tm body (Sub.ext σ) (sub/ (subst σ arg)) ⟩
      (subst (Sub.ext σ ∘𝕊 sub/ (subst σ arg)) body)
        ≈⟨ ≡→≡Tm (subst-≣ (ext∘𝕊/[] arg σ) body) ⟩
      (subst (sub/ arg ∘𝕊 σ) body)
        ≈⟨ symmetry (∘Sub-≡Tm body (sub/ arg) σ) ⟩
      subst σ (subst (sub/ arg) body)
        ≈⟨ reflexivity (subst σ (subst (sub/ arg) body)) ⟩
      subst σ (body /[ arg ]) ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
    module E = IsEquivalence (≡Tm-Equality {Δ} {ty})
  subst-cong {Δ = Δ} {ty = ty} σ tm₁ tm₂ (η-fn fn-tm) =
    begin
      fun (subst (Sub.ext σ) (wk-Tm tm₂) ∙ var Z)
        -- Definition of wk-Tm
        ≈⟨ reflexivity _ ⟩
      fun (subst (Sub.ext σ) (rename tm₂ S) ∙ var Z)
        -- Use subst-wk to rewrite substitution of weakened term
        ≈⟨
          fun-cong _ _
            (∙-cong _ _ _ _ (≡→≡Tm (subst-wk σ tm₂)) (reflexivity (var Z)))
           ⟩
      fun (rename (subst σ tm₂) S ∙ var Z)
        -- Apply η-reduction
        ≈⟨ η-fn (subst σ tm₂) ⟩
      subst σ tm₂ ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
    module E = IsEquivalence (≡Tm-Equality {Δ} {ty})
  subst-cong σ tm₁ tm₂ (var-cong v-eq) = var≡-lemma _ _ σ v-eq
  subst-cong {Δ = Δ} {ty = ty} σ tm₁ tm₂ (∙-cong f1 f2 a1 a2 eq1 eq2) =
    begin
      (subst σ f1 ∙ subst σ a1)
        -- Apply subst-cong inductively to both sides
        ≈⟨ ∙-cong (subst σ f1) (subst σ f2) (subst σ a1) (subst σ a2) (subst-cong σ f1 f2 eq1) (subst-cong σ a1 a2 eq2) ⟩
      (subst σ f2 ∙ subst σ a2) ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
    module E = IsEquivalence (≡Tm-Equality {Δ} {ty})
  subst-cong {Δ = Δ} {ty = ty} σ tm₁ tm₂ (fun-cong bd1 bd2 eq) =
    begin
      fun (subst (Sub.ext σ) bd1)
        -- Apply subst-cong inductively to the body
        ≈⟨ fun-cong (subst (Sub.ext σ) bd1) (subst (Sub.ext σ) bd2) (subst-cong (Sub.ext σ) bd1 bd2 eq) ⟩
      fun (subst (Sub.ext σ) bd2) ∎
    where
    open Reasoning (≡Tm-setoid Δ ty)
  subst-cong {ty = ty} σ tm₁ tm₂ (𝟙-η tm-𝟙) = 𝟙-η (subst σ tm₁)

  ≡Sub-equiv : {Γ Δ : Ctxt} → IsEquivalence (_≡Sub_ {Δ = Δ} {Γ = Γ})
  ≡Sub-equiv {Γ} {Δ} =
    record {
        refl = λ _ → E.refl ≡Tm-Equality
      ; sym = λ {r₁} {r₂} eq v → E.sym ≡Tm-Equality (eq v)
      ; trans = λ {r₁} {r₂} {r₃} eq₁ eq₂ v → E.trans ≡Tm-Equality (eq₁ v) (eq₂ v)
      }
    where
    module E = IsEquivalence

  open import Relation.Binary using (Setoid)
  ≡Sub-setoid : (Γ Δ : Ctxt) → Setoid ℓzero ℓzero
  ≡Sub-setoid Γ Δ =  record
    { Carrier       = Sub Γ Δ
    ; _≈_           = _≡Sub_
    ; isEquivalence = ≡Sub-equiv
    }

  subst-≣𝕊 : {Γ Δ : Ctxt} {ty : Ty} {f g : Sub Γ Δ} →
      (tm : Tm Δ ty) → f ≡Sub g → subst f tm ≡Tm subst g tm
  subst-≣𝕊 {f = f} {g = g} (var v) f≡𝕊g = f≡𝕊g v
  subst-≣𝕊 {Γ = Γ} {ty = ty} {f = f} {g = g} (rator ∙ rand) f≡𝕊g =
    begin
      (subst f rator ∙ subst f rand)
          -- Apply subst-≣𝕊 inductively to both sides
          ≈⟨ ∙-cong
               (subst f rator) (subst g rator)
               (subst f rand) (subst g rand)
               (subst-≣𝕊 rator f≡𝕊g)
               (subst-≣𝕊 rand f≡𝕊g)
           ⟩
      (subst g rator ∙ subst g rand) ∎
    where
    open Reasoning (≡Tm-setoid Γ ty)
  subst-≣𝕊 {Γ = Γ} {ty = ty} {f = f} {g = g} (fun tm) f≡𝕊g =
    begin
      fun (subst (Sub.ext f) tm)
        -- Apply subst-≣𝕊 inductively to the body with extended substitutions
        ≈⟨ fun-cong
             (subst (Sub.ext f) tm)
             (subst (Sub.ext g) tm)
             (subst-≣𝕊 tm (ext-≡Sub f g f≡𝕊g))
         ⟩
      fun (subst (Sub.ext g) tm) ∎
    where
    open Reasoning (≡Tm-setoid Γ ty)
  subst-≣𝕊 {f = f} {g = g} tt f≡𝕊g = reflexivity (subst f tt)

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
