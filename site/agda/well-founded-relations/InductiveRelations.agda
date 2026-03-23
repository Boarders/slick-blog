module InductiveRelations where

open import Level renaming (zero to ℓzero; suc to ℓsuc)
open import Relation.Binary renaming (Rel to Relℓ) using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Data.Nat
open import Function using (_∘_)
open import Function.Bundles using (Equivalence)
open import Agda.Primitive

-- Unlike the stdlib's Rel (which has levels for the carrier and the relation),
-- we use the same level ℓ
Rel :  ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Rel {ℓ = ℓ} A = A → A → Set ℓ

Property : ∀ {ℓ : Level} → Set ℓ → Set (ℓsuc ℓ)
Property {ℓ = ℓ} A = A → Set ℓ

module InductiveDefs {ℓ : Level} (A : Set ℓ) where
  IndPrinciple : (R : Rel A) → (P : Property A) → Set ℓ
  IndPrinciple R P = ∀ (y : A) → ((∀ (x : A) → R x y → P x) → P y)

  InductiveP : (R : Rel A) → (P : Property A) → Set ℓ
  InductiveP R P =
    IndPrinciple R P →
    (∀ (x : A) → P x)

  InductiveR : (R : Rel A) → Set (ℓsuc ℓ)
  InductiveR R = ∀ (P : Property A) → InductiveP R P

  module InductiveTrans where
    -- _⁺ is the transitive closure of the relation
    data _⁺ (R : Rel A) : Rel A where
      gen⁺  : ∀ {x y : A} → R x y → (R ⁺) x y
      _⁺↦_  : ∀ {x y z : A} → (R ⁺) x y → R y z → (R ⁺) x z

    -- _* is the reflexive-transitive closure
    data _* (R : Rel A) : Rel A where
      gen*  : ∀ {x y : A} → R x y → (R *) x y
      id    : ∀ {x : A} → (R *) x x

    belowP : {R : Rel A} → Property A → Property A
    belowP {R = R} P b = ∀ (a : A) → (((R ⁺) *) a b) → P a

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

    -- Conversely, we can use R⁺ induction to prove R induction
    -- by only using a <R b
    RtoR⁺-principle : {P : Property A}{R : Rel A} → IndPrinciple R P → IndPrinciple (R ⁺) P
    RtoR⁺-principle indR b R⁺step-ab =
      indR b (λ a Rab → R⁺step-ab a (gen⁺ Rab))

    R⁺toR-inductive : {R : Rel A} → InductiveR (R ⁺) → InductiveR R
    R⁺toR-inductive IndR⁺ P = λ indR a → IndR⁺ P (RtoR⁺-principle indR) a

    -- Therefore, a relation is inductive iff its transitive closure is inductive
    ⁺Inductive : {R : Rel A} → Equivalence (setoid (InductiveR R)) (setoid (InductiveR (R ⁺)))
    ⁺Inductive {R = R} = record {
         to = RtoR⁺-inductive {R = R} ;
         from =  R⁺toR-inductive {R = R} ;
         to-cong = cong RtoR⁺-inductive ;
         from-cong = cong R⁺toR-inductive
       }

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

-- notes:
-- In a topos/constructive mathematics we don't have the familiar well-ordering principle
-- (WOP) of Nat principle - that any non-empty 'subset' has a least element.
--
-- Consider the above family dec-P (or perhaps some propositional truncation to get
-- a genuine 'subset' in dependent type theory). If the usual WOP held then since
-- this family is non-empty it would have a least element. We could then ask if this
-- element is zero which would tell use whether `P` is true.
--

module WellOrderedAuto where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open Descending

  record RelHom {ℓ : Level} {A B : Set ℓ} (R₁ : Rel A) (R₂ : Rel B) : Set ℓ where
    field
      fn : A → B
      rel-preserve : ∀ {x y} → R₁ x y → R₂ (fn x) (fn y)

  record Iso {ℓ : Level} {A B : Set ℓ} (R₁ : Rel A) (R₂ : Rel B) : Set ℓ where
    field
      to-hom : RelHom R₁ R₂
      from-hom : RelHom R₂ R₁
    module T = RelHom to-hom
    module F = RelHom from-hom
    field
      to∘from : ∀ (b : B) → T.fn (F.fn b) ≡ b
      from∘to : ∀ (a : A) → F.fn (T.fn a) ≡ a

  open RelHom
  open Iso
  open InductiveDefs
  open import Data.Empty.Polymorphic using (⊥)
  open import Data.Product

  -- For any inductive relation R, no R-automorphism can map an element strictly below itself.
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
