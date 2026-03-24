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

  module InductiveTrans where
    -- _⁺ is the transitive closure of a relation
    data _⁺ (R : Rel A) : Rel A where
      gen⁺  : ∀ {x y : A} → R x y → (R ⁺) x y
      _⁺↦_  : ∀ {x y z : A} → (R ⁺) x y → R y z → (R ⁺) x z

    -- _* is the reflexive closure of a relation
    data _* (R : Rel A) : Rel A where
      gen*  : ∀ {x y : A} → R x y → (R *) x y
      id    : ∀ {x : A} → (R *) x x

    belowP : {R : Rel A} → Property A → Property A
    belowP {R = R} P b = ∀ (a : A) → (((R ⁺) *) a b) → P a

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
    -- But, we have that P* b holds by R induction and so we have
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

    -- Use R induction to prove R⁺ induction by only using single steps a <R b
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

  -- pullback relation
  _←R_ : (f : A → B) → Rel B → Rel A
  f ←R R = λ a₀ a₁ → R (f a₀) (f a₁)

  -- pullback of a property
  _←P_ : (f : A → B) → Property B → Property A
  f ←P P = P ∘ f

  -- Π-type: Π_f P b - right adjoint to above pullback/substitution
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

  ArtinianToInd : {R : Rel A} → Artinian R → InductiveR A R
  ArtinianToInd {R = R} fin-desc P indR b =  lemma b (fin-desc b)
    where
      -- We prove P b holds by induction:
      -- if we have aRb, then because b satisfies FinDesc,
      -- so does a, and so we apply the lemma recursively
      -- to prove P a
      lemma : ∀ (b : A) → FinDesc R b → P b
      lemma b (step DaRb) = indR b (λ a Rab → lemma a (DaRb a Rab))

  -- If R is inductive, then we can prove it is Artinian
  -- by applying induction to the FinDesc property
  indToArtinian : {R : Rel A} → InductiveR A R → Artinian R
  indToArtinian {R = R} indR = indR (FinDesc R) λ _ → step

  -- FinDesc R x is equivalent to the standard library's accessibility predicate Acc R x,
  -- and DescR R to WellFounded R.
  open import Induction.WellFounded using (Acc; acc; WellFounded)

  descToAcc : {R : Rel A} {x : A} → FinDesc R x → Acc R x
  descToAcc (step f) = acc (λ {y} Ryx → descToAcc (f y Ryx))

  accToFinDesc : {R : Rel A} {x : A} → Acc R x → FinDesc R x
  accToFinDesc (acc f) = step (λ y Ryx → accToFinDesc (f Ryx))

module InductiveLex {ℓ : Level} (A : Set ℓ) (B : A → Set ℓ) where
  open import Data.Product
  open InductiveDefs
  open Descending

  data Lex (R₀ : Rel A) (R₁ : (a : A) → Rel (B a)) : Rel (Σ A B) where
    FstR : ∀ {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁} → R₀ a₀ a₁ → Lex R₀ R₁ (a₀ , b₀) (a₁ , b₁)
    SndR : ∀ {a : A} {b₀ b₁ : B a} → R₁ a b₀ b₁ → Lex R₀ R₁ (a , b₀) (a , b₁)

  -- We fix a given a and b and want to show that if a satisfies FinDesc
  -- and the relation on B is pointwise Artinian, then (a, b) satisfies
  -- FinDesc for the lex relation
  desc-lem : {R₀ : Rel A} {R₁ : (a : A) → Rel (B a)} →
    (a : A) (b : B a) →
    FinDesc R₀ a →
    ((a : A) → Artinian (R₁ a)) →
    FinDesc (R₁ a) b →
    FinDesc (Lex R₀ R₁) (a , b)
  -- We case on the proof that a satisfies FinDesc
  desc-lem {R₀ = R₀} {R₁ = R₁} a b (step a-step) dB db = inner db
    where
      -- For this fixed a, we then split on the proof that b is Artinian,
      -- where:
      --   - in the case we descend on the first component, we use
      --     that a satisfies FinDesc and recurse with a'
      --   - in the case we recurse on the second component, we
      --     recurse on inner which descends on b
      inner : ∀ {b' : B a} → FinDesc (R₁ a) b' → FinDesc (Lex R₀ R₁) (a , b')
      inner (step b-step) =
        step (λ {
          .(_ , _) (FstR Ra'a) →
            desc-lem _ _ (a-step _ Ra'a) dB (dB _ _) ;
          .(a , _) (SndR Rb'b) →
            inner (b-step _ Rb'b)}
            )

  Desc-Lex : {R₀ : Rel A} {R₁ : (a : A) → Rel (B a)} →
    Artinian R₀ →
    ((a : A) → Artinian (R₁ a)) →
    Artinian (Lex R₀ R₁)
  Desc-Lex desc-R₀ desc-R₁ (a , b) =
    desc-lem a b (desc-R₀ a) desc-R₁ (desc-R₁ a b)

module InductiveNat where
  open InductiveDefs
  open import Data.Product
  open import Data.Empty
  open import Data.Nat

  predRel : Rel ℕ
  predRel n m = m ≡ suc n

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

  open Proof
  predRelInductive : InductiveR ℕ predRel
  predRelInductive P indP with indSplit P indP
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

    -- For each constuctor a with argument p : P a
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

module WellOrdered where
  open import Data.Unit
  open import Data.Empty
  postulate
    P : Set

  dec-P : ℕ → Set
  dec-P zero = P
  dec-P (suc zero) = ⊤
  dec-P (suc (suc n)) = ⊥

-- Flittering notes:
-- In a topos/constructive setting we don't have the familiar well-ordering principle
-- (WOP) for Nat: that any non-empty 'subset' has a least element.
--
-- Consider the above family dec-P (or perhaps some propositional truncation to get
-- a genuine 'subset' in dependent type theory). If the usual WOP held then since
-- this family is non-empty it would have a least element. We could then ask if this
-- element is zero which would tell use whether `P` holds or not.

module WellOrderedAuto where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
  open import Relation.Binary using (Trichotomous; Tri)
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
  open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
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

  -- Applying ind-auto-no-regress to the inverse automorphism at (f a),
  -- and using f⁻¹(f a) ≡ a, shows f cannot map any element strictly above itself.
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
