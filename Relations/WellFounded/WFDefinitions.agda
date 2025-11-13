open import Logic
open import Predicates
open import Datatypes
open import Relations.ClosureOperators

module Relations.WellFounded.WFDefinitions {A : Set} where

module LocalWFDefinitions {R : 𝓡 A} where
  -- An element is R-accessible if all elements R-below it are R-accessible
  data _-accessible : 𝓟 A where
    acc : ∀ {x : A} → (∀ y → R y x → _-accessible y) → _-accessible x

  WFacc : 𝓟 A
  WFacc = _-accessible

  -- A predicate φ is R-inductive if:
  --   φ x is true whenever φ y is true for all elements y R-below x.
  _-inductive_ : 𝓟 A → Set
  _-inductive_ φ = ∀ x → (∀ y → R y x → φ y) → φ x

  WFind : 𝓟₁ A 
  WFind a = ∀ (φ : 𝓟 A) → _-inductive_ φ → φ a

  -- a∈A is sequentially well-founded if every sequence originating from a
  -- contains an index at which it's not decreasing
  WFseq : 𝓟 A
  WFseq a = ∀ (s : ℕ → A) → s 0 ≡ a → Σ[ n ∈ ℕ ] (¬ (R (s (succ n)) (s n)))

  Rmin : 𝓟 A    -- The NF property
  Rmin x = ∀ {y} → ¬ R y x

  -- x is R-φ-minimal if φ(x) is true and φ(y) is false for all y below x
  _-_-minimal : 𝓟 A → 𝓟 A
  _-_-minimal φ x = x ∈ φ × (∀ y → y ∈ φ → R y x → ⊥)

  WFmin : 𝓟₁ A
  WFmin a = ∀ (P : 𝓟 A) → a ∈ P → Σ[ m ∈ A ] ((R ⋆) a m × (_-_-minimal P m))

  -- Like WFmin, but restricted to ¬¬-closed predicates
  WFminDNE : 𝓟₁ A
  WFminDNE a = ∀ (P : 𝓟 A) → ¬¬Closed P → a ∈ P → Σ[ m ∈ A ] ((R ⋆) a m × (_-_-minimal P m))

  -- Like WFmin, but restricted to decidable predicates
  WFminEM : 𝓟₁ A
  WFminEM a = ∀ (P : 𝓟 A) → ¬¬Closed P → a ∈ P → Σ[ m ∈ A ] ((R ⋆) a m × (_-_-minimal P m))

  _-coreductive_ : 𝓟 A → Set
  _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P) 

  WFcor : 𝓟₁ A 
  WFcor a = ∀ (φ : 𝓟 A) → _-coreductive_ φ → φ a

module GlobalWFDefinitions (R : 𝓡 A) where

  open LocalWFDefinitions {R} public

  -- Well-foundedness defined as: every element is accessible
  _isWFacc : Set
  _isWFacc = ∀ x → x ∈ WFacc

  -- Well-foundedness defined as: every inductive predicate is universally true
  _isWFind : Set₁
  _isWFind = ∀ x → WFind x

  -- Well-foundedness defined as: every sequence contains a non-decreasing index
  _isWFseq : Set
  _isWFseq = ∀ (s : ℕ → A) → Σ[ n ∈ ℕ ] (¬ (R (s (succ n)) (s n)))

  -- Well-foundedness defined as: every non-empty subset contains a minimal element
  _isWFmin : Set₁
  _isWFmin = ∀ (P : 𝓟 A) → ∀ a → a ∈ P → Σ[ m ∈ A ] _-_-minimal P m

  _isWFminDNE : Set₁
  _isWFminDNE = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ a → a ∈ P → Σ[ m ∈ A ] _-_-minimal P m

  _isWFminEM : Set₁
  _isWFminEM = ∀ (P : 𝓟 A) → dec P → ∀ a → a ∈ P → Σ[ m ∈ A ] _-_-minimal P m

  _isWFcor : Set₁
  _isWFcor = ∀ x → WFcor x
  
  -- When used without qualification, "WF" refers to the first definition.
  _isWF = _isWFacc

open GlobalWFDefinitions public
