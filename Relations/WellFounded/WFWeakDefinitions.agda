open import Logic
open import Predicates
open import Datatypes
open import Relations.ClosureOperators
open import Relations.WellFounded.WFDefinitions
-- open import Relations.Core
open import Relations.Seq

module Relations.WellFounded.WFWeakDefinitions {A : Set} (R : 𝓡 A) where

-- open LocalWFDefinitions

-- Weaker notions of well-foundedness

isWFacc- : Set
isWFacc- = ∀ x → ¬¬ (x ∈ R -accessible)

isWFind- : Set₁
isWFind- = ∀ (φ : 𝓟 A) → R -inductive φ → ∀ x → ¬¬ (φ x)

-- The classical concept of a well-founded relation [TeReSe]
isWFseq- : Set
isWFseq- = ∀ (s : ℕ → A) → ¬ (s ∈ R -decreasing)

isWFseq+- : Set
isWFseq+- = ∀ (s : ℕ → A) → ¬¬ (Σ[ n ∈ ℕ ] (s n ∈ Rmin R))

isWFmin- : Set₁
isWFmin- = ∀ (P : 𝓟 A) → ∀ {d} → d ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)

isWFminDNE- : Set₁
isWFminDNE- = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ {a} → a ∈ P → ¬¬ Σ[ m ∈ A ] (m ∈ R - P -minimal)

isWFminEM- : Set₁
isWFminEM- = ∀ (P : 𝓟 A) → dec P → ∀ {a} → a ∈ P → ¬¬ Σ[ m ∈ A ] (m ∈ R - P -minimal)

-- open BasicImplications
-- open WeakerWF
