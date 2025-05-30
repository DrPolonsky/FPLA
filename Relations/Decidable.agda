-- open import Relations.ARS-Base
open import Logic
open import Predicates
open import Classical

module Relations.Decidable {A : Set} (R : 𝓡 A) where

-- Decidability of the relation R
_isDec : Set
_isDec = ∀ {x} {y} → EM (R x y)

-- Decidability of being R-minimal, for a given element
MinDec : A → Set
MinDec x = (Σ[ y ∈ A ] R y x) ⊔ (∀ y → ¬ R y x)

-- Decidability of being R-minimal, globally
_isMinDec : Set
_isMinDec = ∀ x → MinDec x

-- A weaker form of decidability of being minimal
MinDec- : A → Set
MinDec- x = ¬ (∀ y → ¬ R y x) → (Σ[ y ∈ A ] R y x)

MinDec⊆MinDec- : MinDec ⊆ MinDec-
MinDec⊆MinDec- x x∈md x∉M with x∈md
... | in1 x→y = x→y
... | in2 x∈M = ∅ (x∉M x∈M)
