{-# OPTIONS --guardedness #-}

open import LAM.Lambda 
open import LAM.Homega.Unsolvable
open import Logic
open import Lifting
open import Predicates 

module LAM.Homega.OmegaReduction where 

data _⟶Ω_ {X : Set} : Λ X → Λ X → Set where 
  ⟶Ωax : ∀ (t : Λ X) → t ∈ 𝓤 → t ⟶Ω Omega
  ⟶ΩappL : ∀ (s t u : Λ X) → s ⟶Ω t → app s u ⟶Ω app t u
  ⟶Ωabs : ∀ (s t : Λ (↑ X)) → s ⟶Ω t → abs s ⟶Ω abs t 

-- Classical definition:
-- ⟶Ωax : ∀ (t : Λ X) → t ∈ 𝓤 → ¬ (t ≡ Omega) → t ⟶Ω Omega
 
