-- open import Relations.ARS-Base
open import Logic
open import Predicates
open import Classical

module Relations.Decidable {A : Set} (R : 𝓡 A) where

RMin : 𝓟 A
RMin x = (∀ y → ¬ R y x)

-- Decidability of the relation R
_isDec : Set
_isDec = ∀ {x} {y} → EM (R x y)

-- Decidability of being R-minimal, for a given element
MinDec : A → Set
MinDec x = (Σ[ y ∈ A ] R y x) ⊔ (∀ y → ¬ R y x)

-- Decidability of being R-minimal, globally
_isMinDec : Set
_isMinDec = ∀ x → MinDec x

-- Any element that isn't a normal form has a reduct.
∁RMin⊆ΣR : A → Set 
∁RMin⊆ΣR x = x ∈ ∁ RMin → (Σ[ y ∈ A ] R y x)

MinDec⊆∁RMin⊆ΣR : MinDec ⊆ ∁RMin⊆ΣR
MinDec⊆∁RMin⊆ΣR x x∈md x∉M with x∈md
... | in1 x→y = x→y
... | in2 x∈M = ∅ (x∉M x∈M)

∁RMin⊆ΣR∩decNF⊆MinDec : ∁RMin⊆ΣR ∩ (EM ∘ RMin) ⊆ MinDec 
-- ∁RMin⊆ΣR∩decNF⊆MinDec : ∀ x → ∁RMin⊆ΣR x × EM (RMin x) → MinDec x
∁RMin⊆ΣR∩decNF⊆MinDec x (md- , decNF) with decNF
... | in1 x∈NF = in2 x∈NF
... | in2 x∉NF = in1 (md- x∉NF )

MinDec⊆∁RMin⊆ΣR∩decNF : MinDec ⊆ ∁RMin⊆ΣR ∩ (EM ∘ RMin)
MinDec⊆∁RMin⊆ΣR∩decNF x md = (MinDec⊆∁RMin⊆ΣR x md )
    , case (λ { (y ,, x→y) → in2 λ x∈NF → x∈NF y x→y } ) in1 md
