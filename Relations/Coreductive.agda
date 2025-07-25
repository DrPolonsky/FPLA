open import Predicates 
open import Logic 
open import Relations.FinitelyBranching
open import Lists

module Relations.Coreductive {A : Set} (R : 𝓡 A) where 
    _-coreductive_ : 𝓟 A → Set 
    _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P)

    FBRel∧WDec→CorP : R isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → _-coreductive_ (P)
    FBRel∧WDec→CorP RisFBRel PwDec a a∉P  = {!   !}  