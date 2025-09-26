-- Classical properties required for WF implications 
open import Predicates
open import Relations.WellFounded.WFDefinitions

module Relations.WellFounded.ClassicalProperties {A : Set} (R : 𝓡 A) where
    accessibilityIsCoreductive : Set 
    accessibilityIsCoreductive = R -coreductive (R -accessible)

    AccDNE : Set
    AccDNE = ¬¬Closed (R -accessible)

    corDNE : ∀ (P : 𝓟 A) → Set 
    corDNE P = R -coreductive P → ¬¬Closed P