-- Classical properties required for WF implications 
open import Predicates
open import Relations.WellFounded.WFDefinitions

module Relations.WellFounded.ClassicalProperties {A : Set} (R : 𝓡 A) where
    accessibilityIsCoreductive : Set 
    accessibilityIsCoreductive = R -coreductive (R -accessible)

    accessibilityIsNotNotClosed : Set
    accessibilityIsNotNotClosed = ¬¬Closed (R -accessible)

    coreductivesAreNotNotClosed : Set₁ 
    coreductivesAreNotNotClosed = ∀ (P : 𝓟 A) → R -coreductive P → ¬¬Closed P