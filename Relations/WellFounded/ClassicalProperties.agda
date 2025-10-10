-- Classical properties required for WF implications
open import Logic
open import Predicates
open import Relations.WellFounded.WFDefinitions
open import Classical

module Relations.WellFounded.ClassicalProperties {A : Set} (R : 𝓡 A) where
    accessibilityIsCoreductive : Set
    accessibilityIsCoreductive = R -coreductive (R -accessible)

    accessibilityIsNotNotClosed : Set
    accessibilityIsNotNotClosed = ¬¬Closed (R -accessible)

    coreductivesAreNotNotClosed : Set₁
    coreductivesAreNotNotClosed = ∀ (P : 𝓟 A) → R -coreductive P → ¬¬Closed P

    EM→accessibilityIsCoreductive : (∀ P → EM P) → accessibilityIsCoreductive
    EM→accessibilityIsCoreductive em x x∉acc
      with em (Σ[ y ∈ A ] (R y x × y ∉ (R -accessible)))
    ... | in1 yes = yes
    ... | in2 no = ∅ (x∉acc (acc x∈acc))
      where x∈acc : (y : A) → R y x → (R -accessible) y
            x∈acc y Ryx with em (y ∈ R -accessible)
            ... | in1 y∈acc = y∈acc
            ... | in2 y∉acc = ∅ (no (y ,, Ryx , y∉acc ))

    EM→coreductivesAreNotNotClosed : (∀ P → EM P) → coreductivesAreNotNotClosed
    EM→coreductivesAreNotNotClosed em P DNECor x = pr2 (EM→WEM×DNE (P x) (em (P x)))
