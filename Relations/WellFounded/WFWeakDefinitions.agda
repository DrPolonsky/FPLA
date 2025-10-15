open import Logic
open import Predicates
open import Datatypes
open import Relations.ClosureOperators
open import Relations.WellFounded.WFDefinitions
open import Relations.Seq

module Relations.WellFounded.WFWeakDefinitions {A : Set} (R : 𝓡 A) where
-- Weaker notions of well-foundedness
_isWFacc¬¬ : Set 
_isWFacc¬¬ = ∀ x → ¬¬ (x ∈ R -accessible)

_isWFind¬¬ : Set₁
_isWFind¬¬ = ∀ (φ : 𝓟 A) → R -inductive φ → ∀ x → ¬¬ (φ x)

-- The classical concept of a well-founded relation [TeReSe]
_isWFseq- : Set -- Don't modify this one just yet 20th August
_isWFseq- = ∀ (s : ℕ → A) → ¬ (s ∈ R -decreasing)

_isWFseq¬¬ : Set
_isWFseq¬¬ = ∀ (s : ℕ → A) → ¬¬ Σ[ n ∈ ℕ ] (¬ (R (s (succ n)) (s n)))

_isWFmin¬¬ : Set₁
_isWFmin¬¬ = ∀ (P : 𝓟 A) → ∀ {d} → d ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)

_isWFminDNE¬¬ : Set₁
_isWFminDNE¬¬ = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ {a} → a ∈ P → ¬¬ Σ[ m ∈ A ] (m ∈ R - P -minimal)

_isWFminEM¬¬ : Set₁
_isWFminEM¬¬ = ∀ (P : 𝓟 A) → dec P → ∀ {a} → a ∈ P → ¬¬ Σ[ m ∈ A ] (m ∈ R - P -minimal)

_isWFcor¬¬ : Set₁
_isWFcor¬¬ = ∀ P → R -coreductive P → ∀ x → ¬¬ P x
 
-- The below definitions are equivalent to _isWFcor¬¬; this is shown in WFCoreductiveImplications.agda. 
-- isWFminCor: isWFmin restricted to complements of coreductive predicates. 
_isWFminCor : Set₁
_isWFminCor = ∀ (P : 𝓟 A) → R -coreductive P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∈ R - ∁ P -minimal)

-- isWFmincor+: A seemingly stronger formulation that is in fact equivalent. 
_isWFminCor+ : Set₁
_isWFminCor+ = ∀ (P : 𝓟 A) → R -coreductive P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x))
