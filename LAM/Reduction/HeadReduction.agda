open import Logic
open import Lifting 
open import LAM.Lambda
open import LAM.Reduction.Beta
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

open import LAM.Reduction.Beta

module LAM.Reduction.HeadReduction where 

-- data _⟶h_ {X} : Λ X → Λ X → Set where 
--   red⟶h : ∀ {s t : Λ X} → s ⟶w t → s ⟶h t
--   abs⟶h : ∀ {s t : Λ (↑ X)} → s ⟶h t → abs s ⟶h abs t 
--

