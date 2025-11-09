open import Logic
open import Classical
open import Datatypes using (ℕ; zero; succ)
open import ARS.Properties
open import Relations.ClosureOperators
-- open import Predicates
-- open import Relations.Seq
open import Relations.WellFounded.WFDefinitions

module ARS.Examples where

module SNimpliesWNiffEM (X : Set) where
  data XRel : ℕ → ℕ → Set where
    XR01 : X → XRel 1 0

  XRelisSN : XRel isSN
  XRelisSN zero = acc (λ x → λ { () })
  XRelisSN (succ n) = acc (λ { y (XR01 x) → XRelisSN zero })

  XRelWN→EMX : XRel isWN → EM X
  XRelWN→EMX wn with wn 1
  ... | zero ,, (XR01 x ,⋆ pr3) , pr4 = in1 x
  ... | succ n ,, ε⋆ , ¬XRel10 = in2 λ x → ¬XRel10 (XR01 x)
  ... | succ n ,, (XR01 x ,⋆ (() ,⋆ pr3)) , pr4

  EMX→XRelWN : EM X → XRel isWN
  EMX→XRelWN = case f g where
    0∈NF : {y : ℕ} → XRel 0 y → ⊥
    0∈NF {y} ()
    f : X → XRel isWN
    f x zero = zero ,, ε⋆ , 0∈NF
    f x (succ zero) = zero ,, XR01 x ,⋆ ε⋆ , 0∈NF
    f x (succ (succ n)) = succ (succ n) ,, ε⋆ , λ {y} ()
    g : ¬ X → XRel isWN
    g nx zero = zero ,, ε⋆ , 0∈NF
    g nx (succ zero) = succ zero ,, ε⋆ , λ { {.zero} (XR01 x) → nx x }
    g nx (succ (succ n)) = succ (succ n) ,, ε⋆ , λ {y} ()
