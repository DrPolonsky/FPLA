open import Relations.Relations
open import Predicates
open import Logic

module ARS.Util {A : Set } {R : 𝓡 A} where

open import ARS.Properties {A}
open import ARS.Propositions -- remove this import when Weakly confluent is removed
open LocalProperties {R}
-- open import ARS.Base

{- This file contains utility functions used throughout the ARS formalization
 which do not cleanly fit within a particular theme-}

NF→ε : ∀ {x : A} → x ∈ NF → ∀ {y} → (R ⋆) x y → x ≡ y
NF→ε {x} x∈NF {.x} ε⋆ = refl
NF→ε {x} x∈NF {y} (Rxy₀ ,⋆ R⋆y₀y) = ∅ (x∈NF Rxy₀)

¬¬NF⊆NF : ∀ x → ¬¬ (NF x) → NF x
¬¬NF⊆NF x nnNFx  Rxy = nnNFx (λ x∈NF → x∈NF Rxy)

¬SN∧NF→⊥ : ∀ {x} → ¬ (SN x) → NF x → ⊥
¬SN∧NF→⊥ x∉SN x∈NF = x∉SN (acc (λ y Rxy → ∅ (x∈NF Rxy)))

weakly-confluent→WCR : weakly-confluent R → R isWCR
weakly-confluent→WCR x x₁ x₂ x₃ = x (x₁ ,, x₂ , x₃)

WCR→weakly-confluent : R isWCR → weakly-confluent R
WCR→weakly-confluent RisWCR (x ,, Rxy , Rxz) = RisWCR x Rxy Rxz

CR→confluent : R isCR → confluent R
CR→confluent RisCR (x ,, R*xy , R*xz)  with RisCR x R*xy R*xz
... | RisConfluent = RisConfluent


wCR→conflInd : R isWCR → (~R R) -inductive CR
wCR→conflInd RisWCR x IND ε⋆ R*xz = _ ,, R*xz , ε⋆
wCR→conflInd RisWCR x IND (Rxy₀ ,⋆ R*y₀y) ε⋆ = _ ,, ε⋆ , (Rxy₀ ,⋆ R*y₀y)
wCR→conflInd RisWCR x IND (Rxy₀ ,⋆ R*y₀y) (Rxz₀ ,⋆ R*z₀z) with RisWCR x Rxy₀ Rxz₀
... | w ,, R*y₀w , R*z₀w with IND _ Rxy₀ R*y₀y R*y₀w
... | v ,, R*yv , R*wv with IND _ Rxz₀ R*z₀z (R*z₀w ⋆!⋆ R*wv)
... | u ,, R*zu , R*vu = u ,, ((R*yv ⋆!⋆ R*vu) , R*zu)

wCR→Conf : R isWCR → SN ⊆ CR
wCR→Conf RisWCR = acc⊆ind (λ x → CR x) (wCR→conflInd RisWCR)
  where open BasicImplications



open import Relations.Decidable

SN⊆∁∁WN : SN ⊆ ∁ (∁ WN)
SN⊆∁∁WN x (acc xacc) ¬WNx = ¬WNx (x ,, ε⋆ , x∈NF _) where
    x∈NF : ∀ y → ¬ R x y
    x∈NF y Rxy = SN⊆∁∁WN y (xacc y Rxy)
            (λ { (n ,, (R*yn , n∈NF)) → ¬WNx ((n ,, (Rxy ,⋆ R*yn) , n∈NF )) } )

¬NFx→Rxy : ∀ {x} → x ∈ MinDec (~R R) → ¬ (NF x) →  Σ[ y ∈ A ] (R x y)
¬NFx→Rxy {x} xdec x∉NF with xdec
... | in1 yRxy = yRxy
... | in2 x∈NF = ∅ (x∉NF λ _ → x∉NF (x∈NF _))
