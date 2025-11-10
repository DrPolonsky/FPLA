-- This file for functions/work that isn't required for the paper and is possibly to be deleted:

open import Relations.Decidable

wf→irrefl : R isWF → ∀ x → ¬ R x x
wf→irrefl RisWF x = go x (RisWF x) where
  go : ∀ y → y ∈ R -accessible → ¬ R y y
  go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

¬¬lemma : ∀ (X : Set) (Q : 𝓡 X) (P : 𝓟 X) (a : X) → ¬¬ (Σ[ b ∈ X ] (Q b a × P b) ⊔ (∀ b → Q b a → ¬ P b))
¬¬lemma X Q P a ¬⊔ = ¬⊔ (in2 λ b Qba b∈P → ¬⊔ (in1 (b ,, Qba , b∈P) ) )

¬¬lemmaA : ∀ (P : 𝓟 A) (a : A) → ¬¬ (Σ[ b ∈ A ] (R b a × P b) ⊔ (∀ b → R b a → ¬ P b))
¬¬lemmaA P a ¬⊔ = ¬⊔ (in2 λ b Rba b∈P → ¬⊔ (in1 (b ,, Rba , b∈P) ) )

¬¬lemmaC : ∀ (P : 𝓟 A) → (∁ (∁ P) ⊆ P) → (a : A) →
      ¬¬ (    (Σ[ bRba ∈ (Σ[ b ∈ A ] R b a) ] (¬ P (fst bRba)))
            ⊔  (∀ (bRba :  Σ[ b ∈ A ] R b a)    → P (fst bRba)))
¬¬lemmaC P CCP⊆P a ¬⊔ = ¬⊔ (in2 λ { (b ,, Rba) → CCP⊆P b (λ b∉P → ¬⊔ (in1 ((b ,, Rba) ,, b∉P ) ) )  } )
