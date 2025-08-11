-- This file for functions/work that isn't required for the paper and is possibly to be deleted:

open import Relations.Decidable
module FBImplications {A : Set} {R : 𝓡 A} (RisFB : (~R _) isFB) where
  FB→isDec→isMinDec : R isDec → R isMinDec
  FB→isDec→isMinDec RisDec x₀ with decList∃ (~R R x₀) (λ _ → RisDec) (fst (RisFB x₀))
  ... | in2 ∄y = in2 (λ y Ryx₀ →
   ∄y (List∃intro (~R R x₀) (fst (RisFB x₀)) y (snd (RisFB x₀) y Ryx₀ , Ryx₀)))
  ... | in1 ∃y with List∃elim (~R R x₀) (fst (RisFB x₀)) ∃y
  ... | (y ,, _ , Ryx₀) = in1 (y ,, Ryx₀ )

  FB→ind∁∁acc : R -inductive (∁ ∁ R -accessible)
  FB→ind∁∁acc x H x∉acc = FB→DNS (~R R) (R -accessible) x (RisFB x) H (λ f → x∉acc (acc f) )

