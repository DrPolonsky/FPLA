open import Logic
open import Predicates
open import Datatypes
open import Lists

module Relations.FinitelyBranching {A : Set} (R : 𝓡 A) where

FB : A → Set
FB a = Σ[ xs ∈ List A ] (∀ b → R b a → b ∈List xs)

_isFB : Set
_isFB = ∀ (a : A) → a ∈ FB

-- [AP: redo]
FB→DNS : ∀ (P : 𝓟 A) → ∀ x → x ∈ FB → (∀ y → R y x → ¬¬ P y) → ¬¬ (∀ y → R y x → P y)
FB→DNS P a aisFB H1 H2 with aisFB
... | (xs ,, w) = ¬¬Allxs (λ allxs → H2 (g allxs))
    where h : ∀ ys → List∀ (λ x → ¬ (¬ (R x a → P x))) ys
          h [] = tt
          h (x ∷ ys) = (λ ¬Rax⊆Px → ¬Rax⊆Px (λ Rax → ∅ (H1 x Rax (λ px → ¬Rax⊆Px (λ _ → px) )) ) ) , (h ys)
          ¬¬Allxs : ¬¬ (List∀ (λ y → R y a → P y) xs)
          ¬¬Allxs ¬allPxs = ListDNS (λ y → R y a → P y) xs (h xs) ¬allPxs
          g : List∀ (λ y → R y a → P y) xs → (∀ y → R y a → P y)
          g allxs y Ray = All∈List (λ z → R z a → P z) (w y Ray) allxs Ray

-- FBfind :
