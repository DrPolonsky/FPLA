{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Datatypes
open import Lists
open import Relations.Decidable using (_isDec)
open import Relations.Core
open import Classical

module Relations.FinitelyBranching {A : Set} (R : 𝓡 A) where

FB : A → Set
FB a = Σ[ xs ∈ List A ] (∀ b → R a b → b ∈List xs)

FBRel : A → Set
FBRel a = Σ[ xs ∈ List A ] (∀ b → R a b ↔ b ∈List xs)

FBRel⊆FB : FBRel ⊆ FB
FBRel⊆FB a (xs ,, f) = xs ,, λ b → pr1 (f b)

_isFB : Set
_isFB = ∀ (a : A) → a ∈ FB

_isFBRel : Set
_isFBRel = ∀ (a : A) → a ∈ FBRel

dec∧FB→FBRel  : R isDec → _isFB → _isFBRel
dec∧FB→FBRel RisDec RisFB a with filterList (λ x → R a x) (λ x → RisDec) (fst (RisFB a))
... | xs ,, f = xs ,, λ b → (λ Rba → pr2 (f b) (snd (RisFB a) b Rba , Rba ) ) , λ b∈xs → pr2 (pr1 (f b) b∈xs)

-- [AP: redo]
FB→DNS : ∀ (P : 𝓟 A) → ∀ x → x ∈ FB → (∀ y → R x y → ¬¬ P y) → ¬¬ (∀ y → R x y → P y)
FB→DNS P a aisFB H1 H2 with aisFB
... | (xs ,, w) = ¬¬Allxs (λ allxs → H2 (g allxs))
    where h : ∀ ys → List∀ (λ x → ¬ (¬ (R a x → P x))) ys
          h [] = tt
          h (x ∷ ys) = (λ ¬Rax⊆Px → ¬Rax⊆Px (λ Rax → ∅ (H1 x Rax (λ px → ¬Rax⊆Px (λ _ → px) )) ) ) , (h ys)
          ¬¬Allxs : ¬¬ (List∀ (λ y → R a y → P y) xs)
          ¬¬Allxs ¬allPxs = ListDNS (λ y → R a y → P y) xs (h xs) ¬allPxs
          g : List∀ (λ y → R a y → P y) xs → (∀ y → R a y → P y)
          g allxs y Ray = All∈List (λ z → R a z → P z) (w y Ray) allxs Ray
 
FBRel∧WDec→EMRyx :  _isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → ∀ {x} → EM (Σ[ y ∈ A ] (R x y × ¬ (P y)))
FBRel∧WDec→EMRyx RisFBRel P PwDec {x} with RisFBRel x 
...| ys ,, Rys 
    with decList∃ (∁ P) PwDec ys
... | in2 no = in2 (λ ∃y → no (List∃intro (∁ P) ys (fst ∃y) (pr1 (Rys (fst ∃y)) (pr1 (snd ∃y)) , pr2 (snd ∃y)))) 
... | in1 yes with List∃elim (∁ P) ys yes 
... | y ,, y∈ys , ¬Py = in1 (y ,, (pr2 (Rys y) y∈ys) , ¬Py)
