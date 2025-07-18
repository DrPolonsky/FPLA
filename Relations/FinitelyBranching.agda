{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Datatypes
open import Lists
open import Relations.Decidable using (_isDec)

module Relations.FinitelyBranching {A : Set} (R : 𝓡 A) where

FB : A → Set
FB a = Σ[ xs ∈ List A ] (∀ b → R b a → b ∈List xs)

FBRel : A → Set
FBRel a = Σ[ xs ∈ List A ] (∀ b → R b a ↔ b ∈List xs)

FBRel⊆FB : FBRel ⊆ FB
FBRel⊆FB a (xs ,, f) = xs ,, λ b → pr1 (f b)

_isFB : Set
_isFB = ∀ (a : A) → a ∈ FB

_isFBRel : Set
_isFBRel = ∀ (a : A) → a ∈ FBRel

dec∧FB→FBRel  : R isDec → _isFB → _isFBRel
dec∧FB→FBRel RisDec RisFB a with filterList (λ x → R x a) (λ x → RisDec) (fst (RisFB a))
... | xs ,, f = xs ,, λ b → (λ Rba → pr2 (f b) (snd (RisFB a) b Rba , Rba ) ) , λ b∈xs → pr2 (pr1 (f b) b∈xs)

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

-- Attempt to improve the above
open import Data.List.Relation.Unary.All

FB→DNS₂ : ∀ (P : 𝓟 A) → ∀ x → x ∈ FB → (∀ y → R y x → ¬¬ P y) → ¬¬ (∀ y → R y x → P y) -- If x is FB, then the (finite) predecessors of x have the DNS property
FB→DNS₂ P a a∈FB@(xs ,, Rba→b∈xs) ¬¬Py ¬∀Py =
    let
        ¬¬Allxs : ¬¬ (All (λ y → R y a → P y ) xs)
        ¬¬Allxs = {!   !}

    in {!   !}
