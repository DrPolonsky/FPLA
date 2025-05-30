module ARS.Base {A : Set} where

open import Relations.Relations
open import Predicates
open import Logic

{- The essential type definitions for ARS-}

_↘_↙_ : A → 𝓡 A → A → Set
_↘_↙_ x R y = (R ∘~ R) x y

_↙_↘_ : A → 𝓡 A → A → Set
_↙_↘_ x R y = (R ~∘ R) x y

-- 𝓖 is \MCG
𝓖 : 𝓡 A → 𝓟 A
𝓖 R x = Σ[ y ∈ A ] (R ⋆) x y

-- Definition 1.1.8: Notions of Confluence
module Confluence (Rα : 𝓡 A) where
    commute-weakly : 𝓡 A → Set
    commute-weakly Rβ =  Rα ~∘ Rβ  ⊆₂  Rβ ⋆ ∘~ Rα ⋆

    commute : 𝓡 A → Set
    commute Rβ =  ∀ {x}{y}{z} → (Rα ⋆) x y → (Rβ ⋆) x z → (Rβ ⋆ ∘~ Rα ⋆) y z

    self-commuting : Set
    self-commuting = commute Rα

    weakly-confluent : Set
    weakly-confluent =  ∀ {y}{z} → y ↙ Rα ↘ z → y ↘ Rα ⋆ ↙ z

    confluent : Set
    confluent = ∀ {y}{z} → y ↙ Rα ⋆ ↘ z → y ↘ Rα ⋆ ↙ z

    subcommutative : Set
    subcommutative = ∀ {y}{z} → y ↙ Rα ↘ z → y ↘ Rα ʳ ↙ z

    -- Diamond property (◆ is \di)
    ◆ : Set
    ◆ = ∀ {x}{y}{z} → Rα x y → Rα x z → (Rα ∘~ Rα) y z

open Confluence public
