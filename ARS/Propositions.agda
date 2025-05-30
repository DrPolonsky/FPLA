module ARS.Propositions {A : Set} where

open import Logic
open import Predicates
open import Relations.Relations

open import ARS.Properties

{- This file contains formalizations of
  Definition 1.1.8, Proposition 1.1.9, 1.1.10, 1.1.11 from TeReSe Chapter 1 -}

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

module Proposition-1-1-9 {Rα Rβ : 𝓡 A} where

    ii : commute Rα Rβ ↔ ~R (Rβ ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R  ~R (Rβ ⋆)
    pr1 ii commRαRβ z y (x ,, Rβ*xz , Rα*xy) with commRαRβ Rα*xy Rβ*xz
    ...| q ,, Rβ*yq , Rα*zq = q ,, Rα*zq , Rβ*yq
    pr2 ii f {x}{y}{z} Rα*xy Rβ⋆xz with f z y (x ,, Rβ⋆xz , Rα*xy)
    ...| q ,, Rα*zq , Rβ*yq = q ,, (Rβ*yq , Rα*zq)

    iii : weakly-confluent Rα ↔ ~R Rα ∘R Rα ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 iii WCRα z y peak@(x ,, Rαxz , Rαxy) with WCRα peak
    ... | q ,, Rα*zq , Rα*zy = q ,, (Rα*zq , Rα*zy)
    pr2 iii RHS {y} {z} valley@(x ,, Rα*xy , Rα*xz) = RHS y z valley

    iv : subcommutative Rα ↔ ~R Rα ∘R Rα ⊆ ((Rα ʳ) ∘R ~R (Rα ʳ))
    pr1 iv subComRα z y peak@(x ,, Rαxz , Rαxy) = subComRα peak
    pr2 iv RHS {y} {z} valley = RHS y z valley

    v : ◆ Rα ↔ ~R Rα ∘R Rα ⊆ Rα ∘R ~R Rα
    pr1 v ◆Rα y z (x ,, Rαxy , Rαxz) = ◆Rα Rαxy Rαxz
    pr2 v f {x}{y}{z} Rαxy Rαxz = f y z (x ,, Rαxy , Rαxz)

    vi : confluent Rα ↔ ~R (Rα ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 vi confRα y z (x ,, Rα*xy , Rα*xz) = confRα (x ,, Rα*xy , Rα*xz)
    pr2 vi RHS {y} {z} peak = RHS y z peak

module Proposition-1-1-10 {R : 𝓡 A} where
    i→ii : confluent R  → weakly-confluent (R ⋆)
    i→ii confR peak with confR peak
    ... | q ,, R*yq , R*zq = q ,, (ax⋆ (R ⋆) R*yq , ax⋆ (R ⋆) R*zq)

    ii→iii : weakly-confluent (R ⋆) → self-commuting (R ⋆)
    ii→iii wconfR* {x} R**xy R**xz with wconfR* (x ,, (**→* R R**xz , **→* R R**xy))
    ... | q ,, R**zq , R**yq = q ,, (R**yq , R**zq)


    iii→iv : self-commuting (R ⋆) → subcommutative (R ⋆)
    iii→iv scR* (x ,, R*xy , R*xz) with scR* (ax⋆ (R ⋆) R*xy) (ax⋆ (R ⋆) R*xz)
    ... | q ,, R**yq , R**zq = q ,, **→*ʳ R R**yq , **→*ʳ R R**zq

    iv→i : subcommutative (R ⋆) → confluent R
    iv→i subcomR* peak@(x ,, R*xz , R*xy)  with subcomR* peak
    ... | q ,, R*=zq , R*=yq = q ,, *ʳ→* R R*=zq , *ʳ→* R R*=yq

    i→v : confluent R → R ~∘ (R ⋆) ⊆ (R ⋆) ∘~ (R ⋆)
    i→v confR y z (x ,, Rxy , R*xz) = confR (x ,, ax⋆ R Rxy , R*xz)

    v→vi : (R ~∘ R ⋆) ⊆ (R ⋆ ∘~ R ⋆) → R ⁼ ⊆ (R ⋆ ∘~ R ⋆)
    v→vi v x .x ε⋆ = x ,, ε⋆ , ε⋆
    v→vi v x y (Rˢxz ,⋆ EQRzy) with v→vi v _ y EQRzy
    ... | q ,, R*zq , R*yq with Rˢxz
    ... | axˢ+ Rxy = q ,, (Rxy ,⋆ R*zq) , R*yq
    ... | axˢ- Ryx with v x q (_ ,, (Ryx , R*zq))
    ... | p ,, R*xp , R*qp = p ,, (R*xp , ( R*yq ⋆!⋆ R*qp ))

    vi→i : R ⁼ ⊆ (R ⋆ ∘~ R ⋆) → confluent R
    vi→i vi {y}{z} peak@(x ,, R*xy , R*xz)  with vi y z ((~⁼ (⋆⊆⁼ R R*xy)) ⁼!⁼ (⋆⊆⁼ R R*xz))
    ... | q ,, R*zq , R*yq = q ,, (R*zq , R*yq)

    i→vi : confluent R → R ⁼ ⊆ (R ⋆ ∘~ R ⋆)
    i→vi confR = v→vi (i→v confR)

    v→i : (R ~∘ R ⋆) ⊆ (R ⋆ ∘~ R ⋆) → confluent R
    v→i v = vi→i (v→vi v)


module Proposition-1-1-11  where
    lemmai : ∀ {R : 𝓡 A} → {x y z : A} → ◆ R → (R ⋆) x y → R x z → Σ[ q ∈ A ] (R y q × (R ⋆) z q)
    lemmai R◆ ε⋆ R◆xz = _ ,, R◆xz , ε⋆
    lemmai R◆ (Rxy₀ ,⋆ R*y₀y) Rxz with R◆ Rxy₀ Rxz
    ... | q ,, Ryq , Rzq with lemmai R◆ R*y₀y Ryq
    ... | p ,, Re , R*qp = p ,, (Re , (Rzq ,⋆ R*qp))

    lemmaii : ∀ {R : 𝓡 A} → ◆ R → ∀ {y}{z} → ∀ (x : A) → (R ⋆) x y → (R ⋆) x z → y ↘ R ⋆ ↙ z
    lemmaii R◆ x R*xy ε⋆ = _ ,, ε⋆ , R*xy
    lemmaii R◆ x R*xy (Rxy ,⋆ R*yz) with  lemmai R◆ R*xy Rxy
    ... | q ,, Ryq , R*yq with lemmaii R◆ _ R*yq R*yz
    ... | p ,, R*qp , R*zp = p ,, ((Ryq ,⋆ R*qp) , R*zp)

    lemmaiii : ∀ {R₁ R₂ : 𝓡 A} → (R₁ ⊆ R₂ ⋆) → (R₁ ⋆ ⊆ R₂ ⋆)
    lemmaiii Rxy⊆R₂*xy x y R*xy = **→* _ (⊆⋆ Rxy⊆R₂*xy x y R*xy)

    proposition11 : ∀ {R R⋄ : 𝓡 A} → (R ⊆ R⋄) → (R⋄ ⊆ R ⋆) → ◆ R⋄ → confluent R
    proposition11 R⊆R⋄ R⋄⊆R* ◆R⋄ {y} {z} peak@(x ,, R*xy , R*xz) with ⊆⋆ R⊆R⋄ x z R*xz
    ... | R⋄*xz with ⊆⋆ R⊆R⋄ x y R*xy
    ... | R⋄*xy with lemmaii ◆R⋄ x R⋄*xy R⋄*xz
    ... | q ,, R⋄*yq , R⋄*zq with lemmaiii R⋄⊆R* z q R⋄*zq
    ... | R*zq with lemmaiii R⋄⊆R* y q R⋄*yq
    ... | R*yq = q ,, R*yq , R*zq
