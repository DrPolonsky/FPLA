{-# OPTIONS --guardedness #-}
module Homega.LambdaHomega where

open import Logic
open import Lifting
open import Lambda
open import Reduction
open import Relations.Core

open import Homega.Unsolvable
open import Homega.LambdaH
open import Homega.OmegaRule

data _=𝓗ω_ {X : Set} : Λ X → Λ X → Set where
  Ω𝓗 : ∀ {s t : Λ X} → s =𝓗 t → s =𝓗ω t
  _,𝓗ω_ : ∀ {u v w : Λ X} → ωΛRel _=𝓗ω_ u v → v =𝓗ω w → u =𝓗ω w

{-# TERMINATING #-}
_𝓗ω[_] : ∀ {X Y} {s t : Λ X} → s =𝓗ω t → ∀ (σ : X → Λ Y) → (s [ σ ]) =𝓗ω (t [ σ ])
Ω𝓗 st       𝓗ω[ σ ] = Ω𝓗 (st 𝓗[ σ ])
_𝓗ω[_] {X} {Y} {s} {t} (_,𝓗ω_ {u} {v} {w} uv uw) σ = f ,𝓗ω (uw 𝓗ω[ σ ])
  where f = bindωΛRel {R = _=𝓗ω_} (λ ξ st → st 𝓗ω[ ξ ]) σ {u} {v} uv

  -- bindωΛRel {R = _=𝓗ω_} {!   !} {!   !} {!   !} {!   !}
  -- bindωΛRel {R = _=𝓗ω_}(λ {X} {Y} σ {p} {q} e → {!   !} ) ?  ? ,𝓗ω (uv ?  𝓗ω[ ? ])

refl𝓗ω : ∀ {X} {s : Λ X} → s =𝓗ω s
refl𝓗ω = Ω𝓗 refl𝓗

var𝓗ω : ∀ {X} (x : X) → var x =𝓗ω var x
var𝓗ω x = refl𝓗ω

{-# TERMINATING #-}
abs𝓗ω : ∀ {X} {r1 r2 : Λ (↑ X)} → r1 =𝓗ω r2 → abs r1 =𝓗ω abs r2
abs𝓗ω (Ω𝓗 x) = Ω𝓗 (abs𝓗 x)
abs𝓗ω {X} {r1} {r2} (_,𝓗ω_ {v = v} om r12) = h ,𝓗ω abs𝓗ω r12 where
  e = λ ξ η → om (bind η ∘ lift ξ)
  f = λ ξ η → transp (λ z → z =𝓗ω (v [ bind η ∘ lift ξ ])) (bind-assoc r1) (e ξ η)
  g = λ ξ η → transp (_=𝓗ω_ ((r1 [ lift ξ ]) [ η ])) (bind-assoc v) (f ξ η)
  h = λ ξ → abs𝓗ω (_,𝓗ω_ {v = v [ lift ξ ]} (g ξ) refl𝓗ω )

{-# TERMINATING #-}
app𝓗ω : ∀ {X} {s1 s2 t1 t2 : Λ X} → s1 =𝓗ω s2 → t1 =𝓗ω t2 → app s1 t1 =𝓗ω app s2 t2
app𝓗ω {X} {s1} {s2} {t1} {t2} (Ω𝓗 s12) (Ω𝓗 t12) = Ω𝓗 (app𝓗 s12 t12)
app𝓗ω {X} {s1} {s2} {t1} {t2} (Ω𝓗 s0) (t0 ,𝓗ω t12) =
  (λ ξ → app𝓗ω (Ω𝓗 (s0 𝓗[ ξ ])) (t0 ξ )) ,𝓗ω (app𝓗ω refl𝓗ω t12)
app𝓗ω {X} {s1} {s2} {t1} {t2} (s0 ,𝓗ω s12) (Ω𝓗 t0) =
  (λ ξ → app𝓗ω (s0 ξ) (Ω𝓗 (t0 𝓗[ ξ ])) ) ,𝓗ω (app𝓗ω s12 refl𝓗ω)
app𝓗ω {X} {s1} {s2} {t1} {t2} (s0 ,𝓗ω s12) (t0 ,𝓗ω t12) =
  (λ ξ → app𝓗ω (s0 ξ) (t0 ξ)) ,𝓗ω app𝓗ω s12 t12

𝓗ωisΛCong : isΛCongruence _=𝓗ω_
𝓗ωisΛCong = ΛCong var𝓗ω app𝓗ω abs𝓗ω

-- Characterization of 𝓗ω-conversion
-- (A standardization theorem for 𝓗ω)

-- Initially, =𝓗ω is an omega theory generated from 𝓗
_=βΩω_ : ΛRel
_=βΩω_ = ωTh (_=𝓗_)

-- But any proof of (s =βΩω t) can be transformed
--   into a tree that only uses the two rules Ω𝓗 and ,𝓗ω postulated above
𝓗ω-standardization : ∀ {X} {s t : Λ X} → s =βΩω t → s =𝓗ω t
𝓗ω-standardization {X} {s} {t} st = ωTh*-elim _=𝓗_ _=𝓗ω_ (λ s t → Ω𝓗) 𝓗ωisΛCong _,𝓗ω_ s t ST
  where ST = ωTh⊆ωTh* _=𝓗_ (λ x y → y 𝓗[ x ]) symm𝓗 s t st

























-- refl=𝓗Ω : ∀ {X} → reflR (_=𝓗ω_ {X})
-- refl=𝓗Ω (var x) = Ω𝓗 refl𝓗
-- refl=𝓗Ω (app s t) = {!   !}
-- refl=𝓗Ω (abs r) = {!   !}
-- symm=𝓗Ω : ∀ {X} → symmR (_=𝓗ω_ {X})
-- symm=𝓗Ω = {!   !}
-- tran=𝓗Ω : ∀ {X} → tranR (_=𝓗ω_ {X})
-- tran=𝓗Ω = {!   !}
