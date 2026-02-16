{-# OPTIONS --guardedness #-}
module Homega.OmegaRule where

open import Logic
open import Lifting
open import Lambda
open import Reduction
-- open import Relations

open import Predicates
open import Relations.Core

open import Homega.Unsolvable
open import Homega.LambdaH

ωΛRel : ΛRel → ΛRel
ωΛRel R {X} s t = ∀ (ξ : X → Λ⁰) → R (s [ ξ ]) (t [ ξ ])

_⊆ΛRel_ : ΛRel → ΛRel → Set₁
R1 ⊆ΛRel R2 = ∀ {X} → R1 {X} ⊆ R2 {X}

Λ-Closed : ΛRel → Set₁
Λ-Closed R = ∀ {X Y} → (σ : X → Λ Y) → {s t : Λ X} → R s t → R (s [ σ ]) (t [ σ ])

bindωΛRel : ∀ {R : ΛRel} → Λ-Closed R
              → ∀ {X Y : Set} (ξ : X → Λ Y) {s t : Λ X}
              → ωΛRel R s t → ωΛRel R (s [ ξ ]) (t [ ξ ])
bindωΛRel {R} sub {X} {Y} ξ {s} {t} st σ =
  let   e1 : (σ : Y → Λ⁰) → s [ bind σ ∘ ξ ] ≡ s [ ξ ] [ σ ]
        e1 σ = bind-assoc {f = ξ} {σ} s
        e2 : (σ : Y → Λ⁰) → t [ bind σ ∘ ξ ] ≡ t [ ξ ] [ σ ]
        e2 σ = (bind-assoc {f = ξ} {σ} t)
     in transp (R ((s [ ξ ]) [ σ ])) (e2 σ)
               (transp (λ z → R z (t [ bind σ ∘ ξ ])) (e1 σ)
                        (st (bind σ ∘ ξ) ) )

module LambdaTheories (R : ΛRel) where

  isΛEquivalence : Set₁
  isΛEquivalence = ∀ {X} → isEquivalence (R {X})

  record isΛCongruence : Set₁ where
    constructor ΛCong
    field
      varR : ∀ {X} (x : X) → R (var x) (var x)
      appR : ∀ {X} {s1 s2 t1 t2 : Λ X} → R s1 t1 → R s2 t2 → R (app s1 s2) (app t1 t2)
      absR : ∀ {X} {r1 r2 : Λ (↑ X)} → R r1 r2 → R (abs r1) (abs r2)

  isωCongruence : Set₁
  isωCongruence = ∀ {X} → ωΛRel R {X} ⊆ R {X}

  record isωTheory : Set₁ where
    field
      isΛEq   : isΛEquivalence
      isΛCong : isΛCongruence
      isωCong : isωCongruence

open LambdaTheories public

module ω-Theory (R : ΛRel) where

  {- Attempt 3. -}

  data ωTh* {X : Set} : Λ X → Λ X → Set where
    axω*  : ∀ {s t : Λ X} → R s t → ωTh* s t
    varω* : ∀ {x : X} → ωTh* (var x) (var x)
    appω* : ∀ {s1 s2 t1 t2 : Λ X} → ωTh* s1 s2 → ωTh* t1 t2 → ωTh* (app s1 t1) (app s2 t2)
    absω* : ∀ {r1 r2 : Λ (↑ X)} → ωTh* r1 r2 → ωTh* (abs r1) (abs r2)
    ω-rule*  : ∀ {s t u : Λ X}   → ωΛRel ωTh* s t → ωTh* t u → ωTh* s u

  reflωTh* : ∀ {X} → reflR (ωTh* {X})
  reflωTh* (var x) = varω*
  reflωTh* (app s s₁) = appω* (reflωTh* s) (reflωTh* s₁)
  reflωTh* (abs s) = absω* (reflωTh* s)

  {- This is not passing Agda's termination checker.
     What is the complexity of this function's termination proof?
      -}
  {-# TERMINATING #-}
  bindωTh* : Λ-Closed R → Λ-Closed ωTh*
  bindωTh* sub ξ (axω* x) = axω* (sub ξ x )
  bindωTh* sub ξ varω* = reflωTh* (ξ _ )
  bindωTh* sub ξ (appω* st st₁) = appω* (bindωTh* sub ξ st) (bindωTh* sub ξ st₁)
  bindωTh* sub ξ (absω* st) = absω* (bindωTh* sub (lift ξ) st)
  bindωTh* sub {X} {Y} ξ (ω-rule* {s} {t} {u} x st) =
    -- ω-rule* (λ σ → transp (λ θ → ωTh* θ _) ({!   !} ! )
    --               (transp (λ u → ωTh* _ u)  {!   !}  ) )
    --         (bindωTh* sub ξ st )
    let   f : (σ : Y → Λ⁰) → ωTh* (t [ bind σ ∘ ξ ]) (u [ bind σ ∘ ξ ])
          f σ = bindωTh* sub (bind σ ∘ ξ) st
          e1 : (σ : Y → Λ⁰) → _
          e1 σ = bind-assoc {f = ξ} {σ} s
          e2 : (σ : Y → Λ⁰) → _
          e2 σ = (bind-assoc {f = ξ} {σ} t)
          e3 : (σ : Y → Λ⁰) → _
          e3 σ = bindωTh* sub (bind σ ∘ ξ) st
          r1 = (bindωΛRel {R = ωTh* } (bindωTh* sub) ξ {s} {t} x)
          r2 = (bindωTh* sub ξ st)
      in ω-rule* {s = s [ ξ ] } {t = t [ ξ ] } {u = u [ ξ ] } r1 r2

  symmωTh* : Λ-Closed R → (∀ {Y} → symmR (R {Y})) → ∀ {X} → symmR (ωTh* {X})
  symmωTh* sub sR (axω* x) = axω* (sR x)
  symmωTh* sub sR varω* = varω*
  symmωTh* sub sR (appω* st st₁) = appω* (symmωTh* sub sR st) (symmωTh* sub sR st₁)
  symmωTh* sub sR (absω* st) = absω* (symmωTh* sub sR st )
    -- where f = ?
  symmωTh* sub sR (ω-rule* {s} {t} {u} x st) =
     ω-rule* (λ ξ → bindωTh* sub ξ (symmωTh* sub sR st))
             (ω-rule* {s = t} {s} {s} (λ ξ → symmωTh* sub sR (x ξ)) (reflωTh* s))

  tranωTh* : Λ-Closed R → ∀ {X} → tranR (ωTh* {X})
  tranωTh* sub {X} (var v) .(var v) u varω* tu = tu
  tranωTh* sub {X} (app s1 s2) (app t1 t2) (app u1 u2) (appω* s1t1 s2t2) (appω* t1u1 t2u2)
    = appω* (tranωTh* sub s1 t1 u1 s1t1 t1u1) (tranωTh* sub s2 t2 u2 s2t2 t2u2)
  tranωTh* sub {X} (abs s0) (abs t0) (abs u0) (absω* st) (absω* tu)
    = absω* (tranωTh* sub s0 t0 u0 st tu)
  tranωTh* sub {X} s t u st tu = ω-rule* (λ ξ → bindωTh* sub ξ st ) tu

  ωTh*isΛEquivalence : Λ-Closed R → (∀ {Y} → symmR (R {Y})) → isΛEquivalence ωTh*
  ωTh*isΛEquivalence sub sR = record
    { isRefl = reflωTh* ; isSymm = symmωTh* sub sR ; isTran = tranωTh* sub }

  ωTh*isΛCongruence : isΛCongruence ωTh*
  ωTh*isΛCongruence = ΛCong (λ x → varω*) appω* absω*

  ωTh*isωCongruence : isωCongruence ωTh*
  ωTh*isωCongruence s t st = ω-rule* st (reflωTh* t )

  ωTh*isωTheory : Λ-Closed R → (∀ {Y} → symmR (R {Y})) → isωTheory ωTh*
  ωTh*isωTheory sub sR = record { isΛEq = ωTh*isΛEquivalence sub sR
                                ; isΛCong = ωTh*isΛCongruence
                                ; isωCong = ωTh*isωCongruence }

  {- Attempt 2 -}

  data ωTh {X : Set} : Λ X → Λ X → Set where
    axω  : ∀ {s t : Λ X} → R s t → ωTh s t
    varω : ∀ {x : X} → ωTh (var x) (var x)
    appω : ∀ {s1 s2 t1 t2 : Λ X} → ωTh s1 s2 → ωTh t1 t2 → ωTh (app s1 t1) (app s2 t2)
    absω : ∀ {r1 r2 : Λ (↑ X)} → ωTh r1 r2 → ωTh (abs r1) (abs r2)
    _!ωTh_  : ∀ {s t u : Λ X} → ωTh s t → ωTh t u → ωTh s u
    _~!ωTh_ : ∀ {s t u : Λ X} → ωTh t s → ωTh t u → ωTh s u
    ω-rule  : ∀ {s t : Λ X}   → ωΛRel ωTh s t → ωTh s t

  reflωTh : ∀ {X} → reflR (ωTh {X})
  reflωTh (var x) = varω
  reflωTh (app s t) = appω (reflωTh s) (reflωTh t)
  reflωTh (abs r) = absω (reflωTh r)

  symmωTh : ∀ {X} → symmR (ωTh {X})
  symmωTh {X} {s} {t} (axω x) = axω x ~!ωTh reflωTh s
  symmωTh {X} {.(var _)} {.(var _)} varω = varω
  symmωTh {X} {.(app _ _)} {.(app _ _)} (appω st st₁) = appω (symmωTh st) (symmωTh st₁)
  symmωTh {X} {.(abs _)} {.(abs _)} (absω st) = absω (symmωTh st)
  symmωTh {X} {s} {t} (st !ωTh st₁) = symmωTh st₁ !ωTh symmωTh st
  symmωTh {X} {s} {t} (st ~!ωTh st₁) = symmωTh st₁ !ωTh st
  symmωTh {X} {s} {t} (ω-rule om) = ω-rule (λ ξ → symmωTh (om ξ ) )

  tranωTh : ∀ {X} → tranR (ωTh {X})
  tranωTh {X} r s t rs st = rs !ωTh st

open ω-Theory public

module UniversalProperty (R : ΛRel) where

  open isΛCongruence

  -- Universal Property For ωTh*
  ωTh*-elim : ∀ (Q : ΛRel) → R ⊆ΛRel Q → isΛCongruence Q →
                (∀ {X} {s t u : Λ X} → ωΛRel Q s t → Q t u → Q s u) → ωTh* R ⊆ΛRel Q
  ωTh*-elim Q R⊆Q QisΛCong Q⊨ω s t (axω* Rst) = R⊆Q s t Rst
  ωTh*-elim Q R⊆Q QisΛCong Q⊨ω (var x) (var .x) varω* = varR QisΛCong x
  ωTh*-elim Q R⊆Q QisΛCong Q⊨ω (app s1 t1) (app s2 t2) (appω* s12 t12)
    = appR QisΛCong (ωTh*-elim Q R⊆Q QisΛCong Q⊨ω s1 s2 s12)
                    (ωTh*-elim Q R⊆Q QisΛCong Q⊨ω t1 t2 t12)
  ωTh*-elim Q R⊆Q QisΛCong Q⊨ω (abs r1) (abs r2) (absω* r12)
    = absR QisΛCong (ωTh*-elim Q R⊆Q QisΛCong Q⊨ω r1 r2 r12)
  ωTh*-elim Q R⊆Q QisΛCong Q⊨ω r t (ω-rule* rs st)
    = Q⊨ω (λ ξ → ωTh*-elim Q R⊆Q QisΛCong Q⊨ω (r [ ξ ]) _ (rs ξ ) )
          (ωTh*-elim Q R⊆Q QisΛCong Q⊨ω _ t st)



  ωTh-isΛEquivalence : isΛEquivalence (ωTh R)
  ωTh-isΛEquivalence = record { isRefl = reflωTh R ; isSymm = symmωTh R ; isTran = tranωTh R }
  ωTh-isΛCongruence  : isΛCongruence  (ωTh R)
  ωTh-isΛCongruence  = record { varR = λ x → varω ; appR = appω ; absR = absω }
  ωTh-isωCongruence  : isωCongruence  (ωTh R)
  ωTh-isωCongruence s t s=ωt = ω-rule s=ωt

  ωTh-isωTheory : isωTheory (ωTh R)
  ωTh-isωTheory = record { isΛEq   = ωTh-isΛEquivalence
                         ; isΛCong = ωTh-isΛCongruence
                         ; isωCong = ωTh-isωCongruence }

  -- Universal Property for ωTh
  -- For any Λ-relation R, ωTh(R) is the least Λ-theory containing R closed under the ω-rule
  ωThElim : ∀ (Q : ΛRel) → R ⊆ΛRel Q → isωTheory Q → ωTh R ⊆ΛRel Q
  ωThElim Q R⊆Q QTh@(record { isΛEq = isΛEq ; isΛCong = (ΛCong varR appR absR) ; isωCong = isωCong })
    {X} s t s=t with s=t
  ... | axω x = R⊆Q s t x
  ... | varω = varR _
  ... | appω c d = appR (ωThElim Q R⊆Q QTh _ _ c) (ωThElim Q R⊆Q QTh _ _ d)
  ... | absω c = absR (ωThElim Q R⊆Q QTh _ _ c)
  ... | c !ωTh  d = isTran (isΛEq) s _ t ((ωThElim Q R⊆Q QTh _ _ c)) ((ωThElim Q R⊆Q QTh _ _ d)) where open isEquivalence
  ... | c ~!ωTh  d = isTran (isΛEq) s _ t (isSymm isΛEq ((ωThElim Q R⊆Q QTh _ _ c)) )
                                          ((ωThElim Q R⊆Q QTh _ _ d)) where open isEquivalence
  ... | ω-rule om = isωCong s t (λ ξ → (ωThElim Q R⊆Q QTh _ _ (om ξ) ) )


  -- A comparison between different formulation of 𝓗ω
  ωTh⊆ωTh* : Λ-Closed R → (∀ {Y} → symmR (R {Y})) → ωTh R ⊆ΛRel ωTh* R
  ωTh⊆ωTh* sub sR s t st = ωThElim (ωTh* R) (λ x y → axω* ) (ωTh*isωTheory R sub sR) s t st

open UniversalProperty public

-- -- First attempt
-- ωΛRel : ΛRel → ΛRel
-- ωΛRel R {X} s t = ∀ {φ1 φ2 : X → Λ ⊥} → (∀ x → R (φ1 x) (φ2 x)) → R (s [ φ1 ]) (t [ φ2 ])
--
-- -- The last rule is not monotone
-- data _=𝓗ω_ {X : Set} : Λ X → Λ X → Set where
--   =Ω⊆=𝓗ω : ∀ {s t : Λ X}   → s =Ω t              → s =𝓗ω t
--   sred𝓗ω : ∀ {s t u : Λ X} → s ⟶s t  → t =𝓗ω u → s =𝓗ω u
--   pred𝓗ω : ∀ {s t u : Λ X} → s =𝓗ω t → u ⇉ t    → s =𝓗ω u
--   om𝓗ω   : ∀ {s t : Λ X} → ωΛRel _=𝓗ω_ s t → s =𝓗ω t
