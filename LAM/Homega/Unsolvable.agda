{-# OPTIONS --guardedness #-}

module LAM.Homega.Unsolvable where

open import Logic
open import Lifting
open import LAM.Lambda
open import LAM.Reduction
open import Predicates

open import Relations.ClosureOperators

-- Single step head reduction
-- Uses weak head reduction ⟶w defined in Reduction.agda
data _⟶h_ {X : Set} : Λ X → Λ X → Set where
  red⟶h : ∀ {s t} → s ⟶w t → s ⟶h t
  abs⟶h : ∀ {u v} → u ⟶h v → abs u ⟶h abs v

-- A coinductive definition of the unsolvability predicate
record 𝓤 {X : Set} (u : Λ X) : Set where
  coinductive
  constructor in𝓤
  field
    hterm : Λ X
    hstep : u ⟶h hterm
    unrec : hterm ∈ 𝓤

omega : ∀ {X} → Λ X
omega = abs (app (var o) (var o) )

Omega : ∀ {X} → Λ X
Omega = app omega omega

Omega⟶hOmega : ∀ {X} → Omega {X} ⟶h Omega
Omega⟶hOmega = red⟶h (red⟶w (redex refl))

open 𝓤

var∉𝓤 : ∀ {X} (x : X) → var x ∉ 𝓤
var∉𝓤 x x∈U with hstep x∈U
... | red⟶h (red⟶w ())


-- Omega is 𝓤
Omega∈𝓤 : ∀ {X} → Omega {X} ∈ 𝓤
hterm Omega∈𝓤 = Omega
hstep Omega∈𝓤 = Omega⟶hOmega
unrec Omega∈𝓤 = Omega∈𝓤

map⟶h : ∀ {X Y : Set} (f : X → Y) {s t : Λ X} → s ⟶h t → Λ→ f s ⟶h Λ→ f t
map⟶h f (red⟶h W) = red⟶h (map⟶w f W)
map⟶h f (abs⟶h st) = abs⟶h (map⟶h (↑→ f) st )

map𝓤 : ∀ {X Y : Set} (f : X → Y) {u : Λ X} → u ∈ 𝓤 → Λ→ f u ∈ 𝓤
-- map𝓤 f {u} u∈U = in𝓤 (Λ→ f (hterm u∈U)) (map⟶h f (hstep u∈U)) (map𝓤 f (unrec u∈U))
hterm (map𝓤 f {u} u∈U) = Λ→ f (hterm u∈U)
hstep (map𝓤 f {u} u∈U) = (map⟶h f (hstep u∈U))
unrec (map𝓤 f {u} u∈U) = (map𝓤 f (unrec u∈U))

-- Omega conversion
data _=Ω_ {X : Set} : Λ X → Λ X → Set where
  redΩ : ∀ {s t : Λ X} → 𝓤 s → 𝓤 t → s =Ω t
  varΩ : ∀ {x : X} → var x =Ω var x
  appΩ : ∀ {s1 s2 t1 t2 : Λ X} → s1 =Ω t1 → s2 =Ω t2 → app s1 s2 =Ω app t1 t2
  absΩ : ∀ {u1 u2 : Λ (↑ X)} → u1 =Ω u2 → abs u1 =Ω abs u2

refl=Ω : ∀ {X} {t : Λ X} → t =Ω t
refl=Ω {X} {var x} = varΩ
refl=Ω {X} {app s t} = appΩ refl=Ω refl=Ω
refl=Ω {X} {abs r} = absΩ refl=Ω

~=Ω : ∀ {X : Set} {s t : Λ X} → s =Ω t → t =Ω s
~=Ω (redΩ x y) = redΩ y x
~=Ω varΩ = varΩ
~=Ω (appΩ st1 st2) = appΩ (~=Ω st1) (~=Ω st2)
~=Ω (absΩ st) = absΩ (~=Ω st)

map=Ω : ∀ {X Y} (f : X → Y) → {s t : Λ X} → s =Ω t → Λ→ f s =Ω Λ→ f t
map=Ω f (redΩ x y) = redΩ (map𝓤 f x) (map𝓤 f y)
map=Ω f varΩ = varΩ
map=Ω f (appΩ st1 st2) = appΩ (map=Ω f st1) (map=Ω f st2)
map=Ω f (absΩ st) = absΩ (map=Ω (↑→ f) st)

bind⟶h : ∀ {X} {Y} {r1 r2 : Λ X} (σ : X → Λ Y) → r1 ⟶h r2 → (r1 [ σ ]) ⟶h (r2 [ σ ])
bind⟶h σ (red⟶h W) = red⟶h (bind⟶w σ W )
bind⟶h σ (abs⟶h r12) = abs⟶h (bind⟶h (io (λ z → Λ→ i (σ z)) (var o)) r12)

-- 𝓤 is a substitution ideal
bind𝓤 : ∀ {X Y : Set} {u : Λ X} (σ : X → Λ Y) → u ∈ 𝓤 → u [ σ ] ∈ 𝓤
hterm (bind𝓤 {u = u} σ u∈U) = hterm u∈U [ σ ]
hstep (bind𝓤 {u = u} σ u∈U) = bind⟶h σ (hstep u∈U)
unrec (bind𝓤 {u = u} σ u∈U) = bind𝓤 σ (unrec u∈U)

=Ω[=Ω] : ∀ {X Y : Set} (σ τ : X → Λ Y) → (∀ x → σ x =Ω τ x) → {s t : Λ X} → s =Ω t → (s [ σ ]) =Ω (t [ τ ])
=Ω[=Ω] σ τ στ (redΩ s∈U t∈U) = redΩ (bind𝓤 σ s∈U) (bind𝓤 τ t∈U)
=Ω[=Ω] σ τ στ varΩ = στ _
=Ω[=Ω] σ τ στ {app s1 s2} {app t1 t2} (appΩ s12 t12) = appΩ (=Ω[=Ω] σ τ στ s12) (=Ω[=Ω] σ τ στ t12)
=Ω[=Ω] σ τ στ (absΩ s=t) = absΩ (=Ω[=Ω] (lift σ) (lift τ) (io𝓟 _ (λ x → map=Ω i (στ x) ) varΩ ) s=t )

-- Omega conversion and reduction
⟶w⊆⟶h : ∀ {X} {s t : Λ X} → s ⟶w t → s ⟶h t
⟶w⊆⟶h {X} {.(app (abs _) _)} {t} (red⟶w (redex x)) = red⟶h (red⟶w (redex x) )
⟶w⊆⟶h {X} {.(app _ _)} {.(app _ _)} (appL⟶w (red⟶w x)) = red⟶h (appL⟶w (red⟶w x) )
⟶w⊆⟶h {X} {.(app (app _ _) _)} {.(app (app _ _) _)} (appL⟶w (appL⟶w (red⟶w x)))
  = red⟶h (appL⟶w (appL⟶w (red⟶w x)))
⟶w⊆⟶h {X} {.(app (app (app _ _) _) _)} {.(app (app (app _ _) _) _)} (appL⟶w (appL⟶w (appL⟶w st)))
  = red⟶h (appL⟶w (appL⟶w (appL⟶w st)))

SingleValued⟶w : ∀ {X} {s t1 t2 : Λ X} → s ⟶w t1 → s ⟶w t2 → t1 ≡ t2
SingleValued⟶w (red⟶w (redex refl)) (red⟶w (redex refl)) = refl
SingleValued⟶w (red⟶w (redex x)) (appL⟶w (red⟶w ()))
SingleValued⟶w (appL⟶w (red⟶w ())) (red⟶w (redex x))
SingleValued⟶w (appL⟶w w1) (appL⟶w w2) = cong2 app (SingleValued⟶w w1 w2) refl

SingleValued⟶h : ∀ {X} {s t1 t2 : Λ X} → s ⟶h t1 → s ⟶h t2 → t1 ≡ t2
SingleValued⟶h (red⟶h (red⟶w (redex R))) (red⟶h (red⟶w (redex R'))) = R ~! R'
SingleValued⟶h (red⟶h (red⟶w (redex refl))) (red⟶h (appL⟶w (red⟶w ())))
SingleValued⟶h (red⟶h (appL⟶w (red⟶w (redex refl)))) (red⟶h (appL⟶w (red⟶w (redex refl)))) = refl
SingleValued⟶h (red⟶h (appL⟶w (red⟶w (redex refl)))) (red⟶h (appL⟶w (appL⟶w (red⟶w ()))))
SingleValued⟶h (red⟶h (appL⟶w (appL⟶w (red⟶w ())))) (red⟶h (appL⟶w (red⟶w (redex refl))))
SingleValued⟶h (red⟶h (appL⟶w (appL⟶w W1))) (red⟶h (appL⟶w (appL⟶w W2)))
  = cong2 app (cong2 app (SingleValued⟶w W1 W2) refl ) refl
-- SingleValued⟶h (red⟶h x) (abs⟶h R2) = {!   !}
SingleValued⟶h (abs⟶h R1) (red⟶h (red⟶w ()))
SingleValued⟶h (abs⟶h R1) (abs⟶h R2) = cong abs (SingleValued⟶h R1 R2)

𝓤↓w⊆𝓤 : ∀ {X} {s t : Λ X} → s ⟶w t → s ∈ 𝓤 → t ∈ 𝓤
𝓤↓w⊆𝓤 {X} {(app (abs r) s)} {t} (red⟶w (redex r[s]=t)) s∈𝓤
  with hterm s∈𝓤 | hstep s∈𝓤 | unrec s∈𝓤
... | h | red⟶h (red⟶w (redex r[s]=h)) | h∈𝓤 = transp 𝓤 (~ r[s]=h ! r[s]=t) h∈𝓤
... | h@(app s0 .s) | red⟶h (appL⟶w (red⟶w ())) | h∈𝓤
𝓤↓w⊆𝓤 (appL⟶w st) s∈𝓤
  with hterm s∈𝓤 | hstep s∈𝓤 | unrec s∈𝓤
... | h | hs | h∈𝓤 = transp 𝓤 (SingleValued⟶h hs (red⟶h (appL⟶w st ) ) ) h∈𝓤

-- For some reason this simple function needs to be broken up into two
-- to pass the guardedness checker
abs𝓤+ : ∀ {X} {r : Λ (↑ X)}   → r ∈ 𝓤 → abs r ∈ 𝓤
-- abs𝓤+ r∈𝓤 with (abs𝓤+ (unrec r∈𝓤))
-- ... | c = in𝓤 (abs (hterm r∈𝓤)) (abs⟶h (hstep r∈𝓤)) c
abs𝓤+h  : ∀ {X} {r : Λ (↑ X)} → r ∈ 𝓤 → Λ X

abs𝓤+h r∈U = abs (hterm r∈U)
hterm (abs𝓤+ r∈𝓤) = abs𝓤+h r∈𝓤
hstep (abs𝓤+ r∈𝓤) = abs⟶h (hstep r∈𝓤)
unrec (abs𝓤+ r∈𝓤) = abs𝓤+ (unrec r∈𝓤)

-- Same
abs𝓤- : ∀ {X} {r : Λ (↑ X)} → abs r ∈ 𝓤 → r ∈ 𝓤
-- abs𝓤- {X} {r} λr∈𝓤 with hterm λr∈𝓤 | hstep λr∈𝓤 | unrec λr∈𝓤
-- ... | h | red⟶h (red⟶w ()) | r∈𝓤
-- ... | .(abs _) | abs⟶h {v} {w} rh | λw∈𝓤 = in𝓤 w rh (abs𝓤- λw∈𝓤)
abs𝓤-h : ∀ {X} {r : Λ (↑ X)} → abs r ∈ 𝓤 → Λ (↑ X)
abs𝓤-h {X} {r} Lr∈U with hterm Lr∈U | hstep Lr∈U
... | h | red⟶h (red⟶w ())
... | (abs v) | abs⟶h s = v

hterm (abs𝓤- Lr∈U) = abs𝓤-h Lr∈U
hstep (abs𝓤- Lr∈U) with hterm Lr∈U | hstep Lr∈U
... | h | red⟶h (red⟶w ())
... | (abs v) | abs⟶h s = s
unrec (abs𝓤- Lr∈U) with hterm Lr∈U | hstep Lr∈U | unrec Lr∈U
... | h | red⟶h (red⟶w ()) | h∈U
... | .(abs _) | abs⟶h hs | h∈U = abs𝓤- h∈U

-- 𝓤=Ω : ∀ {X : Set} (u t : Λ X) → u =Ω t → t ∈ 𝓤 → u ∈ 𝓤
-- 𝓤=Ω u=t u∈U = {!   !}

-- 𝓤 is an application ideal
{-# NON_TERMINATING #-}
appL𝓤 : ∀ {X : Set} {s : Λ X} → s ∈ 𝓤 → (t : Λ X) → app s t ∈ 𝓤
appL𝓤 {X} {s} s∈U t with hterm s∈U | hstep s∈U | unrec s∈U
... | .(a [ b ]ₒ) | red⟶h (red⟶w (redex {_} {a} {b} refl)) | h∈U
  = in𝓤 (app (a [ b ]ₒ) t) (red⟶h (appL⟶w (red⟶w (redex refl)) ) ) (appL𝓤 h∈U t)
... | (app p q) | red⟶h {app r .q} (appL⟶w W) | h∈U
  = in𝓤 (app (app p q) t) (red⟶h (appL⟶w (appL⟶w W ) ) ) (appL𝓤 h∈U t)
... | (abs u) | abs⟶h {v} hs | h∈U -- = {!   !}
  = in𝓤 (v [ t ]ₒ) (red⟶h (red⟶w (redex refl ) ) ) (bind𝓤 (io var t) (abs𝓤- s∈U) )



{-# NON_TERMINATING #-}
𝓤↓p⊆𝓤 : ∀ {X} {s t : Λ X} → s ⇉ t → s ∈ 𝓤 → t ∈ 𝓤
𝓤↓p⊆𝓤 {X} {s} {t} st s∈U with hterm s∈U | hstep s∈U | unrec s∈U
𝓤↓p⊆𝓤 {X} {app (abs r) s} {t} (red⇉ rs2 st2 e) s∈U | .(r [ s ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈U
  = transp 𝓤 e (𝓤↓p⊆𝓤 (⇉[⇉] (io var s) (io var _ ) (io𝓟 _ (λ x → var⇉ ) st2 ) rs2 ) h∈U )
  -- Check: is this guarded ???
  -- = in𝓤 (hterm rc) (hstep rc) (unrec rc) where
  --   rp = (⇉[⇉] (io var s) (io var _) (io𝓟 _ (λ x → var⇉) st2) rs2)
  --   rc = (𝓤↓p⊆𝓤 (transp (λ z → (r [ s ]ₒ) ⇉ z) e rp ) h∈U)
𝓤↓p⊆𝓤 {X} {app (abs r1) t1} {app (abs r2) t2} (app⇉ (abs⇉ r12) t12) s∈U | .(r1 [ t1 ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈U
  = in𝓤 (r2 [ t2 ]ₒ) (red⟶h (red⟶w (redex refl)))
        (𝓤↓p⊆𝓤 (⇉[⇉] (io var t1) (io var t2) (io𝓟 _ (λ x → var⇉) t12 ) r12 ) h∈U )
𝓤↓p⊆𝓤 {X} {.(app (abs _) u)} {t} (red⇉ st st₁ x) s∈U | app s u | red⟶h (appL⟶w {.(abs _)} (red⟶w ())) | h∈U
𝓤↓p⊆𝓤 {X} {.(abs _)} {.(abs _)} (abs⇉ st) s∈U | abs r | abs⟶h sh | h∈U = abs𝓤+ (𝓤↓p⊆𝓤 st (abs𝓤- s∈U) )
𝓤↓p⊆𝓤 {X} {(app s1 t1)} {(app s2 t2)} (app⇉ s12 t12) s∈U | app s3 .t1 | red⟶h (appL⟶w W) | h∈U
  with ⟶w\⇉ W s12
... | u ,, s3⇉u , axʳ W = in𝓤 (app u t2) (red⟶h (appL⟶w W )) (𝓤↓p⊆𝓤 (app⇉ s3⇉u t12) h∈U)
... | .s2 ,, s3⇉u , εʳ = (𝓤↓p⊆𝓤 (app⇉ s3⇉u t12) h∈U)
  -- Check: is the last equation guarded??

𝓤↓β⋆⊆𝓤 : ∀ {X} {s t : Λ X} → s ⟶β⋆ t → s ∈ 𝓤 → t ∈ 𝓤
𝓤↓β⋆⊆𝓤 ε⋆ s∈U = s∈U
𝓤↓β⋆⊆𝓤 (sy ,⋆ yt) s∈U = 𝓤↓β⋆⊆𝓤 yt (𝓤↓p⊆𝓤 (⟶β⊆⇉ sy ) s∈U)

-- 𝓤↓β⊆𝓤 : ∀ {X} {s t : Λ X} → s ⟶β t → s ∈ 𝓤 → t ∈ 𝓤
-- 𝓤↓β⊆𝓤 {X} {app (abs r) s} (red⟶β (redex refl)) s∈𝓤
--   with hterm s∈𝓤 | hstep s∈𝓤 | unrec s∈𝓤
-- ... | .(r [ s ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈𝓤 = h∈𝓤
-- ... | .(app _ _) | red⟶h (appL⟶w (red⟶w ())) | h∈𝓤
-- 𝓤↓β⊆𝓤 {X} {abs s} {abs t} (abs⟶β st) s∈𝓤 = abs𝓤+ (𝓤↓β⊆𝓤 st (abs𝓤- s∈𝓤))
-- 𝓤↓β⊆𝓤 (appL⟶β st) s∈𝓤 = {!   !}
-- 𝓤↓β⊆𝓤 (appR⟶β st) s∈𝓤 = {!   !}

-- -- still need a lemma for the last case of this
-- {-# NON_TERMINATING #-}
-- 𝓤↓s⊆𝓤 : ∀ {X} {s t : Λ X} → s ⟶s t → s ∈ 𝓤 → t ∈ 𝓤
-- 𝓤↓s⊆𝓤 (red⟶s w st) s∈𝓤 = 𝓤↓s⊆𝓤 st (𝓤↓w⊆𝓤 w s∈𝓤)
-- 𝓤↓s⊆𝓤 var⟶s s∈𝓤 with hstep s∈𝓤
-- ... | red⟶h (red⟶w ())
-- 𝓤↓s⊆𝓤 (abs⟶s st) s∈𝓤 with hterm s∈𝓤 | hstep s∈𝓤 | unrec s∈𝓤
-- ... | h | red⟶h (red⟶w ()) | h∈𝓤
-- ... | (abs h') | abs⟶h sh | h∈𝓤 = abs𝓤+ (𝓤↓s⊆𝓤 st (abs𝓤- s∈𝓤))
-- 𝓤↓s⊆𝓤 (app⟶s {s1} {s2} {t1} {t2} s1s2 t1t2) s∈𝓤
--   with hterm s∈𝓤 | hstep s∈𝓤 | unrec s∈𝓤
-- 𝓤↓s⊆𝓤 (app⟶s (red⟶s (red⟶w ()) s1s2) t1t2) s∈𝓤 | h | red⟶h (red⟶w (redex x)) | h∈𝓤
-- 𝓤↓s⊆𝓤 (app⟶s {s1} {s2} {t1} {t2} (abs⟶s {r1} {r2} s1s2) t1t2) s∈𝓤
--     | .(r1 [ t1 ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈𝓤
--   = in𝓤 (r2 [ io var t2 ]) (red⟶h (red⟶w (redex refl) ) )
--         (𝓤↓s⊆𝓤 (⟶s[⟶s] (io var t1) (io var t2) (io𝓟 _ (λ x → var⟶s) t1t2) s1s2) h∈𝓤 )
-- ... | (app t0 t1) | red⟶h (appL⟶w W) | h∈𝓤 = {!   !}

-- Commutation of Omega-conversion and reduction relations

⇉\=Ω : ∀ {X} {r s t : Λ X} → r ⇉ s → r =Ω t → Σ[ u ∈ Λ X ] (s =Ω u × t ⇉ u)
⇉\=Ω {X} {var x} {s} {t} rs (redΩ x∈U _) = ∅ (var∉𝓤 x x∈U)
⇉\=Ω {X} {var x} {.(var x)} {.(var x)} var⇉ varΩ = (var x ,, varΩ , var⇉ )
⇉\=Ω {X} {abs r} {abs u} {(abs v)} (abs⇉ ru) (absΩ rv) with ⇉\=Ω ru rv
... | (w ,, uw , vw) = abs w ,, (absΩ uw ) , abs⇉ vw
⇉\=Ω {X} {abs r} {abs u} {t} (abs⇉ rs) (redΩ λr∈U t∈U) = t ,, λu=t , refl⇉ where
  λu=t = redΩ (abs𝓤+ (𝓤↓p⊆𝓤 rs (abs𝓤- λr∈U ) ) ) t∈U
⇉\=Ω {X} {app (abs r0) t0} {.(v [ u ]ₒ)} {t} (red⇉ {.r0} {v} {.t0} {u} r0v t0u refl) (redΩ Δ∈U t∈U)
  with hterm Δ∈U | hstep Δ∈U | unrec Δ∈U
... | .(r0 [ t0 ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈U = (t ,, redΩ (𝓤↓p⊆𝓤 ρ h∈U ) t∈U , refl⇉ )
  where ρ = (⇉[⇉] (io var t0) (io var u) (io𝓟 _ (λ x → var⇉ ) t0u) r0v )
... | app a t0 | red⟶h (appL⟶w (red⟶w ())) | h∈U
⇉\=Ω {X} {app (abs r0) t0} {.(v [ u ]ₒ)} {(app t1 t2)} (red⇉ {.r0} {v} {.t0} {u} r0v t0u refl) (appΩ Lr0t1 t02)
  with ⇉\=Ω t0u t02 | Lr0t1
... | s ,, u=s , t2s | redΩ Lr0∈U t1∈U = app t1 t2 ,, omeq , refl⇉
  where omeq = redΩ (bind𝓤 (io var u) (𝓤↓p⊆𝓤 r0v (abs𝓤- Lr0∈U) ) ) (appL𝓤 t1∈U t2)
... | s ,, u=s , t2s | absΩ r0=u2
  with ⇉\=Ω r0v r0=u2
... | p ,, v=p , u2p = p [ s ]ₒ ,, =Ω[=Ω] (io var u) (io var s) (io𝓟 _ (λ x → varΩ) u=s ) v=p , (red⇉ u2p t2s refl)
⇉\=Ω {X} {app r1 r2} {app s1 s2} {t} (app⇉ rs1 rs2) (redΩ x y) =
  t ,, redΩ (𝓤↓p⊆𝓤 (app⇉ rs1 rs2 ) x ) y , refl⇉
⇉\=Ω {X} {app r1 r2} {app s1 s2} {(app t1 t2)} (app⇉ rs1 rs2) (appΩ rt1 rt2)
  with ⇉\=Ω rs1 rt1 | ⇉\=Ω rs2 rt2
... | (u ,, su , tu) | (v ,, sv , tv) = app u v ,, appΩ su sv , app⇉ tu tv

⇉/=Ω : ∀ {X} {r s t : Λ X} → r =Ω s → s ⇉ t → Σ[ u ∈ Λ X ] (r ⇉ u × u =Ω t)
⇉/=Ω rs st with ⇉\=Ω st (~=Ω rs)
... | (u ,, tu , ru) = u ,, ru , ~=Ω tu

⟶h⊆⇉ : ∀ {X} {s t : Λ X} → s ⟶h t → s ⇉ t
⟶h⊆⇉ (red⟶h (red⟶w (redex e))) = red⇉ refl⇉ refl⇉ e
⟶h⊆⇉ (red⟶h (appL⟶w W)) = app⇉ (⟶h⊆⇉ (red⟶h W) ) refl⇉
⟶h⊆⇉ (abs⟶h st) = abs⇉ (⟶h⊆⇉ st)

=Ω/⟶w : ∀ {X} {r s t : Λ X} → r =Ω s → s ⟶w t → Σ[ u ∈ Λ X ] ((_⟶w_ ʳ) r u × u =Ω t)
=Ω/⟶w {r = r} (redΩ r∈U s∈U) st = r ,, εʳ , redΩ r∈U (𝓤↓w⊆𝓤 st s∈U )
=Ω/⟶w varΩ (red⟶w ())
=Ω/⟶w (appΩ {s1} {s2} {abs u2} {t2} (redΩ x x₁) rs₁) (red⟶w (redex {_} {u2} refl))
  = app s1 s2 ,, εʳ , redΩ (appL𝓤 x s2) (bind𝓤 (io var t2) (abs𝓤- x₁ ) )
=Ω/⟶w (appΩ {.(abs _)} {s2} {abs u2} {t2} (absΩ {v2} rs) rs₁) (red⟶w (redex {_} {u2} refl))
  = v2 [ s2 ]ₒ ,, (axʳ (red⟶w (redex refl) ) ) , =Ω[=Ω] (io var s2) (io var t2) (io𝓟 _ (λ x → refl=Ω) rs₁ ) rs
=Ω/⟶w (appΩ rs rs₁) (appL⟶w st) with =Ω/⟶w rs st
... | u ,, axʳ s1→u , u=t = app u _ ,, axʳ (appL⟶w s1→u ) , (appΩ u=t rs₁ )
... | u ,, εʳ , u=t = app u _ ,, εʳ , (appΩ u=t rs₁)
=Ω/⟶w (absΩ rs) (red⟶w ())

=Ω/⟶s : ∀ {X} {r s t : Λ X} → r =Ω s → s ⟶s t → Σ[ u ∈ Λ X ] (r ⟶s u × u =Ω t)
=Ω/⟶s (redΩ r∈U s∈U) (red⟶s W st) = =Ω/⟶s (redΩ r∈U (𝓤↓w⊆𝓤 W s∈U)) st
=Ω/⟶s (redΩ r∈U s∈U) var⟶s = ∅ (var∉𝓤 _ s∈U)
=Ω/⟶s {r = r} (redΩ r∈U s∈U) S@(app⟶s s12 t12) = r ,, refl⟶s , (redΩ r∈U (𝓤↓β⋆⊆𝓤 (⟶s⊆⟶β⋆ _ _ S) s∈U ))
=Ω/⟶s (redΩ r∈U s∈U) (abs⟶s st) = _ ,, refl⟶s , redΩ r∈U (abs𝓤+ (𝓤↓β⋆⊆𝓤 (⟶s⊆⟶β⋆ _ _ st) (abs𝓤- s∈U ) ) )
=Ω/⟶s varΩ (red⟶s (red⟶w ()) st)
=Ω/⟶s varΩ var⟶s = _ ,, (var⟶s , varΩ)
=Ω/⟶s (absΩ rs) (red⟶s (red⟶w ()) st)
=Ω/⟶s (absΩ rs) (abs⟶s st) with =Ω/⟶s rs st
... | (v ,, vu , ur2) = abs v ,, abs⟶s vu , absΩ ur2
=Ω/⟶s (appΩ st1 st2) (app⟶s t1s3 t3t2) with =Ω/⟶s st1 t1s3 | =Ω/⟶s st2 t3t2
... | (u ,, U1 , U2) | (v ,, V1 , V2) = app u v ,, (app⟶s U1 V1) , (appΩ U2 V2)
=Ω/⟶s A@(appΩ st1 st2) (red⟶s W t1t2→t) with =Ω/⟶w A W
... | (app x1 x2) ,, εʳ , u=s with =Ω/⟶s u=s t1t2→t
... | v ,, uv , v=t = v ,, uv , v=t
=Ω/⟶s A@(appΩ st1 st2) (red⟶s W t1t2→t) | u ,, axʳ x , u=s with =Ω/⟶s u=s t1t2→t
... | v ,, uv , v=t = v ,, (red⟶s x uv ) , v=t

=Ω\⟶s : ∀ {X} {r s t : Λ X} → r =Ω s → r ⟶s t → Σ[ u ∈ Λ X ] (s ⟶s u × t =Ω u)
=Ω\⟶s rs rt with =Ω/⟶s (~=Ω rs) rt
... | (u ,, su , ut) = u ,, su , ~=Ω ut

{-# NON_TERMINATING #-}
𝓤=Ω : ∀ {X : Set} (u t : Λ X) → u ∈ 𝓤 → u =Ω t → t ∈ 𝓤
𝓤=Ω u t u∈U (redΩ _ t∈U) = t∈U
𝓤=Ω .(var _) .(var _) u∈U varΩ = ∅ (var∉𝓤 _ u∈U )
𝓤=Ω .(abs _) .(abs _) u∈U (absΩ u=t) = abs𝓤+ (𝓤=Ω _ _ (abs𝓤- u∈U) u=t )
𝓤=Ω (app (var x) s2) (app t1 t2) u∈U (appΩ (redΩ x₁ x₂) st2) = ∅ (var∉𝓤 x x₁ )
𝓤=Ω (app (var x) s2) (app .(var x) t2) u∈U (appΩ varΩ st2) with hterm u∈U | hstep u∈U
... | .(app _ s2) | red⟶h (appL⟶w (red⟶w ()))
𝓤=Ω (app (app s1 s3) s2) (app t1 t2) u∈U (appΩ st1 st2) with hterm u∈U | hstep u∈U
𝓤=Ω (app (app s1 s3) s2) (app t1 t2) u∈U (appΩ (redΩ x₁ x₂) st2) | app s0 s2 | red⟶h (appL⟶w x) = appL𝓤 x₂ _
𝓤=Ω (app (app s0 s1) s2) (app (app t0 t1) t2) u∈U (appΩ A@(appΩ st1 st3) st2) | app s3 s2 | red⟶h S@(appL⟶w x)
  with =Ω/⟶w (~=Ω A) x
... | v ,, axʳ W , u=s0 = in𝓤 f g h where
  f = app v t2
  g = red⟶h (appL⟶w W)
  h = 𝓤=Ω (app s3 s2) f (𝓤↓w⊆𝓤 S u∈U ) (appΩ (~=Ω u=s0) st2)
... | (app v1 v2) ,, εʳ , u=s0 with hterm u∈U | hstep u∈U | unrec u∈U
... | (app _ _) | red⟶h (appL⟶w W) | v∈U =
  𝓤=Ω (app s3 s2) _ (transp (λ z → app z s2 ∈ 𝓤) (SingleValued⟶w W x ) v∈U )
       (appΩ (~=Ω u=s0) st2) -- in𝓤 (app s3 s2) (app )
-- = 𝓤=Ω (app s3 s2) _ (unrec {!   !} ) (appΩ (~=Ω u=s0) st2 )
𝓤=Ω (app (abs s1) s2) (app t1 t2) u∈U (appΩ (redΩ x x₁) st2) = appL𝓤 x₁ t2
𝓤=Ω (app (abs s1) s2) (app (abs v) t2) u∈U (appΩ (absΩ st1) st2)
  with hterm u∈U | hstep u∈U | unrec u∈U
... | .(s1 [ s2 ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈U
  = in𝓤 (v [ t2 ]ₒ) (red⟶h (red⟶w (redex refl))) (𝓤=Ω (s1 [ s2 ]ₒ) (v [ t2 ]ₒ) h∈U
        (=Ω[=Ω] (io var s2) (io var t2) (io𝓟 _ (λ x → varΩ) st2) st1 ) )
... | .(app _ s2) | red⟶h (appL⟶w (red⟶w ())) | h∈U

--   with hterm u∈U | hstep u∈U | unrec u∈U
-- 𝓤=Ω (app .(abs _) s2) (app t1 t2) u∈U (appΩ (redΩ x x₁) st2) | h | red⟶h (red⟶w (redex e)) | h∈U
--   = {!   !}
-- -- 𝓤=Ω (app (abs u2) s2) (app (abs u3) t2) u∈U (appΩ (absΩ st1) st2) | h | red⟶h (red⟶w (redex e)) | h∈U
-- 𝓤=Ω (app (abs u2) s2) (app (abs u3) t2) u∈U (appΩ (absΩ st1) st2) | .(u2 [ s2 ]ₒ) | red⟶h (red⟶w (redex refl)) | h∈U = in𝓤 (u3 [ t2 ]ₒ) (red⟶h (red⟶w (redex refl)))
--   (𝓤=Ω (u2 [ s2 ]ₒ) (u3 [ t2 ]ₒ) h∈U (=Ω[=Ω] (io var s2) (io var t2) (io𝓟 _ (λ x → varΩ) st2) st1) )
-- ... | .(app _ s2) | red⟶h (appL⟶w x) | h∈U = {!   !}

_=Ω!=Ω_ : ∀ {X} {r s t : Λ X} → r =Ω s → s =Ω t → r =Ω t
_=Ω!=Ω_ {r = r} {var x} {t} (redΩ x₁ x₂) st = ∅ (var∉𝓤 x x₂ )
_=Ω!=Ω_ {r = .(var x)} {var x} {t} varΩ (redΩ x₁ x₂) = ∅ (var∉𝓤 x x₁ )
_=Ω!=Ω_ {r = .(var x)} {var x} {.(var x)} varΩ varΩ = varΩ
_=Ω!=Ω_ {r = r} {abs s} {t} rs (redΩ x x₁) = redΩ (𝓤=Ω _ _ x (~=Ω rs) ) x₁
_=Ω!=Ω_ {r = r} {abs s} {abs u2} (redΩ x x₁) (absΩ st) = redΩ x (abs𝓤+ (𝓤=Ω _ _ (abs𝓤- x₁ ) st ) )
_=Ω!=Ω_ {r = .(abs _)} {abs s} {abs u2} (absΩ rs) (absΩ st) = absΩ (_=Ω!=Ω_ rs  st)
_=Ω!=Ω_ {r = r} {app s1 s2} {t} (redΩ s12∈U r∈U) (redΩ _ t∈U) = redΩ s12∈U t∈U
_=Ω!=Ω_ {r = r} {app s1 s2} {(app t1 t2)} (redΩ s12∈U r∈U) A@(appΩ s12 t12) = redΩ s12∈U (𝓤=Ω _ _ r∈U A )
_=Ω!=Ω_ {r = app r1 r2} {app s1 s2} {t} A@(appΩ rs rs₁) (redΩ x x₁) = redΩ (𝓤=Ω _ _ x (~=Ω A) ) x₁
_=Ω!=Ω_ {r = app r1 r2} {app s1 s2} {.(app _ _)} (appΩ rs rs₁) (appΩ st st₁) = appΩ (_=Ω!=Ω_ rs st) (_=Ω!=Ω_ rs₁ st₁)


-- =Ω/⟶h : ∀ {X} {r s t : Λ X} → r =Ω s → s ⟶h t → Σ[ u ∈ Λ X ] (r ⟶h u × u =Ω t)
-- =Ω/⟶h {r = r} {s} {t} (redΩ r∈U s∈U) st = {!   !}
-- =Ω/⟶h {r = .(var _)} {.(var _)} {t} varΩ st = {!   !}
-- =Ω/⟶h {r = .(app _ _)} {.(app _ _)} {t} (appΩ rs rs₁) st = {!   !}
-- =Ω/⟶h {r = .(abs _)} {.(abs _)} {t} (absΩ rs) st = {!   !}

-- =Ω/⟶w : ∀ {X} {r s t : Λ X} → r =Ω s → s ⟶w t → Σ[ u ∈ Λ X ] (r ⟶w u × u =Ω t)
-- =Ω/⟶w (redΩ {r0} r0∈U s∈U) (red⟶w (redex {r} {s} {t} e)) with hstep s∈U
-- ... | hs = {!   !}
-- =Ω/⟶w (redΩ r∈U s∈U) (appL⟶w st) = {!   !}
-- =Ω/⟶w varΩ st = {!   !}
-- =Ω/⟶w (appΩ rs rs₁) st = {!   !}
-- =Ω/⟶w (absΩ rs) st = {!   !}

-- ⟶w\=Ω : ∀ {X} {r s t : Λ X} → r ⟶w s → r =Ω t → Σ[ u ∈ Λ X ] (s =Ω u × t ⟶w u)
-- ⟶w\=Ω {t = t} (red⟶w (redex {_} {r} {s} refl)) (redΩ Lrs∈U t∈U) = {!   !}
-- ⟶w\=Ω {t = .(app _ _)} (red⟶w (redex {_} {r} {s} refl)) (appΩ st st₁) = {!   !}
-- ⟶w\=Ω (appL⟶w rw) st = {!   !}
--
-- ⟶s\=Ω : ∀ {X} {r s t : Λ X} → r ⟶s s → r =Ω t → Σ[ u ∈ Λ X ] (s =Ω u × t ⟶s u)
-- ⟶s\=Ω {X} {r} {s} {t} (red⟶s {s = u} W rs) rt = {!   !}
-- ⟶s\=Ω {X} {.(var _)} {(var _)} {t} var⟶s rt = {!   !}
-- ⟶s\=Ω {X} {.(app _ _)} {.(app _ _)} {t} (app⟶s rs rs₁) rt = {!   !}
-- ⟶s\=Ω {X} {.(abs _)} {.(abs _)} {t} (abs⟶s rs) rt = {!   !}

-- ⟶s\=Ω : ∀ {X} {r s t : Λ X} → r ⟶s s → s =Ω t → Σ[ u ∈ Λ X ] (s =Ω u × t ⟶s u)
-- ⟶s\=Ω (red⟶s {s = s'} ss' s'r) (redΩ s=Ω t=Ω) = {!   !}
-- ⟶s\=Ω var⟶s (redΩ s∈𝓤 t∈𝓤) = {!   !}
-- ⟶s\=Ω (app⟶s rs rs₁) (redΩ s=Ω t=Ω) = {!   !}
-- ⟶s\=Ω (abs⟶s rs) (redΩ s=Ω t=Ω) = {!   !}
-- ⟶s\=Ω rs varΩ = {!   !}
-- ⟶s\=Ω rs (appΩ st st₁) = {!   !}
-- ⟶s\=Ω rs (absΩ st) = {!   !}








-- the end
