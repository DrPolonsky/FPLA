open import Logic
open import Lifting 
open import LAM.Lambda
open import LAM.Reduction.Beta
open import LAM.Reduction.StandardBeta
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

module LAM.Reduction.ParallelBeta where 

-- Parallel reduction
-- AKA "inside-out" reduction strategy
-- ­⇉ is \r-2
data _⇉_ {X : Set} : Λ X → Λ X → Set where
  red⇉ : ∀ {s1 s2 : Λ (↑ X)} {t1 t2 t3 : Λ X}
           → s1 ⇉ s2 → t1 ⇉ t2 → s2 [ t2 ]ₒ ≡ t3 → (app (abs s1) t1) ⇉ t3
  var⇉ : ∀ {x}           → var x ⇉ var x
  app⇉ : ∀ {s1 s2 t1 t2} → s1 ⇉ s2 → t1 ⇉ t2 → app s1 t1 ⇉ app s2 t2
  abs⇉ : ∀ {r1 r2}       → r1 ⇉ r2 → abs r1 ⇉ abs r2

map⇉ : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⇉ t2 → Λ→ f t1 ⇉ Λ→ f t2
map⇉ f (red⇉ {s1} {s2} {t1} {t2} s12 t12 refl) =
  red⇉ (map⇉ (↑→ f) s12) (map⇉ f t12) (~ (bind-map s2 t2 f) )
map⇉ f var⇉ = var⇉
map⇉ f (app⇉ t12 t13) = app⇉ (map⇉ f t12) (map⇉ f t13)
map⇉ f (abs⇉ t12) = abs⇉ (map⇉ (↑→ f) t12)

lift⇉ : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⇉ g x) → (∀ y → lift f y ⇉ lift g y)
lift⇉ f g f→g (i x) = map⇉ i (f→g x)
lift⇉ f g f→g o = var⇉

⇉[⇉] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⇉ g x)
             → ∀ {s t : Λ X} → s ⇉ t →   (s [ f ])  ⇉  (t [ g ])
⇉[⇉] f g f⇉g {(app (abs s1) s2)} {t} (red⇉ {u1} {u2} {t1} {t2} s⇉t1 s⇉t2 refl) =
  red⇉ (⇉[⇉] (lift f) (lift g) (lift⇉ f g f⇉g) s⇉t1) (⇉[⇉] f g f⇉g s⇉t2)
        (~ (subst-lemma u2 t2 g) )
⇉[⇉] f g f⇉g {(var x)} {.(var x)} var⇉ = f⇉g x
⇉[⇉] f g f⇉g {(app s1 s2)} {(app t1 t2)} (app⇉ s1⇉t1 s2⇉t2) = app⇉ (⇉[⇉] f g f⇉g s1⇉t1) (⇉[⇉] f g f⇉g s2⇉t2)
⇉[⇉] f g f⇉g {(abs r1)} {(abs r2)} (abs⇉ s⇉t) = abs⇉ (⇉[⇉] (lift f) (lift g) (lift⇉ f g f⇉g) s⇉t )

⇉[⇉]ₒ : ∀ {X} → {s1 s2 : Λ (↑ X)} → {t1 t2 : Λ X} → s1 ⇉ s2 → t1 ⇉ t2 → (s1 [ t1 ]ₒ) ⇉ (s2 [ t2 ]ₒ)
⇉[⇉]ₒ {X} {s1} {s2} {t1} {t2} s12 t12 =
  ⇉[⇉] (io var t1) (io var t2) (io𝓟 _ (λ x → var⇉) t12) s12

⟶w\⇉ : ∀ {X} {s t1 t2 : Λ X} → s ⟶w t1 → s ⇉ t2 → Σ[ u ∈ Λ X ] (t1 ⇉ u × (_⟶w_ ʳ) t2 u)
⟶w\⇉ (red⟶w (redex refl)) (red⇉ {s2 = s2} {t2 = t2} s⇉s2 t⇉t2 refl) =
  s2 [ t2 ]ₒ ,, ⇉[⇉]ₒ s⇉s2 t⇉t2 , εʳ
⟶w\⇉ (red⟶w (redex refl)) (app⇉ {s2 = (abs s3)} {t2 = t2} (abs⇉ s⇉s3) t⇉t2) =
  s3 [ t2 ]ₒ ,, ⇉[⇉]ₒ s⇉s3 t⇉t2 , axʳ (red⟶w (redex refl))
⟶w\⇉ (appL⟶w (red⟶w ())) (red⇉ s⇉t2 s⇉t3 x)
⟶w\⇉ (appL⟶w s⟶t1) (app⇉ s⇉t2 s⇉t3) with ⟶w\⇉ s⟶t1 s⇉t2
... | u ,, t1⇉u , axʳ W = app u _ ,, app⇉ t1⇉u s⇉t3 , axʳ (appL⟶w W )
... | u ,, t1⇉u , εʳ    = app u _ ,, app⇉ t1⇉u s⇉t3 , εʳ

⟶s\⇉ : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⇉ t2 → Σ[ u ∈ Λ X ] (t1 ⇉ u × t2 ⟶s u)
⟶s\⇉ (red⟶s W s⟶t1) s⇉t2 with ⟶w\⇉ W s⇉t2
... | u ,, s1⇉u , εʳ       = ⟶s\⇉ s⟶t1 s1⇉u
... | u ,, s1⇉u , axʳ W with ⟶s\⇉ s⟶t1 s1⇉u
... | v ,, t1⇉v , u⟶sv = v ,, t1⇉v , red⟶s W u⟶sv
⟶s\⇉ var⟶s var⇉ = var _ ,, var⇉ , var⟶s
⟶s\⇉ (app⟶s (red⟶s (red⟶w ()) s⟶t1) s⟶t2) (red⇉ s⇉t2 s⇉t3 r)
⟶s\⇉ (app⟶s (abs⟶s s1⟶t11) s2⟶t21) (red⇉ {s1} {s2} {t1} {t2} {t3} s1⇉t12 s2⇉t22 refl)
  with ⟶s\⇉ s1⟶t11 s1⇉t12 | ⟶s\⇉ s2⟶t21 s2⇉t22
... | (u1 ,, t11⇉u1 , t21⟶u1) | (u2 ,, t21⇉u2 , t22⟶u2) =
  u1 [ u2 ]ₒ ,, red⇉ t11⇉u1 t21⇉u2 refl , (⟶s[⟶s]ₒ t21⟶u1 t22⟶u2  )
⟶s\⇉ (app⟶s s1⟶t11 s2⟶t21) (app⇉ s1⇉t12 s2⇉t22) with ⟶s\⇉ s1⟶t11 s1⇉t12 | ⟶s\⇉ s2⟶t21 s2⇉t22
... | (u1 ,, t11⇉u1 , t21⟶u1) | (u2 ,, t21⇉u2 , t22⟶u2) = (app u1 u2 ,, app⇉ t11⇉u1 t21⇉u2 , app⟶s t21⟶u1 t22⟶u2 )
⟶s\⇉ (abs⟶s s⟶t1) (abs⇉ s⇉t2) with ⟶s\⇉ s⟶t1 s⇉t2
... | (u ,, t1⇉u , t2⟶u) = abs u ,, abs⇉ t1⇉u , abs⟶s t2⟶u

refl⇉ : ∀ {X} {t : Λ X} → t ⇉ t
refl⇉ {X} {var x} = var⇉
refl⇉ {X} {app s t} = app⇉ refl⇉ refl⇉
refl⇉ {X} {abs r} = abs⇉ refl⇉

⟶β⊆⇉ : ∀ {X} {s t : Λ X} → s ⟶β t  →  s ⇉ t
⟶β⊆⇉ (red⟶β (redex e)) = red⇉ refl⇉ refl⇉ e
⟶β⊆⇉ (appL⟶β st) = app⇉ (⟶β⊆⇉ st ) refl⇉
⟶β⊆⇉ (appR⟶β st) = app⇉ refl⇉ (⟶β⊆⇉ st)
⟶β⊆⇉ (abs⟶β st) = abs⇉ (⟶β⊆⇉ st)

_⇉⋆_ : ∀ {X} → Λ X → Λ X → Set
_⇉⋆_ = _⇉_ ⋆

⟶β⋆⊆⇉⋆ : ∀ {X} {s t : Λ X} → s ⟶β⋆ t  →  s ⇉⋆ t
⟶β⋆⊆⇉⋆ = ⊆⋆ (λ x y → ⟶β⊆⇉) _ _

_⇉[_] : ∀ {X Y : Set} {s t : Λ X} → s ⇉ t → ∀ (σ : X → Λ Y) → s [ σ ] ⇉ t [ σ ]
red⇉ {s1 = s1} {s2} {t1} {t2} p1 p2 e ⇉[ σ ]
  = red⇉ (p1 ⇉[ lift σ ]) (p2 ⇉[ σ ]) (subst-lemma s2 t2 σ ~! cong (λ z → z [ σ ]) e)
var⇉         ⇉[ σ ] = refl⇉
app⇉ st1 st2 ⇉[ σ ] = app⇉ (st1 ⇉[ σ ]) (st2 ⇉[ σ ])
abs⇉ st      ⇉[ σ ] = abs⇉ (st ⇉[ lift σ ])

app⇉⋆ : ∀ {X} {s1 s2 t1 t2 : Λ X} → s1 ⇉⋆ s2 → t1 ⇉⋆ t2 → app s1 t1 ⇉⋆ app s2 t2
app⇉⋆ ε⋆ ε⋆ = ε⋆
app⇉⋆ ε⋆ (t0 ,⋆ t12) = app⇉ refl⇉ t0 ,⋆ app⇉⋆ ε⋆ t12
app⇉⋆ (s0 ,⋆ s12) ε⋆ = app⇉ s0 refl⇉ ,⋆ app⇉⋆ s12 ε⋆
app⇉⋆ (s0 ,⋆ s12) (t0 ,⋆ t12) = app⇉ s0 t0 ,⋆ app⇉⋆ s12 t12

_⇉⋆[_] : ∀ {X Y : Set} {s t : Λ X} → s ⇉⋆ t → ∀ (σ : X → Λ Y) → s [ σ ] ⇉⋆ t [ σ ]
ε⋆         ⇉⋆[ σ ] = ε⋆
(st ,⋆ tu) ⇉⋆[ σ ] = (st ⇉[ σ ]) ,⋆ (tu ⇉⋆[ σ ])

⟶s\⇉⋆ : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⇉⋆ t2 → Σ[ u ∈ Λ X ] (t1 ⇉⋆ u × t2 ⟶s u)
⟶s\⇉⋆ st1 ε⋆ = _ ,, ε⋆ , st1
⟶s\⇉⋆ st1 (pr0 ,⋆ pr1) with ⟶s\⇉ st1 pr0
... | (u ,, pr2 , st2) with ⟶s\⇉⋆ st2 pr1
... | (v ,, pr3 , st3) = v ,, (pr2 ,⋆ pr3) , st3

{-# TERMINATING #-}
⇉⊆⟶β⋆ : ∀ {X} {s t : Λ X} → s ⇉ t  →  s ⟶β⋆ t
⇉⊆⟶β⋆ (red⇉ {s1} {s2} {t1} {t2} s12 t12 e) =
  (red⟶β (redex refl ) ) ,⋆ ⇉⊆⟶β⋆ (transp (_⇉_ (s1 [ t1 ]ₒ)) e p )
    where p = ⇉[⇉] (io var t1) (io var t2) (io𝓟 _ (λ _ → var⇉) t12 ) s12
⇉⊆⟶β⋆ var⇉ = ε⋆
⇉⊆⟶β⋆ (app⇉ s12 t12) = (appL⟶β⋆ (⇉⊆⟶β⋆ s12) _ ) ⋆!⋆ appR⟶β⋆ (⇉⊆⟶β⋆ t12 ) _
⇉⊆⟶β⋆ (abs⇉ st) = abs⟶β⋆ (⇉⊆⟶β⋆ st)

⇉⋆⊆⟶β⋆ : ∀ {X} {s t : Λ X} → s ⇉⋆ t  →  s ⟶β⋆ t
⇉⋆⊆⟶β⋆ ε⋆ = ε⋆
⇉⋆⊆⟶β⋆ (st ,⋆ tu) = ⇉⊆⟶β⋆ st ⋆!⋆ ⇉⋆⊆⟶β⋆ tu


