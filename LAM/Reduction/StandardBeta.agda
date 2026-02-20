open import Logic
open import Lifting 
open import LAM.Lambda
open import LAM.Reduction.Beta
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

module LAM.Reduction.StandardBeta where 

-- Standard reduction is the least congruence closed under
-- weak head expansion
-- AKA "outside-in" reduction strategy
data _⟶s_ {X} : Λ X → Λ X → Set where
  red⟶s : ∀ {r s t}       → r ⟶w s   →  s ⟶s t   →  r ⟶s t
  var⟶s : ∀ {x}           → var x ⟶s var x
  app⟶s : ∀ {s1 s2 t1 t2} → s1 ⟶s s2 → t1 ⟶s t2 → app s1 t1 ⟶s app s2 t2
  abs⟶s : ∀ {r1 r2}       → r1 ⟶s r2 → abs r1 ⟶s abs r2

_≡!⟶s_ : ∀ {X} {r s t : Λ X} → (r ≡ s) → (s ⟶s t) → (r ⟶s t)
refl ≡!⟶s st = st

map⟶s : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶s t2 → Λ→ f t1 ⟶s Λ→ f t2
map⟶s f (red⟶s W t12) = red⟶s (map⟶w f W ) (map⟶s f t12)
map⟶s f var⟶s = var⟶s
map⟶s f (app⟶s t12 t13) = app⟶s (map⟶s f t12) (map⟶s f t13)
map⟶s f (abs⟶s t12) = abs⟶s (map⟶s (↑→ f) t12)

lift⟶s : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⟶s g x) → (∀ y → lift f y ⟶s lift g y)
lift⟶s f g f→g (i x) = map⟶s i (f→g x)
lift⟶s f g f→g o = var⟶s

bind⟶ₒ : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶ₒ t) → (s [ f ]) ⟶ₒ (t [ f ])
bind⟶ₒ f (redex {_} {s} {t} refl) = redex ((bind-assoc s ~! (e ! bind-assoc s))) where
  e1 = λ { (i x) → bind-lift2 (t [ f ]) (f x) ; o → refl }
  e = bind≅ e1 s

bind⟶w : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶w t) → (s [ f ]) ⟶w (t [ f ])
bind⟶w f (red⟶w rd) = red⟶w (bind⟶ₒ f rd)
bind⟶w f (appL⟶w st) = appL⟶w (bind⟶w f st)

bind⟶s : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⟶s g x) → (∀ t → (t [ f ]) ⟶s (t [ g ]))
bind⟶s f g f→g (var x) = f→g x
bind⟶s f g f→g (app s t) = app⟶s (bind⟶s f g f→g s) (bind⟶s f g f→g t)
bind⟶s f g f→g (abs t) = abs⟶s (bind⟶s (lift f) (lift g) (lift⟶s f g f→g) t )

⟶ₒ[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶ₒ t →   (s [ f ])  ⟶s  (t [ g ])
⟶ₒ[⟶s] f g f→g (redex {s = s} {t} refl) = red⟶s (red⟶w (redex refl) ) (E ≡!⟶s R) where
  E1 = bind-assoc≅ {f = lift f} {io var (t [ f ])} {io f (t [ f ])}
                   (io𝓟 _ (λ x → ~ (bind-lift2 (t [ f ]) (f x) ) ) refl ) s
  E2 = bind-assoc≅ (io𝓟 _ (λ x → refl) refl) s
  E = E1 ~! E2 -- E1 ! E2
  R = bind⟶s f g f→g (s [ io var t ])

⟶w[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶w t →   (s [ f ])  ⟶s  (t [ g ])
⟶w[⟶s] f g f→g (red⟶w Δ) = ⟶ₒ[⟶s] f g f→g Δ
⟶w[⟶s] f g f→g (appL⟶w {r = r} s→t) = app⟶s (⟶w[⟶s] f g f→g s→t ) (bind⟶s f g f→g r )

⟶s[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶s t →   (s [ f ])  ⟶s  (t [ g ])
⟶s[⟶s] f g f→g (red⟶s s→t t→u) = red⟶s (bind⟶w f s→t ) (⟶s[⟶s] f g f→g  t→u)
⟶s[⟶s] f g f→g var⟶s = f→g _
⟶s[⟶s] f g f→g (app⟶s R1 R2) = app⟶s (⟶s[⟶s] f g f→g R1) (⟶s[⟶s] f g f→g R2)
⟶s[⟶s] f g f→g (abs⟶s R0) = abs⟶s (⟶s[⟶s] (lift f) (lift g) (lift⟶s f g f→g) R0 )

⟶s[⟶s]ₒ : ∀ {X} → {s1 s2 : Λ (↑ X)} → {t1 t2 : Λ X} → s1 ⟶s s2 → t1 ⟶s t2 → (s1 [ t1 ]ₒ) ⟶s (s2 [ t2 ]ₒ)
⟶s[⟶s]ₒ {X} {s1} {s2} {t1} {t2} s12 t12 =
  ⟶s[⟶s] (io var t1) (io var t2) (io𝓟 _ (λ x → var⟶s) t12) s12

⟶s!⟶ₒ : ∀ {X} {t1 t2 t3 : Λ X} → (t1 ⟶s t2) → (t2 ⟶ₒ t3) → (t1 ⟶s t3)
⟶s!⟶ₒ (red⟶s W t12) r@(redex refl) = red⟶s W (⟶s!⟶ₒ t12 r)
⟶s!⟶ₒ (app⟶s {s1 = s1} {s2} {t1} {t2} s1s2 t1t2) r@(redex {s = s} refl) = wredLemma s1 s1s2 where
  wredLemma : ∀ u → (u ⟶s abs s) → app u t1 ⟶s (s [ t2 ]ₒ)
  wredLemma u (red⟶s {s = v} u→v u→λs) = red⟶s (appL⟶w u→v ) (wredLemma v u→λs )
  wredLemma (abs w) (abs⟶s u→λs) = red⟶s (red⟶w (redex refl) ) R
    where R = ⟶s[⟶s] (io var _) (io var _) (io𝓟 _ (λ x → var⟶s) t1t2 ) u→λs

⟶s!⟶w : ∀ {X} {t1 t2 t3 : Λ X} → (t1 ⟶s t2) → (t2 ⟶w t3) → (t1 ⟶s t3)
⟶s!⟶w (red⟶s W t12) (red⟶w (redex {r0} {r1} {r2} re)) rewrite ~ re =
        red⟶s W (⟶s!⟶w t12 (red⟶w (redex refl)) )
⟶s!⟶w (app⟶s {s1} {s2} {t1} {t2} s1r1 t12) (red⟶w (redex {r0} {r1} {t2} re)) rewrite ~ re = sr _ s1r1
  where sr : ∀ u → u ⟶s abs r1 → app u t1 ⟶s (r1 [ t2 ]ₒ)
        sr u (red⟶s u→s u→λr1) = red⟶s (appL⟶w u→s ) (sr _ u→λr1)
        sr (abs w) (abs⟶s u→λr1) = red⟶s (red⟶w (redex refl))
          (⟶s[⟶s] (io var t1 ) (io var t2)  (io𝓟 _ (λ x → var⟶s) t12 ) u→λr1)
⟶s!⟶w (red⟶s W t12) (appL⟶w t23) = red⟶s W (⟶s!⟶w t12 (appL⟶w t23))
⟶s!⟶w (app⟶s t12 t13) (appL⟶w t23) = app⟶s (⟶s!⟶w t12 t23) t13

⟶s!⟶s : ∀ {X} {r s t : Λ X} → (r ⟶s s) → (s ⟶s t) → (r ⟶s t)
⟶s!⟶s rs               (red⟶s W st)    = ⟶s!⟶s (⟶s!⟶w rs W ) st
⟶s!⟶s (red⟶s W rs)    st               = red⟶s W (⟶s!⟶s rs st)
⟶s!⟶s rs               var⟶s           = rs
⟶s!⟶s (app⟶s rs1 rs2) (app⟶s st1 st2) = app⟶s (⟶s!⟶s rs1 st1) (⟶s!⟶s rs2 st2)
⟶s!⟶s (abs⟶s rs)      (abs⟶s st)      = abs⟶s (⟶s!⟶s rs st)

⟶w!red : ∀ {X} {s t1 t2 : Λ X} {r} (sr : s ⟶s abs r) (t12 : t1 ⟶s t2)
          → app s t1 ⟶s (r [ t2 ]ₒ)
⟶w!red (red⟶s W sr) t12 = red⟶s (appL⟶w W ) (⟶w!red sr t12 )
⟶w!red {t1 = t1} {t2} (abs⟶s sr) t12 = red⟶s (red⟶w (redex refl ) ) (⟶s[⟶s] (io var t1) (io var t2) f=g sr )
  where f=g = λ {  (i x) → var⟶s ; o → t12 }

⟶s!⟶β : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β t → r ⟶s t
⟶s!⟶β (red⟶s r0 rs) st = red⟶s r0 (⟶s!⟶β rs st)
⟶s!⟶β var⟶s (red⟶β ())
⟶s!⟶β (abs⟶s rs) (abs⟶β st) = abs⟶s (⟶s!⟶β rs st)
⟶s!⟶β (app⟶s (red⟶s W rs) t12) br@(red⟶β (redex s[t2]=t)) rewrite ~ s[t2]=t
  = ⟶w!red (red⟶s W rs ) t12
⟶s!⟶β (app⟶s (abs⟶s rs) t12) (red⟶β (redex s[t2]=t)) rewrite ~ s[t2]=t
  = red⟶s (red⟶w (redex refl ) ) (⟶s[⟶s] _ _ e rs )
    where e = io𝓟 _ (λ x → var⟶s) t12
⟶s!⟶β (app⟶s s12 t12) (appL⟶β st) = app⟶s (⟶s!⟶β s12 st) t12
⟶s!⟶β (app⟶s s12 t12) (appR⟶β st) = app⟶s s12 (⟶s!⟶β t12 st)

⟶s!⟶β⋆ : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β⋆ t → r ⟶s t
⟶s!⟶β⋆ rs ε⋆ = rs
⟶s!⟶β⋆ rs (sy ,⋆ yt) = ⟶s!⟶β⋆ (⟶s!⟶β rs sy) yt

refl⟶s : ∀ {X} {t : Λ X} → t ⟶s t
refl⟶s {X} {var x} = var⟶s
refl⟶s {X} {app t t₁} = app⟶s refl⟶s refl⟶s
refl⟶s {X} {abs t} = abs⟶s refl⟶s

-- Standardization theorem for beta reduction
⟶β⋆⊆⟶s : ∀ {X} {s t : Λ X} →  s ⟶β⋆ t → s ⟶s t
⟶β⋆⊆⟶s = ⟶s!⟶β⋆ refl⟶s

⟶β⋆!⟶s⊆⟶s : ∀ {X} {r s t : Λ X} → r ⟶β⋆ s → s ⟶s t → r ⟶s t
⟶β⋆!⟶s⊆⟶s = ⟶s!⟶s ∘ ⟶β⋆⊆⟶s

⟶s⊆⟶β⋆ : ∀ {X} → _⟶s_ {X} ⊆ _⟶β⋆_ {X}
⟶s⊆⟶β⋆ s t (red⟶s W st) = ⟶w⊆⟶β W ,⋆ ⟶s⊆⟶β⋆ _ _ st
⟶s⊆⟶β⋆ (var _) (var _) var⟶s = ε⋆
⟶s⊆⟶β⋆ (abs r1) (abs r2) (abs⟶s r12) = abs⟶β⋆ (⟶s⊆⟶β⋆ _ _ r12)
⟶s⊆⟶β⋆ (app s1 s2) (app t1 t2) (app⟶s s12 t12) =
  appL⟶β⋆ (⟶s⊆⟶β⋆ _ _ s12) s2 ⋆!⋆ appR⟶β⋆ (⟶s⊆⟶β⋆ _ _ t12) t1


