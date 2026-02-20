-- {-# OPTIONS --allow-unsolved-metas #-}
module LAM.Reduction.Beta where

open import Logic
open import Lifting
open import LAM.Lambda
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

𝓡Λ : Set₁
𝓡Λ = ∀ {X} → Λ X → Λ X → Set

-- The axiom of beta reduction
-- s ⟶ₒ t  if t results from s by contracting a beta redex
--             AT THE ROOT of the syntax tree
-- ⟶ₒ is \-->\_o
data _⟶ₒ_ {X : Set} : Λ X → Λ X → Set where
  redex : ∀ {r s t}  →  (e : s [ t ]ₒ ≡ r)  →  app (abs s) t ⟶ₒ r



-- One-step beta reduction is the contextual closure of ⟶ₒ
data _⟶β_ {X : Set} : Λ X → Λ X → Set where
  red⟶β  : ∀ {s t}     →  s ⟶ₒ t       →  s ⟶β t
  appL⟶β : ∀ {s1 s2 t} → s1 ⟶β s2      → app s1 t ⟶β app s2 t
  appR⟶β : ∀ {s t1 t2} → t1 ⟶β t2      → app s t1 ⟶β app s t2
  abs⟶β  : ∀ {r1 r2}   → r1 ⟶β r2      → abs r1   ⟶β abs r2

-- Weak head reduction is weaker than one-step reduction
data _⟶w_ {X} : Λ X → Λ X → Set where
  red⟶w : ∀ {s t}     →  s ⟶ₒ t  →  s ⟶w t
  appL⟶w : ∀ {s t r}  →  s ⟶w t  →  app s r ⟶w app t r

map⟶ₒ : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶ₒ t2 → Λ→ f t1 ⟶ₒ Λ→ f t2
map⟶ₒ f (redex {_} {r} {t} refl) = redex (e1 ~! e2) where
  e0 = λ {  (i x) → refl ; o → refl }
  e1 = bind-nat₁ {f = ↑→ f} {io var (Λ→ f t)} e0 r
  e2 = bind-nat₂ {f = io var t} {f} !≅! r

map⟶β : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶β t2 → Λ→ f t1 ⟶β Λ→ f t2
map⟶β f (red⟶β x) = red⟶β (map⟶ₒ f x )
map⟶β f (appL⟶β t12) = appL⟶β (map⟶β f t12)
map⟶β f (appR⟶β t12) = appR⟶β (map⟶β f t12)
map⟶β f (abs⟶β t12) = abs⟶β (map⟶β (↑→ f) t12)

map⟶w : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶w t2 → Λ→ f t1 ⟶w Λ→ f t2
map⟶w f {t1} {t2} (red⟶w Δ) = red⟶w (map⟶ₒ f Δ)
map⟶w f (appL⟶w t12) = appL⟶w (map⟶w f t12)

_⟶β[_] : ∀ {X Y : Set} {s t : Λ X} → s ⟶β t → ∀ (f : X → Λ Y) → (s [ f ]) ⟶β (t [ f ])
red⟶β {s = app (abs s) t} (redex refl) ⟶β[ f ] = red⟶β (redex (~ (subst-lemma s t f)) )
appL⟶β st ⟶β[ f ] = appL⟶β (st ⟶β[ f ])
appR⟶β st ⟶β[ f ] = appR⟶β (st ⟶β[ f ])
abs⟶β st ⟶β[ f ] = abs⟶β (st ⟶β[ lift f ])

-- Multistep reduction is the reflexive-transitive closure of one-step reduction
_⟶β⋆_ : ∀ {X} → Λ X → Λ X → Set
_⟶β⋆_ = (_⟶β_) ⋆


-- Relations between reduction relations
⟶w⊆⟶β : ∀ {X} {s t : Λ X} → s ⟶w t  →  s ⟶β t
⟶w⊆⟶β (red⟶w st) = red⟶β st
⟶w⊆⟶β (appL⟶w  s12) = appL⟶β (⟶w⊆⟶β s12)


-- NF : ∀ {X} → 𝓟 (Λ X)
-- NF M = ∀ N → ¬ (M ⟶β N)

abs⟶β⋆ : ∀ {X} {r1 r2 : Λ (↑ X)} → r1 ⟶β⋆ r2 → abs r1 ⟶β⋆ abs r2
abs⟶β⋆ ε⋆ = ε⋆
abs⟶β⋆ (r0 ,⋆ r12) = abs⟶β r0 ,⋆ abs⟶β⋆ r12

appL⟶β⋆ : ∀ {X} {s1 s2 : Λ X} → s1 ⟶β⋆ s2 → ∀ t → app s1 t ⟶β⋆ app s2 t
appL⟶β⋆ ε⋆ t = ε⋆
appL⟶β⋆ (s0 ,⋆ s12) t = appL⟶β s0 ,⋆ appL⟶β⋆ s12 t

appR⟶β⋆ : ∀ {X} {s1 s2 : Λ X} → s1 ⟶β⋆ s2 → ∀ t → app t s1 ⟶β⋆ app t s2
appR⟶β⋆ ε⋆ t = ε⋆
appR⟶β⋆ (s0 ,⋆ s12) t = appR⟶β s0 ,⋆ appR⟶β⋆ s12 t

NF : ∀ {X} → 𝓟 (Λ X)
NF M = ∀ N → ¬ (M ⟶β N)

absInv : ∀ {V} {N1 N2 : Λ (↑ V)} → abs N1 ≡ abs N2 → N1 ≡ N2
absInv refl = refl
appInvL : ∀ {V} {M1 M2 N1 N2 : Λ V} → app M1 M2 ≡ app N1 N2 → M1 ≡ N1
appInvL refl = refl
appInvR : ∀ {V} {M1 M2 N1 N2 : Λ V} → app M1 M2 ≡ app N1 N2 → M2 ≡ N2
appInvR refl = refl

absNFinv : ∀ {V} {s : Λ (↑ V)} → abs s ∈ NF → s ∈ NF
absNFinv s∈NF t s→t = s∈NF (abs t) (abs⟶β s→t )
appNFinvL : ∀ {V} {s t : Λ V} → app s t ∈ NF → s ∈ NF
appNFinvL {t = t} st∈NF u s→u = st∈NF (app u t) (appL⟶β s→u )
appNFinvR : ∀ {V} {s t : Λ V} → app s t ∈ NF → t ∈ NF
appNFinvR {s = s} st∈NF u t→u = st∈NF (app s u) (appR⟶β t→u )


{-

bindCong : ∀ (R : (∀ {X} → 𝓡Λ X)) → isCong R
             → ∀ {X Y : Set} → (f g : X → Λ Y) → (∀ x → R (f x) (g x))
             → ∀ t → R (bind f t) (bind g t)
bindCong R Rcong f g fRg (var x) = fRg x
bindCong R Rcong f g fRg (app s t) = Rcong _ _ (appCC (axCC (bindCong R Rcong f g fRg s))
                                                      (axCC (bindCong R Rcong f g fRg t)))
bindCong R Rcong f g fRg (abs r) = Rcong (abs (r [ io (λ z → Λ→ i (f z)) (var o) ])) (abs (r [ io (λ z → Λ→ i (g z)) (var o) ]))
                                    (absCC (axCC (bindCong R Rcong (lift f) (lift g) lfg r ) ) )
                                    where lfg = io𝓟 _ {!   !} (Rcong (var o) (var o) varCC)

reflCC : ∀ (R : ∀ {X} → 𝓡 (Λ X)) {X : Set} → ∀ (t : Λ X) → CC R t t
reflCC R (var x) = varCC
reflCC R (app t1 t2) = appCC (reflCC R t1) (reflCC R t2)
reflCC R (abs t0) = absCC (reflCC R t0 )


-- Relations between reduction relations
⟶w⊆⟶β : ∀ {X} → _⟶w_ {X} ⊆ _⟶β_
⟶w⊆⟶β s t (red⟶w st) = ax𝓡Λ st
⟶w⊆⟶β (app s t) (app  s' .t) (appL⟶w s→ws') = appL𝓡Λ (⟶w⊆⟶β s s' s→ws')

⟶s⊆⟶β⋆ : ∀ {X} → _⟶s_ {X} ⊆ _⟶β⋆_
⟶s⊆⟶β⋆ s t (red⟶s ss' s't) = ⟶w⊆⟶β s _ ss' ,⋆ ⟶s⊆⟶β⋆ _ t s't
⟶s⊆⟶β⋆ s t (CC⟶s st) = {!   !}

⟶β!⟶s : ∀ {X} {r s t : Λ X} → r ⟶β s → s ⟶s t → r ⟶s t
⟶β!⟶s (ax𝓡Λ rs) st = red⟶s (red⟶w rs ) st
⟶β!⟶s (appL𝓡Λ rs) st = {!   !}
⟶β!⟶s (appR𝓡Λ rs) st = {!   !}
⟶β!⟶s (abs𝓡Λ rs) = {!   !}

⟶s!⟶β : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β t → r ⟶s t
⟶s!⟶β (red⟶s rr' r's) st = red⟶s rr' (⟶s!⟶β r's st)
⟶s!⟶β (CC⟶s (axCC rs)) st = ⟶s!⟶β rs st
⟶s!⟶β (CC⟶s varCC) (ax𝓡Λ st) = red⟶s (red⟶w st ) {!   !}
⟶s!⟶β (CC⟶s (appCC rs rs₁)) st = {!   !}
⟶s!⟶β (CC⟶s (absCC rs)) (abs𝓡Λ st) = CC⟶s (absCC (axCC (⟶s!⟶β {! rs  !} {!   !} ) ) )

⟶s!⟶s : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶s t → r ⟶s t
⟶s!⟶s (red⟶s rr' r's) st = red⟶s rr' (⟶s!⟶s r's st)
⟶s!⟶s (CC⟶s x) st = {!   !}

-- Examples

-- The identity combinator
IC : ∀ {X} → Λ X
IC = abs (var o )

-- One-step beta reduction (contraction at the root)
II→I : ∀ {X} → app (IC {X}) IC ⟶β IC
II→I = ax𝓡Λ (red refl)
-- II→I = redexβ refl

-- Two-step beta reduction
I[II]→⋆I : ∀ {X} → (_⟶β_ ⋆) (app (IC {X}) (app IC IC)) IC
I[II]→⋆I = ax𝓡Λ (red refl) ,⋆ ax⋆ (ax𝓡Λ (red refl))
-- I[II]→⋆I = (redexβ refl ) ,⋆ (II→I ,⋆ ε⋆ )
-- I[II]→⋆I = (appRβ II→I ) ,⋆ (II→I ,⋆ ε⋆ )

-- Parallel reduction (contracting one redex only)
II⇉I : ∀ {X} → app IC IC ⇉ IC {X}
II⇉I {X} = red⇉ (CC⇉ varCC) (CC⇉ (absCC varCC)) refl
-- II⇉I {X} = red⇉ {X} {var o} {var o} {IC} {IC} {IC} (CC⇉ varCC )
--                 (CC⇉ (reflCC _⇉_ (abs (var o)) ) )
--                 refl

-- Parallel reduction (contracting multiple redexes)
src : Λ ⊥ -- (λx.x(II)(Ix))(II)
src = app (abs (app (app (var o) (app IC IC)) (app IC (var o)) ) ) (app IC IC)
tgt : Λ ⊥ -- (II)I
tgt = app (app IC IC) IC
src⇉tgt : src ⇉ tgt
src⇉tgt = red⇉ {s2 = app (app (var o) IC) (var o)} {t2 = IC}
            (CC⇉ (appCC {s1 = app (var o) (app IC IC)} {s2 = app (var o) IC}
                        {t1 = app IC (var o)} {t2 = var o}
                        (appCC varCC (axCC II⇉I ) ) (axCC (red⇉ (CC⇉ varCC) (CC⇉ varCC) refl) ) ) )
          II⇉I refl






-- Fixed Point Theorem
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

FPT : ∀ {X} (F : Λ X) → Σ[ YF ∈ Λ X ] (YF ⟶β⋆ app F YF)
FPT F =
  let W = abs (app (Λ→ i F) (app (var o) (var o)))
      WW→FWW : app W W ⟶β⋆ app F (app W W)
      WW→FWW = ax𝓡Λ (red (cong2 app {!   !} refl) ) ,⋆ ε⋆
   in (app W W ,, WW→FWW )

-- The end
-}
