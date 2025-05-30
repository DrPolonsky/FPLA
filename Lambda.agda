-- {-# OPTIONS --allow-unsolved-metas #-}
module Lambda where

open import Logic
open import Lifting
open import Datatypes

-- Lambda terms as a type constructor
-- For a set X, Λ X = terms whose free variables come from the set X
-- Λ is \GL
data Λ (V : Set) : Set where
  var : V → Λ V
  app : Λ V → Λ V → Λ V
  abs : Λ (↑ V) → Λ V

-- Terms over a finite set of variables, Λᶠ n = Λ {x1, ..., xn}
-- ᶠ is \^f
Λᶠ : ℕ → Set
Λᶠ n = Λ (Fin n)

-- The set of closed terms, whose set of free variables is empty
-- ⁰ is \^0
Λ⁰ : Set
Λ⁰ = Λᶠ 0 -- Λ ⊥

-- Functorial action on morphisms
Λ→ : ∀ {A B : Set} (f : A → B) → Λ A → Λ B
Λ→ f (var x)   = var (f x)
Λ→ f (app s t) = app (Λ→ f s) (Λ→ f t)
Λ→ f (abs r)   = abs (Λ→ (↑→ f) r)

-- A very common special case
Λ→i : ∀ {A : Set} → Λ A → Λ (↑ A)
Λ→i = Λ→ i

-- Preservation of pointwise equality
Λ→≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → Λ→ f ≅ Λ→ g
Λ→≅ fg (var x)   = cong  var (fg x)
Λ→≅ fg (app s t) = cong2 app (Λ→≅ fg s) (Λ→≅ fg t)
Λ→≅ fg (abs r)   = cong  abs (Λ→≅ (↑→≅ fg) r)

-- Preservation of identity
Λ→≅I : ∀ {A} {f : A → A} → f ≅ I → Λ→ f ≅ I
Λ→≅I f≅I (var x)   = cong  var (f≅I x)
Λ→≅I f≅I (app s t) = cong2 app (Λ→≅I f≅I s) (Λ→≅I f≅I t)
Λ→≅I f≅I (abs r)   = cong  abs (Λ→≅I (↑→≅I f≅I) r)

-- Preservation of composition
Λ→∘ : ∀ {A B C} (f : A → B) (g : B → C) → Λ→ (g ∘ f) ≅ Λ→ g ∘ Λ→ f
Λ→∘ f g (var x)   = refl
Λ→∘ f g (app s t) = cong2 app (Λ→∘ f g s) (Λ→∘ f g t)
Λ→∘ f g (abs r)   = cong  abs (Λ→≅ (↑→∘ f g) r ! Λ→∘ (↑→ f) (↑→ g) r)

-- Preservation of composition modulo pointwise equality
-- The Original Version
-- (This lemma looks more complicated, but its proof is simpler than the above)
Λ→≅∘ : ∀ {A B C} (f : A → B) (g : B → C) {h} → h ≅ g ∘ f → Λ→ h ≅ Λ→ g ∘ Λ→ f
-- Λ→≅∘ f g h≅g∘f = Λ→≅ h≅g∘f ≅!≅ Λ→∘ f g
Λ→≅∘ f g h≅g∘f (var x)   = cong  var (h≅g∘f x)
Λ→≅∘ f g h≅g∘f (app s t) = cong2 app (Λ→≅∘ f g h≅g∘f s) (Λ→≅∘ f g h≅g∘f t)
Λ→≅∘ f g h≅g∘f (abs r)   = cong  abs (Λ→≅∘ (↑→ f) (↑→ g) (↑→≅∘ f g h≅g∘f) r )

-- Preservation of composition modulo pointwise equality
-- Symmetric version
Λ→∘≅ : ∀ {A B C} (f : A → B) (g : B → C) {h} → g ∘ f ≅ h → Λ→ g ∘ Λ→ f ≅ Λ→ h
-- Λ→∘≅ f g gf≅h = Λ→∘ f g ~!≅ Λ→≅ gf≅h
Λ→∘≅ f g gf≅h (var x)     = cong  var (gf≅h x)
Λ→∘≅ f g gf≅h (app t1 t2) = cong2 app (Λ→∘≅ f g gf≅h t1) (Λ→∘≅ f g gf≅h t2)
Λ→∘≅ f g gf≅h (abs t0)    = cong  abs (Λ→∘≅ (↑→ f) (↑→ g) (↑→∘≅ f g gf≅h) t0)

-- Lifting a function over the type of terms
lift : ∀ {A B : Set} → (A → Λ B) → ↑ A → Λ (↑ B)
lift f = io (Λ→i ∘ f) (var o)

-- Lifting preserves pointwise equality
lift≅ : ∀ {A B : Set} {f g : A → Λ B} → f ≅ g → lift f ≅ lift g
lift≅ f≅g (i x) = cong Λ→i (f≅g x)
lift≅ f≅g o     = refl
-- lift≅ f≅g = io𝓟 _ (λ x → cong Λ→i (f≅g x)) refl

lift≅∘ : ∀ {A B C} {f : A → B} {g : B → Λ C} {h} → h ≅ g ∘ f → lift h ≅ lift g ∘ ↑→ f
lift≅∘ h≅gf (i x) = cong Λ→i (h≅gf x)
lift≅∘ h≅gf o = refl

lift-nat : ∀ {A B C} {f : A → B} {g : B → Λ C} {h} → h ≅ g ∘ f → lift h ≅ lift g ∘ ↑→ f
lift-nat h≅gf (i x) = cong Λ→i (h≅gf x)
lift-nat h≅gf o = refl

lift+nat : ∀ {A B C} {f : A → Λ B} {g : B → C} {h} → h ≅ Λ→ g ∘ f → lift h ≅ Λ→ (↑→ g) ∘ lift f
lift+nat {f = f} {g} h≅Λg∘f (i x) = cong Λ→i (h≅Λg∘f x) ! ~ (Λ→∘ g i (f x) ) ! Λ→≅∘ i (↑→ g) (i-nat g) (f x) -- -- Λ→≅∘ i (↑→ g) !≅! (f x)
lift+nat h≅Λg∘f o = refl

-- lift≅∘ : ∀ {A B C} {f : A → B} {g : B → Λ C} {h} → h ≅ g ∘ f → lift h ≅ lift g ∘ ↑→ f

-- Distribution law for syntax over lifting
Λ↑ : ∀ {A : Set} → ↑ (Λ A) → Λ (↑ A)
Λ↑ = lift I

Λ↑-nat : ∀ {A B : Set} (f : A → B) → Λ↑ ∘ (↑→ (Λ→ f)) ≅ Λ→ (↑→ f) ∘ Λ↑
Λ↑-nat f = io𝓟 _ (Λ→∘≅ f i  (i-nat f) ≅!≅ Λ→≅∘ i (↑→ f) (i-nat f)) refl
-- Λ↑-nat f (i x) = Λ→∘≅ f i  (i-nat f) x ! Λ→≅∘ i (↑→ f) (i-nat f) x
-- Λ↑-nat f o = refl

-- Substitution is the monadic bind for Λ (Haskell's >>=)
_[_] : ∀ {A B : Set} → Λ A → (A → Λ B) → Λ B
var x   [ f ] = f x
app s t [ f ] = app (s [ f ]) (t [ f ])
abs r   [ f ] = abs (r [ lift f ])

-- A special case of the above for finitely many variables
_[_]ᶠ : ∀ {m n : ℕ} → Λᶠ m → (Fin m → Λᶠ n) → Λᶠ n
_[_]ᶠ = _[_]

_[_]ₒ : ∀ {X : Set} → Λ (↑ X) → Λ X → Λ X
M [ N ]ₒ  = M [ io var N ]

bind : ∀ {A B : Set} → (A → Λ B) → Λ A → Λ B
bind f t = t [ f ]

bind≅ : ∀ {A B : Set} {f g : A → Λ B} → f ≅ g → bind f ≅ bind g
bind≅ f≅g (var x)     = f≅g x
bind≅ f≅g (app t1 t2) = cong2 app (bind≅ f≅g t1 ) (bind≅ f≅g t2)
bind≅ f≅g (abs t0)    = cong abs (bind≅ (lift≅ f≅g) t0)

bind-nat₁ : ∀ {X Y Z : Set} {f : X → Y} {g : Y → Λ Z} {h}
              → h ≅ g ∘ f → bind h ≅ bind g ∘ Λ→ f
bind-nat₁ h≅gf (var x)     = h≅gf x
bind-nat₁ h≅gf (app t1 t2) = cong2 app (bind-nat₁ h≅gf t1) (bind-nat₁ h≅gf t2)
bind-nat₁ h≅gf (abs t0)    = cong abs (bind-nat₁ (lift≅∘ h≅gf) t0 )

bind-nat₂ : ∀ {X Y Z : Set} {f : X → Λ Y} {g : Y → Z} {h}
              → h ≅ Λ→ g ∘ f → bind h ≅ Λ→ g ∘ bind f
bind-nat₂ h≅Λg∘f (var x) = h≅Λg∘f x
bind-nat₂ h≅Λg∘f (app t1 t2) = cong2 app (bind-nat₂ h≅Λg∘f t1) (bind-nat₂ h≅Λg∘f t2)
bind-nat₂ h≅Λg∘f (abs t0) = cong abs (bind-nat₂ (lift+nat h≅Λg∘f) t0)

-- bind-nat : ∀ {X X' Y Y' : Set} (f : X → X') (g : X → Λ Y) (h : Y → Y') → Λ→ f ∘ bind f ≅ bind (lift g) ∘ Λ→ i

bind-nat≅ : ∀ {X1 X2 Y1 Y2 : Set} (f : X1 → X2) (g : X2 → Λ Y1) (h : Y1 → Y2)
              → Λ→ h ∘ bind (g ∘ f) ≅ bind (Λ→ h ∘ g) ∘ Λ→ f
bind-nat≅ f g h = bind-nat₂ !≅! ~!≅ bind-nat₁ !≅!
-- bind-nat≅ f g h (var x) = refl
-- bind-nat≅ f g h (app t1 t2) = cong2 app (bind-nat≅ f g h t1) (bind-nat≅ f g h t2)
-- bind-nat≅ f g h (abs t0) = cong abs ( cong (Λ→ (↑→ h)) (bind≅ (lift≅∘ λ x → refl ) t0)
--                                     ! (bind-nat≅ (↑→ f) (lift g) (↑→ h) t0
--                                     ! bind≅ (~≅ lift+nat !≅! ) (Λ→ (↑→ f) t0) ))

bind-lift : ∀ {X Y : Set} (g : X → Λ Y) → Λ→ i ∘ bind g ≅ bind (lift g) ∘ Λ→ i
bind-lift g = bind-nat₂ !≅! ~!≅ bind-nat₁ !≅!

bind-assoc≅ : ∀ {A B C : Set} {f : A → Λ B} {g : B → Λ C} {h : A → Λ C}
               → h ≅ bind g ∘ f → bind h ≅ bind g ∘ bind f
bind-assoc≅ bg∘f≅h (var x)     = bg∘f≅h x
bind-assoc≅ bg∘f≅h (app t1 t2) = cong2 app (bind-assoc≅ bg∘f≅h t1) (bind-assoc≅ bg∘f≅h t2)
bind-assoc≅ {f = f} {g} {h} bg∘f≅h (abs t0)    = cong abs (bind-assoc≅ eq t0) where
  eq = lift≅∘ {f = f} {g = bind g}  bg∘f≅h ≅!≅ λ {  (i x) → bind-lift g (f x) ; o → refl }

bind-assoc : ∀ {A B C : Set} {f : A → Λ B} {g : B → Λ C}
               → bind (bind g ∘ f) ≅ bind g ∘ bind f
bind-assoc {f = f} {g} = bind-assoc≅ refl≅

liftvar≅var : ∀ {A : Set} → lift {A} var ≅ var
liftvar≅var (i x) = refl
liftvar≅var o = refl

bind-unit0 : ∀ {A : Set} → bind {A} var ≅ I
bind-unit0 (var x) = refl
bind-unit0 (app s t) = cong2 app (bind-unit0 s) (bind-unit0 t)
bind-unit0 (abs r) = cong abs (bind≅ liftvar≅var r ! bind-unit0 r)

bind-unit1 : ∀ {A B : Set} {f : A → Λ B} → bind var ∘ f ≅ f
bind-unit1 _ = bind-unit0 _

bind-unit2 : ∀ {A B : Set} {f : A → Λ B} → bind f ∘ var ≅ f
bind-unit2 = !≅!

bind-lift2 : ∀ {A : Set} (N : Λ A) → bind (io var N) ∘ Λ→i ≅ I
bind-lift2 N = bind-nat₁ {f = i} {io var N} {var} !≅! ~!≅ bind-unit0

subst-lemma : ∀ {A B : Set} (t : Λ (↑ A)) (N : Λ A) (f : A → Λ B)
                → (t [ N ]ₒ) [ f ] ≡ (t [ lift f ]) [ N [ f ] ]ₒ
subst-lemma t N f = (bind-assoc  {f = io var N} {g = f} t ) ~! bind-assoc≅ e t
  where e = io𝓟 _ (λ x → ~ (bind-lift2 (N [ f ]) (f x) ) ) refl

bind-map : ∀ {A B : Set} (s : Λ (↑ A)) (t : Λ A) (f : A → B)
           → Λ→ f (s [ t ]ₒ) ≡ (Λ→ (↑→ f) s [ Λ→ f t ]ₒ)
bind-map s t f = bind-nat₂ {f = io var t} {f} !≅! s
              ~! bind-nat₁ (io𝓟 _ (λ x → refl) refl ) s
-- bind-map : ∀ {X Y Z : Set} (f : X → Y) (g : Y → Λ Z)
--               → bind (Λ→ f ∘ g) ∘ Λ→ (↑→ f) ≅ Λ→ f ∘ bind g ?????
-- bind-nat₁ : ∀ {X Y Z : Set} {f : X → Y} {g : Y → Λ Z} {h}
--               → h ≅ g ∘ f → bind h ≅ bind g ∘ Λ→ f
-- bind-nat₂ : ∀ {X Y Z : Set} {f : X → Λ Y} {g : Y → Z} {h}
--               → h ≅ Λ→ g ∘ f → bind h ≅ Λ→ g ∘ bind f

-- The End
