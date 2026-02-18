-- {-# OPTIONS --cubical-compatible #-}

module Lifting where

open import Logic

-- LIFTING MONAD
-- ↑ is \u
-- ↑ X = X + 1 (in types) = X ⊔ {*} (in sets) = Maybe X (in Haskell)
data ↑ (A : Set) : Set where
  i : A → ↑ A
  o : ↑ A

-- The generic eliminator for ↑
io : ∀ {A B : Set} → (A → B) → B → ↑ A → B
io f b (i x) = f x
io f b o = b

-- Dependent eliminator for predicates on ↑A
io𝓟 : ∀ {A} → ∀ (B : ↑ A → Set) → (∀ x → B (i x)) → B o → ∀ x → B x
io𝓟 B bi bo (i x) = bi x
io𝓟 B bi bo o     = bo

-- The lifting eliminator preserves pointwise equality
io≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → ∀ {b1 b2} → b1 ≡ b2 → io f b1 ≅ io g b2
io≅ fg b12 (i x) = fg x
io≅ fg b12 o = b12

-- The map function AKA functorial action
↑→ : ∀ {A B : Set} → (A → B) → ↑ A → ↑ B
↑→ f (i x) = i (f x)
↑→ f o = o

-- Preservation of identity
↑→≅I : ∀ {A} {f : A → A} → f ≅ I → ↑→ f ≅ I
↑→≅I f≅I (i x) = cong i (f≅I x)
↑→≅I f≅I o     = refl

-- Presevation of pointwise equality
↑→≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → ↑→ f ≅ ↑→ g
↑→≅ fg (i x) = cong i (fg x)
↑→≅ fg o = refl

-- Preservation of composition
↑→∘ : ∀ {A B C : Set} (f : A → B) (g : B → C) → ↑→ (g ∘ f) ≅ ↑→ g ∘ ↑→ f
↑→∘ f g (i x) = refl
↑→∘ f g o = refl

-- Combination of the two properties above
↑→≅∘ : ∀ {A B C} (f : A → B) (g : B → C) {h} → (h ≅ g ∘ f) → (↑→ h ≅ ↑→ g ∘ ↑→ f)
↑→≅∘ f g h≅g∘f = (↑→≅ h≅g∘f) ≅!≅ (↑→∘ f g)

-- A symmetric version of the above
↑→∘≅ : ∀ {A B C} (f : A → B) (g : B → C) {h} → (g ∘ f ≅ h) → (↑→ g ∘ ↑→ f ≅ ↑→ h)
↑→∘≅ f g g∘f≅h = (↑→∘ f g) ~!≅ (↑→≅ g∘f≅h)

-- Naturality of the i constructor
i-nat : ∀ {A B : Set} → (f : A → B) → i ∘ f ≅ ↑→ f ∘ i
i-nat f x = refl

-- Naturality of the io eliminator
io-nat : ∀ {A B C : Set} (f : B → C) (g : A → B) (c : C) → io (f ∘ g) c ≅ io f c ∘ ↑→ g
io-nat f g d (i x) = refl
io-nat f g d o = refl

-- Preservation of decidability of equality
dec≡↑ : ∀ {X} → dec≡ X → dec≡ (↑ X)
dec≡↑ dX o     o     = in1 refl 
dec≡↑ dX o     (i y) = in2 λ { () }
dec≡↑ dX (i x) o     = in2 λ { () }
dec≡↑ dX (i x) (i y) = case (λ e → in1 (cong i e)) (λ ne → in2 λ { refl → ne refl }) (dX x y)

-- open import Datatypes public
