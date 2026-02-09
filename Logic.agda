-- {-# OPTIONS --cubical-compatible #-}

module Logic where

-- BASIC COMBINATORS
I : ∀ {l} {A : Set l} → A → A
I x = x

K : ∀ {l k} {A : Set l} {B : Set k} → A → B → A
K x y = x

KI : ∀ {l k} {A : Set l} {B : Set k} → A → B → B
KI = K I

-- ∘ is \o
_∘_ : ∀ {l m n} {A : Set l} {B : Set m} {C : Set n} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- PROPOSITIONAL CONSTANTS AND CONNECTIVES
-- ⊤ is \top
data ⊤ : Set where
  tt : ⊤

-- ⊥ is \bot
data ⊥ : Set where

-- ∅ is \emptyset
∅ : ∀ {A : Set} → ⊥ → A
∅ ()

-- × is \x
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pr1 : A
    pr2 : B
open _×_ public

-- ⊔ is \lub or \sqcup
data _⊔_ (A B : Set) : Set where
  in1 : A → A ⊔ B
  in2 : B → A ⊔ B

case : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊔ B → C
case f g (in1 x) = f x
case f g (in2 y) = g y

-- ¬ is \lnot
¬_ : ∀ {l} → Set l → Set l
¬_ A = A → ⊥

¬¬_ : ∀ {l} → Set l → Set l
¬¬_ A = ¬ (¬ A)

-- ↔ is \<->
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

_↔!↔_ : ∀ {A B C} → A ↔ B → B ↔ C → A ↔ C
(AB , BA) ↔!↔ (BC , CB) = (BC ∘ AB) , (BA ∘ CB)

-- EQUALITY
-- ≡ is \== or \equiv
-- data _≡_ {l} {A : Set l} (a : A) : A → Set l where
--   refl : a ≡ a
-- {-# BUILTIN EQUALITY _≡_ #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl) public

~ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
~ refl = refl

_!_ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ! bc = bc

_!~_ : ∀ {A : Set} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p !~ q = p ! ~ q

_~!_ : ∀ {A : Set} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
p ~! q = ~ p ! q

transp : ∀ {A : Set} (B : A → Set) {a1 a2 : A} → a1 ≡ a2 → B a1 → B a2
transp B refl = I

cong : ∀ {A B : Set} (f : A → B) {a1 a2 : A} → a1 ≡ a2 → f a1 ≡ f a2
cong f refl = refl

cong2 : ∀ {A B C : Set} (f : A → B → C)
         {a1 a2 : A} → a1 ≡ a2 → {b1 b2 : B} → b1 ≡ b2 → f a1 b1 ≡ f a2 b2
cong2 f refl refl = refl

cong3 : ∀ {A B C D : Set} (f : A → B → C → D) {a1 a2 b1 b2 c1 c2}
          → a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → f a1 b1 c1 ≡ f a2 b2 c2
cong3 f refl refl refl = refl

-- POINTWISE EQUALITY OF FUNCTIONS
-- ≅ is \~= or \cong
_≅_ : ∀ {A B : Set} (f g : A → B) → Set
f ≅ g = ∀ x → f x ≡ g x

refl≅ : ∀ {A B : Set} {f : A → B} → f ≅ f
refl≅ x = refl
symm≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → g ≅ f
symm≅ fg x = ~ (fg x)
tran≅ : ∀ {A B : Set} {f g h : A → B} → f ≅ g → g ≅ h → f ≅ h
tran≅ fg gh x = (fg x) ! (gh x)

ap : ∀ {A B : Set} {f g : A → B} → f ≅ g → ∀ {x y : A} → x ≡ y → f x ≡ g y
ap {g = g} fg {x} xy = fg x ! cong g xy

!≅! : ∀ {A B : Set} {f : A → B} → f ≅ f
!≅! = refl≅
~≅_ : ∀ {A B : Set} {f g : A → B} → f ≅ g → g ≅ f
~≅_ = symm≅
_≅!≅_ : ∀ {A B : Set} {f g h : A → B} → f ≅ g → g ≅ h → f ≅ h
_≅!≅_ = tran≅
_~!≅_ : ∀ {A B : Set} {f g h : A → B} → g ≅ f → g ≅ h → f ≅ h
p ~!≅ q = (~≅ p) ≅!≅ q
_≅!~_ : ∀ {A B : Set} {f g h : A → B} → f ≅ g → h ≅ g → f ≅ h
p ≅!~ q = p ≅!≅ (~≅ q)
_≅~≅_ : ∀ {A B : Set} {f g h : A → B} → g ≅ f → h ≅ g → f ≅ h
p ≅~≅ q = (~≅ p) ≅!≅ (~≅ q)

_≅∘_ : ∀ {A B C} {f g : B → C} → f ≅ g → ∀ (h : A → B) → f ∘ h ≅ g ∘ h
fg ≅∘ h = λ a → fg (h a)

_∘≅_ : ∀ {A B C} (f : B → C) {g h : A → B} → g ≅ h → f ∘ g ≅ f ∘ h
f ∘≅ gh = λ a → cong f (gh a)

infix 10 _↔_
infix 14 _⊔_
infix 15 _×_
-- infix 18 _≡_
infix 18 _≅_
infixr 22 _!_
infix 25 _∘_
infix 10 _,_
infix 17 ¬_
infix 25 ~≅_
infixr 23 _≅!≅_
infixr 23 _~!≅_
infixr 23 _≅!~_
-- infix 23 _≅~≅_
-- infix 23 _~≅~_

-- SIGMA TYPE
open import Agda.Builtin.Sigma renaming (_,_ to _,,_) public

Σ-syntax : (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

dec≡ : Set → Set
dec≡ A = ∀ (x y : A) → (x ≡ y) ⊔ ¬ (x ≡ y)

-- Injectivity of constructors of standard datatypes
-- module InjectiveConstructors where

in1inj : ∀ {A B} {a1 a2 : A} → in1 {B = B} a1 ≡ in1 a2 → a1 ≡ a2
in1inj refl = refl

in2inj : ∀ {A B} {a1 a2 : B} → in2 {A = A} a1 ≡ in2 a2 → a1 ≡ a2
in2inj refl = refl

in1≠in2 : ∀ {A B : Set} {a : A} {b : B} → in1 a ≡ in2 b → ⊥
in1≠in2 ()

_,_inj : ∀ {A B} {a1 a2 : A} {b1 b2 : B} → (a1 , b1) ≡ (a2 , b2) → (a1 ≡ a2) × (b1 ≡ b2) 
_,_inj refl = (refl , refl)

-- THE END
