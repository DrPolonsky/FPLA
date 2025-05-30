module Relations.Core where

open import Logic
-- open import Logic-Levels
open import Predicates

Rel : Set → Set → Set₁
Rel A B = A → B → Set

module LogicOps₂ {A B : Set} where

  -- The empty relation ∅ ⊆ 𝓟 A×B.
  K⊥₂ : Rel A B
  K⊥₂ _ _ = ⊥

  -- The maximal relation A×B ⊆ 𝓟 A×B.
  K⊤₂ : Rel A B
  K⊤₂ _ _ = ⊤

  _∩₂_ : Rel A B → Rel A B → Rel A B
  R ∩₂ S = λ x y → R x y  ×  S x y
  infix 17 _∩₂_

  _∪₂_ : Rel A B → Rel A B → Rel A B
  R ∪₂ S = λ x y →  R x y  ⊔  S x y
  infix 17 _∪₂_

  ∁₂_ : Rel A B → Rel A B
  ∁₂ R = λ x y → ¬ R x y
  infix 19 ∁₂_

  -- ⋃ is \bigcup
  ⋃₂ : ∀ {I : Set} (R : I → Rel A B) → Rel A B
  ⋃₂ {I} R x y = Σ[ α ∈ I ] (R α x y)

  -- Inclusion of relations.
  _⊆₂_ : Rel A B → Rel A B → Set
  R ⊆₂ S = ∀ x y → R x y → S x y
  infix 16 _⊆₂_

  -- Extensional equivalence of relations.
  _⇔₂_ : Rel A B → Rel A B → Set
  R ⇔₂ S = R ⊆₂ S × S ⊆₂ R
  infix 15 _⇔₂_

  relEq : ∀ {R S : Rel A B} →   R ⇔₂ S   ↔   ∀ x y → R x y ↔ S x y
  relEq = (λ RS x y → pr1 RS x y , pr2 RS x y )
        , λ H → (λ x y → pr1 (H x y)) , (λ x y → pr2 (H x y))

  _⊆!⊆₂_ : ∀ {P Q R : Rel A B} → P ⊆₂ Q → Q ⊆₂ R → P ⊆₂ R
  PQ ⊆!⊆₂ QR = λ x y → QR x y ∘ PQ x y

  _⇔!⇔₂_ : ∀ {P Q R : Rel A B} → P ⇔₂  Q → Q ⇔₂  R → P ⇔₂  R
  (PQ , QP) ⇔!⇔₂ (QR , RQ) = (PQ ⊆!⊆₂ QR) , (RQ ⊆!⊆₂ QP)
  infixr 18 _⇔!⇔₂_

open LogicOps₂ public

-- Identity, Converse, and Composition
≡R : ∀ {A} → Rel A A
≡R = _≡_

~R : ∀ {A B} → Rel A B → Rel B A
~R R = λ x y → R y x

_∘R_ : ∀ {A B C} → Rel A B → Rel B C → Rel A C
_∘R_ {B = B} R S = λ x z → Σ[ y ∈ B ] (R x y × S y z)

_R∘_ : ∀ {A B C} → Rel B C → Rel A B → Rel A C
S R∘ R = R ∘R S

_∘~_ : ∀ {A B C} → Rel A B → Rel C B → Rel A C
R ∘~ Q = R ∘R (~R Q)

_~∘_ : ∀ {A B C} → Rel A B → Rel A C → Rel B C
R ~∘ Q = (~R R) ∘R Q

infixr 18 _∘R_
infixr 18 _R∘_
infixr 18 _~∘_
infixr 18 _∘~_

module RelationLaws where

  law1 : ∀ {A B : Set} (R : Rel A B) → ≡R ∘R R ⇔₂ R
  law2 : ∀ {A B : Set} (R : Rel A B) → R ∘R ≡R ⇔₂ R
  law3 : ∀ {A : Set} → ~R (≡R {A}) ⇔ ≡R
  law4 : ∀ {A B C : Set} (R : Rel A B) (S : Rel B C) → ~R (R ∘R S) ⇔₂ (~R S) ∘R (~R R)
  law5 : ∀ {A B C D : Set} (R : Rel A B) (S : Rel B C) (T : Rel C D)
          → ((R ∘R S) ∘R T) ⇔₂ (R ∘R (S ∘R T))
  law6 : ∀ {A B : Set} (R : Rel A B) → ~R (~R R) ⇔₂ R

  pr1 (law1 R) x y (.x ,, refl , Rxy) = Rxy
  pr2 (law1 R) x y Rxy = x ,, (refl , Rxy)

  pr1 (law2 R) x y (.y ,, Rxy , refl) = Rxy
  pr2 (law2 R) x y Rxy = y ,, Rxy , refl

  pr1 law3 x .x refl = refl
  pr2 law3 x .x refl = refl

  pr1 (law4 R S) x y (z ,, Ryx , Szx) = z ,, Szx , Ryx
  pr2 (law4 R S) x y (z ,, Szx , Ryz) = z ,, Ryz , Szx

  pr1 (law5 R S T) a d (c ,, (b ,, Rab , Sbc) , Tcd) = b ,, (Rab , (c ,, Sbc , Tcd))
  pr2 (law5 R S T) a d (b ,, Rab , (c ,, Sbc , Tcd)) = c ,, ((b ,, (Rab , Sbc)) , Tcd)

  pr1 (law6 R) x y LHS = LHS
  pr2 (law6 R) x y Rxy = Rxy

-- Properties of relations
module RelationProperties {U : Set} (R : 𝓡 U) where
  reflR   : Set
  irreflR : Set
  symmR   : Set
  asymmR  : Set
  tranR   : Set

  reflR   = ∀ x → R x x
  irreflR = ∀ x → ¬ R x x
  symmR   = ∀ {x} {y} → R x y → R y x
  asymmR  = ∀ x y → R x y → R y x → x ≡ y
  tranR   = ∀ x y z → R x y → R y z → R x z

  record isEquivalence : Set where
    field
      isRefl : reflR
      isSymm : symmR
      isTran : tranR

  record isPartialOrder : Set where
    field
      isRefl : reflR
      isAsym : asymmR
      isTran : tranR

  record isStrictOrder : Set where
    field
      isIrrefl : irreflR
      isTran   : tranR

  record isPreorder : Set where
    field
      isRefl : reflR
      isTran : tranR

open RelationProperties public

module RelationsAndFunctions where

  Graph : ∀ {A B} → (A → B) → Rel A B
  Graph f = λ a b → f a ≡ b

  isTotal : ∀ {A B} → Rel A B → Set
  isTotal {A} {B} R = ∀ x → Σ[ y ∈ B ] R x y

  total→Fun : ∀ {A B} (R : Rel A B) → isTotal R → (A → B)
  total→Fun R totR x with totR x
  ... | t1 ,, t2 = t1
