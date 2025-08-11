module Predicates where

-- open import Logic-Levels
open import Logic
open import Lifting
open import Datatypes
open import Lambda
-- open import Data.Nat.Base using (ℕ; zero; succ)


-- The type of n-ary predicates on A
𝓟^ : ℕ → Set → Set₁
𝓟^ zero     A = Set
𝓟^ (succ n) A = A → 𝓟^ n A

-- The type of unary predicates on A, AKA the powerset of A
-- 𝓟 is \MCP
𝓟 : Set → Set₁
𝓟 = 𝓟^ 1

-- The type of binary predicates, AKA relations, on A
-- 𝓟 is \MCR
𝓡 : Set → Set₁
𝓡 = 𝓟^ 2

-- Membership relation
-- ∈ is \in
_∈_ : ∀ {A : Set} → A → 𝓟 A → Set
a ∈ P = P a

-- ∉ is \inn
_∉_ : ∀ {A : Set} → A → 𝓟 A → Set
a ∉ P = ¬ a ∈ P
infix 18 _∈_
infix 18 _∉_

-- The functorial action of 𝓟^
𝓟^← : ∀ {n : ℕ} {A B : Set} → (A → B) → 𝓟^ n B → 𝓟^ n A
𝓟^← {zero}   f P = P
𝓟^← {succ n} f P = λ a → 𝓟^← f (P (f a))

-- Second-order predicates
𝓟₁ : Set → Set₂
𝓟₁ A = A → Set₁

module LogicOps {A : Set} where
  -- Constantly true predicate
  K⊤ : ∀ {n} → 𝓟^ n A
  K⊤ {zero}   = ⊤
  K⊤ {succ n} = λ _ → K⊤

  -- Constantly false predicate
  K⊥ : ∀ {n} → 𝓟^ n A
  K⊥ {zero}   = ⊥
  K⊥ {succ n} = λ _ → K⊥

  -- Intersection
  _∩_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A → 𝓟^ n A
  _∩_ {zero}   P Q =          P × Q
  _∩_ {succ n} P Q = λ a → (P a ∩ Q a)

  -- Union
  _∪_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A → 𝓟^ n A
  _∪_ {zero}   P Q =          P ⊔ Q
  _∪_ {succ n} P Q = λ a → (P a ∪ Q a)

  -- Complement
  ∁_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A
  ∁_ {zero}   P = ¬ P
  ∁_ {succ n} P = λ x → ∁ (P x)

  -- ¬¬-closure
  ∁∁_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A
  ∁∁_ P = ∁ (∁ P)

  infix 19 ∁∁_
  infix 17 _∩_
  infix 17 _∪_
  infix 19 ∁_

open LogicOps public

module ContainmentAndEquivalence {A : Set} where

  -- Subset relation
  _⊆_ : ∀ {n : ℕ} → 𝓟^ n A → 𝓟^ n A → Set
  _⊆_ {zero}   P Q = P → Q
  _⊆_ {succ n} P Q = ∀ x → P x ⊆ Q x

  -- Extensional equivalence of predicates
  _⇔_ : ∀ {n : ℕ} → 𝓟^ n A → 𝓟^ n A → Set
  A ⇔ B = A ⊆ B × B ⊆ A

  infixr 15 _⇔_
  infix 16 _⊆_

  -- Properties of operations on relations
  Elem : ∀ {n} → 𝓟^ n A → Set
  Elem {zero}   X = X
  Elem {succ n} P = Σ[ a ∈ A ] (Elem (P a))

  ⊆⊤ : ∀ {n : ℕ} (P : 𝓟^ n A) → P ⊆ K⊤
  ⊆⊤ {zero}   P = K tt
  ⊆⊤ {succ n} P = λ _ → ⊆⊤ _

  ⊥⊆ : ∀ {n : ℕ} (P : 𝓟^ n A) → K⊥ ⊆ P
  ⊥⊆ {zero}   P = ∅
  ⊥⊆ {succ n} P = λ x → ⊥⊆ (P x)

  refl⊆^ : ∀ (n : ℕ) {P : 𝓟^ n A} → P ⊆ P
  refl⊆^ zero = I
  refl⊆^ (succ n) = λ x → refl⊆^ n

  tran⊆^ : ∀ (n : ℕ) {P Q R : 𝓟^ n A} → P ⊆ Q → Q ⊆ R → P ⊆ R
  tran⊆^ (zero)   PQ QR = QR ∘ PQ
  tran⊆^ (succ n) PQ QR = λ x → tran⊆^ n (PQ x) (QR x)

  -- For the operators below, Agda cannot infer the implicit argument

  _⊆!⊆_ : ∀ {n : ℕ} {P Q R : 𝓟^ n A} → P ⊆ Q → Q ⊆ R → P ⊆ R
  _⊆!⊆_ {zero}   PQ QR = QR ∘ PQ
  _⊆!⊆_ {succ n} PQ QR = λ x → PQ x ⊆!⊆ QR x

  _⇔!⇔_ : ∀ {n : ℕ} {P Q R : 𝓟^ n A} → P ⇔ Q → Q ⇔ R → P ⇔ R
  _⇔!⇔_ {zero}   PQ QR = PQ ↔!↔ QR
  _⇔!⇔_ {succ n} PQ QR = PR , RP where
                         PR = λ x → pr1 PQ x ⊆!⊆ pr1 QR x
                         RP = λ x → pr2 QR x ⊆!⊆ pr2 PQ x

  ~⇔ : ∀ {n} {P Q : 𝓟^ n A} → P ⇔ Q → Q ⇔ P
  ~⇔ (PQ , QP) = QP , PQ

  _⊆!⇔_ : ∀ {n : ℕ} → {P Q R : 𝓟^ n A} → P ⊆ Q → Q ⇔ R → P ⊆ R
  _⊆!⇔_ {n} PQ (QR , RQ) = PQ ⊆!⊆ QR

  _⇔!⊆_ : ∀ {n : ℕ} → {P Q R : 𝓟^ n A} → P ⇔ Q → Q ⊆ R → P ⊆ R
  _⇔!⊆_ {n} (PQ , QP) QR = PQ ⊆!⊆ QR

open ContainmentAndEquivalence public

module ClassicalProperties {A : Set} where

  open import Classical

  dec : 𝓟 A → Set
  dec P = ∀ x → EM (P x)

  -- dec≡ : Set
  -- dec≡ = ∀ x → dec (_≡_ x)
  
  ¬¬Closed : 𝓟 A → Set
  ¬¬Closed P = ∁∁ P ⊆ P

  -- The image of every sequence is not not closed
  MP≡ : Set
  MP≡ = ∀ (f : ℕ → A) → ¬¬Closed (λ x → ( Σ[ k ∈ ℕ ] (f k ≡ x)))
  -- MP≡ = ∀ (f : ℕ → A) → ∀ x → ¬¬ ( Σ[ k ∈ ℕ ] (f k ≡ x)) → Σ[ k ∈ ℕ ] (f k ≡ x)

  DNS : 𝓟 A → Set
  DNS P = (∀ x → ¬¬ (P x)) → ¬¬ (∀ x → P x)

  dec→¬¬Closed : ∀ (P : 𝓟 A) → dec P → ¬¬Closed P
  dec→¬¬Closed P dp a ¬¬pa = case I (λ ¬pa → ∅ (¬¬pa ¬pa) ) (dp a) 

  ¬¬Closed∁ : ∀ (P : 𝓟 A) → ¬¬Closed (∁ P)
  ¬¬Closed∁ P x ¬¬¬x∈P Px = ¬¬¬x∈P (λ ¬Px → ¬Px Px)


  

open ClassicalProperties public

-- Markov Principle -- already defined in Properties
-- MP : Set₁
-- MP = ∀ (P : 𝓟 ℕ) → dec P → ¬¬ ( Σ[ k ∈ ℕ ] (P k)) → Σ[ k ∈ ℕ ] (P k)

module BigOps {A : Set} where

  -- ⋃ is \bigcup
  data ⋃ {D : Set} (s : D → 𝓟 A) : 𝓟 A where
    Sup : ∀ d x → x ∈ s d → x ∈ ⋃ s

  ⋃-ub : ∀ {D : Set} (s : D → 𝓟 A) → (∀ d → s d ⊆ ⋃ s)
  ⋃-ub s d = Sup d
  ⋃-lub : ∀ {D : Set} (s : D → 𝓟 A) (X : 𝓟 A) → (∀ d → s d ⊆ X) → ⋃ s ⊆ X
  ⋃-lub s X H x (Sup d .x x∈sd) = H d x x∈sd

  ⋃-mono : ∀ {D : Set} (s1 s2 : D → 𝓟 A) → (∀ d → s1 d ⊆ s2 d) → ⋃ s1 ⊆ ⋃ s2
  ⋃-mono s1 s2 ∀xs1x⊆s2x = ⋃-lub s1 (⋃ s2) (λ d x x∈s1d → ⋃-ub s2 d x (∀xs1x⊆s2x d x x∈s1d)  )

  ⋃-empty : ∀ (s : ⊥ → 𝓟 A) → ⋃ s ⊆ K⊥
  ⋃-empty s x (Sup ω .x _) = ω

open BigOps public

module Lifting^ where
  o^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (↑ A)
  o^ {zero}         = ⊤
  o^ {succ n} (i x) = K⊥
  o^ {succ n} o     = o^

  i^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (↑ A)
  i^ {zero}   P       = P
  i^ {succ n} P (i x) = i^ (P x)
  i^ {succ n} P o     = K⊥

  ↑^ : ∀  {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (↑ A)
  ↑^ P = i^ P ∪ o^

  -- The dependent eliminator into k-ary predicates ?

open Lifting^ public

module Lambda^ where
  var^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (Λ A)
  var^ {zero}   P         = P
  var^ {succ n} P (var x) = var^ (P x)
  var^ {succ n} P _       = K⊥

  app^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (Λ A) → 𝓟^ n (Λ A) → 𝓟^ n (Λ A)
  app^ {zero}   P Q             = P × Q
  app^ {succ n} P Q (app t1 t2) = app^ (P t1) (Q t2)
  app^ {succ n} P Q _           = K⊥

  abs^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (Λ (↑ A)) → 𝓟^ n (Λ A)
  abs^ {zero}   P         = P
  abs^ {succ n} P (abs t) = abs^ (P t)
  abs^ {succ n} P _       = K⊥

  Λ^ : ∀  {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (Λ A)
  Λ^ {zero}   {A} P             = P
  Λ^ {succ n} {A} P (var x)     = var^ (P x)
  Λ^ {succ n} {A} P (app t1 t2) = app^ (Λ^ P t1) (Λ^ P t2)
  Λ^ {succ n} {A} P (abs t0)    = abs^ (Λ^ (↑^ P) t0)
open Lambda^ public
 