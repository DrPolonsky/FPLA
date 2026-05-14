open import Logic
open import Lifting
open import LAM.Lambda
open import Predicates

open import Relations.Core
open import Relations.ClosureOperators


{-
The following is defined in Lambda.agda

-- The type of binary relations on lambda terms
ΛRel : Set₁
ΛRel = ∀ {X : Set} → Λ X → Λ X → Set

-}
module LAM.LambdaPredicates where

Λ𝓟 : Set₁
Λ𝓟 = ∀ {X} → 𝓟 (Λ X)

Λ𝓡 : Set₁
Λ𝓡 = ∀ {X} → Λ X → Λ X → Set

~Λ𝓡 : Λ𝓡 → Λ𝓡 
~Λ𝓡 R {X} = ~R (R {X}) 

_Λ↓_ : Λ𝓟 → Λ𝓡 → Λ𝓟 
_Λ↓_ P R {X} t = Σ[ s ∈ Λ X ] (s ∈ P × R s t)

-- Λ𝓡 : Set₁
-- Λ𝓡 = ΛRel

Functorial : Λ𝓡 → Set₁
Functorial R = ∀ {X Y : Set} (f : X → Y)
                 → ∀ {s t : Λ X} → R s t → R (Λ→ f s) (Λ→ f t)

Substitutive : Λ𝓡 → Set₁
Substitutive R = ∀ {X Y : Set} (f : X → Λ Y) (g : X → Λ Y)
                   → (∀ x → R (f x) (g x)) → ∀ s → R (s [ f ]) (s [ g ])

record ΛCongruence (R : Λ𝓡) : Set₁ where
  constructor ΛCong
  field
    var𝓡 : ∀ {X} (x : X) → R (var x) (var x)
    abs𝓡 : ∀ {X} (r1 r2 : Λ (↑ X)) → R r1 r2 → R (abs r1) (abs r2)
    app𝓡 : ∀ {X} (s1 s2 t1 t2 : Λ X) → R s1 s2 → R t1 t2 → R (app s1 t1) (app s2 t2)

  CongSubst : Functorial R → Substitutive R
  CongSubst Rmap f g fRg (var x) = fRg x
  CongSubst Rmap f g fRg (app s t) =
    app𝓡 (s [ f ]) (s [ g ]) (t [ f ]) (t [ g ])
          (CongSubst Rmap f g fRg s) (CongSubst Rmap f g fRg t)
  CongSubst Rmap f g fRg (abs s) =
    abs𝓡 (s [ lift f ]) (s [ lift g ])
          (CongSubst Rmap (lift f) (lift g) (io𝓟 _ (λ x → Rmap i (fRg x)) (var𝓡 o) ) s )

{-
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
-}
