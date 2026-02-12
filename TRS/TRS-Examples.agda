module TRS.TRS-Examples where

open import Logic
open import TRS.TRS-Base
open import Data.Fin
open import Data.Vec
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Classical
open import Relation.Nullary
open import Relations.ClosureOperators
open import Predicates
open import ARS.Properties

fdecFin : ∀ {n : ℕ} → (x y : Fin n) → EM (x ≡ y)
fdecFin x y with x ≟ y
... | yes p = in1 p
... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y)) where open import Data.Empty using (⊥-elim)

module Example1 where
  -- p1: F(a,x) -> G(x,x)
  -- p2: b -> F(b,b)
  -- Taken from Example 2.2.8 in TeReSe

  S : Signature
  S = Sig (Fin 4) ar (λ {x} {y} → fdecFin x y )  where
    ar : _
    ar zero = 0 -- a
    ar (suc zero) = 0 -- b
    ar (suc (suc zero)) = 2 -- F
    ar (suc (suc (suc zero))) = 2 -- G
 

  open Signature S
  open Substitution S

  p1lhs : Pattern 1 -- F(a,x)
  p1lhs = funp (suc (suc zero)) (Pa ∷ Px ∷ []) where
    Pa = 0 ,, funp zero []
    Px = 1 ,, hole

  p2lhs : Pattern 0 -- b
  p2lhs = funp (suc zero) []

  p1 : RRule
  p1 = RR 1 p1lhs (fun (suc (suc (suc zero))) (var zero ∷ var zero ∷ []) )

  p2 : RRule
  p2 = RR 0 p2lhs (fun (suc (suc zero)) (b ∷ b ∷ []) )
    where b = fun (suc zero) []

  p12 : Fin 2 → RRule 
  p12 zero = p1
  p12 (suc zero) = p2

  R12 : ∀ {V} → 𝓡 (Terms V)
  R12 {V} = GeneralTRS.InScope.R {RuleIdx = Fin 2} p12 V

  s : Terms ⊥  -- F(a,b)
  s = fun (suc (suc zero)) (fun zero [] ∷ fun (suc zero) [] ∷ [])

  t : Terms ⊥ -- G(b,F(b,b))
  t = fun (suc (suc (suc zero)))
        (fun (suc zero) []
        ∷ fun (suc (suc zero)) (fun (suc zero) [] ∷ fun (suc zero) [] ∷ [])
        ∷ [])

  s→*t : (R12 ⋆) s t
  s→*t = Rax (zero ,, refl)
      ,⋆ (Rfun (suc (suc (suc zero))) (b ∷ b ∷ []) (suc zero) b→fbb refl refl ,⋆ ε⋆)
    where
      b : Terms ⊥
      b = fun (suc zero) []

      fbb : Terms ⊥
      fbb = fun (suc (suc zero)) (b ∷ b ∷ [])

      b→fbb : R12 b fbb
      b→fbb = Rax ((suc zero) ,, refl)



module Example-aa where
    -- a -> a 
  -- Signature with one constant symbol a : 0-ary function
  S : Signature
  S = Sig (Fin 1) ar (λ {x} {y} → fdecFin x y ) where
    ar : Fin 1 → ℕ 
    ar zero = 0 -- a 


  open Signature S
  open Substitution S

  lhs-aa : Pattern  0 -- a 
  lhs-aa = funp zero []

  rhs-aa : Terms (Fin 0)
  rhs-aa = fun zero []

  rule-aa : RRule 
  rule-aa = RR 0 lhs-aa rhs-aa

  rules-aa : Fin 1 → RRule 
  rules-aa zero = rule-aa

  Raa : ∀ {V} → 𝓡 (Terms V)
  Raa {V} = GeneralTRS.InScope.R  {RuleIdx = Fin 1} rules-aa V

  Raa⊥ : 𝓡 (Terms ⊥)
  Raa⊥ = Raa {V = ⊥}
  -- showing this example is locally SM
  open LocalProperties {A = Terms ⊥} {R = Raa⊥}

  a : Terms ⊥
  a = fun zero []

  a→a : Raa a a
  a→a = Rax (zero ,, refl)

  a-step-id : ∀ {y} → Raa⊥ a y → y ≡ a
  a-step-id (Rax (zero ,, refl)) = refl
  a-step-id (Rfun .zero .[] () r refl refl)

  a→*a-id : ∀ {y} → (Raa⊥ ⋆) a y → y ≡ a
  a→*a-id ε⋆ = refl
  a→*a-id (Rxy ,⋆ R*xy) rewrite a-step-id Rxy = a→*a-id R*xy

  a∈MF : MF a
  a∈MF y R*ay rewrite a→*a-id R*ay = ε⋆

  a∈SM : SM a
  a∈SM = MF⊆SM a a∈MF

module Example-bubble where
  -- bubble-sort style swap:
  -- cons(x, cons(y, z)) -> cons(y, cons(x, z))

  S : Signature
  S = Sig (Fin 1) ar (λ {x} {y} → fdecFin x y) where
    ar : Fin 1 → ℕ
    ar zero = 2 -- cons

  open Signature S
  open Substitution S

  lhs-swap : Pattern 3 -- cons(x, cons(y, z))
  lhs-swap = funp zero (Px ∷ Pyz ∷ []) where
    Px : Σ-syntax ℕ Pattern
    Px = 1 ,, hole

    Py : Σ-syntax ℕ Pattern
    Py = 1 ,, hole

    Pz : Σ-syntax ℕ Pattern
    Pz = 1 ,, hole

    Pyz : Σ-syntax ℕ Pattern
    Pyz = 2 ,, funp zero (Py ∷ Pz ∷ [])
  
  rhs-swap : Terms (Fin 3) -- cons(y, cons(x, z))
  rhs-swap = fun zero
    (var (suc zero) ∷ fun zero (var zero ∷ var (suc (suc zero)) ∷ []) ∷ [])

  rule-swap : RRule
  rule-swap = RR 3 lhs-swap rhs-swap

  rules-swap : Fin 1 → RRule
  rules-swap zero = rule-swap

  Rswap : ∀ {V} → 𝓡 (Terms V)
  Rswap {V} = GeneralTRS.InScope.R {RuleIdx = Fin 1} rules-swap V

  t₁ : Terms (Fin 3)
  t₁ = fun zero (var zero ∷ fun zero (var (suc zero) ∷ var (suc (suc zero)) ∷ []) ∷ [])

  t₂ : Terms (Fin 3)
  t₂ = fun zero (var (suc zero) ∷ fun zero (var zero ∷ var (suc (suc zero)) ∷ []) ∷ [])

  t₁→t₂ : Rswap t₁ t₂
  t₁→t₂ = Rax (zero ,, refl)

module Example-NewmanCandidate where
  -- Rules:
  --   p(a) -> p(b)
  --   p(b) -> p(a)
  --   f(p(a), p(a)) -> k
  --   f(p(b), p(b)) -> k

  S : Signature
  S = Sig (Fin 5) ar (λ {x} {y} → fdecFin x y) where
    ar : Fin 5 → ℕ
    ar zero = 0                              -- a
    ar (suc zero) = 0                        -- b
    ar (suc (suc zero)) = 1                  -- p
    ar (suc (suc (suc zero))) = 2            -- f
    ar (suc (suc (suc (suc zero)))) = 0      -- k

  open Signature S
  open Substitution S

  aS : Fin 5
  aS = zero

  bS : Fin 5
  bS = suc zero

  pS : Fin 5
  pS = suc (suc zero)

  fS : Fin 5
  fS = suc (suc (suc zero))

  kS : Fin 5
  kS = suc (suc (suc (suc zero)))

  lhs₁ : Pattern 0
  lhs₁ = funp pS ((0 ,, funp aS []) ∷ [])

  rhs₁ : Terms (Fin 0)
  rhs₁ = funp→term where
    funp→term : Terms (Fin 0)
    funp→term = fun pS (fun bS [] ∷ [])

  lhs₂ : Pattern 0
  lhs₂ = funp pS ((0 ,, funp bS []) ∷ [])

  rhs₂ : Terms (Fin 0)
  rhs₂ = fun pS (fun aS [] ∷ [])

  lhs₃ : Pattern 0
  lhs₃ = funp fS ((0 ,, funp pS ((0 ,, funp aS []) ∷ []))
               ∷ (0 ,, funp pS ((0 ,, funp aS []) ∷ []))
               ∷ [])

  rhs₃ : Terms (Fin 0)
  rhs₃ = fun kS []

  lhs₄ : Pattern 0
  lhs₄ = funp fS ((0 ,, funp pS ((0 ,, funp bS []) ∷ []))
               ∷ (0 ,, funp pS ((0 ,, funp bS []) ∷ []))
               ∷ [])

  rhs₄ : Terms (Fin 0)
  rhs₄ = fun kS []

  r₁ : RRule
  r₁ = RR 0 lhs₁ rhs₁

  r₂ : RRule
  r₂ = RR 0 lhs₂ rhs₂

  r₃ : RRule
  r₃ = RR 0 lhs₃ rhs₃

  r₄ : RRule
  r₄ = RR 0 lhs₄ rhs₄

  rules : Fin 4 → RRule
  rules zero = r₁
  rules (suc zero) = r₂
  rules (suc (suc zero)) = r₃
  rules (suc (suc (suc zero))) = r₄

  Rnc : ∀ {V} → 𝓡 (Terms V)
  Rnc {V} = GeneralTRS.InScope.R {RuleIdx = Fin 4} rules V

  a : Terms ⊥
  a = fun aS []

  b : Terms ⊥
  b = fun bS []

  pa : Terms ⊥
  pa = fun pS (a ∷ [])

  pb : Terms ⊥
  pb = fun pS (b ∷ [])

  k : Terms ⊥
  k = fun kS []

  faa : Terms ⊥
  faa = fun fS (pa ∷ pa ∷ [])

  fba : Terms ⊥
  fba = fun fS (pb ∷ pa ∷ [])

  p-a→p-b : Rnc pa pb
  p-a→p-b = Rax (zero ,, refl)

  p-b→p-a : Rnc pb pa
  p-b→p-a = Rax ((suc zero) ,, refl)

  faa→k : Rnc faa k
  faa→k = Rax ((suc (suc zero)) ,, refl)

  faa→fba : Rnc faa fba
  faa→fba = Rfun fS (pa ∷ pa ∷ []) zero p-a→p-b refl refl

