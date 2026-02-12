module TRS.TRS-Examples where

open import Logic
open import TRS.TRS-Base
open import Data.Fin
open import Data.Vec
-- open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Classical
open import Relation.Nullary
open import Relations.ClosureOperators
open import Predicates

module Example1 where
  -- p1: F(a,x) -> G(x,x)
  -- p2: b -> F(b,b)
  -- Taken from Example 2.2.8 in TeReSe

  S : Signature
  S = Sig (Fin 4) ar (λ {x} {y} → fdec x y )  where
    ar : _
    ar zero = 0 -- a
    ar (suc zero) = 0 -- b
    ar (suc (suc zero)) = 2 -- F
    ar (suc (suc (suc zero))) = 2 -- G
    fdec : ∀ x y → EM (x ≡ y)
    fdec x y with x ≟ y
    ... | yes p = in1 p
    ... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y)) where open import Data.Empty

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
  S = Sig (Fin 1) ar (λ {x} {y} → fdec x y ) where
    ar : _
    ar zero = 0 -- a 

    fdec : ∀ x y → EM (x ≡ y)
    fdec x y with x ≟ y
    ... | yes p = in1 p
    ... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y))  where open import Data.Empty

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

  a : Terms ⊥
  a = fun zero []

  a→a : Raa a a
  a→a = Rax (zero ,, refl)

