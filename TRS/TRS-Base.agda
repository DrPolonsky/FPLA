open import Logic
open import Classical
open import Lifting
open import Datatypes using (ℕ)
open import Relations.Decidable
open import Data.Vec
open import Data.Fin
open import Predicates

module TRS.TRS-Base where

record Signature : Set₁ where
  constructor Sig
  field
    Fs : Set
    Ar : Fs → ℕ
    FsDec : (_≡_ {A = Fs} isDec)

  data Terms (V : Set) : Set where
    var : V → Terms V
    fun : ∀ (f : Fs) → Vec (Terms V) (Ar f) → Terms V

-- open Signature
module Substitution (S : Signature) where
  open Signature S

  {-# TERMINATING #-}
  subst : ∀ {V W} → Terms V → (V → Terms W) → Terms W
  subst (var x) ts = ts x
  subst (fun f args) ts = fun f (map (λ s → subst s ts) args)
      -- f(a1,..,ak) [vs := ts] = f(a1[vs:=ts],...,ak[vk:=ts])

  data Pattern : ℕ → Set where
    hole : Pattern 1
    funp : ∀ (f : Fs) → (W : Vec ℕ (Ar f))
             → (ps : ∀ (p : Fin (Ar f)) → Pattern (lookup W p))
             → Pattern (sum W)
             -- f(g([],a),f([],[])) : Pattern 3, where f = f, W = [1,2],
             -- ps = λ { o → g([],a); io → f([],[]) }

  record RRule : Set where
    constructor RR
    field
      holes : ℕ
      lhs : Pattern holes
      rhs : Terms (Fin holes)
    -- This encodes left-linear first-order TRSs
  open RRule

  match : ∀ {V : Set} {h : ℕ} (p : Pattern h) → Terms V → ↑ (Fin h → Terms V)
  match hole t = i (λ _ → t )
  match (funp f W ps) (var x) = o
  match (funp f W ps) (fun g x) with FsDec {f} {g}
  ... | in2 no = o
  ... | in1 yes = {!   !}
  {- match f([x],g(a,[y])) f(f(a,b),g(a,g(b,b))) = i σ, where
           σ = λ {[x] → f(a,b); [y] → g(b,b)}     -}

  module GeneralTRS {RuleIdx : Set} (Rules : RuleIdx → RRule) where

    module InScope (V : Set) where

      applyRule : RuleIdx → Terms V → Terms V → Set
      applyRule ri s t with match (lhs (Rules ri)) s
      ... | i σ = t ≡ subst (rhs (Rules ri)) σ
      ... | o = ⊥

      -- The root relation AKA contraction of a rewrite rule
      R₀ : 𝓡 (Terms V)
      R₀ s t = Σ[ ri ∈ RuleIdx ] (applyRule ri s t)

      data R : 𝓡 (Terms V) where
        Rax : ∀ {s t} → R₀ s t → R s t
        Rfun : ∀ (f : Fs) (ts : Vec (Terms V) (Ar f)) (j : Fin (Ar f)) {s t tj u : Terms V}
                 → R tj u → s ≡ fun f ts → t ≡ fun f (ts [ j ]≔ u) → R s t

open Substitution
open import Relation.Nullary

module Example1 where
-- p1: F(a,x) -> G(x,x)
-- p2: b -> F(b,b)

S : Signature
S = Sig (Fin 4) ar (λ {x} {y} → fdec x y )  where
  ar : _
  ar 0F = 0 -- a
  ar 1F = 0 -- b
  ar 2F = 2 -- F
  ar 3F = 2 -- G
  fdec : ∀ x y → EM (x ≡ y)
  fdec x y with x ≟ y
  ... | yes p = in1 p
  ... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y) ) where open import Data.Empty

open Signature S

p1lhs : Pattern S 1 -- F(a,x)
p1lhs = funp 2F (0 ∷ 1 ∷ []) ps where
  ps : _
  ps 0F = funp 0F [] (λ {()})
  ps 1F = hole
p2lhs : Pattern S 0 -- b
p2lhs = funp 1F [] (λ {()})

p1 : RRule S
p1 = RR 1 p1lhs (fun 3F (var 0F ∷ var 0F ∷ []) )

p2 : RRule S
p2 = RR 0 p2lhs (fun 2F (b ∷ b ∷ []) )
  where b = fun 1F []

p12 : Fin 2 → RRule S
p12 0F = p1
p12 1F = p2

R12 : ∀ V → 𝓡 (Terms V)
R12 V = GeneralTRS.InScope.R S {RuleIdx = Fin 2} p12 V
  -- data RootRed ∀ {V}




   -- data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
   --   here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
   --   there : ∀ {n} {i} {x y} {xs : Vec A n}
   --           (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
