open import Logic
open import Lifting
open import Relations.Decidable

module TRS.TRS-Abstract where

record Signature : Set₁ where
  constructor Sig
  field
    Fs : Set
    Ar : Fs → Set
    FsDec : (_≡_ {A = Fs} isDec)

  data Terms (V : Set) : Set where
    var : V → Terms V
    fun : ∀ (f : Fs) → (args : Ar f → Terms V) → Terms V

  subst : ∀ {V W : Set} → Terms V → (V → Terms W) → Terms W
  subst (var x) t = t x
  subst (fun f args) t = fun f (λ i → subst (args i) t)

  PreRule : Set → Set
  PreRule V = Terms V × Terms V

  data Pattern (V : Set) : Set → Set₁ where
    term : Terms V → Pattern V ⊥
    hole : Pattern V ⊤
    funp : ∀ (f : Fs) → (W : Ar f → Set) → (ps : ∀ (i : Ar f) → Pattern V (W i))
             → Pattern V (Σ (Ar f) W)

  record PatternRule : Set₁ where
    pattern
    constructor PRule
    field
      consts : Set
      lhsVars : Set
      lhs : Pattern consts lhsVars
      rhs : Terms (consts ⊔ lhsVars)

  match : ∀ {V W} → Terms V → Pattern V W → ↑ (W → Terms V)
  match t (term x) = {!   !} -- need decidability of equality between terms
  match t hole = i (K t)
  match (var x) (funp f W ps) = o
  match (fun g args) (funp f W ps)
    with FsDec {g} {f}
  ... | in1 yes = {!   !}
  ... | in2 no = o
