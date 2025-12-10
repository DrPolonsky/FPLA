open import Logic

module TRS.TRS-Base where

record Signature : Set₁ where
  constructor Sig
  field
    Fs : Set
    Ar : Fs → Set

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
    field
      consts : Set
      lhsVars : Set
      lhs : Pattern consts lhsVars
      rhs : Terms lhsVars
