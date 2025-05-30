open import Relations.ClosureOperators
open import Predicates
open import Logic
open import Datatypes using (ℕ;zero; succ)


module Relations.Seq  {A : Set} (R : 𝓡 A) where 

_-increasing : 𝓟 (ℕ → A)
_-increasing s = ∀ n → R (s n) (s (succ n)) -- xₙ < xₙ₊₁

_-decreasing : 𝓟 (ℕ → A)
_-decreasing s = ∀ n → R (s (succ n)) (s n) -- xₙ > xₙ₊₁

seq-lemma : ∀ (f : ℕ → A) → f ∈ _-increasing → ∀ n → (R ⋆) (f zero) (f n)
seq-lemma f f-inc zero = ε⋆
seq-lemma f f-inc (succ n) = f-inc zero ,⋆ seq-lemma (f ∘ succ) (λ k → f-inc (succ k)) n

seq-lemma2 : ∀ (f : ℕ → A) → f ∈ _-increasing → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
seq-lemma2 f f-inc zero m = in1 (seq-lemma f f-inc m)
seq-lemma2 f f-inc (succ n) zero = in2 (seq-lemma f f-inc (succ n))
seq-lemma2 f f-inc (succ n) (succ m) = seq-lemma2 (f ∘ succ) (λ k → f-inc (succ k) ) n m