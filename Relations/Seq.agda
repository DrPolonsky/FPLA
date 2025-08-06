open import Relations.ClosureOperators
open import Predicates
open import Logic
open import Datatypes using (ℕ;zero; succ)
open import Relations.Decidable
open import Relations.Core


module Relations.Seq  {A : Set} (R : 𝓡 A) where 

_-increasing : 𝓟 (ℕ → A)
_-increasing s = ∀ n → R (s n) (s (succ n)) -- xₙ < xₙ₊₁

_-decreasing : 𝓟 (ℕ → A)
_-decreasing s = ∀ n → R (s (succ n)) (s n) -- xₙ > xₙ₊₁

is_-_bound_ : (f : ℕ → A) → A → Set
is_-_bound_ f x = ∀ n → (R ⋆) (f n) x

_isBP : Set
_isBP = ∀ (f : ℕ → A) → f ∈ _-increasing → Σ[ x ∈ A ] ( is_-_bound_ f x )


seq-lemma : ∀ (f : ℕ → A) → f ∈ _-increasing → ∀ n → (R ⋆) (f zero) (f n)
seq-lemma f f-inc zero = ε⋆
seq-lemma f f-inc (succ n) = f-inc zero ,⋆ seq-lemma (f ∘ succ) (λ k → f-inc (succ k)) n

seq-lemma2 : ∀ (f : ℕ → A) → f ∈ _-increasing → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
seq-lemma2 f f-inc zero m = in1 (seq-lemma f f-inc m)
seq-lemma2 f f-inc (succ n) zero = in2 (seq-lemma f f-inc (succ n))
seq-lemma2 f f-inc (succ n) (succ m) = seq-lemma2 (f ∘ succ) (λ k → f-inc (succ k) ) n m

module MinDecImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where 
  -- REF: Move both of the below functions to Seq? They aren't used anywhere. 
  dMseq : A → ℕ → A
  dMseq a0 zero = a0
  dMseq a0 (succ n) with dM (dMseq a0 n)
  ... | in1 (b ,, bRsn) = b
  ... | in2 x = dMseq a0 n
  -- REF: The below isn't used. Do we want to keep it?
  ¬¬∃seqDec : ∀ a → ¬¬ (   (Σ[ k ∈ ℕ ] ∀ x → ¬ R x (dMseq a k))
                         ⊔ (∀ k → R (dMseq a (succ k)) (dMseq a k)))
  ¬¬∃seqDec a ¬EM = ¬EM (in2 f) where
    f : _ -- (dMseq a) ∈ R -decreasing 
    f k with dM (dMseq a k) | dMseq a (succ k) in e
    ... | in1 (c ,, Rcsk) | b = transp (~R R (dMseq a k)) e Rcsk
    ... | in2 x∈NF | b = ∅ (¬EM (in1 (k ,, x∈NF)))

