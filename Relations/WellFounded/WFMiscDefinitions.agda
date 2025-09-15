-- This file for definitions we are not including in our report (e.g. seq+)

-- A variation of ``minimal'' with focus on the complement of the given predicate
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )




{- This formulation of WFseq+ is wrong:
  Consider ARS a -> b.
  Consider the sequence s(k) = a.
  Then s(k) is not a normal form, and the sequence s does not contain a normal form.
  Yet every sequence in this ARS does contain an element not reducing to its successor.

  Say that s : ℕ → A is *almost increasing* if for all n,
  either s(n) -> s(n+1) or s(n) is a normal form.

  WFseq+ could be something like: "every almost increasing sequence ends in a normal form".
  (IE, ∀ s : ℕ → A, AlmostIncreasing(s) → Σ[ n ∈ ℕ ] (s n ∈ NF ).)

  Let's check that such WFseq+ would indeed be equivalent to WFseq.
  1. WFseq⊆WFseq+. Assume WFseq.  Let s be given, suppose s is almost increasing.
  By assumption, exists k s.t. s(k) does not reduce to s(k+1).
  Since s is almost increasing, s(k) must be a normal form.
  2. WFseq+⊆WFseq.
  (That is, if every almost increasing sequence contains/ends in a normal form,
  then every sequence contains an element not reducing to its successor.)
  Classical argument.  Assume WFseq+.
  Let s be a sequence.
  By excluded middle, either s is almost increasing, or
  there exists an n, such that s(n) is neither a normal form, nor s(n) -> s(n+1).
  This n yields an index on which s does not reduce to its successor.
-}