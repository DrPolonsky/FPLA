open import Predicates
open import Logic
open import Relations.FinitelyBranching
open import Lists
open import Datatypes
open import Relations.Seq
open import Relations.Core
open import Relations.WellFounded.WFDefinitions
open import Classical

module Relations.Coreductive {A : Set} (R : 𝓡 A) where
  Cor→ind¬¬ : ∀ (P : 𝓟 A) → R -coreductive P → R -inductive (∁ (∁ P))
  Cor→ind¬¬ P Pco x xind ¬Px with Pco x ¬Px
  ... | (y ,, Ryx , ¬Py) = xind y Ryx ¬Py

-- We think that below we can claim with (~R R) isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) 
-- We can decide for all x, EM (exists y st Ryx and not Py)
-- Can we show anything stronger than this too? Or can we use this to imply the following:
-- If inductive P. Then we can show FBRel and WDec to CorP using FB to DNS and this proof above. 
  FBRel∧WDec→ind⊆cor : (~R R) isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → R -inductive P → R -coreductive P
  FBRel∧WDec→ind⊆cor RisFBRel P PwDec Rind a a∉P with decList∃ (∁ P) PwDec (fst (RisFBRel a))
  ... | in2 no = ∅ (f λ Ra⊆P → a∉P (Rind a Ra⊆P)) where
      g = FBRel⊆FB (~R R) a (RisFBRel a)
      h = λ y Rya y∉P → no (List∃intro _ (fst (RisFBRel a)) y (pr1 (snd (RisFBRel a) y) Rya , y∉P) )
      f : ¬¬(∀ y → R y a → y ∈ P)
      f = FB→DNS (~R R) P a g h
  ... | in1 yes with List∃elim _ _ yes
  ... | y ,, y∈Rx , y∉P = y ,, pr2 (snd (RisFBRel a) y) y∈Rx , y∉P

  -- TODO: move this function below to finitely branching as it doesn't directly deal with coreductive
  FBRel∧WDec→EMRyx : (~R R) isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → ∀ {x} → EM (Σ[ y ∈ A ] (R y x × ¬ (P y)))
  FBRel∧WDec→EMRyx RisFBRel P PwDec {x} with RisFBRel x 
  ...| ys ,, Rys 
    with decList∃ (∁ P) PwDec ys
  ... | in2 no = in2 (λ ∃y → no (List∃intro (∁ P) ys (fst ∃y) (pr1 (Rys (fst ∃y)) (pr1 (snd ∃y)) , pr2 (snd ∃y)))) 
  ... | in1 yes with List∃elim (∁ P) ys yes 
  ... | y ,, y∈ys , ¬Py = in1 (y ,, (pr2 (Rys y) y∈ys) , ¬Py)

  -- Rename below to make explicit classical properties. Then rename the function two above with the same type to make clear it is an alternative way of proving the same thing. We prefer the below function to the one 2 above. 
  indP→CorP : (~R R) isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → R -inductive P → R -coreductive P
  indP→CorP RisFBRel P PwDec Rind a a∉P with FBRel∧WDec→EMRyx RisFBRel P PwDec {a} 
  ... | in1 yes = yes
  ... | in2 no = ∅ (FB→DNS (~R R) P a (FBRel⊆FB ((~R R)) a (RisFBRel a)) (λ y Rya y∉P → no (y ,, Rya , y∉P)) λ H → a∉P (Rind a H)) 
  -- Can we weaken this to FB from FBRel?
  

  record CorSequence (P : 𝓟 A) (Pcor : R -coreductive P) : Set where
      constructor CS
      field
          init : Σ[ a ∈ A ] (a ∉ P)
      CorSeq : ℕ → Σ[ e ∈ A ] (e ∉ P)
      CorSeq zero = init
      CorSeq  (succ n) with CorSeq n
      ... | (a' ,, Ha') with Pcor a' Ha'
      ... | (x ,, Rxa , x∉P) = (x ,, x∉P)
      seq : (ℕ → A)
      seq = fst ∘ CorSeq
      seq⊆CP : ∀ (n : ℕ) → seq n ∈ (∁ P)
      seq⊆CP n = snd (CorSeq n)
      seq-inc : (R -decreasing) seq
      seq-inc n with CorSeq n
      ... | a ,, Ha with Pcor a Ha
      ... | (x ,, Rax , x∉P) = Rax
