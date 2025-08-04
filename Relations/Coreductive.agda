open import Predicates 
open import Logic 
open import Relations.FinitelyBranching
open import Lists
open import Datatypes
open import Relations.Seq
open import Relations.Core 
open import Relations.WellFounded.WFDefinitions

module Relations.Coreductive {A : Set} (R : 𝓡 A) where 
    _-coreductive_ : 𝓟 A → Set 
    _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P) 

    Cor→ind¬¬ : ∀ (P : 𝓟 A) → _-coreductive_ P → R -inductive (∁ (∁ P))
    Cor→ind¬¬ P Pco x xind ¬Px with Pco x ¬Px
    ... | (y ,, Ryx , ¬Py) = xind y Ryx ¬Py

    FBRel∧WDec→CorP : (~R R) isFBRel → ∀ (P : 𝓟 A) → dec (∁ P) → R -inductive P → _-coreductive_ (P)
    FBRel∧WDec→CorP RisFBRel P PwDec Rind a a∉P with decList∃ (∁ P) PwDec (fst (RisFBRel a)) 
    ... | in2 no = ∅ (f λ Ra⊆P → a∉P (Rind a Ra⊆P)) where 
        g = FBRel⊆FB (~R R) a (RisFBRel a)
        h = λ y Rya y∉P → no (List∃intro _ (fst (RisFBRel a)) y (pr1 (snd (RisFBRel a) y) Rya , y∉P) )
        f : ¬¬(∀ y → R y a → y ∈ P) 
        f = FB→DNS (~R R) P a g h   
    ... | in1 yes with List∃elim _ _ yes
    ... | y ,, y∈Rx , y∉P = y ,, pr2 (snd (RisFBRel a) y) y∈Rx , y∉P 

    record CorSequence (P : 𝓟 A) (Pcor : _-coreductive_ P) : Set where
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

