open import Predicates 
open import Logic 
open import Relations.FinitelyBranching
open import Lists
open import Datatypes
open import Relations.Seq
open import Relations.Core 

module Relations.Coreductive {A : Set} (R : 𝓡 A) where 
    _-coreductive_ : 𝓟 A → Set 
    _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R x y × y ∉ P) -- I swapped the x and y in R xy, does that work?

    Pacc : 𝓟 A → Set 
    Pacc P = ∀ {x} → (∀ {y} → R x y → P y) → P x

    FBRel∧WDec→CorP : R isFBRel → ∀ (P : 𝓟 A) → Pacc P → dec (∁ P) → _-coreductive_ (P)
    FBRel∧WDec→CorP RisFBRel P Pacc PwDec a a∉P with decList∃ (∁ P) PwDec (fst (RisFBRel a)) 
    ... | in2 no = ∅ (f λ Ra⊆P → a∉P (Pacc (Ra⊆P _))) where 
        g = FBRel⊆FB R a (RisFBRel a)
        h = λ y Rya y∉P → no (List∃intro _ (fst (RisFBRel a)) y (pr1 (snd (RisFBRel a) y) Rya , y∉P) )
        f : ¬¬(∀ y → R a y → y ∈ P) 
        f = FB→DNS R P a g h   
    ... | in1 yes with List∃elim _ _ yes
    ... | y ,, y∈Rx , y∉P = y ,, pr2 (snd (RisFBRel a) y) y∈Rx , y∉P 

    CorSequence : ∀ P → _-coreductive_ P → Σ[ a ∈ A ] (a ∉ P) → ℕ → Σ[ e ∈ A ] (e ∉ P)
    CorSequence P CI aH zero = aH
    CorSequence P CI (a ,, Ha) (succ n) with CorSequence P CI (a ,, Ha) n
    ... | (a' ,, Ha') with CI a' Ha'
    ... | (x ,, Rxa , x∉P) = (x ,, x∉P)

    CorSequence-inc : ∀ P → (PCor : _-coreductive_ P) (init : Σ[ a ∈ A ] (a ∉ P)) →
                           ((~R R) -decreasing) (fst ∘ CorSequence P PCor init)
    CorSequence-inc P PCor init k with CorSequence P PCor init k
    ... | (a ,, Ha) with PCor a Ha
    ... | (x ,, Rax , x∉P) = Rax