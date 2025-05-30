module Classical where

-- open import Logic-Levels
open import Logic

-- Classical Principles
EM : Set → Set
EM A = A ⊔ ¬ A

WEM : Set → Set
WEM A = ¬ A ⊔ ¬¬ A

DNE : Set → Set
DNE A = ¬¬ A → A

EM→WEM×DNE : ∀ A → EM A → WEM A × DNE A
pr1 (EM→WEM×DNE A (in1 x)) = in2 λ ¬x → ¬x x
pr1 (EM→WEM×DNE A (in2 ¬x)) = in1 ¬x
pr2 (EM→WEM×DNE A (in1 x)) = λ ¬¬x → x
pr2 (EM→WEM×DNE A (in2 ¬x)) = λ ¬¬x → ∅ (¬¬x ¬x)

WEM×DNE→EM : ∀ A → WEM A → DNE A → EM A
WEM×DNE→EM A (in1 ¬x) DNE = in2 ¬x
WEM×DNE→EM A (in2 ¬¬x) DNE = in1 (DNE ¬¬x)
