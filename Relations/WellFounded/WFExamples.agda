open import Logic
open import Datatypes
open import Predicates
open import Classical
open import Relations.Core
open import Relations.WellFounded.WFDefinitions

module Relations.WellFounded.WFExamples where 

module naturalNumbers where 
    data _<_ : ℕ → ℕ → Set where
        base< : ∀ {n} → n < succ n
        succ< : ∀ {n m} → n < m → n < succ m

    mono< : ∀ {m n} → m < n → succ m < succ n
    mono< base< = base<
    mono< (succ< mn) = succ< (mono< mn)

    zero< : ∀ {m} → zero < succ m
    zero< {zero} = base<
    zero< {succ m} = succ< zero<

    -- 
    <isWFacc : _<_ isWFacc
    <isWFacc zero = acc λ {y ()}
    <isWFacc (succ n) with <isWFacc n 
    ... | acc h = acc f where 
        f : (x : ℕ) (x<sn : x < succ n) → (_<_ -accessible) x 
        f x base< = acc h
        f x (succ< x<n) = h x x<n  