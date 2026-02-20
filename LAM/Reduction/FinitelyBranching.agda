open import Logic 
open import Classical using (EM)
open import Lifting 
open import Predicates
open import LAM.Lambda 
open import LAM.Reduction.Beta
open import Relations.FinitelyBranching 

open import Agda.Builtin.List
open import Data.List using (map ; _++_)
open import Lists 

module LAM.Reduction.FinitelyBranching where

_isFB𝓡Λ : 𝓡Λ → Set₁ 
R isFB𝓡Λ = ∀ {X} → (R {X}) isFB 

⟶βisFB : _⟶β_ isFB𝓡Λ 
⟶βisFB (var x) = [] ,, λ { _ (red⟶β ()) }
⟶βisFB (abs s) with ⟶βisFB s 
... | ts ,, covering = map abs ts ,, λ { x (abs⟶β r) → map∈ abs _ ts (covering _ r) }
⟶βisFB (app (var x) s2) with ⟶βisFB s2 
... | ts ,, covering = map (app (var x)) ts ,, cases where 
  cases : _ 
  cases x (appL⟶β (red⟶β ()))
  cases .(app (var x) _) (appR⟶β r) = map∈ (app (var x)) _ ts (covering _ r)
⟶βisFB (app (abs s1) s2) 
  with ⟶βisFB s1 | ⟶βisFB s2 
... | ts1 ,, covering1 | ts2 ,, covering2 = ts ,, prf where 
  contr = s1 [ s2 ]ₒ 
  us1 = map (λ x → app (abs x) s2) ts1 
  us2 = map (app (abs s1)) ts2 
  ts = contr ∷ us1 ++ us2 
  prf : _ 
  prf b (red⟶β (redex refl)) = in1 refl
  prf b (appL⟶β (abs⟶β r)) = in2 (++∈L us1 us2 _ (map∈ (λ x → app (abs x) s2) _ ts1 (covering1 _ r)))
  prf b (appR⟶β r) = in2 (++∈R us1 us2 _ (map∈ (app (abs s1)) _ ts2 (covering2 _ r)))
⟶βisFB (app s1@(app s11 s12) s2) 
  with ⟶βisFB s1 | ⟶βisFB s2 
... | ts1 ,, cov1 | ts2 ,, cov2 = ts ,, prf where 
  us1 = map (λ x → app x s2) ts1 
  us2 = map (app s1) ts2 
  ts = us1 ++ us2 
  prf : _ 
  prf b (appL⟶β r) = ++∈L us1 us2 _ (map∈ (λ x → app x s2) _ ts1 (cov1 _ r))
  prf b (appR⟶β r) = ++∈R us1 us2 _ (map∈ (app s1) _ ts2 (cov2 _ r))


