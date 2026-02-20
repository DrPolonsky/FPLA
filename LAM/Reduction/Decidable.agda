module LAM.Reduction.Decidable where 

open import Logic 
open import Predicates
open import Classical using (EM)
open import Lifting 
open import LAM.Lambda 
open import LAM.Reduction.Beta
-- open import Predicates using (dec2)

dec𝓡Λ : 𝓡Λ → Set₁ 
dec𝓡Λ R = ∀ {X} → dec≡ X → ∀ (s t : Λ X) → EM (R s t)

dec⟶ₒ : dec𝓡Λ _⟶ₒ_
dec⟶ₒ dX (var x) t = in2 λ { () }
dec⟶ₒ dX (app (var x) s) t = in2 λ { () }
dec⟶ₒ dX (app (app r r₁) s) t = in2 λ { () }
dec⟶ₒ dX (app (abs r) s) t with dec≡Λ dX (r [ s ]ₒ) t 
... | in1 yes = in1 (redex yes)
... | in2 no  = in2 λ { (redex eq) → no eq }
dec⟶ₒ dX (abs s) t = in2 λ { () } 

dec⟶β : dec𝓡Λ _⟶β_ 
dec⟶β dX (var x) t = in2 λ { (red⟶β ()) }
dec⟶β dX (abs s) (var x) = in2 λ { (red⟶β ()) }
dec⟶β dX (abs s) (app t0 t1) = in2 λ { (red⟶β ()) }
dec⟶β dX (abs s) (abs t) 
  with dec⟶β (dec≡↑ dX) s t
... | in1 yes = in1 (abs⟶β yes)  
... | in2 no  = in2 λ { (abs⟶β s→t) → no s→t } 
dec⟶β dX (app s1 s2) t 
  with dec⟶ₒ dX (app s1 s2) t
... | in1 yes = in1 (red⟶β yes)
... | in2 noRoot 
  with t 
... | var x  = in2 λ { (red⟶β rdx) → noRoot rdx }
... | abs t0 = in2 λ { (red⟶β rdx) → noRoot rdx }
... | app t1 t2 
  with dec⟶β dX s1 t1 | dec⟶β dX s2 t2 | dec≡Λ dX s1 t1 | dec≡Λ dX s2 t2 
... | in1 yes1 | b | c | in1 refl = in1 (appL⟶β yes1)
... | in1 yes1 | in1 yes2 | in1 refl | in2 no4 = in1 (appR⟶β yes2) 
-- ... | in1 yes1 | in1 yes2 | in2 no3 | in2 no4 = in1 (appR⟶β yes2) -- subsumed 
... | in1 yes1 | in2 no2 | c | in2 no4 = in2 λ { (red⟶β x) → noRoot x ; (appL⟶β rdx) → no4 refl ; (appR⟶β rdx) → no2 rdx }
... | in2 no1 | in1 yes2 | in1 refl | d = in1 (appR⟶β yes2) 
... | in2 no1 | in1 yes2 | in2 no3 | d = in2 λ { (red⟶β x) → noRoot x ; (appL⟶β rdx) → no1 rdx ; (appR⟶β rdx) → no3 refl }
... | in2 no1 | in2 no2 | c | d = in2 λ { (red⟶β x) → noRoot x ; (appL⟶β rdx) → no1 rdx ; (appR⟶β rdx) → no2 rdx }
... | a | b | in2 no3 | in2 no4 = in2 (λ { (red⟶β x) → noRoot x ; (appL⟶β apl) → no4 refl ; (appR⟶β apr) → no3 refl }  ) 

open import LAM.Reduction.FinitelyBranching 
open import ARS.Properties
open import ARS.Implications 
open LocalProperties 

open Hierarchy-Implications

SN⊆WN⟶β : ∀ {X : Set} → dec≡ X → ∀ (t : Λ X) → t ∈ SN {R = _⟶β_ {X}} → t ∈ WN {R = _⟶β_ {X}}
SN⊆WN⟶β dX t t∈SN = dec∧FB→SN⊆WN (dec⟶β dX _ _) ⟶βisFB t t∈SN 

-- The end 
