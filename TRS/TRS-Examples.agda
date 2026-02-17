module TRS.TRS-Examples where

open import Logic
open import TRS.TRS-Base
open import Data.Fin
open import Data.Vec
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Classical
open import Relation.Nullary
open import Relations.ClosureOperators
open import Predicates
open import ARS.Properties

fdecFin : ∀ {n : ℕ} → (x y : Fin n) → EM (x ≡ y)
fdecFin x y with x ≟ y
... | yes p = in1 p
... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y)) where open import Data.Empty using (⊥-elim)

module Example1 where
  -- p1: F(a,x) -> G(x,x)
  -- p2: b -> F(b,b)
  -- Taken from Example 2.2.8 in TeReSe

  S : Signature
  S = Sig (Fin 4) ar (λ {x} {y} → fdecFin x y )  where
    ar : _
    ar zero = 0 -- a
    ar (suc zero) = 0 -- b
    ar (suc (suc zero)) = 2 -- F
    ar (suc (suc (suc zero))) = 2 -- G
 
  open Signature S
  open Substitution S

  p1lhs : Pattern 1 -- F(a,x)
  p1lhs = funp (suc (suc zero)) (Pa ∷ Px ∷ []) where
    Pa = 0 ,, funp zero []
    Px = 1 ,, hole

  p2lhs : Pattern 0 -- b
  p2lhs = funp (suc zero) []

  p1 : RRule
  p1 = RR 1 p1lhs (fun (suc (suc (suc zero))) (var zero ∷ var zero ∷ []) )

  p2 : RRule
  p2 = RR 0 p2lhs (fun (suc (suc zero)) (b ∷ b ∷ []) )
    where b = fun (suc zero) []

  p12 : Fin 2 → RRule 
  p12 zero = p1
  p12 (suc zero) = p2

  R12 : ∀ {V} → 𝓡 (Terms V)
  R12 {V} = GeneralTRS.InScope.R {RuleIdx = Fin 2} p12 V

  s : Terms ⊥  -- F(a,b)
  s = fun (suc (suc zero)) (fun zero [] ∷ fun (suc zero) [] ∷ [])

  t : Terms ⊥ -- G(b,F(b,b))
  t = fun (suc (suc (suc zero)))
        (fun (suc zero) []
        ∷ fun (suc (suc zero)) (fun (suc zero) [] ∷ fun (suc zero) [] ∷ [])
        ∷ [])

  s→*t : (R12 ⋆) s t
  s→*t = Rax (zero ,, refl)
      ,⋆ (Rfun (suc (suc (suc zero))) (b ∷ b ∷ []) (suc zero) b→fbb refl refl ,⋆ ε⋆)
    where
      b : Terms ⊥
      b = fun (suc zero) []

      fbb : Terms ⊥
      fbb = fun (suc (suc zero)) (b ∷ b ∷ [])

      b→fbb : R12 b fbb
      b→fbb = Rax ((suc zero) ,, refl)



module Example-aa where
    -- a -> a 
  -- Signature with one constant symbol a : 0-ary function
  S : Signature
  S = Sig (Fin 1) ar (λ {x} {y} → fdecFin x y ) where
    ar : Fin 1 → ℕ 
    ar zero = 0 -- a 


  open Signature S
  open Substitution S

  lhs-aa : Pattern  0 -- a 
  lhs-aa = funp zero []

  rhs-aa : Terms (Fin 0)
  rhs-aa = fun zero []

  rule-aa : RRule 
  rule-aa = RR 0 lhs-aa rhs-aa

  rules-aa : Fin 1 → RRule 
  rules-aa zero = rule-aa

  Raa : ∀ {V} → 𝓡 (Terms V)
  Raa {V} = GeneralTRS.InScope.R  {RuleIdx = Fin 1} rules-aa V

  Raa⊥ : 𝓡 (Terms ⊥)
  Raa⊥ = Raa {V = ⊥}
  -- showing this example is locally SM
  open LocalProperties {A = Terms ⊥} {R = Raa⊥}

  a : Terms ⊥
  a = fun zero []

  a→a : Raa a a
  a→a = Rax (zero ,, refl)

  a-step-id : ∀ {y} → Raa⊥ a y → y ≡ a
  a-step-id (Rax (zero ,, refl)) = refl
  a-step-id (Rfun .zero .[] () r refl refl)

  a→*a-id : ∀ {y} → (Raa⊥ ⋆) a y → y ≡ a
  a→*a-id ε⋆ = refl
  a→*a-id (Rxy ,⋆ R*xy) rewrite a-step-id Rxy = a→*a-id R*xy

  a∈MF : MF a
  a∈MF y R*ay rewrite a→*a-id R*ay = ε⋆

  a∈SM : SM a
  a∈SM = MF⊆SM a a∈MF

module Example-bubble where
  -- bubble-sort style swap:
  -- cons(x, cons(y, z)) -> cons(y, cons(x, z))

  S : Signature
  S = Sig (Fin 1) ar (λ {x} {y} → fdecFin x y) where
    ar : Fin 1 → ℕ
    ar zero = 2 -- cons

  open Signature S
  open Substitution S

  lhs-swap : Pattern 3 -- cons(x, cons(y, z))
  lhs-swap = funp zero (Px ∷ Pyz ∷ []) where
    Px : Σ-syntax ℕ Pattern
    Px = 1 ,, hole

    Py : Σ-syntax ℕ Pattern
    Py = 1 ,, hole

    Pz : Σ-syntax ℕ Pattern
    Pz = 1 ,, hole

    Pyz : Σ-syntax ℕ Pattern
    Pyz = 2 ,, funp zero (Py ∷ Pz ∷ [])
  
  rhs-swap : Terms (Fin 3) -- cons(y, cons(x, z))
  rhs-swap = fun zero
    (var (suc zero) ∷ fun zero (var zero ∷ var (suc (suc zero)) ∷ []) ∷ [])

  rule-swap : RRule
  rule-swap = RR 3 lhs-swap rhs-swap

  rules-swap : Fin 1 → RRule
  rules-swap zero = rule-swap

  Rswap : ∀ {V} → 𝓡 (Terms V)
  Rswap {V} = GeneralTRS.InScope.R {RuleIdx = Fin 1} rules-swap V

  t₁ : Terms (Fin 3)
  t₁ = fun zero (var zero ∷ fun zero (var (suc zero) ∷ var (suc (suc zero)) ∷ []) ∷ [])

  t₂ : Terms (Fin 3)
  t₂ = fun zero (var (suc zero) ∷ fun zero (var zero ∷ var (suc (suc zero)) ∷ []) ∷ [])

  t₁→t₂ : Rswap t₁ t₂
  t₁→t₂ = Rax (zero ,, refl)

module Example-NewmanCandidatev2 where

  pattern aS = zero 
  pattern bS = suc zero 
  pattern pS = suc (suc zero) 
  pattern fS = suc (suc (suc zero)) 
  pattern kS = suc (suc (suc (suc zero)))

  -- Rules:
  --   p(a) -> p(b)
  --   p(b) -> p(a)
  --   f(p(a), p(a)) -> k
  --   f(p(b), p(b)) -> k

  S : Signature
  S = Sig (Fin 5) ar (λ {x} {y} → fdecFin x y) where
    ar : Fin 5 → ℕ
    ar aS = 0 -- a
    ar bS = 0 -- b
    ar pS = 1 -- p
    ar fS = 2 -- f
    ar kS = 0 -- k

  open Signature 
  open Substitution 

  lhs₁ : Pattern S 0
  lhs₁ = funp pS ((0 ,, funp aS []) ∷ [])

  rhs₁ : Terms S (Fin 0)
  rhs₁ = funp→term where
    funp→term : Terms S (Fin 0)
    funp→term = fun pS (fun bS [] ∷ [])

  lhs₂ : Pattern S 0 
  lhs₂ = funp pS ((0 ,, funp bS []) ∷ [])

  rhs₂ : Terms S (Fin 0)
  rhs₂ = fun pS (fun aS [] ∷ [])

  lhs₃ : Pattern S 0
  lhs₃ = funp fS ((0 ,, funp pS ((0 ,, funp aS []) ∷ []))
               ∷ (0 ,, funp pS ((0 ,, funp aS []) ∷ []))
               ∷ [])

  rhs₃ : Terms S (Fin 0)
  rhs₃ = fun kS []

  lhs₄ : Pattern S 0
  lhs₄ = funp fS ((0 ,, funp pS ((0 ,, funp bS []) ∷ []))
               ∷ (0 ,, funp pS ((0 ,, funp bS []) ∷ []))
               ∷ [])

  rhs₄ : Terms S (Fin 0)
  rhs₄ = fun kS []

  r₁ : RRule S
  r₁ = RR 0 lhs₁ rhs₁

  r₂ : RRule S
  r₂ = RR 0 lhs₂ rhs₂

  r₃ : RRule S
  r₃ = RR 0 lhs₃ rhs₃

  r₄ : RRule S
  r₄ = RR 0 lhs₄ rhs₄

  rules : Fin 4 → RRule S
  rules zero = r₁
  rules (suc zero) = r₂
  rules (suc (suc zero)) = r₃
  rules (suc (suc (suc zero))) = r₄

  Rnc : ∀ {V} → 𝓡 (Terms S V)
  Rnc {V} = GeneralTRS.InScope.R S {RuleIdx = Fin 4} rules V

  open LocalProperties
  
  {- Plan: 
  -- a,b,k are normal forms 
  -- p(a), p(b) are minimal forms 
  -- the rhs of each rule results in one of the above
  -- f(p(a),p(b)) -> f(p(a),p(a)) -> k 
  -- For p, need lemma: t ->⋆ a, then t = a, also if t ->⋆ b, then t = b
  --
  -- Needed lemmas:
  -- p(p(t)) ->⋆ p(u) ⇒ p(t) → u 
  -- p(f(t1,t2)) ->⋆ p(u) ⇒ f(t1,t2) → u
  -}

  p-lemma-1 : ∀ {V} (t : Terms S V) (u : Terms S V) 
                → Rnc (fun pS (fun pS (t ∷ []) ∷ [])) u 
                → Σ[ v ∈ Terms S V ] ((u ≡ fun pS (v ∷ [])) × Rnc (fun pS (t ∷ [])) v)
  p-lemma-1 t u (Substitution.Rax (suc (suc (suc zero)) ,, ()))
  p-lemma-1 t u (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))
  p-lemma-1 t u (Substitution.Rfun (suc (suc zero)) (v ∷ []) zero {u = w} ppt→u refl refl) 
    = w ,, refl , ppt→u

  p-lemma-1* : ∀ {V} (t : Terms S V) (u : Terms S V) 
                → (Rnc ⋆) (fun pS (fun pS (t ∷ []) ∷ [])) u 
                → Σ[ v ∈ Terms S V ] ((u ≡ fun pS (v ∷ [])) × (Rnc ⋆) (fun pS (t ∷ [])) v)
   
  p-lemma-1* t u ε⋆ = fun pS (t ∷ []) ,, refl , ε⋆
  p-lemma-1* t u (_,⋆_ {y = s} Rts R*su) 
    with p-lemma-1 t s Rts 
  ... | w ,, refl , pt→w 
    with t | pt→w 
  ... | var x | Substitution.Rax (fS ,, ())
  ... | var x | Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁)
  ... | Signature.fun aS [] | Substitution.Rax (aS ,, refl) = f (p-lemma-1* (fun bS []) u R*su)
    where f : _ → Σ[ v ∈ Terms S _ ] ((u ≡ fun pS (v ∷ [])) × (Rnc ⋆) (fun pS ((fun aS []) ∷ [])) v)
          f (z ,, refl , pb→z) = z ,, refl , (Rax (zero ,, refl) ,⋆ pb→z)
  ... | Signature.fun aS [] | Substitution.Rax (fS ,, ())
  ... | Signature.fun bS [] | Substitution.Rax (bS ,, refl) = f (p-lemma-1* (fun aS []) u R*su)
    where f : _ → Σ[ v ∈ Terms S _ ] ((u ≡ fun pS (v ∷ [])) × (Rnc ⋆) (fun pS ((fun bS []) ∷ [])) v)
          f (z ,, refl , pa→z) = z ,, refl , (Rax (suc zero ,, refl) ,⋆ pa→z)
  ... | Signature.fun bS [] | Substitution.Rax (fS ,, ())
  ... | Signature.fun bS [] | Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁)
  ... | fun pS (t' ∷ []) | Substitution.Rax (fS ,, ())
  ... | Signature.fun fS _ | Substitution.Rax (fS ,, ())
  ... | Signature.fun fS _ | Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁)
  ... | Signature.fun kS x | Substitution.Rax (fS ,, ())
  ... | Signature.fun kS x | Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁)
  ... | x | Substitution.Rfun .pS (t' ∷ []) zero {u = y} Rxy refl refl 
    with p-lemma-1* y u R*su 
  ... | z ,, refl , py→z  = z ,, refl , (Rfun pS (x ∷ []) zero Rxy refl refl ,⋆ py→z) 
  

  -- p(f(t1,t2)) -> p(u) ⇒ f(t1,t2) → u
  p-lemma-2 : ∀ {V} (t1 t2 u : Terms S V)
                → Rnc (fun pS (fun fS (t1 ∷ t2 ∷ []) ∷ [])) u 
                → Σ[ v ∈ Terms S V ] ((u ≡ fun pS (v ∷ [])) × (Rnc (fun fS (t1 ∷ t2 ∷ [])) v))
  p-lemma-2 t1 t2 u (Substitution.Rax (suc (suc (suc zero)) ,, ()))
  p-lemma-2 t1 t2 u (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))
  p-lemma-2 t1 t2 u (Substitution.Rfun f ts zero {u = w} Rtu refl refl) = w ,, refl , Rtu

  p-lemma-2* : ∀ {V} (t1 t2 : Terms S V) (u : Terms S V)
    → (Rnc ⋆) (fun pS (fun fS (t1 ∷ t2 ∷ []) ∷ [])) u
    → Σ[ v ∈ Terms S V ] ((u ≡ fun pS (v ∷ [])) × (Rnc ⋆) (fun fS (t1 ∷ t2 ∷ [])) v)
  p-lemma-2* t1 t2 u ε⋆ = fun fS (t1 ∷ t2 ∷ []) ,, refl , ε⋆
  p-lemma-2* t1 t2 u (Rxy ,⋆ R*yu) with p-lemma-2 t1 t2 _ Rxy
  ... | v ,, eq , f→v rewrite eq with p-lemma-2* t1 t2 u {! R*yu  !}
  ... | w ,, refl , f→*w = {!   !} -- w ,, refl , (f→v ,⋆ f→*w)

  pa-step-shape : ∀ {V : Set} {u : Terms S V} → -- P(a) only reduces to P(b) in single step
    Rnc  (fun pS (fun aS [] ∷ [])) u →
    u ≡ fun pS (fun bS [] ∷ [])
  pa-step-shape (Rax (aS ,, refl)) = refl
  pa-step-shape (Rax (fS ,, ()))
  pa-step-shape (Rax (suc (suc (suc (suc ()))) ,, snd₁))
  pa-step-shape (Rfun pS (fun aS [] ∷ []) aS (Rax (fS ,, ())) x₁ x₂)
  pa-step-shape (Rfun pS (fun aS [] ∷ []) aS (Rax (suc (suc (suc (suc ()))) ,, snd₁)) x₁ x₂)
  pa-step-shape (Rfun pS (fun aS [] ∷ []) aS (Rfun f ts () x refl refl) refl refl)  

  pb-step-shape : ∀ {V : Set} {u : Terms S V} → -- P(b) only reduces to P(a) in single step
    Rnc  (fun pS (fun bS [] ∷ [])) u →
    u ≡ fun pS (fun aS [] ∷ [])
  pb-step-shape (Rax (bS ,, refl)) = refl
  pb-step-shape (Rax (fS ,, ()))
  pb-step-shape (Rax (suc (suc (suc (suc ()))) ,, snd₁))
  pb-step-shape (Rfun pS (fun bS [] ∷ []) aS (Rax (fS ,, ())) refl refl)
  pb-step-shape (Rfun pS (fun bS [] ∷ []) aS (Rax (suc (suc (suc (suc ()))) ,, snd₁)) refl refl)
  pb-step-shape (Rfun pS (fun bS [] ∷ []) aS (Rfun f ts () x refl refl) refl refl)

  pa-step-shape* : ∀ {V : Set} {u : Terms S V} → -- P(a) only reduces to P(b) or P(a) in multi step
    (Rnc ⋆)  (fun pS (fun aS [] ∷ [])) u →
    (u ≡ fun pS (fun bS [] ∷ [])) ⊔ (u ≡ fun pS (fun aS [] ∷ []))
  pb-step-shape* : ∀ {V : Set} {u : Terms S V} → -- P(b) only reduces to P(a) or P(b) in multi step
    (Rnc ⋆)  (fun pS (fun bS [] ∷ [])) u →
    (u ≡ fun pS (fun bS [] ∷ [])) ⊔ (u ≡ fun pS (fun aS [] ∷ []))
  
  pa-step-shape* ε⋆ = in2 refl
  pa-step-shape* (Rxy ,⋆ R*yu) rewrite pa-step-shape Rxy = pb-step-shape* R*yu
  pb-step-shape* ε⋆ = in1 refl
  pb-step-shape* (Rxy ,⋆ R*yu) rewrite pb-step-shape Rxy = pa-step-shape* R*yu 

  -- t ∈ MF → p(t) ∈ MF 
  p-lemma-3 :  ∀ {V} (t : Terms S V) → t ∈ MF {R = Rnc} → fun pS (t ∷ []) ∈ MF {R = Rnc}
  p-lemma-3 (Signature.var x) t∈MF u ε⋆ = ε⋆
  p-lemma-3 (Signature.var x) t∈MF u (Rxy ,⋆ R*yu) = ∅ (pvar-nostep Rxy)
    where
    pvar-nostep : ∀ {y} → (Rnc (fun pS (var x ∷ [])) y) → ⊥
    pvar-nostep (Substitution.Rax (aS ,, ()))
    pvar-nostep (Substitution.Rax (bS ,, ()))
    pvar-nostep (Substitution.Rax (pS ,, ()))
    pvar-nostep (Substitution.Rax (fS ,, ())) 
    pvar-nostep (Substitution.Rfun pS (var t ∷ ts) aS (Substitution.Rax (fS ,, ())) refl refl)
    pvar-nostep (Substitution.Rfun pS (var t ∷ ts) aS (Substitution.Rax (suc (suc (suc (suc ()))) ,, y)) refl refl)
  p-lemma-3 (fun aS []) t∈MF u t→*u with pa-step-shape* t→*u -- p(a) is mf 
  ... | in1 refl = Rax (bS ,, refl) ,⋆ ε⋆
  ... | in2 refl = t→*u
  p-lemma-3 (fun bS []) t∈MF u t→*u with pb-step-shape* t→*u -- p(b) is mf 
  ... | in1 refl = t→*u
  ... | in2 refl = Rax (aS ,, refl) ,⋆ ε⋆  
  p-lemma-3 {V} (Signature.fun pS (t ∷ [])) t∈MF u t→*u  
      with p-lemma-1* t u t→*u
  ... | w ,, refl , pt→w with t∈MF w pt→w 
  ... | w→pt = Rfun-cong S rules V pS (w ∷ []) (fun pS (t ∷ []) ∷ [] ) λ { aS → w→pt}
  p-lemma-3 (Signature.fun fS ts) t∈MF u ε⋆ = ε⋆        
  p-lemma-3 (Signature.fun fS ts) t∈MF u (Rxy ,⋆ R*yu) = {! !}  -- this one needs "p-lemma-2*"
  p-lemma-3 (fun kS []) t∈MF u ε⋆ = ε⋆                -- p(k) is nf
  p-lemma-3 (fun kS []) t∈MF u (Rxy ,⋆ R*yu) = ∅ (pk-nostep Rxy )
    where 
    pk-nostep : ∀ {V : Set} {y : Terms S V} → (Rnc (fun pS (fun kS [] ∷ [])) y) → ⊥
    pk-nostep (Rax (fS ,, ()))
    pk-nostep (Rax (suc (suc (suc (suc ()))) ,, snd₁))
    pk-nostep (Rfun pS ts aS (Rax (fS ,, ())) refl refl)
    pk-nostep (Rfun pS ts aS (Rax (suc (suc (suc (suc ()))) ,, snd₁)) refl refl)
    pk-nostep (Rfun pS ts aS (Rfun kS [] () x x₁ x₂) refl refl)
    pk-nostep (Rfun pS ts aS (Rfun (suc (suc (suc (suc (suc f))))) ts₁ j x () x₂) refl refl)

  RncIsSM : ∀ {V} → Rnc {V} isSM 
  RncIsSM (Signature.var x) = SMind (var x) impossible-step where
    impossible-step : ∀ y → Rnc (Signature.var x) y → SM y
    impossible-step y (Substitution.Rax (suc (suc (suc zero)) ,, ()))
    impossible-step y (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))

  RncIsSM (fun aS []) = SMind (fun aS []) impossible-step where -- a ∈ NF
    impossible-step : ∀ y → Rnc (fun aS []) y → SM y
    impossible-step y (Substitution.Rax (aS ,, ()))
    impossible-step y (Substitution.Rax (bS ,, ()))
    impossible-step y (Substitution.Rax (fS ,, ()))
    impossible-step y (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))
    impossible-step y (Substitution.Rfun aS [] () r refl refl)

  RncIsSM (fun bS []) = SMind (fun bS []) impossible-step where -- b ∈ NF
    impossible-step : ∀ y → Rnc (fun bS []) y → SM y
    impossible-step y (Substitution.Rax (aS ,, ()))
    impossible-step y (Substitution.Rax (bS ,, ()))
    impossible-step y (Substitution.Rax (fS ,, ()))
    impossible-step y (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))
    impossible-step y (Substitution.Rfun bS [] () r refl refl) 
  
  RncIsSM (Signature.fun pS (t ∷ [])) 
    with RncIsSM t 
  ... | MF⊆SM m t∈SM = MF⊆SM _ (p-lemma-3 t t∈SM)
  ... | SMind .t H = SMind _ t∈SM where 
    t∈SM : _ 
    t∈SM y (Substitution.Rax x) = {! x  !} -- p(a) or p(b), hence MF, and SM 
    t∈SM y (Substitution.Rfun (suc (suc zero)) (Signature.var x ∷ []) zero (Substitution.Rax (suc (suc (suc zero)) ,, ())) refl refl)
    t∈SM y (Substitution.Rfun (suc (suc zero)) (Signature.var x ∷ []) zero (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁)) refl refl)
    t∈SM y (Substitution.Rfun (suc (suc zero)) (Signature.fun f x ∷ []) zero t→y refl refl) 
      -- with p-lemma-1 
      = {! H _ t→y   !}
    
  RncIsSM (Signature.fun fS ts) = {! !} -- f 
  RncIsSM (fun kS []) = SMind (fun kS []) impossible-step where -- k ∈ NF
    impossible-step : ∀ y → Rnc (fun kS []) y → SM y
    impossible-step y (Substitution.Rax (aS ,, ()))
    impossible-step y (Substitution.Rax (bS ,, ()))
    impossible-step y (Substitution.Rax (fS ,, ()))
    impossible-step y (Substitution.Rax (suc (suc (suc (suc ()))) ,, snd₁))
    impossible-step y (Substitution.Rfun kS [] () r refl refl)   

  a : Terms S ⊥
  a = fun aS []

  b : Terms S ⊥
  b = fun bS []

  pa : Terms S ⊥
  pa = fun pS (a ∷ [])

  pb : Terms S ⊥
  pb = fun pS (b ∷ [])

  k : Terms S ⊥
  k = fun kS []

  faa : Terms S ⊥
  faa = fun fS (pa ∷ pa ∷ [])

  fba : Terms S ⊥
  fba = fun fS (pb ∷ pa ∷ [])

  p-a→p-b : Rnc pa pb
  p-a→p-b = Rax (zero ,, refl)

  p-b→p-a : Rnc pb pa
  p-b→p-a = Rax ((suc zero) ,, refl)

  faa→k : Rnc faa k
  faa→k = Rax ((suc (suc zero)) ,, refl)

  faa→fba : Rnc faa fba
  faa→fba = Rfun fS (pa ∷ pa ∷ []) zero p-a→p-b refl refl
 