open import Logic hiding (_×_)
open import Classical
open import Lifting
-- open import Datatypes using (ℕ)
open import Relations.Decidable
open import Data.Vec
open import Data.Fin renaming (_+_ to _Fin+_)
open import Data.Product using (_×_)
open import Predicates
open import Agda.Builtin.Nat renaming (Nat to ℕ)

module TRS.TRS-Base where

record Signature : Set₁ where
  constructor Sig
  field
    Fs : Set
    Ar : Fs → ℕ
    FsDec : (_≡_ {A = Fs} isDec)

  data Terms (V : Set) : Set where
    var : V → Terms V
    fun : ∀ (f : Fs) → Vec (Terms V) (Ar f) → Terms V

-- open Signature
module Substitution (S : Signature) where
  open Signature S

  {-# TERMINATING #-}
  subst : ∀ {V W} → Terms V → (V → Terms W) → Terms W
  subst (var x) ts = ts x
  subst (fun f args) ts = fun f (map (λ s → subst s ts) args)
      -- f(a1,..,ak) [vs := ts] = f(a1[vs:=ts],...,ak[vk:=ts])

  data Pattern : ℕ → Set where
    hole : Pattern 1
    funp : ∀ (f : Fs) → (W : Vec (Σ[ k ∈ ℕ ] Pattern k) (Ar f))
             → Pattern (sum (map fst W))
             -- f(g([],a),f([],[])) : Pattern 3, where f = f, W = [1,2],
             -- ps = λ { o → g([],a); io → f([],[]) }


  substPattern :  ∀ {V} {h : ℕ} (p : Pattern h) → Vec (Terms V) h → Terms V 
  substPatterns : ∀ {V} {n : ℕ} (W : Vec (Σ-syntax ℕ Pattern) n) (ts : Vec (Terms V) (sum (map (λ r → fst r) W)))
                  → Vec (Terms V) n
  substPattern hole (t ∷ []) = t
  substPattern (funp f W) ts = fun f (substPatterns W ts)
  substPatterns {V} {n = 0F} [] [] = []
  substPatterns {V} {n = suc n} ((h ,, p) ∷ W) ts 
    with sum (map fst W) in e 
  ... | m 
    with splitAt h ts 
  ... | tsh ,, tsm ,, ts=tsh++tsm = substPattern p tsh ∷ substPatterns W (transp _ (~ e) tsm)

  record Match_With_ {V : Set} {h : ℕ} (t : Terms V) (p : Pattern h) : Set  where 
    constructor match 
    field 
      sub : Vec (Terms V) h 
      sub-id : t ≡ substPattern p sub 

  matchDec : ∀ {V : Set} {h : ℕ} (p : Pattern h) (t : Terms V) → EM (Match t With p)
  matchDec {V} {h} hole t = in1 (match (t ∷ []) refl)
  matchDec {V} {h} (funp f W) t = {!    !}




{-
  record RRule : Set where
    constructor RR
    field
      holes : ℕ
      lhs : Pattern holes
      rhs : Terms (Fin holes)
    -- This encodes left-linear first-order TRSs
  open RRule

  -- foldSum : ∀ {A : Set} {B : ℕ → Set} {n} (W : Vec ℕ n) (xs : Vec A n)
  --             → (b0 : B zero) → (fn : Fin n → B (toℕ fn) → B (suc n))
  --             → B (sum W)
  -- foldSum {A} {B} {0F} [] [] b0 fn = b0
  -- foldSum {A} {B} {suc n} W xs b0 fn = {!  !}
  
  finElimCoprod : ∀ {A : Set} {m n} → (Fin m → A) → (Fin n → A) → Fin (m + n) → A 
  finElimCoprod {A} {0F} {n} fm fn x = fn x
  finElimCoprod {A} {suc m} {n} fm fn 0F = fm 0F
  finElimCoprod {A} {suc m} {n} fm fn (suc x) = finElimCoprod {m = m} fm' fn x 
    where fm' = λ j → fm (suc j)

  -- foldLemma : 

  open import Function.Core

  sumLemma : ∀ {n} {A B C : Set} {D : B → Set} (W : Vec A n) (ts : Vec C n)
             → (bc1 : B) → (bc2 : D bc1)
             → (rf1 : A → B → B)
             → (rf2 : ∀ (pc : Fin n × C) → (q : Σ[ y ∈ B ] (D y)) → D (rf1 (lookup W (fst pc)) (fst q)))
             → (xs : Vec (Fin n × C) n) → (∀ (i : Fin n) → fst (lookup xs i) ≡ i)
                                → (∀ (i : Fin n) → snd (lookup xs i) ≡ lookup ts i)
             →       foldr (λ _ → B) rf1 bc1 W  
              ≡ fst (foldr (λ _ → Σ[ y ∈ B ] (D y)) 
                           (λ {(p ,, c) q → (rf1 (lookup W p) (fst q) ,, rf2 (p ,, c) q) })
                           (bc1 ,, bc2)
                           xs)
  sumLemma {0F} {A} {B} {C} {D} [] [] bc1 bc2 rf1 rf2 [] H1 H2 = refl
  sumLemma {suc n} {A} {B} {C} {D} (w ∷ W) (t ∷ ts) bc1 bc2 rf1 rf2 (x ∷ xs) H1 H2 
    with sumLemma {n} {A} {B} {C} {D} W ts bc1 bc2 rf1 ? xs ? ? 
  ... | e = {! cong (rf1 w) !}
  --   with sumLemma {n} {A} {B} {C} {D} W ts bc1 bc2 rf1 {!   !}
  -- ... | e = cong (rf1 w) (e ! {!  !})  
  {-        = cong (rf1 w) eqTail where 
    eqTail : _ 
    eqTail with (foldr (λ _ → Σ-syntax B D) (λ { (p ,, c) q → rf1 (lookup (w ∷ W) p) (fst q) ,, rf2 (p ,, c) q })
                       (bc1 ,, bc2) (zipWith _,,_ (tabulate (id Function.Core.∘ suc)) ts)) in e1 
    ... | (b ,, d) = {!  !} -- sumLemma {n} {A} {B} {C} {D} W ts bc1 bc2 rf1 ? 
    -}

  match : ∀ {V : Set} {h : ℕ} (p : Pattern h) → Terms V → ↑ (Fin h → Terms V)
  match hole t = i (λ _ → t )
  match (funp f W ps) (var x) = o
  match {V} (funp f W ps) (fun g ts) with FsDec {f} {g}
  ... | in2 no = o
  ... | in1 refl = result where 
    A = Fin (Ar f) × Terms V
    B = λ _ → Σ[ k ∈ ℕ ] (↑ (Fin k → Terms V))
    op : _
    op (pi ,, ti) (si ,, y) = lookup W pi + si 
                  ,, io (λ σ → io (λ τi → i (finElimCoprod τi σ)) o (match (ps pi) ti)) o y
    b0 = (0 ,, i (λ {()}))
    xs =  zip (allFin (Ar f)) ts
    res = foldr B op b0 xs
    fst=sum : sum W ≡ fst res
    fst=sum = ? 
    -- fst=sum = sumLemma W ts 0 (snd b0) _+_ (λ pt sy → snd (op pt sy))
    result = transp (λ k → ↑ (Fin k → Terms V)) (~ fst=sum) (snd res)

  {- match f([x],g(a,[y])) f(f(a,b),g(a,g(b,b))) = i σ, where
           σ = λ {[x] → f(a,b); [y] → g(b,b)}     -}

  module GeneralTRS {RuleIdx : Set} (Rules : RuleIdx → RRule) where

    module InScope (V : Set) where

      applyRule : RuleIdx → Terms V → Terms V → Set
      applyRule ri s t with match (lhs (Rules ri)) s
      ... | i σ = t ≡ subst (rhs (Rules ri)) σ
      ... | o = ⊥

      -- The root relation AKA contraction of a rewrite rule
      R₀ : 𝓡 (Terms V)
      R₀ s t = Σ[ ri ∈ RuleIdx ] (applyRule ri s t)

      data R : 𝓡 (Terms V) where
        Rax : ∀ {s t} → R₀ s t → R s t
        Rfun : ∀ (f : Fs) (ts : Vec (Terms V) (Ar f)) (j : Fin (Ar f)) {s t tj u : Terms V}
                 → R tj u → s ≡ fun f ts → t ≡ fun f (ts [ j ]≔ u) → R s t

open Substitution
open import Relation.Nullary

module Example1 where
-- p1: F(a,x) -> G(x,x)
-- p2: b -> F(b,b)

S : Signature
S = Sig (Fin 4) ar (λ {x} {y} → fdec x y )  where
  ar : _
  ar 0F = 0 -- a
  ar 1F = 0 -- b
  ar 2F = 2 -- F
  ar 3F = 2 -- G
  fdec : ∀ x y → EM (x ≡ y)
  fdec x y with x ≟ y
  ... | yes p = in1 p
  ... | no ¬p = in2 (λ x=y → ⊥-elim (¬p x=y) ) where open import Data.Empty

open Signature S

p1lhs : Pattern S 1 -- F(a,x)
p1lhs = funp 2F (0 ∷ 1 ∷ []) ps where
  ps : _
  ps 0F = funp 0F [] (λ {()})
  ps 1F = hole
p2lhs : Pattern S 0 -- b
p2lhs = funp 1F [] (λ {()})

p1 : RRule S
p1 = RR 1 p1lhs (fun 3F (var 0F ∷ var 0F ∷ []) )

p2 : RRule S
p2 = RR 0 p2lhs (fun 2F (b ∷ b ∷ []) )
  where b = fun 1F []

p12 : Fin 2 → RRule S
p12 0F = p1
p12 1F = p2

R12 : ∀ V → 𝓡 (Terms V)
R12 V = GeneralTRS.InScope.R S {RuleIdx = Fin 2} p12 V
  -- data RootRed ∀ {V}



-}
   -- data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
   --   here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
   --   there : ∀ {n} {i} {x y} {xs : Vec A n}
   --           (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
