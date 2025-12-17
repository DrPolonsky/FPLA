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
    funp : ∀ (f : Fs) → (W : Vec ℕ (Ar f))
             → (ps : ∀ (p : Fin (Ar f)) → Pattern (lookup W p))
             → Pattern (sum W)
             -- f(g([],a),f([],[])) : Pattern 3, where f = f, W = [1,2],
             -- ps = λ { o → g([],a); io → f([],[]) }
  
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

  sumLemma : ∀ {n} {A B C : Set} {D : B → Set} (W : Vec A n) (ts : Vec C n)
             → (rf1 : A → B → B) → (bc1 : B)
             → (rf2 : Fin n × C → (Σ[ y ∈ B ] (D y)) → (Σ[ y ∈ B ] (D y))) → (bc2 : D bc1)
             → (∀ (p : Fin n) (b : B) (c : C) (d : D b) → rf1 (lookup W p) b ≡ fst (rf2 (p ,, c) (b ,, d)))
             →  foldr (λ _ → B) rf1 bc1 W  
              ≡ fst (foldr (λ _ → Σ[ y ∈ B ] (D y)) rf2 (bc1 ,, bc2) (zip (allFin n) ts))
  sumLemma {0F} {A} {B} {C} {D} [] [] rf1 bc1 rf2 bc2 Heq = refl 
  sumLemma {suc n} {A} {B} {C} {D} (w ∷ W) (t ∷ ts) rf1 bc1 rf2 bc2 Heq 
    with foldr (λ _ → B) rf1 bc1 W in e1 
       | fst (foldr (λ _ → Σ[ y ∈ B ] (D y)) (λ { (p ,, c) → rf2 (suc p ,, c) })  (bc1 ,, bc2) (zip (allFin (n)) (ts))) in e2
  ... | b1 | b2 with rf2 (0F ,, t ) (foldr  (λ _ → Σ B D) (λ { (p ,, c) → rf2 (suc p ,, c) }) (bc1 ,, bc2) (zip (allFin n) ts)) in e3
  ... | b ,, d = {!  !} 
  -- ... | k with Heq 0F b1 {!  !}  {!  !}
  -- ... | c = {!   !}   
  --
  {-
    with sumLemma {n} {A} {B} {C} {D} W ts rf1 bc1 rf2' bc2 Heq' 
      where rf2' : _ 
            rf2' (p ,, c) bd = rf2 (suc p ,, c) bd
            Heq' : _ 
            Heq' p b c d = Heq (suc p) b c d 
  ... | e1 with (foldr (λ _ → Σ[ y ∈ B ] (D y)) rf2' (bc1 ,, bc2) (zip (allFin n) ts))
      where rf2' : _ 
            rf2' (p ,, c) bd = rf2 (suc p ,, c) bd
  ... | (b ,, d) with Heq 0F b t d
  -- ... | e2 = e2 ! cong fst (cong (rf2 (0F ,, t)) {!   !}) 
  ... | e2 = {!  !}  
  -}

  match : ∀ {V : Set} {h : ℕ} (p : Pattern h) → Terms V → ↑ (Fin h → Terms V)
  match hole t = i (λ _ → t )
  match (funp f W ps) (var x) = o
  match {V} (funp f W ps) (fun g ts) with FsDec {f} {g}
  ... | in2 no = o
  ... | in1 refl = result where 
    A = Fin (Ar f) × Terms V
    B = λ _ → Σ[ k ∈ ℕ ] (↑ (Fin k → Terms V))
    xs =  zip (allFin (Ar f)) ts
    op : _
    op (pi ,, ti) (si ,, o) = lookup W pi + si ,, o
    op (pi ,, ti) (si ,, i σ) with match (ps pi) ti 
    ... | o = lookup W pi + si ,, o
    ... | i τi = lookup W pi + si ,, i (finElimCoprod τi σ)
    b0 = (0 ,, i (λ {()}))
    res = foldr B op b0 xs
    e : _ 
    e p b c (i x) with match (ps p) c
    ... | o = refl
    ... | i tau = refl
    e p b c o = refl 
    fst=sum : sum W ≡ fst res
    fst=sum = sumLemma W ts _+_ 0 op (snd b0) e  
    result = transp (λ k → ↑ (Fin k → Terms V)) (~ fst=sum) (snd res)

{-  A = Fin (Ar f) × Terms V
    B = λ k → ↑ (Fin k → Terms V)
    n = Ar f
    xs =  zip (allFin (Ar f)) ts
    b0 : B 0 
    b0 = {!  !} 
    fn : Fin n → B n → B (suc n)
    fn pi o = o
    fn pi (i σ) = {!   !} 
    -- fn pi (i σ) with match (ps pi) (lookup ts pi)
    -- ... | o = o
    -- ... | i τ = i λ { 0F → {! τ  !}
    --                 ; (suc x) → σ x }
    result = foldSum {A} {B} {n} W xs b0 fn  
-}
{-    pts : (Vec (Fin (Ar f) × Terms V) (Ar f))
    pts = zip (allFin (Ar f)) ts
    pfun : _ 
    pfun (pi ,, ti) = match {h = lookup W pi} (ps pi) ti   
    mms = map pfun pts
    rf : _ 
    rf ni ti = match {h = ni} ps (?? ni
    zs = zipWith rf W ts
    B : ℕ → Set 
    B k = ↑ (Fin (sum W) → Terms V)
    W×ts = zip W ts 
    basecase = ?  
    recFun : _ 
    recFun = ? 
    res0 = (foldl B recFun basecase W×ts) 
    res5 = transp (λ k →  ↑ (Fin k → Terms V)) ? r
    result = ? -}

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




   -- data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
   --   here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
   --   there : ∀ {n} {i} {x y} {xs : Vec A n}
   --           (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
