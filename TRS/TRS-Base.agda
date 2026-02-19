open import Logic hiding (_×_)
open import Classical
open import Lifting
-- open import Datatypes using (ℕ)
open import Relations.Decidable
open import Data.Vec 
open import Data.Vec.Properties
open import Data.Fin renaming (_+_ to _Fin+_) hiding (splitAt)
open import Data.Product using (_×_)
open import Predicates
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Relations.ClosureOperators

module TRS.TRS-Base where

record Signature : Set₁ where
  constructor Sig
  field
    Fs : Set 
    Ar : Fs → ℕ
    FsDec : dec≡ Fs

  data  Terms (V : Set) : Set where
    var : V → Terms V
    fun : ∀ (f : Fs) → Vec (Terms V) (Ar f) → Terms V

  fun≡inv : ∀ {V} (f : Fs) (s t : Vec (Terms V) (Ar f)) → fun f s ≡ fun f t → s ≡ t 
  fun≡inv f s t refl = refl 

  lookup≡ : ∀ {V : Set} {n} (xs ys : Vec V n) → (∀ j → lookup xs j ≡ lookup ys j) → xs ≡ ys
  lookup≡ {V} {zero} [] [] H = refl
  lookup≡ {V} {suc n} (x ∷ xs) (y ∷ ys) H = cong2 _∷_ (H zero) (lookup≡ xs ys λ j → H (suc j)) 

  dec≡Terms : ∀ {V} → dec≡ V → dec≡ (Terms V) 
  dec≡TermsVec : ∀ {V} {n} → dec≡ V → dec≡ (Vec (Terms V) n)

  dec≡Terms dV (var x) (var y) = case (λ { refl → in1 refl }) (λ x≠y → in2 λ { refl → x≠y refl }) (dV x y)
  dec≡Terms dV (var x) (fun f x₁) = in2 λ { () }
  dec≡Terms dV (fun f x) (var x₁) = in2 λ { () }
  dec≡Terms dV (fun f ts) (fun g us)
    with FsDec f g
  ... | in2 f≠g = in2 λ { refl → f≠g refl } 
  ... | in1 refl 
    with dec≡TermsVec dV ts us
  ... | in1 yes = in1 (cong (fun f) yes)
  ... | in2 no  = in2 λ { refl → no refl }
  
  dec≡TermsVec {n = zero} dV  [] [] = in1 refl 
  dec≡TermsVec {n = suc k} dV (x ∷ xs) (y ∷ ys) 
    with dec≡Terms dV x y | dec≡TermsVec dV xs ys 
  ... | in1 yes1 | in1 yes2 = in1 (cong2 _∷_ yes1 yes2)
  ... | in1 yes1 | in2 no2  = in2 λ { refl → no2 refl } 
  ... | in2 no1  | _        = in2 λ { refl → no1 refl }

-- open Signature
module Substitution (S : Signature) where
  open Signature S

  {-# TERMINATING #-}
  subst : ∀ {V W} → Terms V → (V → Terms W) → Terms W
  subst (var x) ts = ts x
  subst (fun f args) ts = fun f (map (λ s → subst s ts) args)

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

  splitAt≡ : ∀ {V : Set} {m n : ℕ} (h : Vec V m) (t : Vec V n) → 
    ((h , t) ≡ (fst (splitAt m (h ++ t)) , fst (snd (splitAt m (h ++ t)))))
  splitAt≡ {V} {0F} {n} [] t = refl 
  splitAt≡ {V} {suc m} {n} (x ∷ h) t 
    with splitAt (suc m) (x ∷ h ++ t) 
  ... | y ∷ ys ,, ts ,, eq 
    with _,_inj (splitAt≡ h t)
  ... | e3 , e4 = cong2 _,_ (cong (_∷_ x) e3) e4

  subPat≡ : ∀ {V} {n : ℕ} (W : Vec (Σ-syntax ℕ Pattern) n) 
                  (ts : Vec (Terms V) (sum (map (λ r → fst r) W))) (us : Vec (Terms V) n)
                  → substPatterns W ts ≡ us 
                  → ∀ j → Σ[ tj ∈ Vec (Terms V) (fst (lookup W j)) ] 
                            (lookup us j ≡ substPattern (snd (lookup W j)) tj)
  subPat≡ {n} (_∷_ {m} (k ,, p) W) ts us refl zero with splitAt k ts 
  ... | tsk ,, tsl ,, e2 = tsk ,, refl
  subPat≡ {n} (_∷_ {m} (k ,, p) W) ts (u ∷ us) refl (suc j) 
    = subPat≡ W (fst (snd (splitAt k ts))) us (cong (substPatterns W) refl) j 

  subPat≡inv : ∀ {V} {n : ℕ} (W : Vec (Σ-syntax ℕ Pattern) n) (us : Vec (Terms V) n)
                  → (∀ j → Σ[ tj ∈ Vec (Terms V) (fst (lookup W j)) ] 
                            (lookup us j ≡ substPattern (snd (lookup W j)) tj) )
                  → Σ[ ts ∈ Vec (Terms V) (sum (map (λ r → fst r) W)) ] (us ≡ substPatterns W ts)
  subPat≡inv {V} {0F} [] [] H = [] ,, refl
  subPat≡inv {V} {suc n} ((h ,, p) ∷ W) (u ∷ us) H 
    with H zero | subPat≡inv {V} {n} W us (λ j → H (suc j) ) 
  ... | th ,, refl | tls ,, refl 
    with splitAt≡ th tls 
  ... | c 
    = th ++ tls ,, cong2 _∷_ (cong (substPattern p) e1) (cong (substPatterns W) e2)
      where e1 = pr1 (_,_inj (splitAt≡ th tls))
            e2 = pr2 (_,_inj (splitAt≡ th tls))

  Match_To_ : ∀ {V : Set} {h : ℕ} (t : Terms V) (p : Pattern h) → Set 
  Match_To_ {V} {h} t p = Σ[ sub ∈ Vec (Terms V) h ] (t ≡ substPattern p sub)

  matchDec : ∀ {V : Set} {h : ℕ} (p : Pattern h) (t : Terms V) → EM (Match t To p)
  matchDecs : ∀ {V : Set} {n : ℕ} (ps : Vec (Σ-syntax ℕ Pattern) n) (ts : Vec (Terms V) n)
    → (∀ (i : Fin n) → Match (lookup ts i) To snd (lookup ps i))
       ⊔ Σ[ i ∈ Fin n ] (¬ Match (lookup ts i) To snd (lookup ps i))
  matchDec {V} {h} hole t = in1 (t ∷ [] ,, refl)
  matchDec {V} {h} (funp f W) (var x)  = in2 λ {(_ ,, ())}
  matchDec {V} {h} (funp f W) (fun g ts) with FsDec f g
  ... | in2 no = in2 λ {(s ,, refl) → no refl}
  ... | in1 refl -- = {!  !}
    with matchDecs {n = Ar f} W ts
  ... | in1 yes with subPat≡inv W ts yes 
  ... | sub ,, eq = in1 (sub ,, cong (fun f) eq)
  matchDec {V} {h} (funp f W) (fun g ts) | in1 refl | in2 (j ,, q) 
    with lookup W j in e1 | lookup ts j in e2
  ... | (k ,, p) | tj =
    in2 c where 
      c : _ 
      c (nts ,, e3) with fun≡inv f ts (substPatterns W nts) e3 
      ... | e4 
        with subPat≡ W nts ts (~ e4) j 
      ... | (sub ,, e5) rewrite e1 = q (sub ,, (e2 ~! e5)) 

  matchDecs {V} {0F} [] [] = in1 λ { () }
  matchDecs {V} {suc n} ((k ,, p) ∷ ps) (t ∷ ts) 
    with matchDec p t 
  ... | in2 no  = in2 (zero ,, no)
  ... | in1 qQ
    with matchDecs ps ts 
  ... | in2 (j ,, J) = in2 (suc j ,, J)
  ... | in1 yes = in1 YES 
    where YES : _ 
          YES zero = qQ
          YES (suc k) = yes k 

  -- This defines the type of left-linear Term Rewriting Systems
  record RRule : Set where
    constructor RR
    field
      holes : ℕ
      lhs : Pattern holes
      rhs : Terms (Fin holes)
    -- This encodes left-linear first-order TRSs
  open RRule
 
  module GeneralTRS {RuleIdx : Set} (Rules : RuleIdx → RRule) where

    module GTRSScope {V : Set} where

      applyRule : RuleIdx → Terms V → Terms V → Set
      applyRule ri s t with matchDec (lhs (Rules ri)) s
      ... | in1 (sub ,, lhs[sub]=s) = t ≡ subst (rhs (Rules ri)) (lookup sub)
      ... | in2 no = ⊥

      -- applyRuleInv : ∀ (ri : RuleIdx) → ∀ (s t : Terms V) → applyRule ri s t 
      --   → Σ[ sub ∈ _ ] ((_) × t ≡ subst (rhs (Rules ri)) (lookup sub))
      -- applyRuleInv ri s t ar with matchDec (lhs (Rules ri)) s 
      -- ... | in1 (sub ,, lhs[sub]=s) = sub ,, lhs[sub]=s , ar
      -- ... | in2 x = ∅ ar 

      -- The root relation AKA contraction of a rewrite rule
      R₀ : 𝓡 (Terms V)
      R₀ s t = Σ[ ri ∈ RuleIdx ] (applyRule ri s t)

      data R : 𝓡 (Terms V) where
        Rax : ∀ {s t} → R₀ s t → R s t
        Rfun : ∀ (f : Fs) (ts : Vec (Terms V) (Ar f)) (j : Fin (Ar f)) {s t u : Terms V}
                 → R (lookup ts j) u → s ≡ fun f ts → t ≡ fun f (ts [ j ]≔ u) → R s t

    open GTRSScope public 
  -- open GeneralTRS public 

  -- Finite TRS 
  record FTRS {k : ℕ} : Set where 
    constructor ftrs 
    field 
      Rules : Fin k → RRule 

    open GeneralTRS Rules 
    module FTRSScope {V : Set} where 

      open import Agda.Builtin.List 
      open import Lists
      open import Relations.FinitelyBranching

      applyRules : ∀ (rs : List (Fin k)) (t : Terms V)
          → Σ[ us ∈ List (Terms V) ] (∀ u → u ∈List us ↔ List∃ (λ r → applyRule r t u) rs)
      applyRules [] t = [] ,, λ _ → (λ { () }) , λ { () }
      applyRules (r ∷ rs) t
        with applyRules rs t 
      ... | us ,, U+-
        with matchDec (lhs (Rules r)) t in eq
      ... | in1 (sub ,, refl)  = (subst (rhs (Rules r)) (lookup sub) ∷ us) 
        ,, λ u → (λ { (in1 refl) → in1 refl
                    ; (in2 down) → in2 (pr1 (U+- u) down) }) 
               , λ { (in1 refl) → in1 refl
                   ; (in2 down) → in2 (pr2 (U+- u) down) }
      ... | in2 no  = us 
        ,, λ u → (λ occ → in2 (pr1 (U+- u) occ))
               , λ { (in2 prf) → pr2 (U+- u) prf }

      Fin∈allFin : ∀ {m} (j : Fin m) → j ∈List toList (allFin m)
      Fin∈allFin zero = in1 refl
      Fin∈allFin {suc m} (suc j) = 
        in2 (transp (λ x → suc j ∈List toList x) (~ (tabulate-allFin suc)) 
                    (transp (λ x → suc j ∈List x) (~ (toList-map suc (allFin m)))
                    (map∈ suc j (toList (allFin m)) (Fin∈allFin j)) ))

      R₀isFBRel  : R₀ {V} isFBRel
      R₀isFBRel s 
        with applyRules (toList (allFin k)) s 
      ... | (us ,, US) = us ,, λ b 
        → (λ { (j ,, p) → pr2 (US b) (List∃intro _ (toList (allFin k)) j 
                (Fin∈allFin j , p)) } ) 
              , λ b∈us → Case (List∃elim _ (toList (allFin k)) (pr1 (US b) b∈us)) 
                              λ p q →  p ,, pr2 q 
      RisFBRel  : R isFBRel
      RisFBRels : ∀ {n} (ts : Vec (Terms V) n) → ∀ j → FBRel R (lookup ts j)
      RisFBRel  t = {!   !}
      RisFBRels (t ∷ ts) zero = RisFBRel t
      RisFBRels (t ∷ ts) (suc j) = RisFBRels ts j


open Substitution
open import Relation.Nullary


--    -- data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
--    --   here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
--    --   there : ∀ {n} {i} {x y} {xs : Vec A n}
--    --           (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

-- show that 
  -- \all XS ys.  \all f \all j in Ar f \to R (lookup XS j) (lookup ys j) 
  -- -> R (fun f XS) (fun f ys)
