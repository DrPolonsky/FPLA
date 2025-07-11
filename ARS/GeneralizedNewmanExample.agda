-- Generalized Newman Example in Agda
-- SN fails, SM and WCR hold, so CR follows via generalized Newman's Lemma

module ARS.GeneralizedNewmanExample where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Decidable)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
∃ = Σ

------------------------------------------------------------------------
-- Define Term Language
------------------------------------------------------------------------
data Term : Set where
  loop  : Term
  wrap  : Term → Term
  base  : Term

------------------------------------------------------------------------
-- Define Rewrite Relation → : Term → Term → Set
------------------------------------------------------------------------

infix 40 _↦_
data _↦_ : Term → Term → Set where
  loopStep : loop ↦ loop
  escape   : (t : Term) → wrap loop ↦ wrap t
  unwrap   : (t : Term) → wrap t ↦ t

-- Reflexive-transitive closure (→*)
infix 40 _↦*_ 
data _↦*_ : Term → Term → Set where
  refl : ∀ {a} → a ↦* a
  step : ∀ {a b c} → a ↦ b → b ↦* c → a ↦* c

------------------------------------------------------------------------
-- SN Fails: Loop reduces to itself infinitely
------------------------------------------------------------------------

¬SN : ¬ (∀ x → ∃ λ y → x ↦* y ∧ ¬ (∃ λ z → y ↦ z))
¬SN sn = let
  p = sn loop
 in
   let (_ , (_ , red)) = p in
   red (wrap loop , escape loop)

------------------------------------------------------------------------
-- Define Minimal Forms (no forward reduction)
------------------------------------------------------------------------

isNF : Term → Set
isNF t = ¬ (∃ λ t' → t ↦ t')

------------------------------------------------------------------------
-- Strong Minimalization (SM): defined inductively
------------------------------------------------------------------------
data SM : Term → Set where
  smNF : ∀ {t} → isNF t → SM t
  smStep : ∀ {t} → (∀ t' → t ↦ t' → SM t') → SM t

-- Prove SM holds for all terms
smAll : (t : Term) → SM t
smAll loop = smStep (λ t' step → smAll loop)
smAll (wrap loop) = smStep (λ t' step →
  case step of λ
    { escape _ → smAll (wrap base)
    ; unwrap _ → smAll base })
smAll (wrap t) = smStep (λ t' step → smAll t)
smAll base = smNF (λ { (t , ()) })

------------------------------------------------------------------------
-- Weak Confluence (WCR)
------------------------------------------------------------------------

WCR : Set
WCR = ∀ a b c → a ↦ b → a ↦ c → ∃ λ d → b ↦* d × c ↦* d

wcr : WCR
wcr loop loop loop loopStep loopStep = ⟨ loop , refl , refl ⟩
wcr (wrap loop) (wrap _) (wrap _) (escape _) (unwrap _) = ⟨ base , refl , step (unwrap _) refl ⟩
wcr (wrap t) (wrap t1) (wrap t2) (unwrap _) (unwrap _) = ⟨ t , refl , refl ⟩
wcr base _ _ p q = ⟨ base , refl , refl ⟩

------------------------------------------------------------------------
-- Confluence via Generalized Newman's Lemma
------------------------------------------------------------------------

CR : Set
CR = ∀ a b c → a ↦* b → a ↦* c → ∃ λ d → b ↦* d × c ↦* d

-- Placeholder proof using SM ∧ WCR → CR
generalizedNewman : (∀ t → SM t) → WCR → CR
generalizedNewman = {!!} -- You can fill this using your own lemma
