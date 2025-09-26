-- This file for implications between those definitions which we are not including in our report (e.g. seq+)

isWFmin+→isWFind¬¬ : isWFmin+ → R isWFind¬¬ 
isWFmin+→isWFind¬¬ RisWF P Pind x ¬px with RisWF P ¬px
... | (y ,, ¬py , yind) = ¬py ((Pind y yind))

isWFmin+→isWFmin¬¬ : isWFmin+ → R isWFmin¬¬
isWFmin+→isWFmin¬¬ Rmin+ P {d} p ¬∃minP with Rmin+ (∁ P ) (λ x → x p)
... | (a ,, ¬¬Pa , aMin) = ¬¬Pa (λ pa → ¬∃minP ((a ,, pa , λ y Py Rya → aMin y Rya Py )) )

isWFmin+→isWFminDNE : isWFmin+ → R isWFminDNE
isWFmin+→isWFminDNE RisWFmin+ P ∁∁P⊆P a a∈P with RisWFmin+ (∁ P) (λ a∉P → a∉P a∈P)
... | x ,, ¬¬x∈P , xmin = x ,, ∁∁P⊆P x ¬¬x∈P , (λ y y∈P Ryx → xmin y Ryx y∈P)


-- -- A correct(?) but non-terminating proof.
  -- {-# TERMINATING #-}
  -- isWFseq→isWFacc : R isWFseq → R isWFacc
  -- isWFseq→isWFacc R∈WFs x = acc (λ y Ryx → isWFseq→isWFacc R∈WFs y )

  
  -- WFminDNE→WFcor : ¬¬Closed R isWFminDNE → R isWFcor
  -- WFminDNE→WFcor RisWFminDNE x P Pcor =
  --   let nn : ¬¬ (P x) 
  --   nn = WFmin→WFcor¬¬ (?) x P Pcor
  --   in ?  -- DNE-on-P (nn) dec→¬¬Closed -- use your available double-negation elimination instance
  
  -- WFminDNE→WFcor : R isWFminDNE → R isWFcor 
  -- WFminDNE→WFcor RisWFminDNE x P P∈Cor with RisWFminDNE (∁ P) (¬¬Closed∁ P) x 
  -- ... | z = {!   !}



  -- SA: Sep 15th Do we want to keep this or scrap at this point?
  -- MP→isWFcor→isWFseq : R isWFcor → R isWFseq
  -- MP→isWFcor→isWFseq RisWFcor s with RisWFcor (s 0) (λ x → ((R ⋆) x (s 0) ) → ¬ (Σ[ k ∈ ℕ ] ((R ⋆) (s k) x))) f ε⋆  
  --   where 
  --     f : _ 
  --     f x H = ?
  -- ... | z  = ∅ (z (0 ,, ε⋆))
  -- try and build on this implication. Will probably need to apply MP≡ twice. 
  -- What correductive property associated with the sequence which if assumed to always be true would give a counterexample to the sequence?
  -- predicate cand: if you're in the image of s then none of your successors should be in the image of s
  -- Pred: Given x, the xomplement of sigma k 
{- 
  MP→isWFcor→isWFseq : R isWFcor → R isWFseq
  MP→isWFcor→isWFseq RisWFcor s = {!   !} -- ∅ (g (fst lr) snd lr) 
    where 
      g : ∀ (k : ℕ) → (¬(R ⋆) (s k) (s 0))
      g = {!   !} 
      f : R -coreductive (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) 
      f x x∉P with mp≡ s x (λ x∉s → x∉P (λ x∈s → ∅ (x∉s x∈s)))
      ... | k ,, sk≡x rewrite ~ sk≡x = (s (succ k)) ,, ( ?  , λ H → x∉P λ x₁ → fst (H (succ k ,, refl)) ,, λ R*ssucksk → snd (H (succ k ,, refl)) ? )           

      lr = RisWFcor (s 0) (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) f (0 ,, refl)
-}

module MP→isWFcor→isWFseq {A : Set} {R : 𝓡 A} (RisWFcor : R isWFcor) (s : ℕ → A) (mp≡ : MP≡) where 
  g : ∀ (k : ℕ) → (¬(R ⋆) (s k) (s 0))
  g = {!   !} 
  
  f : R -coreductive (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) 
  f x x∉P with mp≡ s x (λ x∉s → x∉P (λ x∈s → ∅ (x∉s x∈s)))
  ... | k ,, sk≡x rewrite ~ sk≡x 
    = (s (succ k)) ,,
      ( {!   !}  , λ H → x∉P λ x₁ → fst (H (succ k ,, refl)) ,,  
      λ R*ssucksk → snd (H (succ k ,, refl)) {!   !} )   

  ims∈cor : R -coreductive (λ x → ¬ Σ[ k ∈ ℕ ] ((s k) ≡ x))
  ims∈cor x x∉s with mp≡ s x x∉s 
  ... | k ,, sk≡x = s (succ k) ,, {!   !}           

  lr = RisWFcor (s 0) (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) f (0 ,, refl)



isWFminDNE→isWFminCor+ : R isWFminDNE → R isWFminCor+ -- We have a stronger version of this implication.
  isWFminDNE→isWFminCor+ RisWFminDNE P Pco {a} a∉P
    with  RisWFminDNE (∁ P) DNS¬ a a∉P
    where DNS¬ = λ x ¬Px ¬¬Px → ¬Px (λ z → z ¬¬Px)
  ... | (y ,, ¬Py , ymin) with Pco y ¬Py
  ... | (z ,, Rzy , ¬Pz) = ∅ (ymin z ¬Pz Rzy)