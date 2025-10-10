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


module ReductionSequence (wfSeq- : R isWFseq-) (s : ℕ → A) (H : ¬ Σ-syntax ℕ (λ n → ¬ R (s (succ n)) (s n))) where

    -- RedSeq n asserts that s is R-decreasing up to n
    data RedSeq : ℕ → Set where
      rsinit : RedSeq 0
      rsstep : ∀ n → RedSeq n → R (s (succ n)) (s n) → RedSeq (succ n)

    ¬¬RS : ∀ n → ¬¬ (RedSeq n)
    ¬¬RS zero = λ z → z rsinit
    ¬¬RS (succ n) = λ ¬RSsuccn → H (n ,, λ Rnsn → ¬¬RS n λ n∈RS → ¬RSsuccn (rsstep n n∈RS Rnsn) )

    ¬¬∁∁RS⊆RS : ¬¬ (∁∁ RedSeq ⊆ RedSeq)
    ¬¬∁∁RS⊆RS not⊆ = not⊆ f where
      f : _
      f zero y = rsinit
      f (succ x) ¬sx∉RS = {!   !} -- ∅ (not⊆ λ y ¬y∉RS → {!   !} )

    -- ∁∁RS⊆RS : ∁∁ RedSeq ⊆ RedSeq
    -- ∁∁RS⊆RS zero ¬n∉RS = rsinit
    -- ∁∁RS⊆RS (succ n) ¬n∉RS with ∁∁RS⊆RS n
    -- ... | rc = rsstep n (rc (¬¬RS n )) {!   !}

    DNSRS : ¬¬ (∀ n → RedSeq n)
    DNSRS notAllRS = wfSeq- s (λ n → {!   !} )

  --
  MP→isWFcor→isWFseq : MP≡ {A = A} → R isWFcor → R isWFseq
  MP→isWFcor→isWFseq mp RisWFcor s with RisWFcor (s 0) (∁ (λ x → Σ[ k ∈ ℕ ] (s k ≡ x))) ccor
    where ccor : _
          ccor a H with mp s a H
          ... | (k ,, sk=a) = (s (succ k) ,, {! transp (R (succ k))   !} , (λ ne → ne (succ k ,, refl) ) ) 
  MP→isWFcor→isWFseq mp RisWFcor s | c = ∅ (c (0 ,, refl ))

  -- MP→isWFcor→isWFseq mp RisWFcor s with RisWFcor (s 0) (λ x → ((R ⋆) x (s 0) ) → ¬ (Σ[ k ∈ ℕ ] ((R ⋆) (s k) x))) f ε⋆
  --   where
  --     f : _
  --     f x H with mp s x
  --     ... | c with c (λ p → H λ R*xs0 → λ {(j ,, R*sjx) → {!   !} } )
  --     ... | n = {!   !}
  -- MP→isWFcor→isWFseq mp RisWFcor s | z  = ∅ (z (0 ,, ε⋆))

  isWFseq-→isWFseq¬¬ : R isWFseq- → R isWFseq¬¬ -- Think we need R to be not not closed. We don't have this. But we might be able to get away with R not being not not closed
  isWFseq-→isWFseq¬¬ RisWFseq- s H = {!   !} -- RisWFseq- s (λ k → {!   !})

  -- g where
  --   g : Σ ℕ (λ z → (x : R (s (succ z)) (s z)) → ⊥)
  --   g = {!   !}