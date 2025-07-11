{-# OPTIONS --allow-unsolved-metas #-}
open import Relations.Relations
open import Predicates
open import Logic
open import Datatypes using (ℕ; zero; succ)
open import Relations.Seq

module ARS.Theorems {A : Set } {R : 𝓡 A} where

open import ARS.Util
open import ARS.Implications
open import ARS.Properties {A}
open LocalProperties {R}
open import ARS.Propositions
open import Relations.WellFounded.WFWeakDefinitions
{-This file contains formalization of the theorems of TeReSe Chapter 1-}

module Theorem-1-2-2 where
    CR→NP : R isCR → R isNP₌
    CR→NP RisCR {x} {y} y∈NF R⁼xy with Proposition-1-1-10.i→vi (CR→confluent RisCR )  x y R⁼xy
    ... | z ,, R*xz , ε⋆ = R*xz
    ... | z ,, R*xz , (Ryy₀ ,⋆ R*y₀z) = ∅ (y∈NF Ryy₀)

    NP→UN : R isNP₌ → R isUN
    NP→UN RisNP₌ x∈NF y∈NF R⁼xy = NF→ε x∈NF (RisNP₌ y∈NF R⁼xy)

    CP→UN : R isCR → R isUN
    CP→UN RisCR = NP→UN (CR→NP RisCR)

    ii+ : R isWN × R isUN→ → R isCR
    ii+ (RisWN ,  RisUN→) x {y}{z} R*xy R*xz with RisWN y | RisWN z
    ... | n₀ ,, R*yn₀ , n₀∈NF |  n₁ ,, R*zn₁ , n₁∈NF with
                RisUN→ x n₀∈NF n₁∈NF (R*xy ⋆!⋆ R*yn₀) (R*xz ⋆!⋆ R*zn₁)
    ... | n₀≡n₁ = n₀ ,, (R*yn₀ , transp ((R ⋆) z) (~ n₀≡n₁) R*zn₁)

    ii : R isWN × R isUN → R isCR
    ii (RisWN , RisUN) = ii+ (RisWN , (Terese-Alternative.UN→UN→ RisUN))


    iii : subcommutative R → R isCR
    iii RisSC x R*xy R*xz = Proposition-1-1-10.v→i (λ { b c (a ,, Rab , R*ac) → f b c a Rab R*ac } ) (x ,, (R*xy , R*xz))  where
      f : (x y z : A) → R z x → (R ⋆) z y → ((R ⋆) ∘R ~R (R ⋆)) x y
      f x y .y Rzx ε⋆ = x ,, ε⋆ , (Rzx ,⋆ ε⋆)
      f x y z Rzx (Rzy₁ ,⋆ R*y₁y) with RisSC (z ,, (Rzx , Rzy₁))
      ... | d ,, R , εʳ = y ,, R ʳ!⋆ R*y₁y , ε⋆
      ... | d ,, Rʳxd , axʳ x₁ with f d y _ x₁ R*y₁y
      ... | w ,, R*dw , R*yw = w ,, (Rʳxd ʳ!⋆ R*dw ) , R*yw

module Theorem-1-2-3 where
  refl-closure-lemma : ∀ (Φ : (∀ x y → (R ʳ) x y → Set))
                         (Φax  : ∀ x y (ρ : R x y) → Φ x y (axʳ ρ))
                         (Φeps : ∀ x y (p : x ≡ y) → Φ x y (transp ((R ʳ) x) p εʳ) )
                         → ∀ x y (ρ : (R ʳ) x y) → Φ x y ρ
  refl-closure-lemma Φ Φax Φeps x y (axʳ ρ) = Φax x y ρ
  refl-closure-lemma Φ Φax Φeps x .x εʳ = Φeps x x refl

  wseq-lemma : ∀ (f : ℕ → A) → f ∈ (R ʳ) -increasing → ∀ n → (R ⋆) (f zero) (f n)
  wseq-lemma f f-winc zero = ε⋆
  wseq-lemma f f-winc (succ n) =
    let Φ = λ x y Rʳxy → (R ⋆) y (f (succ n)) → (R ⋆) x (f (succ n))
        Φax = λ x y → _,⋆_
        Φeps = λ { x .x refl → I }
        rcl = refl-closure-lemma Φ Φax Φeps (f zero) (f (succ zero)) (f-winc zero)
      in rcl (wseq-lemma (f ∘ succ) (λ k → f-winc (succ k)) n)

  wseq-lemma2 : ∀ (f : ℕ → A) → f ∈ (R ʳ) -increasing → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
  wseq-lemma2 f f-winc zero m = in1 (wseq-lemma f f-winc m)
  wseq-lemma2 f f-winc (succ n) zero = in2 (wseq-lemma f f-winc (succ n))
  wseq-lemma2 f f-winc (succ n) (succ m) = wseq-lemma2 (f ∘ succ) (λ k → f-winc (succ k) ) n m

  i : R isWN → R isUN → R isBP
  i RisWN RisUN f f-inc with RisWN (f zero)
  ... | (n ,, R*f0n , n∈NF) = n ,, g where
    g : ∀ k → (R ⋆) (f k) n
    g k with Theorem-1-2-2.ii (RisWN , RisUN)  (f 0) R*f0n (seq-lemma R f f-inc k)
    ... | .n ,, ε⋆ , R*fkn = R*fkn
    ... | n' ,, (Rnn₀ ,⋆ R*n₀n') , R*fkn = ∅ (n∈NF Rnn₀ )

  -- Using UN→ rather than UN
  i→ : R isWN → R isUN→ → R isBP
  i→ RisWN RisUN→ f f-inc  with RisWN (f zero)
  ... | (a ,, R*f0a , a∈NF) = a ,, g where
    g : ∀ k → (R ⋆) (f k) a
    g k with RisWN (f k)
    ... | b ,, R*fkb , b∈NF with RisUN→ (f zero) a∈NF b∈NF R*f0a ((seq-lemma R f f-inc k) ⋆!⋆ R*fkb)
    ... | refl = R*fkb


  -- A variant on theorem 1-2-3 ii)
  iiSeq : R isWN → R isUN → R isRP → isWFseq- (~R R)
  iiSeq wnR unR rp s sIsRdec with i wnR unR
  ... | bdR with wnR (s 0)
  ... | a ,, R*s₀a , a∈NF with bdR s sIsRdec
  ... | b ,, bisωLimit with bisωLimit 0
  ... | R*s₀b with rp s sIsRdec b bisωLimit
  ... | c ,, ScisRecurrent with Theorem-1-2-2.ii (wnR , unR)
  ... | RisCR with RisCR (s 0)  R*s₀a  (seq-lemma R s sIsRdec c)
  ... | d ,, (Raa₁ ,⋆ R*a₁d) , R*bd = a∈NF Raa₁
  ... | .a ,, ε⋆ , R*sca with ScisRecurrent a (R*sca)
  ... | Raa₃ ,⋆ R*as_c = a∈NF Raa₃
  ... | ε⋆ = a∈NF (sIsRdec c)

  iv : R isCP → R isCR
  iv RhasCP a R*ab R*ac with RhasCP a
  ... | f ,, f-winc , (refl , fisCof) with fisCof _ R*ab | fisCof _ R*ac
  ... | bₙ ,, R*bfbₙ | cₙ ,, R*cfcₙ
    with wseq-lemma2 f f-winc bₙ cₙ
  ... | in1 R*fbₙfcₙ = (f cₙ) ,, ((R*bfbₙ ⋆!⋆ R*fbₙfcₙ) , R*cfcₙ)
  ... | in2 R*fcₙfbₙ = (f bₙ) ,, R*bfbₙ , (R*cfcₙ ⋆!⋆ R*fcₙfbₙ)

  -- Proving the reverse: Prove this with an assumption of finite branchingness.  
  -- iv← : R isCR → _isFB →  R isCP
  -- iv← = ? 

  -- The proof of Theorem-1-2-3-iii requires classical principles
  open import Classical
  record preSN (n x : A) : Set where
    constructor pSN
    field
      n∈NF : NF n
      x∉SN : ¬ (SN x)
      s : A
      x→s : R x s
      s→n : (R ⋆) s n
      s∈SN : SN s

  -- open WFDefinitions
  open MinimalComplement

  AccCor : Set
  AccCor = (~R R) -coreductive (~R R -accessible)

  x∉SN→∃y∉SN : AccCor → ∀ {x} → ¬(SN x) → Σ[ y ∈ A ] (¬(SN y) × R x y)
  x∉SN→∃y∉SN accCor {x} x∉SN with accCor x x∉SN
  ... | (y ,, Rxy , y∉SN) = y ,, y∉SN , Rxy

  preSNlemma1 : dec (SN) → ∀ {x n} → (R ⋆) x n → NF n → ¬ SN x →
                                  Σ[ y ∈ A ] ((R ⋆) x y × preSN n y)
  preSNlemma1 decSN {x} {.x} ε⋆ n∈NF x∉SN = ∅ (¬SN∧NF→⊥ x∉SN n∈NF )
  preSNlemma1 decSN {x} {n} (_,⋆_ {y = y} Rxy R*yn) n∈NF x∉SN
    with decSN y
  ... | in1 y∈SN = x ,, (ε⋆ , pSN n∈NF x∉SN y Rxy R*yn y∈SN)
  ... | in2 y∉SN
    with preSNlemma1 decSN R*yn n∈NF y∉SN
  ... | (z ,, R*yz , p) = (z ,, (Rxy ,⋆ R*yz , p ))

  WCR→SN⊆NP : R isWCR → ∀ x → SN x → NP x
  WCR→SN⊆NP RisWCR x x∈SN y∈NF R*xy R*xz
    with ARS.Util.wCR→Conf (λ a  Rab  Rac → RisWCR a Rab Rac) x x∈SN R*xy R*xz
  ... | w ,, ε⋆ , R*zw = R*zw
  ... | w ,, (Ry- ,⋆ _) , R*zw = ∅ (y∈NF Ry-)

  preSNlemma2 : R isWCR → dec (SN) → AccCor →
                ∀ n x → preSN n x → Σ[ y ∈ A ] ((R ⁺) x y × preSN n y)
  preSNlemma2 RisWCR decSN accCor n x (pSN n∈NF x∉SN s x→s s→n s∈SN)
    with x∉SN→∃y∉SN accCor x∉SN
  ... | (y ,, y∉SN , Rxy)
    with RisWCR x x→s Rxy
  ... | (z ,, R*sz , R*yz)
    with preSNlemma1 decSN (R*yz ⋆!⋆ WCR→SN⊆NP RisWCR s s∈SN n∈NF s→n R*sz )  n∈NF y∉SN
  ... | (v ,, R*yv , p) = (v ,, RR⋆⊆R⁺ R Rxy R*yv , p)

  preSNlemma3 : R isWCR → dec (SN) → AccCor → ∀ n x → preSN n x →
                  Σ[ f ∈ (ℕ → A) ] ((∀ k → preSN n (f k)) × f ∈ (R ⁺) -increasing)
  preSNlemma3 RisWCR decSN acccor n x p = f ,, pf , finc where
    f : ℕ → A
    pf : ∀ (k : ℕ) → preSN n (f k)
    f zero = x
    f (succ k) = fst (preSNlemma2 RisWCR decSN acccor n (f k) (pf k))
    pf zero = p
    pf (succ k) = pr2 (snd (preSNlemma2 RisWCR decSN acccor n (f k) (pf k)))
    finc : f ∈ (R ⁺) -increasing
    finc k = pr1 (snd (preSNlemma2 RisWCR decSN acccor n (f k) (pf k)))


  seq→sseq : ∀ (f : ℕ → A) → f ∈ (R ⁺) -increasing → ∀ (k : ℕ) → Σ[ a ∈ A ] (R ⋆) a (f k)
  seq→sseq f finc zero = f zero ,, ε⋆
  seq→sseq f finc (succ k)
    with seq→sseq f finc k
  ... | x ,, (_,⋆_ {y = y} h r) = y ,, (r ⋆!⋆ ⁺→⋆ R (finc k) )
  ... | .(f k) ,, ε⋆ with finc k
  ... | (_,⁺_ {y = y} h r) = (y ,, ⁺→⋆ R  r )
  ... | ε⁺ = f (succ k) ,, ε⋆

  seq→sseq-inc :  ∀ (f : ℕ → A) (finc : f ∈ (R ⁺) -increasing)
                   → (λ k → fst (seq→sseq f finc k)) ∈ R -increasing
  seq→sseq-inc f finc zero with seq→sseq f finc zero | finc zero
  ... | x ,, (x₁ ,⋆ R*xf0) | ax⁺ f0f1 = f0f1
  ... | x ,, (x₁ ,⋆ R*xf0) | h ,⁺ t = h
  ... | .(f 0) ,, ε⋆ | ax⁺ f0f1 = f0f1
  ... | .(f 0) ,, ε⋆ | h ,⁺ t = h
  seq→sseq-inc f finc (succ k) with seq→sseq f finc (succ k)
  ... | x ,, (h ,⋆ x→fsk) = h
  ... | .(f (succ k)) ,, ε⋆ with finc (succ k)
  ... | ax⁺ h = h
  ... | h ,⁺ c = h

  seq→sseq-bnd : ∀ (f : ℕ → A) (finc : f ∈ (R ⁺) -increasing) (b : A) →
               is R - f bound b → is R - (λ k → fst (seq→sseq f finc k)) bound b
  seq→sseq-bnd f finc b fbnd k = snd (seq→sseq f finc k) ⋆!⋆ (fbnd k)


  Theorem123Lemma : R isWCR → dec (SN) → AccCor → ∀ n x → preSN n x →
                    Σ[ f ∈ (ℕ → A) ] (f ∈ R -increasing × is R - f bound n)
  Theorem123Lemma RisWCR decSN ac n x p
    with preSNlemma3 RisWCR decSN ac n x p
  ... | (f ,, pf , fisR+inc) =
        (λ k → fst (seq→sseq f fisR+inc k))
        ,,  seq→sseq-inc f fisR+inc
          , seq→sseq-bnd f fisR+inc n (λ k → x→s (pf k) ,⋆ s→n (pf k) ) where open preSN

  iii : R isWN → R isWCR → R isRP- → dec (SN) → AccCor → R isSN
  iii RisWN RisWCR RisRP decSN ac x with decSN x
  ... | in1 x∈SN = x∈SN
  ... | in2 x∉SN with RisWN x
  ... | n ,, R*xn , n∈NF with preSNlemma1 decSN R*xn n∈NF x∉SN
  ... | b₀ ,, R*xb₀ , nb₀∈preSN with Theorem123Lemma RisWCR decSN ac n b₀ nb₀∈preSN
  ... | s ,, s-inc , n∈s-bound with RisRP s s-inc n n∈s-bound
  ... | i ,, ε⋆ = ∅ (n∈NF (s-inc i))
  ... | i ,, (Rnz ,⋆ R*zsᵢ) = ∅ (n∈NF Rnz)
