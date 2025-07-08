open import Relations.Relations
open import Predicates
open import Logic
open import Datatypes using (ℕ; zero;  succ)
open import Relations.Seq


module ARS.Implications {A : Set } {R : 𝓡 A} where

open import ARS.Util
open import ARS.Closure
open import ARS.Properties {A}
open LocalProperties {R}
open MiscProperties

CR→WCR : R isCR → R isWCR
CR→WCR RisCR x Rxy Rxz = RisCR x (Rxy ,⋆ ε⋆) (Rxz ,⋆ ε⋆)

module Hierarchy-Implications where
    -- These implications establish the hierarchy of normalizing properties and confluent properties as set out in the report.

    CR→MP : ∀ {x} → CR x → MP x
    CR→MP x∈CR y∈MF R*xy R*xz with x∈CR R*xy R*xz
    ... | q ,, R*yq , R*zq with y∈MF q R*yq
    ... | R*qy = R*zq ⋆!⋆ R*qy

    NF⊆MF : ∀ {x} → NF x → MF x
    NF⊆MF x∈NF y ε⋆ = ε⋆
    NF⊆MF x∈NF y (Rxx₁ ,⋆ R*x₁y) = ∅ (x∈NF Rxx₁)

    MP→NP : ∀ {x} → MP x → NP x
    MP→NP x∈MP y∈NF R*xy R*xz = x∈MP (NF⊆MF y∈NF) R*xy R*xz

    NP→UN : ∀ {x} → NP x → UN x
    NP→UN x∈NP y∈NF z∈NF R*xy R*xz with x∈NP y∈NF R*xy R*xz
    ... | ε⋆ = refl
    ... | Rzz₁ ,⋆ R*z₁y = ∅ (z∈NF Rzz₁)

    SN→SM : ∀ {x} → SN x → SM x
    SN→SM (acc xa) = SMacc _ (λ y Rxy → SN→SM (xa y Rxy))

    SN→SMseq : ∀ {x} → SN x → SMseq R x
    SN→SMseq {x} (acc accx) f refl f-inc with
        SN→SMseq (accx (f (succ zero)) (f-inc zero)) (λ m → f (succ m)) refl (λ n → f-inc (succ n))
    ... | (k ,, H) = (succ k ,, H)

    WN→WM : ∀ {x} → WN x → WM x
    WN→WM (n ,, R*xn , x∈NF) = n ,, (R*xn , (NF⊆MF x∈NF))

    -- open ClassicalImplications -- using (decMin)
    open import Relations.Decidable

    SNdec→WN : (~R R) isMinDec → SN ⊆ WN
    SNdec→WN decR x (acc accx) with decR x
    ... | in2 y∈NF = x ,, (ε⋆ , y∈NF _)
    ... | in1 (y ,, Rxy) with SNdec→WN decR y (accx y Rxy)
    ... | (n ,, R*yn , n∈NF) = n ,, (Rxy ,⋆ R*yn) , n∈NF

    SN→WN∧SM : (~R R) isMinDec → ∀ {x} → SN x → (WN x × SMseq R x)
    SN→WN∧SM decR {x} x∈SN = SNdec→WN decR x x∈SN , SN→SMseq x∈SN

    SM→WM : (~R R) isMinDec → ∀ {x} → SM x → WM x
    SM→WM decR {x} (SMrec .x x∈rec) = x ,, ε⋆ , x∈rec
    SM→WM decR {x} (SMacc .x x∈acc) with decR x
    ... | in2 xIsMin = x ,, (ε⋆ , λ { y ε⋆ → ε⋆
                                    ; y (Rxx₁ ,⋆ R*x₁y) → ∅ (xIsMin _ Rxx₁)})
    ... | in1 (y ,, Rxy) with SM→WM decR (x∈acc y Rxy)
    ... | r ,, R*yr , r∈acc = r ,, (Rxy ,⋆ R*yr) , r∈acc

-- Equivalence of RP definitions
open Hierarchy-Implications

module Confluent-Implications where
    WM∧MP→CR : ∀ {x} → WM x → MP x → CR x
    WM∧MP→CR (q ,, (R*xq , q∈MF)) x∈MP R*xy R*xz = q ,, (x∈MP q∈MF R*xq R*xy) , (x∈MP q∈MF R*xq R*xz)

    WN∧NP→CR : ∀ {x} → WN x → NP x → CR x
    WN∧NP→CR (n ,, (R*xn , x∈NF)) x∈NP R*xy R*xz = n ,, x∈NP x∈NF R*xn R*xy , x∈NP x∈NF R*xn R*xz

    -- UN→∧WN→CR : R isUN→ → R isWN → R isCR
    -- UN→∧WN→CR RisUN→ RisWN x {y}{z} R*xy R*xz with RisWN y | RisWN z
    -- ... | n₀ ,, R*yn₀ , n₀∈NF |  n₁ ,, R*zn₁ , n₁∈NF with
    --             RisUN→ x n₀∈NF n₁∈NF (R*xy ⋆!⋆ R*yn₀) (R*xz ⋆!⋆ R*zn₁)
    -- ... | n₀≡n₁ = n₀ ,, (R*yn₀ , transp ((R ⋆) z) (~ n₀≡n₁) R*zn₁)

module Normalizing-Implications where
    NF⊆SN : ∀ {x} → NF x → SN x
    NF⊆SN {x} x∈NF = acc λ y Rxy → ∅ (x∈NF Rxy)

    WN∧MF→SN : ∀ {x} → WN x → MF x → SN x
    WN∧MF→SN (n ,, R*xn , n∈NF) x∈MF =
        acc (λ y Rxy → ∅ (NF↓⊆NF n∈NF (x∈MF n R*xn) Rxy))

    MF∧SN→NF : ∀ {x} → MF x → SN x → NF x 
    MF∧SN→NF x∈MF (acc xacc) {y} Rxy 
        with MF∧SN→NF (MF↓⊆MF x∈MF (Rxy ,⋆ ε⋆)) (xacc y Rxy) 
    ... | y∈NF with x∈MF y (Rxy ,⋆ ε⋆)  
    ... | ε⋆ = y∈NF Rxy
    ... | Ryy₁ ,⋆ _ = y∈NF Ryy₁    
    
    NF→MF∧SN : ∀ {x} → NF x → MF x × SN x 
    NF→MF∧SN xinNF = (NF⊆MF xinNF) , NF⊆SN xinNF  
    
    MF∧SN↔NF : ∀ {x} → MF x × SN x ↔ NF x 
    MF∧SN↔NF = (λ (x∈MF , x∈SN) → MF∧SN→NF x∈MF x∈SN) , NF→MF∧SN 

    MF∧WN↔NF : ∀ {x} → MF x × WN x ↔ NF x 
    pr1 MF∧WN↔NF (x∈MF , x∈WN)  with WN∧MF→SN x∈WN x∈MF
    ... | x∈SN = MF∧SN→NF x∈MF x∈SN
    pr2 MF∧WN↔NF x∈NF = NF⊆MF x∈NF , ((_ ,, ε⋆ , x∈NF)) 

    WN∧NP∧SM→SN : ∀ {x} → WN x → NP x → SM x → SN x
    WN∧NP∧SM→SN {x} x∈WN x∈NP (SMrec .x x∈MF) = WN∧MF→SN x∈WN x∈MF
    WN∧NP∧SM→SN {x} (n ,, R*xn , n∈NF) x∈NP (SMacc .x xAcc) = acc f where
        f : ∀ (y : A) → ~R R y x → y ∈ ~R R -accessible
        f y Rxy = WN∧NP∧SM→SN
                    (n ,, x∈NP n∈NF R*xn (Rxy ,⋆ ε⋆) , n∈NF)
                    (λ {w} {z} H R*yw R*yz → x∈NP H (Rxy ,⋆ R*yw) (Rxy ,⋆ R*yz) )
                    (xAcc y Rxy)

    isWN∧SM→SN : R isWN → ∀ {x} → SM x → SN x
    isWN∧SM→SN RisWN {x} (SMrec .x x∈MF) = WN∧MF→SN (RisWN x) x∈MF
    isWN∧SM→SN RisWN {x} (SMacc .x x∈SMacc) with RisWN x
    ... | .x ,, ε⋆ , n∈NF = NF⊆SN n∈NF
    ... | n ,, (Rxy ,⋆ R*xn) , n∈NF = acc f where
        f :  ∀ (y : A) → ~R R y x → y ∈ ~R R -accessible
        f y Rxy = isWN∧SM→SN RisWN  (x∈SMacc y Rxy)

    isWN∧isSM→isSN : R isWN → R isSM → R isSN
    isWN∧isSM→isSN RisWN RisSM x =  isWN∧SM→SN RisWN (RisSM x)

    open import ARS.NewmansLemma
    open Newmans-Lemma-SM

    isWCR→WN∩SM⊆SN : R isWCR → ∀ {x} → x ∈ WN → x ∈ SM → x ∈ SN
    isWCR→WN∩SM⊆SN RisWCR {x} x∈WN x∈SM
      with LocalNewmansLemmaRecurrent R RisWCR _ x∈SM
    ... | x∈CR = WN∧NP∧SM→SN x∈WN ((MP→NP ∘ CR→MP) x∈CR ) x∈SM

module Terese-Alternative where
    -- These are implications for using alternative definitions to those given in TeReSe

    NP→NP₌ : R isNP → R isNP₌
    NP→NP₌ RisNP y∈NF ε⋆ = ε⋆
    NP→NP₌ RisNP y∈NF (_,⋆_ {y = w} Rsxw R=wy) with NP→NP₌ RisNP y∈NF R=wy
    NP→NP₌ RisNP y∈NF (_,⋆_ {y = w} (axˢ+ Rxw) R=wy) | R*wy = Rxw ,⋆ R*wy
    NP→NP₌ RisNP y∈NF (_,⋆_ {y = w} (axˢ- Rwx) R=wy) | R*wy = RisNP w y∈NF R*wy (Rwx ,⋆ ε⋆)

    NP₌→NP : R isNP₌ → R isNP
    NP₌→NP RisNP₌ x {y} {z} y∈NF  R*xy R*xz = RisNP₌ y∈NF R=zy
        where
            R=zy : (R ⁼) z y
            R=zy = (~ˢ⋆ (⋆⊆⁼ R R*xz)) ⋆!⋆ (⋆⊆⁼ R R*xy)

    NP₌↔NP : R isNP₌ ↔ R isNP
    NP₌↔NP = NP₌→NP , NP→NP₌

    -- Counterexample: (n <- a -> b <-> c <- d -> m)
    -- n,m ∈ NF, R isUN→, n R⁼ m, but n ≢ m.
    -- Possible fix: Provably with WN, via (WN∧UN→)→CR→WNFP→NP→UN (??)
    -- Add a note to the report noting the distinction between these.
    -- UN→→UN : R isUN→ → R isUN
    -- UN→→UN RisUN→ {x} {.x} x∈NF y∈NF ε⋆ = refl
    -- UN→→UN RisUN→ {x} {y} x∈NF y∈NF (_,⋆_ {y = w} (axˢ+ Rxw) R=wy) = ∅ (x∈NF Rxw)
    -- UN→→UN RisUN→ {x} {y} x∈NF y∈NF (_,⋆_ {y = w} (axˢ- Rwx) R=wy) = {!   !}
    --   with UN→→UN RisUN→ ({!   !}) y∈NF R=x₁y
    -- ... | refl = {!   !}

    UN→UN→ : R isUN → R isUN→
    UN→UN→ RisUN x {n} {m} n∈NF m∈NF R*xn R*xm
      = RisUN n∈NF m∈NF ((~⁼ (⋆⊆⁼ R R*xn) ) ⁼!⁼ ⋆⊆⁼ R R*xm )

    -- if we show this for SMseq we can investigate whether it holds for SM
    RP∧BP→SMseq : R isRP → R isBP → ∀ {x : A} → SMseq R x
    RP∧BP→SMseq RisRP RisBP f f0≡x f-inc with RisBP f f-inc
    ... | (b ,, b-bnd) = RisRP f f-inc b b-bnd

    RisSMseq→RisRP : (∀ {x : A} → SMseq R x) → R isRP
    RisSMseq→RisRP RisSM f f-inc a a-bnd = RisSM f refl f-inc


    RisSMseq→RisBP : (∀ {x : A} → SMseq R x) → R isBP
    RisSMseq→RisBP RisSM f f-inc with RisSM f refl f-inc
    ... | i ,, i∈rec = (f i) ,, boundProof
        where
        boundProof  : (x : ℕ) → (R ⋆) (f x) (f i)
        boundProof n with seq-lemma2 R f f-inc i n
        ... | in1 R*fᵢfₙ = i∈rec (f n) R*fᵢfₙ
        ... | in2 R*fₙfᵢ = R*fₙfᵢ

RP→RP- : R isRP → R isRP-
RP→RP- RisRP f f-inc b bis-bound with RisRP f f-inc b bis-bound
... | i ,, i∈RP = i ,, (i∈RP b (bis-bound i))

RP-lemma : ∀ (f : ℕ → A) → f ∈ R -increasing → ∀ a → (is R - f bound a)
          →  ∀ i → (R ⋆) a (f i) → ∀ x → (R ⋆) (f i) x → is R - f bound x
RP-lemma f f-inc a aisf-bound i R*afᵢ y R*fᵢy n = (aisf-bound n ⋆!⋆ R*afᵢ) ⋆!⋆ R*fᵢy

RP-→RP : R isRP- → R isRP
RP-→RP RP- f f-inc a aisf-bound with RP- f f-inc a aisf-bound
... | i ,, R*afᵢ = i ,, proof
    where   proof : (y : A) (R*fᵢy : (R ⋆) (f i) y) → (R ⋆) y (f i)
            proof y R*fᵢy with RP-lemma f f-inc a aisf-bound i R*afᵢ y R*fᵢy
            ... | yisf-bound with RP- f f-inc y yisf-bound
            ... | j ,, R*yfⱼ = R*yfⱼ ⋆!⋆ (aisf-bound j ⋆!⋆ R*afᵢ)

RP-↔RP : R isRP- ↔ R isRP
RP-↔RP  = RP-→RP , RP→RP-


WCR∧SNx→NPx : R isWCR → SN ⊆ NP
WCR∧SNx→NPx RisWCR x x∈SN y∈NF ε⋆ ε⋆ = ε⋆
WCR∧SNx→NPx RisWCR x x∈SN y∈NF ε⋆ (Rxx₀ ,⋆ R*x₀z) = ∅ (y∈NF Rxx₀)
WCR∧SNx→NPx RisWCR x x∈SN y∈NF (Rxy₀ ,⋆ R*y₀y) ε⋆ = Rxy₀ ,⋆ R*y₀y
WCR∧SNx→NPx RisWCR x (acc xacc) y∈NF (Rxy₀ ,⋆ R*y₀y) (Rxz₀ ,⋆ R*z₀z) with RisWCR x Rxy₀ Rxz₀
... | w ,, R*y₀w , R*z₀w with WCR∧SNx→NPx RisWCR  _ (xacc _ Rxy₀) y∈NF R*y₀y R*y₀w
... | R*wy = WCR∧SNx→NPx RisWCR _ (xacc _ Rxz₀) y∈NF (R*z₀w ⋆!⋆ R*wy) R*z₀z


WCR∧SNx→UNx : R isWCR → ∀ (x : A) → SN x → UN x
WCR∧SNx→UNx RisWCR x x∈SN y∈NF z∈NF R*xy R*xz with WCR∧SNx→NPx RisWCR x x∈SN y∈NF R*xy R*xz
... | R*zy = ~ (NF→ε z∈NF R*zy)

open import Relations.Decidable

WN→isMinDec- : ∀ (x : A) → x ∈ WN  → x ∈ MinDec- (~R R)
WN→isMinDec- x (.x ,, ε⋆ , n∈NF) x∉NF = ∅ (x∉NF (λ y → n∈NF))
WN→isMinDec- x (n ,, (_,⋆_ {y = y} Rxy R*yn) , n∈NF) x∉NF = y ,, Rxy

decMin∧SNx∧UNx→NP  : (~R R) isMinDec  → ∀ x → SN x → UN x → NP x     -- Formerly UN-lemma
decMin∧SNx∧UNx→NP decNF x x∈SN x∈UN y∈NF R*xy  ε⋆ = R*xy
decMin∧SNx∧UNx→NP decNF x (acc xacc) x∈UN y∈NF R*xy (Rxz₀ ,⋆ R*z₀z)
    with SNdec→WN decNF _ (xacc _ Rxz₀)
... | z' ,, R*z₀z' , z'∈NF with x∈UN y∈NF z'∈NF R*xy (Rxz₀ ,⋆ R*z₀z')
... | refl = decMin∧SNx∧UNx→NP decNF _ (xacc _ Rxz₀) (λ {a} {b} → z₀∈UN {a} {b}) y∈NF R*z₀z' R*z₀z
    where z₀∈UN =  λ {a} {b} a∈NF b∈NF R*z₀a R*z₀b → x∈UN (λ Rav → a∈NF Rav)  (λ Rbw → b∈NF Rbw) (Rxz₀ ,⋆ R*z₀a) (Rxz₀ ,⋆ R*z₀b)

SN∧UN→CRelem : (~R R) isMinDec → ∀ x → SN x → UN x → CR x
SN∧UN→CRelem decNF x x∈SN x∈UN R*xb R*xc with SNdec→WN decNF x x∈SN
... | (z ,, R*xz , z∈NF) = (z ,, decMin∧SNx∧UNx→NP  decNF x x∈SN x∈UN  z∈NF R*xz  R*xb
                                , decMin∧SNx∧UNx→NP  decNF x x∈SN x∈UN z∈NF R*xz R*xc )
