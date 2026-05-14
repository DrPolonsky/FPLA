open import Logic
open import Lifting 
open import LAM.Lambda
open import LAM.LambdaPredicates
open import LAM.Reduction.Beta
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

open import LAM.Reduction.Beta
open import LAM.Reduction.StandardBeta

open import Lists

module LAM.Reduction.Wadsworth where 

-- data WHNF {X : Set} : Λ X → Set where 
--   varWHNF : ∀ (x : X) → var x ∈ WHNF 
--   appWHNF : ∀ (s t : Λ X) → s ∈ WHNF → app s t ∈ WHNF 

WHNF : Λ𝓟 
WHNF t = ∀ u → ¬ (t ⟶w u) 

_⟵w*_ : Λ𝓡 
t ⟵w* s = (_⟶w_ ⋆) s t

WHNF↑ : Λ𝓟 
WHNF↑ = WHNF Λ↓ _⟵w*_

var⊆WHNF : ∀ {X} (x : X) → var x ∈ WHNF 
var⊆WHNF x u (red⟶w ())

appWHNF : ∀ {X} (x : X) (t : Λ X) → app (var x) t ∈ WHNF 
appWHNF x t u (appL⟶w (red⟶w ()))

abs[f]∈WHNF : ∀ {X Y} (s : Λ (↑ X)) (f : X → Λ Y) → (abs s [ f ] ∈ WHNF)
abs[f]∈WHNF s f u (red⟶w ())

WHNF-lemma : ∀ {X Y} (s : Λ X) (f : X → Λ Y) (t : Λ Y) → 
               (s [ f ] ⟶w t) → s ∈ WHNF ⊔ Σ[ u ∈ Λ X ] ((t ≡ (u [ f ])) × s ⟶w u)
WHNF-lemma (var x) f t s[f]->t = in1 (var⊆WHNF x)
WHNF-lemma (abs s0) f t (red⟶w ()) 
WHNF-lemma (app (var x) s2) f t (red⟶w r) = in1 (appWHNF x s2)
WHNF-lemma (app (abs s1) s2) f t (red⟶w (redex e)) = in2 ((s1 [ s2 ]ₒ) ,, e1 , red⟶w (redex refl))
  where e1 = ~ (subst-lemma s1 s2 f ! e)
WHNF-lemma (app s1 s2) f t (appL⟶w {t = u} s[f]->u) with WHNF-lemma s1 f u s[f]->u
... | in2 (v ,, u=v[f] , s1->v) = in2 (app v s2 ,, cong2 app u=v[f] refl , appL⟶w s1->v)
... | in1 s1∈WHNF = in1 g where 
  g : _ 
  g v (appL⟶w s1s2->v) = s1∈WHNF _ s1s2->v
  g v (red⟶w (redex {s = s} e)) = abs[f]∈WHNF s f u s[f]->u

-- Σ[ s ∈ Λ X ] (s ∈ P × R s t)

WHNF-subst : ∀ {X Y} (t : Λ X) (f : X → Λ Y) (v : Λ Y) → (v ∈ WHNF) → ((_⟶w_ ⋆) (t [ f ]) v) → t ∈ WHNF↑ 
WHNF-subst t f v v∈W ε⋆ = t ,, (λ u t->wu → v∈W (u [ f ]) (bind⟶w f t->wu)) , ε⋆
WHNF-subst t f v v∈W (_,⋆_ {y = u} t[f]->u u->*v)
  with WHNF-lemma t f u t[f]->u
... | in1 t∈WHNF = t ,, t∈WHNF , ε⋆
... | in2 (p ,, refl , t->p)
  with WHNF-subst p f v v∈W u->*v
... | u' ,, u'∈W , p→u' = u' ,, u'∈W , (t->p ,⋆ p→u')

data _⟶h_ {X} : Λ X → Λ X → Set where 
  red⟶h : ∀ {s t : Λ X} → s ⟶w t → s ⟶h t
  abs⟶h : ∀ {s t : Λ (↑ X)} → s ⟶h t → abs s ⟶h abs t 

⟶h⊆⟶β : ∀ {X} {s t : Λ X} → s ⟶h t → s ⟶β t
⟶h⊆⟶β (red⟶h x) = ⟶w⊆⟶β x
⟶h⊆⟶β (abs⟶h st) = abs⟶β (⟶h⊆⟶β st)

HNF : Λ𝓟 
HNF t = ∀ u → ¬ (t ⟶h u) 

_⟶h⋆_ : Λ𝓡 
_⟶h⋆_ {X} = _⟶h_ ⋆ 

_⟵h⋆_ : Λ𝓡 
t ⟵h⋆ s = (_⟶h_ ⋆) s t

HNF↑ : Λ𝓟 
HNF↑ = HNF Λ↓ _⟵h⋆_

var⊆HNF : ∀ {X} (x : X) → var x ∈ HNF 
var⊆HNF x u (red⟶h (red⟶w ())) 

appWHNF⊆HNF : ∀ {X} (s t : Λ X) → (app s t ∈ WHNF) → (app s t ∈ HNF)
appWHNF⊆HNF s t st∈W u (red⟶h x) = st∈W u x

absHNF : ∀ {X} (s : Λ (↑ X)) → s ∈ HNF → abs s ∈ HNF
absHNF s s∈H t (red⟶h (red⟶w ()))
absHNF s s∈H t (abs⟶h {t = u} λs->t) = s∈H u λs->t

bind⟶h : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶h t) → (s [ f ]) ⟶h (t [ f ])
bind⟶h f (red⟶h x) = red⟶h (bind⟶w f x)
bind⟶h f (abs⟶h st) = abs⟶h (bind⟶h (lift f) st) 

HNF-lemma : ∀ {X Y} (s : Λ X) (f : X → Λ Y) (t : Λ Y) → 
               (s [ f ] ⟶h t) → s ∈ HNF ⊔ Σ[ u ∈ Λ X ] ((t ≡ (u [ f ])) × s ⟶h u)
HNF-lemma (var x) f t s[f]t->s = in1 (var⊆HNF x)
HNF-lemma (abs s0) f t (red⟶h (red⟶w ()))
HNF-lemma (abs s0) f t (abs⟶h {t = u} s[f]t->s) 
  with HNF-lemma s0 (lift f) u s[f]t->s 
... | in1 s0∈H = in1 (absHNF s0 s0∈H)
... | in2 (t0 ,, refl , s0->t0) = in2 (abs t0 ,, refl , abs⟶h s0->t0)
HNF-lemma s@(app s1 s2) f t (red⟶h W)
  with WHNF-lemma s f t W
... | in1 s∈W = in1 (appWHNF⊆HNF s1 s2 s∈W)
... | in2 (u ,, refl , s1s2->u) = in2 (u ,, refl , red⟶h s1s2->u)

HNF-subst : ∀ {X Y} (t : Λ X) (f : X → Λ Y) (v : Λ Y) → (v ∈ HNF) → ((_⟶h_ ⋆) (t [ f ]) v) → t ∈ HNF↑ 
HNF-subst t f v v∈H ε⋆ = t ,, (λ u t->hu → v∈H (u [ f ]) (bind⟶h f t->hu)) , ε⋆
HNF-subst t f v v∈H (_,⋆_ {y = y} t[f]->y y->v) 
  with HNF-lemma t f y t[f]->y
... | in1 t∈H = t ,, t∈H , ε⋆
... | in2 (u ,, refl , t->u) 
  with HNF-subst u f v v∈H y->v
... | (w ,, w∈H , u->w) = w ,, w∈H , (t->u ,⋆ u->w)


module Solvable where 

  open import Datatypes 
  
  -- \MbI
  𝐈 : ∀ {X} → Λ X 
  𝐈 = abs (var o)

  𝐊ⁿ : ∀ {X} → ℕ → Λ X 
  𝐊ⁿ zero = 𝐈
  𝐊ⁿ (succ n) = abs (𝐊ⁿ n)

  𝐊ⁿ[] : ∀ {X Y} (σ : X → Λ Y) (n : ℕ) → 𝐊ⁿ n [ σ ] ≡ 𝐊ⁿ n 
  𝐊ⁿ[] σ zero = refl
  𝐊ⁿ[] σ (succ n) = cong abs (𝐊ⁿ[] (lift σ) n)

  ApplyList : ∀ {X} → Λ X → List (Λ X) → Λ X 
  ApplyList t [] = t
  ApplyList t (x ∷ xs) = ApplyList (app t x) xs 

  ApplyRed : ∀ {X} (s1 s2 : Λ X) (ts : List (Λ X)) → 
             s1 ⟶β s2 → ApplyList s1 ts ⟶β ApplyList s2 ts 
  ApplyRed s1 s2 [] = I
  ApplyRed s1 s2 (t0 ∷ ts) s12 = ApplyRed (app s1 t0) (app s2 t0) ts (appL⟶β s12)

  AppKⁿ : ∀ {X} (ts : List (Λ X)) (n : ℕ) → n ≡ length ts → ApplyList (𝐊ⁿ n) ts ⟶β⋆ 𝐈
  AppKⁿ [] zero refl = ε⋆
  AppKⁿ (t ∷ ts) (succ n) refl = ApplyRed (app (abs (𝐊ⁿ n)) t) (𝐊ⁿ n) ts R0 ,⋆ AppKⁿ ts n refl
                   where R0 = red⟶β (redex (𝐊ⁿ[] (io var t) (length ts)))

  ApplySub : ∀ {X Y} (σ : X → Λ Y) (t : Λ X) (ts : List (Λ X)) → 
               ApplyList t ts [ σ ] ≡ ApplyList (t [ σ ]) (List→ (bind σ) ts)
  ApplySub σ s [] = refl
  ApplySub σ s (t ∷ ts) = ApplySub σ (app s t) ts

  AppSolvable : Λ𝓟 
  AppSolvable {X} t = Σ[ ts ∈ List (Λ X) ] (ApplyList t ts ⟶β⋆ 𝐈)

  SubSolvable : Λ𝓟 
  SubSolvable {X} t = Σ[ σ ∈ (X → Λ ⊥) ] (t [ σ ] ⟶β⋆ 𝐈)

  Solvable : Λ𝓟 
  Solvable {X} t = Σ[ σ ∈ (X → Λ ⊥) ] AppSolvable (t [ σ ])

  SubSolvable⊆Solvable : ∀ {X} → SubSolvable {X} ⊆ Solvable 
  SubSolvable⊆Solvable t (σ ,, R) = σ ,, [] ,, R

  data HNF2 {X : Set} : Λ X → Set where 
    HNFneut : ∀ (x : X) (ts : List (Λ X)) → HNF2 (ApplyList (var x) ts) 
    HNFabs : ∀ (r : Λ (↑ X)) → HNF2 r → HNF2 (abs r)

  Neutral⊆Solvable : ∀ {X} (x : X) (ts : List (Λ X))
                     → SubSolvable (ApplyList (var x) ts)
  Neutral⊆Solvable {X} x ts = K (𝐊ⁿ (length ts)) ,, R where 
    e = List→length (λ t → t [ K (𝐊ⁿ (length ts)) ]) ts
    R0 = AppKⁿ (List→ (bind (K (𝐊ⁿ (length ts)))) ts) (length ts) e
    R = transp (λ x → x ⟶β⋆ 𝐈) (~ (ApplySub (K (𝐊ⁿ (length ts))) (var x) ts)) R0

  HNF2⊆Solvable : ∀ {X} → HNF2 {X} ⊆ Solvable 
  HNF2⊆Solvable t (HNFneut x ts) = 
    SubSolvable⊆Solvable (ApplyList (var x) ts) 
                         (Neutral⊆Solvable x ts)
  HNF2⊆Solvable t (HNFabs r h∈H) 
    with HNF2⊆Solvable r h∈H 
  ... | σ ,, ts ,, R = σ ∘ i ,, σ o ∷ ts ,, R0 ,⋆ R where 
    R0 = ApplyRed (app (abs r [ σ ∘ i ]) (σ o)) (r [ σ ]) ts (red⟶β (redex (~ e1)))
            where e0 = io𝓟 _ (λ x → ~ (bind-lift2 (σ o) (σ (i x)))) refl 
                  e1 = bind-assoc≅ {f = lift (σ ∘ i)} {io var (σ o)} {σ} e0 r
    
  HNF2↑⊆Solvable : ∀ {X} (t h : Λ X) → h ∈ HNF2 → t ⟶h⋆ h → t ∈ Solvable 
  HNF2↑⊆Solvable t h h∈H ε⋆ = HNF2⊆Solvable t h∈H
  HNF2↑⊆Solvable t h h∈H (_,⋆_ {y = u} t->u u->h) 
    with HNF2↑⊆Solvable u h h∈H u->h 
  ... | (σ ,, ps ,, R) = σ ,, ps ,, (ApplyRed (t [ σ ]) (u [ σ ]) ps (⟶h⊆⟶β t->u ⟶β[ σ ]) ,⋆ R)

