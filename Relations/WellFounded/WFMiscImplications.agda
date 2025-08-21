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