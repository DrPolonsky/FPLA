open import Logic
open import Lifting
open import Lambda
open import Reduction
open import Predicates

module Conversion where

open import ARS.Base

module BetaConversion where

  -- The canonical proof terms for beta conversion
  _=β_ : ΛRel
  s =β t = s ↘ (_⟶β⋆_) ↙ t
  -- _↘R↙_ is a "valley" for the relation R, defined in ARS.Base

  -- Perhaps we should make the left side into a standard reduction?

open BetaConversion public
