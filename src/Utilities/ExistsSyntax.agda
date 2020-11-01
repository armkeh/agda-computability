module Utilities.ExistsSyntax where

open import Level using (Level ; _⊔_)
open import Data.Product using (Σ)

variable
  a b : Level
  A : Set a
  B : Set b

∃-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
∃-syntax = Σ

syntax ∃-syntax A (λ x → B) = ∃ x ∶ A • B
