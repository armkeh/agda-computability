module Automata.Nondeterministic where

-- Standard libraries imports ----------------------------------------
open import Level using ()
  renaming (zero to ℓ₀)

open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Vec using (Vec ; [] ; _∷_)

open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_)
----------------------------------------------------------------------

-- Thesis imports ----------------------------------------------------
open import Utilities.ExistsSyntax using (∃-syntax)
----------------------------------------------------------------------

record NDA (Σ : Set) : Set₁ where
  constructor ⟨_,_,_,_⟩

  field
    Q : Set
    S : Pred Q ℓ₀
    F : Pred Q ℓ₀
    Δ : Q → Σ → Pred Q ℓ₀

  Δ* : Q → {n : ℕ} → Vec Σ n → Pred Q ℓ₀
  Δ* q [] = q ≡_
  Δ* q (x ∷ xs) q′ = ∃ q₀ ∶ Q • ((Δ q x q₀) × (Δ* q₀ xs q′))

  Accepts : {n : ℕ} → Pred (Vec Σ n) ℓ₀
  Accepts xs = ∃ q ∶ Q • (S q
                       × ∃ q′ ∶ Q • ((F q′)
                                  × (Δ* q xs q′)))

  -- :TODO: are these useful?
  _-Reachable : ℕ → Q → Pred Q ℓ₀
  _-Reachable n q q′ = ∃ xs ∶ Vec Σ n • (Δ* q xs q′)

  Reachable : Q → Pred Q ℓ₀
  Reachable q q′ = ∃ n ∶ ℕ • (n -Reachable) q q′
