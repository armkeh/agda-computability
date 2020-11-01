module Utilities.VecSplit where

-- Standard libraries imports ----------------------------------------
open import Data.Nat using (ℕ ; _+_)
open import Data.Vec using (Vec ; _++_)

open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_)
----------------------------------------------------------------------

record Split {A : Set} {n : ℕ} (xs : Vec A n) : Set where
  field
    {m₁} {m₂} : ℕ
    n≡m₁+m₂ : n ≡ m₁ + m₂
    ys : Vec A m₁
    zs : Vec A m₂
    xs≅ys++zs : xs ≅ ys ++ zs
