module Automata.Composition.Union (Σ : Set) where

-- Standard libraries imports ----------------------------------------
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
----------------------------------------------------------------------

-- Thesis imports ----------------------------------------------------
open import Automata.Nondeterministic
----------------------------------------------------------------------

_∪_ : (M : NDA Σ) → (N : NDA Σ) → NDA Σ
⟨ Q₁ , S₁ , F₁ , Δ₁ ⟩ ∪ ⟨ Q₂ , S₂ , F₂ , Δ₂ ⟩ = ⟨ Q , S , F , Δ ⟩
  where
    Q : Set _
    Q = Q₁ ⊎ Q₂

    S : Q → Set _
    S (inj₁ q) = S₁ q
    S (inj₂ q) = S₂ q

    F : Q → Set
    F (inj₁ q) = F₁ q
    F (inj₂ q) = F₂ q

    Δ : Q → Σ → Q → Set
    Δ (inj₁ q) c (inj₁ q′) = Δ₁ q c q′
    Δ (inj₂ q) c (inj₂ q′) = Δ₂ q c q′
    {-# CATCHALL #-}
    Δ _ _ _ = ⊥ -- No connections between the machines

M-Δ*⇒M∪N-Δ* : {M N : NDA Σ}
             → let Q₁ = NDA.Q M
                   Δ₁* = NDA.Δ* M
                   Δ* = NDA.Δ* (M ∪ N) in
               (q : Q₁) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₁)
             → Δ₁* q xs q′
             → Δ* (inj₁ q) xs (inj₁ q′)
M-Δ*⇒M∪N-Δ* q [] .q refl = refl
M-Δ*⇒M∪N-Δ* q (x ∷ xs) q′ (q₀ , Δ₁-q-x-q₀ , Δ₁*-q₀-xs-q′) =
  inj₁ q₀ , Δ₁-q-x-q₀ , M-Δ*⇒M∪N-Δ* q₀ xs q′ Δ₁*-q₀-xs-q′

N-Δ*⇒M∪N-Δ* : {M N : NDA Σ}
             → let Q₂ = NDA.Q N
                   Δ₂* = NDA.Δ* N
                   Δ* = NDA.Δ* (M ∪ N) in
               (q : Q₂) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₂)
             → Δ₂* q xs q′
             → Δ* (inj₂ q) xs (inj₂ q′)
N-Δ*⇒M∪N-Δ* q [] .q refl = refl
N-Δ*⇒M∪N-Δ* q (x ∷ xs) q′ (q₀ , Δ₂-q-x-q₀ , Δ₂*-q₀-xs-q′) =
  inj₂ q₀ , Δ₂-q-x-q₀ , N-Δ*⇒M∪N-Δ* q₀ xs q′ Δ₂*-q₀-xs-q′

M∪N-Δ*⇒M-Δ* : {M N : NDA Σ}
             → let Q₁ = NDA.Q M
                   Δ₁* = NDA.Δ* M
                   Δ* = NDA.Δ* (M ∪ N) in
               (q : Q₁) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₁)
             → Δ* (inj₁ q) xs (inj₁ q′)
             → Δ₁* q xs q′
M∪N-Δ*⇒M-Δ* q [] .q refl = refl
M∪N-Δ*⇒M-Δ* q (x ∷ xs) q′ (inj₁ q₀ , Δ-q-x-q₀ , Δ*-q₀-xs-q′) =
  q₀ , Δ-q-x-q₀ , M∪N-Δ*⇒M-Δ* q₀ xs q′ Δ*-q₀-xs-q′

M∪N-Δ*⇒N-Δ* : {M N : NDA Σ}
             → let Q₂ = NDA.Q N
                   Δ₂* = NDA.Δ* N
                   Δ* = NDA.Δ* (M ∪ N) in
               (q : Q₂) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₂)
             → Δ* (inj₂ q) xs (inj₂ q′)
             → Δ₂* q xs q′
M∪N-Δ*⇒N-Δ* q [] .q refl = refl
M∪N-Δ*⇒N-Δ* q (x ∷ xs) q′ (inj₂ q₀ , Δ-q-x-q₀ , Δ*-q₀-xs-q′) =
  q₀ , Δ-q-x-q₀ , M∪N-Δ*⇒N-Δ* q₀ xs q′ Δ*-q₀-xs-q′

M∪N-Δ*-disconnectedˡ : {M N : NDA Σ}
                     → let Q₁ = NDA.Q M
                           Q₂ = NDA.Q N
                           Δ* = NDA.Δ* (M ∪ N) in
                       (q : Q₁) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₂)
                     → ¬ (Δ* (inj₁ q) xs (inj₂ q′))
M∪N-Δ*-disconnectedˡ q (x ∷ xs) q′ (inj₁ q₀ , _ , Δ*-q₀-xs-q′) =
  M∪N-Δ*-disconnectedˡ q₀ xs q′ Δ*-q₀-xs-q′

M∪N-Δ*-disconnectedʳ : {M N : NDA Σ}
                     → let Q₁ = NDA.Q M
                           Q₂ = NDA.Q N
                           Δ* = NDA.Δ* (M ∪ N) in
                       (q : Q₂) → {n : ℕ} → (xs : Vec Σ n) → (q′ : Q₁)
                     → ¬ (Δ* (inj₂ q) xs (inj₁ q′))
M∪N-Δ*-disconnectedʳ q (x ∷ xs) q′ (inj₂ q₀ , _ , Δ*-q₀-xs-q′) =
  M∪N-Δ*-disconnectedʳ q₀ xs q′ Δ*-q₀-xs-q′

M-Accepts⇒M∪N-Accepts : {M N : NDA Σ}
                      → {n : ℕ} → (xs : Vec Σ n)
                      → NDA.Accepts M xs
                      → NDA.Accepts (M ∪ N) xs
M-Accepts⇒M∪N-Accepts [] (q , S-q , .q , F-q , refl) =
  inj₁ q , S-q , inj₁ q , F-q , refl
M-Accepts⇒M∪N-Accepts (x ∷ xs)
  ( q  , S-q         -- The beginning state
  , q′ , F-q′       -- The ending state
  , q₀ , Δ₁-q-x-q₀   -- The first step
  , Δ₁*-q₀-xs-q′) =  -- The remaining steps
  -- Translate to the union:
    (inj₁ q , S-q        -- The beginning state
    , inj₁ q′ , F-q′     -- The ending state
    , inj₁ q₀ , Δ₁-q-x-q₀  -- The first step
    , M-Δ*⇒M∪N-Δ* q₀ xs q′ Δ₁*-q₀-xs-q′)   -- The remaining steps (applying I.H.)

N-Accepts⇒M∪N-Accepts : {M N : NDA Σ}
                      → {n : ℕ} → (xs : Vec Σ n)
                      → NDA.Accepts N xs
                      → NDA.Accepts (M ∪ N) xs
N-Accepts⇒M∪N-Accepts [] (q , S-q , .q , F-q , refl) =
  inj₂ q , S-q , inj₂ q , F-q , refl
N-Accepts⇒M∪N-Accepts (x ∷ xs)
  ( q , S-q
  , q′ , F-q′
  , q₀ , Δ-q-x-q₀
  , Δ*-q₀-xs-q′) =
    ( inj₂ q , S-q
    , inj₂ q′ , F-q′
    , inj₂ q₀ , Δ-q-x-q₀
    , N-Δ*⇒M∪N-Δ* q₀ xs q′ Δ*-q₀-xs-q′ )

----------------------------------------------------------------------

M∪N-Accepts⇒M-Accepts∨N-Accepts : {M N : NDA Σ}
                                → {n : ℕ} → (xs : Vec Σ n)
                                → NDA.Accepts (M ∪ N) xs
                                → NDA.Accepts M xs  ⊎  NDA.Accepts N xs

-- Base cases.

M∪N-Accepts⇒M-Accepts∨N-Accepts []
  (inj₁ q , S-q , .(inj₁ q) , F-q , refl) =
    inj₁ (q , S-q , q , F-q , refl)
M∪N-Accepts⇒M-Accepts∨N-Accepts []
  (inj₂ q , S-q , .(inj₂ q) , F-q , refl) =
    inj₂ (q , S-q , q , F-q , refl)

-- Induction step 1: both the start and final state are in M.

M∪N-Accepts⇒M-Accepts∨N-Accepts (x ∷ xs)
  ( inj₁ q  , S-q
  , inj₁ q′ , F-q′
  , inj₁ q₀ , Δ-q-x-q₀
  , Δ*-q₀-xs-q′) =
    inj₁ ( q , S-q
         , q′ , F-q′
         , q₀ , Δ-q-x-q₀
         , M∪N-Δ*⇒M-Δ* q₀ xs q′ Δ*-q₀-xs-q′)

-- Induction step 2: both the start and final state are in N.

M∪N-Accepts⇒M-Accepts∨N-Accepts (x ∷ xs)
  ( inj₂ q  , S-q
  , inj₂ q′ , F-q′
  , inj₂ q₀ , Δ-q-x-q₀
  , Δ*-q₀-xs-q′) =
    inj₂ ( q  , S-q
         , q′ , F-q′
         , q₀ , Δ-q-x-q₀
         , M∪N-Δ*⇒N-Δ* q₀ xs q′ Δ*-q₀-xs-q′)

-- Unreachable cases: the proof of “Accepts (M ∪ N) xs”
-- asserts M and N are connected.

M∪N-Accepts⇒M-Accepts∨N-Accepts (x ∷ xs)
  (inj₁ q , _ , inj₂ q′ , _ , inj₁ q₀ , _ , Δ*-q₀-xs-q′) =
    ⊥-elim (M∪N-Δ*-disconnectedˡ q₀ xs q′ Δ*-q₀-xs-q′)
M∪N-Accepts⇒M-Accepts∨N-Accepts (x ∷ xs)
  (inj₂ q , _ , inj₁ q′ , _ , inj₂ q₀ , _ , Δ*-q₀-xs-q′) =
    ⊥-elim (M∪N-Δ*-disconnectedʳ q₀ xs q′ Δ*-q₀-xs-q′)

----------------------------------------------------------------------
