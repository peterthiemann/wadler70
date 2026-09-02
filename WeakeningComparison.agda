{-# OPTIONS --rewriting #-}
module WeakeningComparison where

-- Philip Wadler, Explicit Weakening (2024), published Agda artifact:
-- https://homepages.inf.ed.ac.uk/wadler/papers/weakening/Weakening.lagda.md
-- The local copy only renames its module from Weaken to Weakening.
open import Weakening
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

--! EWComparison >

-- Corresponds to STLC70.example5: weakening commutes with η-expansion.
-- Written as the σ = id ↑ instance of STLC70.example3.
-- Here substitution reduces the proposed equality to
--   (ƛ ((N ↑) · ●)) ↑ ≡ ƛ (((N ↑) ↑) · ●)
-- whose outer constructors are different: _↑ versus ƛ_.
-- The hole is intentional; refl cannot fill it.
--! WeakeningEta {
example5 : ∀ {C} → (N : Γ ⊢ A ⇒ B) → Set
example5 {Γ}{A}{B}{C} N =
      let _≡_ = _≡_ {A = Γ ▷ C ⊢ A ⇒ B} in
      ((ƛ ((N ↑) · ●)) [ id ↑ ])
      ≡
      (ƛ (((N [ id ↑ ]) ↑) · ●))
--! }

-- In fact, no propositional proof of this equality can exist.
--! WeakeningEtaImpossible {
example5-impossible : (N : Γ ⊢ A ⇒ B)
  → _≡_ {A = Γ ▷ C ⊢ A ⇒ B}
      ((ƛ ((N ↑) · ●)) [ id ↑ ])
      (ƛ (((N [ id ↑ ]) ↑) · ●))
  → ⊥
--! }
--! WeakeningEtaImpossibleProof {
example5-impossible N ()
--! }

--! <
