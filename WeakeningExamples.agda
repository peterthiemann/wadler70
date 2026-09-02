{-# OPTIONS --rewriting #-}
module WeakeningExamples where

open import Weakening
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

--! EWExamples >

-- STLC70.example3, translated to Wadler's explicit-weakening syntax.
-- It is stated as a proposition because it does not hold for every σ.
--! SubstEta {
example3 : (N : Δ ⊢ A ⇒ B) (σ : Γ ⊨ Δ) → Set
example3 N σ =
  (ƛ (N ↑ · ●)) [ σ ] ≡ ƛ ((N [ σ ]) ↑ · ●)
--! }

-- Identity and cons substitutions push through the outer lambda.
example3-id : (N : Γ ⊢ A ⇒ B) → example3 N id
example3-id N = refl

example3-cons :
  (N : Δ ▷ C ⊢ A ⇒ B) (σ : Γ ⊨ Δ) (M : Γ ⊢ C)
  → example3 N (σ ▷ M)
example3-cons N σ M = refl

-- For a weakened substitution, the two sides reduce to terms with
-- distinct outer constructors:
--   (ƛ ((N [ σ ]) ↑ · ●)) ↑
--   ƛ (((N [ σ ]) ↑) ↑ · ●)
example3-weaken-impossible :
  (N : Δ ⊢ A ⇒ B) (σ : Γ ⊨ Δ)
  → example3 N (_↑ {A = C} σ) → ⊥
example3-weaken-impossible N σ ()

I-closed : ∅ ⊢ `ℕ ⇒ `ℕ
I-closed = ƛ ●

wk-empty : ∅ ▷ `ℕ ⊨ ∅
wk-empty = id ↑

-- Consequently there is no proof of example3 uniformly for all
-- intrinsically typed terms and substitutions in Weakening.
--! SubstEtaUnprovable {
example3-unprovable :
  (∀ {Γ Δ A B} (N : Δ ⊢ A ⇒ B) (σ : Γ ⊨ Δ) → example3 N σ)
  → ⊥
example3-unprovable theorem =
  example3-weaken-impossible
    {C = `ℕ}
    I-closed id (theorem I-closed wk-empty)
--! }


-- STLC70.example4, translated to Wadler's notation. Here σ ↑ ▷ ●
-- is the lift of σ under the newest binder.
--! SubstSingle {
example4 :
  (N : Δ ▷ A ⊢ B) (M : Δ ⊢ A) (σ : Γ ⊨ Δ) → Set
example4 N M σ =
  (N [ id ▷ M ]) [ σ ]
    ≡ (N [ σ ↑ ▷ ● ]) [ id ▷ (M [ σ ]) ]
--! }

example4-id : (N : Γ ▷ A ⊢ B) (M : Γ ⊢ A)
  → example4 N M id
example4-id N M = refl

example4-cons :
  (N : Δ ▷ C ▷ A ⊢ B) (M : Δ ▷ C ⊢ A)
  (σ : Γ ⊨ Δ) (P : Γ ⊢ C)
  → example4 N M (σ ▷ P)
example4-cons N M σ P = refl

-- A concrete weakening case reduces to an outer _↑ on the left and
-- an outer ƛ_ on the right, so the proposed equality is impossible.
I-open : ∅ ▷ (`ℕ ⇒ `ℕ) ⊢ `ℕ ⇒ `ℕ
I-open = ƛ ●

example4-weaken-impossible :
  example4 I-open I-closed wk-empty → ⊥
example4-weaken-impossible ()

-- Hence STLC70.example4 also has no uniform proof in Weakening.
--! SubstSingleUnprovable {
example4-unprovable :
  (∀ {Γ Δ A B} (N : Δ ▷ A ⊢ B) (M : Δ ⊢ A) (σ : Γ ⊨ Δ)
    → example4 N M σ)
  → ⊥
example4-unprovable theorem =
  example4-weaken-impossible
    (theorem I-open I-closed wk-empty)
--! }

--! <
