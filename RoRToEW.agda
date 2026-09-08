{-# OPTIONS --rewriting #-}
module RoRToEW where

open import Weakening as EW
import STLC70Notation as RoR
open import WeakeningToSTLC70 using (Tm)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

-- EW terms are written in the common surface notation.  Their RoR
-- equality is equality of their interpretations in STLC70.
infix 4 _≡ᴿᵒᴿ_ _≡ᴱᵂ_

_≡ᴿᵒᴿ_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
M ≡ᴿᵒᴿ N = Tm M ≡ Tm N

_≡ᴱᵂ_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
M ≡ᴱᵂ N = M ≡ N

-- Literal form of the proposed comparison lemma.
RoR⇒EW-under-substitution :
  ∀ {Δ A} (M N : Δ ⊢ A) → Set
RoR⇒EW-under-substitution {Δ} M N =
  M ≡ᴿᵒᴿ N →
  ∀ {Γ} (s : Γ ⊨ Δ) → M [ s ] ≡ᴱᵂ N [ s ]

-- A possible restricted form: a cons substitution forces EW
-- instantiation to inspect and normalize the term structure.
RoR⇒EW-under-cons :
  ∀ {Δ A B} (M N : Δ ▷ B ⊢ A) → Set
RoR⇒EW-under-cons {Δ} {B = B} M N =
  M ≡ᴿᵒᴿ N →
  ∀ {Γ} (s : Γ ⊨ Δ) (P : Γ ⊢ B) →
    M [ s ▷ P ] ≡ᴱᵂ N [ s ▷ P ]

------------------------------------------------------------------------
-- Counterexamples

zero-weakened zero-unweakened : ∅ ▷ `ℕ ⊢ `ℕ
zero-weakened   = (zero {Γ = ∅}) ↑
zero-unweakened = zero

-- RoR computes weakening structurally, hence erases weakening on zero.
zero-weakened≡ᴿᵒᴿzero : zero-weakened ≡ᴿᵒᴿ zero-unweakened
zero-weakened≡ᴿᵒᴿzero = refl

-- EW retains the explicit weakening constructor.
zero-weakened≢ᴱᵂzero : zero-weakened ≡ᴱᵂ zero-unweakened → ⊥
zero-weakened≢ᴱᵂzero ()

RoR⇒EW-under-substitution-impossible :
  RoR⇒EW-under-substitution zero-weakened zero-unweakened → ⊥
RoR⇒EW-under-substitution-impossible theorem =
  zero-weakened≢ᴱᵂzero
    (theorem zero-weakened≡ᴿᵒᴿzero id)

twice-weakened-zero once-weakened-zero : ∅ ▷ `ℕ ▷ `ℕ ⊢ `ℕ
twice-weakened-zero = zero-weakened ↑
once-weakened-zero  = zero-unweakened ↑

twice-weakened≡ᴿᵒᴿonce-weakened :
  twice-weakened-zero ≡ᴿᵒᴿ once-weakened-zero
twice-weakened≡ᴿᵒᴿonce-weakened = refl

RoR⇒EW-under-cons-impossible :
  RoR⇒EW-under-cons twice-weakened-zero once-weakened-zero → ⊥
RoR⇒EW-under-cons-impossible theorem =
  zero-weakened≢ᴱᵂzero
    (theorem twice-weakened≡ᴿᵒᴿonce-weakened
      id zero-unweakened)
