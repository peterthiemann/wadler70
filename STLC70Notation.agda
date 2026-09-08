{-# OPTIONS --rewriting #-}
module STLC70Notation where

-- Presentation-facing notation for Return of the Renamings.
--
-- The surface notation deliberately matches Explicit Weakening, but the
-- underlying representation does not.  In particular, ● abbreviates the
-- standard de Bruijn variable `var here`, and STLC70's _↑ is the derived
-- renaming operation M [ wkᴿ ]ᴿ rather than a constructor of terms.
--
-- Substitutions are functions, so Agda cannot overload the term-level
-- function _↑ or the context constructor _▷_ for them.  The substitution
-- forms therefore carry STLC70's ˢ marker: idˢ, _↑ˢ, _▷ˢ_, and _⨟ˢ_.

open import STLC70 public hiding (η-id; η-law)
open import Agda.Builtin.Equality using (_≡_; refl)

--! RoR >

infix  5 ƛ_
infixl 7 _·_
infixl 9 _[_]
infix  8 _↑ˢ
infixl 5 _▷ˢ_

-- Aligned term notation.

--! SurfaceTerms {
● : (Γ ▷ T) ⊢ T
● = var here

ƛ_ : (Γ ▷ T) ⊢ U → Γ ⊢ T ⇒ U
ƛ N = lam N

_·_ : Γ ⊢ T ⇒ U → Γ ⊢ T → Γ ⊢ U
L · M = app L M
--! }

-- Unadorned brackets denote substitution in the presentation.

--! SubstitutionNotation {
_[_] : Γ₁ ⊢ T → Sub Γ₁ Γ₂ → Γ₂ ⊢ T
M [ σ ] = M [ σ ]ˢ
--! }

-- Aligned substitution notation: weakening a substitution and consing a
-- term onto it, in Explicit Weakening's argument order.

--! SurfaceSubstitutions {
_↑ˢ : Sub Γ₁ Γ₂ → Sub Γ₁ (Γ₂ ▷ T)
σ ↑ˢ = σ ⨟ˢ ⟨ wkᴿ ⟩

_▷ˢ_ : Sub Γ₁ Γ₂ → Γ₂ ⊢ T → Sub (Γ₁ ▷ T) Γ₂
σ ▷ˢ M = M ∙ˢ σ
--! }

-- The presentation notation exposes the defining status of weakening.

--! WeakenByRenaming {
weaken-by-renaming :
  (M : Γ ⊢ T)
  → M ↑ ≡ M [ wkᴿ {T = U} ]ᴿ
weaken-by-renaming M = refl
--! }

-- The strictness witness can now be stated with exactly the same surface
-- term syntax as its Explicit Weakening analogue.

weakening-η : let _≡_ = _≡_ {A = Γ ▷ V ⊢ T ⇒ U} in
  (N : Γ ⊢ T ⇒ U) →
--! WeakeningEta {
  ((ƛ ((N ↑) · ●)) ↑) ≡ (ƛ (((N ↑) ↑) · ●))
--! }
weakening-η N = refl

-- Substitution η in the presentation notation.  The surface forms unfold
-- and rewrite to STLC70's η-id and η-law, so those proofs apply verbatim.

η-id :
  let _≡_ = _≡_ {A = Sub (Γ ▷ U) (Γ ▷ U)} in
--!! EtaId
    ((idˢ ↑ˢ) ▷ˢ ●) ≡ idˢ

η-id = STLC70.η-id

η-law :
  (σ : Sub (Γ ▷ U) Γ₂)
  → let _≡_ = _≡_ {A = Sub (Γ ▷ U) Γ₂} in
--!! EtaLaw
      (((idˢ ↑ˢ) ⨟ˢ σ) ▷ˢ (● [ σ ])) ≡ σ

η-law σ = STLC70.η-law

--! <

app-law : _↑ {U = U} (M · N)  ≡ (M ↑) · (N ↑)
app-law = refl
