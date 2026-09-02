{-# OPTIONS --rewriting #-}
module WeakeningEta where

open import Weakening
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

--! EWEta >

-- The STLC70 substitution η-laws, translated to Wadler's notation.
-- These name propositions, not proofs. In particular, Γ ⊨ Δ denotes
-- substitution syntax here, rather than a function on variables.
--! EtaId {
η-id : (Γ : Con) (A : Type) → Set
η-id Γ A = let _≡_ = _≡_ {A = (Γ ▷ A) ⊨ (Γ ▷ A)} in
           ((id ↑) ▷ ●) ≡ id
--! }

--! EtaLaw {
η-law : (σ : Γ ⊨ Δ ▷ A) → Set
η-law σ = (((id ↑) ⨾ σ) ▷ (● [ σ ])) ≡ σ
--! }

-- η-id is false as an equality of substitution syntax: cons is not id.
η-id-impossible : η-id Γ A → ⊥
η-id-impossible ()

-- The id instance of η-law is precisely η-id, hence also false.
η-law-id-impossible : η-law (id {Δ = Γ ▷ A}) → ⊥
η-law-id-impossible ()

-- Every weakening instance also has distinct outer constructors:
-- the reconstructed substitution is a cons, while σ ↑ is a weakening.
η-law-wk-impossible : (σ : Γ ⊨ Δ ▷ A)
  → η-law (_↑ {A = B} σ) → ⊥
η-law-wk-impossible σ ()

-- The cons case does hold, by the published definitions and rewrites.
η-law-cons : (σ : Γ ⊨ Δ) (M : Γ ⊢ A) → η-law (σ ▷ M)
η-law-cons σ M = refl

-- Thus there cannot be a proof of η-law for all substitutions.
--! EtaLawImpossible {
η-law-impossible :
  (∀ {Γ Δ A} (σ : Γ ⊨ Δ ▷ A) → η-law σ) → ⊥
η-law-impossible law = η-law-id-impossible {Γ = ∅} {A = `ℕ} (law id)
--! }

--! <
