{-# OPTIONS --rewriting #-}
module WeakeningToSTLC70 where

import Weakening as W
import STLC70 as S

open import Agda.Builtin.Equality using (_≡_; refl)

--! Translation >

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

------------------------------------------------------------------------
-- A type- and natural-number-preserving interpretation of Wadler's
-- explicit-weakening calculus.

Ty : W.Type → S.Type
Ty W.`ℕ          = S.`ℕ
Ty (W._⇒_ A B)  = S._⇒_ (Ty A) (Ty B)

Cx : W.Con → S.Ctx
Cx W.∅          = S.∅
Cx (W._▷_ Γ A) = S._▷_ (Cx Γ) (Ty A)

Tm : ∀ {Γ A} → W._⊢_ Γ A → S._⊢_ (Cx Γ) (Ty A)
Tm W.●             = S.var S.here
Tm (W._↑ M)        = S._↑ (Tm M)
Tm (W.ƛ_ N)        = S.lam (Tm N)
Tm (W._·_ L M)     = S.app (Tm L) (Tm M)
Tm W.zero          = S.zero
Tm (W.suc M)       = S.suc (Tm M)

Sb : ∀ {Γ Δ} → W._⊨_ Γ Δ → S.Sub (Cx Δ) (Cx Γ)
Sb W.id          = S.idˢ
Sb (W._↑ σ)     = S._⨟ˢ_ (Sb σ) (S.⟨ S.wkᴿ ⟩)
Sb (W._▷_ σ M)  = S._∙ˢ_ (Tm M) (Sb σ)

cong-postcompose :
  ∀ {Γ₁ Γ₂ Γ₃} {σ τ : S.Sub Γ₁ Γ₂} (υ : S.Sub Γ₂ Γ₃)
  → _≡_ {A = S.Sub Γ₁ Γ₂} σ τ
  → _≡_ {A = S.Sub Γ₁ Γ₃} (S._⨟ˢ_ σ υ) (S._⨟ˢ_ τ υ)
cong-postcompose υ refl = refl

cong-extend :
  ∀ {Γ₁ Γ₂ T} {e e′ : S._⊢_ Γ₂ T} {σ τ : S.Sub Γ₁ Γ₂}
  → e ≡ e′
  → _≡_ {A = S.Sub Γ₁ Γ₂} σ τ
  → _≡_ {A = S.Sub (S._▷_ Γ₁ T) Γ₂}
      (S._∙ˢ_ e σ) (S._∙ˢ_ e′ τ)
cong-extend refl refl = refl

-- Wadler writes lifting as explicit weakening followed by consing the
-- newest variable.  STLC70 packages the same map as _⇑ˢ.
translate-lift :
  ∀ {Γ Δ A} (σ : W._⊨_ Γ Δ)
  → _≡_ {A = S.Sub (Cx (W._▷_ Δ A)) (Cx (W._▷_ Γ A))}
      (Sb (W._▷_ (W._↑ σ) W.●)) (S._⇑ˢ (Sb σ))
translate-lift σ = S.η-law

------------------------------------------------------------------------
-- Every propositional equality in Weakening has an STLC70 proof.

--! PreserveEquations {
preserve-term-equation :
  ∀ {Γ A} {M N : W._⊢_ Γ A}
  → M ≡ N
  → Tm M ≡ Tm N
preserve-term-equation refl = refl

preserve-substitution-equation :
  ∀ {Γ Δ} {σ τ : W._⊨_ Γ Δ}
  → σ ≡ τ
  → _≡_ {A = S.Sub (Cx Δ) (Cx Γ)} (Sb σ) (Sb τ)
preserve-substitution-equation refl = refl
--! }

------------------------------------------------------------------------
-- The interpretation respects the two substitution operations.

translate-instantiation :
  ∀ {Γ Δ A} (M : W._⊢_ Δ A) (σ : W._⊨_ Γ Δ)
  → Tm (W._[_] M σ) ≡ S._[_]ˢ (Tm M) (Sb σ)
translate-instantiation M W.id = refl
translate-instantiation M (σ W.↑) = cong S._↑ (translate-instantiation M σ)
translate-instantiation W.● (σ W.▷ M₁) = refl
translate-instantiation (M W.↑) (σ W.▷ M₁) =
  translate-instantiation M σ
translate-instantiation (W.ƛ M) (σ W.▷ M₁) =
  cong S.lam
    (trans
      (translate-instantiation M ((σ W.▷ M₁) W.↑ W.▷ W.●))
      (cong (S._[_]ˢ (Tm M)) (translate-lift (σ W.▷ M₁))))
translate-instantiation (M W.· M₂) (σ W.▷ M₁) =
  cong₂ S.app
    (translate-instantiation M (σ W.▷ M₁))
    (translate-instantiation M₂ (σ W.▷ M₁))
translate-instantiation W.zero (σ W.▷ M₁) = refl
translate-instantiation (W.suc M) (σ W.▷ M₁) =
  cong S.suc (translate-instantiation M (σ W.▷ M₁))

translate-composition :
  ∀ {Γ Δ Θ} (σ : W._⊨_ Θ Δ) (τ : W._⊨_ Γ Θ)
  → _≡_ {A = S.Sub (Cx Δ) (Cx Γ)}
      (Sb (W._⨾_ σ τ)) (S._⨟ˢ_ (Sb σ) (Sb τ))
translate-composition σ W.id = refl
translate-composition {Δ = Δ} σ (W._↑ {Γ = Γ} {A = A} τ) =
  cong-postcompose (S.⟨ S.wkᴿ {Γ = Cx Γ} {T = Ty A} ⟩)
    (translate-composition σ τ)
translate-composition W.id (τ W.▷ M) = refl
translate-composition (σ W.↑) (τ W.▷ M) =
  translate-composition σ τ
translate-composition (σ W.▷ M₁) (τ W.▷ M) =
  cong-extend
    (translate-instantiation M₁ (τ W.▷ M))
    (translate-composition σ (τ W.▷ M))

------------------------------------------------------------------------
-- Equations written with the source operations translate to equations
-- written with the corresponding STLC70 operations.

sound-instantiation-equation :
  ∀ {Γ Δ A} {M N : W._⊢_ Δ A} {σ τ : W._⊨_ Γ Δ}
  → W._[_] M σ ≡ W._[_] N τ
  → S._[_]ˢ (Tm M) (Sb σ) ≡ S._[_]ˢ (Tm N) (Sb τ)
sound-instantiation-equation {M = M} {N = N} {σ = σ} {τ = τ} p =
  trans (sym (translate-instantiation M σ))
    (trans (preserve-term-equation p) (translate-instantiation N τ))

sound-composition-equation :
  ∀ {Γ Δ Θ}
    {σ σ′ : W._⊨_ Θ Δ} {τ τ′ : W._⊨_ Γ Θ}
  → W._⨾_ σ τ ≡ W._⨾_ σ′ τ′
  → _≡_ {A = S.Sub (Cx Δ) (Cx Γ)}
      (S._⨟ˢ_ (Sb σ) (Sb τ)) (S._⨟ˢ_ (Sb σ′) (Sb τ′))
sound-composition-equation
    {σ = σ} {σ′ = σ′} {τ = τ} {τ′ = τ′} p =
  trans (sym (translate-composition σ τ))
    (trans (preserve-substitution-equation p)
           (translate-composition σ′ τ′))

--! <
