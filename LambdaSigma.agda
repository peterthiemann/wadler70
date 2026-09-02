{-# OPTIONS --rewriting --local-confluence-check #-}
module LambdaSigma where

-- Abadi, Cardelli, Curien, Lévy, Explicit Substitutions:
-- §3.1 (printed p. 11): Beta and the ten basic σ rules.
-- §3.2 (printed p. 16): Id, IdR, VarShift, SCons.
-- §4   (printed pp. 27–30): first-order intrinsic typing.
--
-- Contexts are snoc lists, as in STLC70 and Weakening; the paper puts
-- the newest binding on the left. Sub Γ₁ Γ₂ maps Γ₁ terms to Γ₂ terms,
-- corresponding to the paper's judgment Γ₂ ⊢ σ ▷ Γ₁.
--
-- Only types and contexts are data. Terms, substitutions, and all their
-- constructors are postulates; their only computation is rewriting.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite public

infix 4 _⊢_
infixl 5 _▷_ _⨟ˢ_
infixr 6 _∙ˢ_
infixr 7 _⇒_
infix 8 _↑ _⇑ˢ
infixl 9 _[_]ˢ
infixl 6 _[_]₀ _[_]₁

data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type

data Ctx : Set where
  ∅   : Ctx
  _▷_ : Ctx → Type → Ctx

variable
  Γ Γ₁ Γ₂ Γ₃ : Ctx
  T U V : Type

postulate
  _⊢_ : Ctx → Type → Set
  Sub : Ctx → Ctx → Set

  -- S1-var, S1-lambda, S1-app, S1-clos (Definition 4.2).
  var₀  : (Γ ▷ T) ⊢ T
  lam   : (Γ ▷ T) ⊢ U → Γ ⊢ T ⇒ U
  app   : Γ ⊢ T ⇒ U → Γ ⊢ T → Γ ⊢ U
  _[_]ˢ : Γ₁ ⊢ T → Sub Γ₁ Γ₂ → Γ₂ ⊢ T

  -- S1-id, S1-shift, S1-cons, S1-comp (Definition 4.2).
  idˢ   : Sub Γ Γ
  wkˢ   : Sub Γ (Γ ▷ T)
  _∙ˢ_  : Γ₂ ⊢ T → Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) Γ₂
  _⨟ˢ_  : Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃

variable
  e e₁ e₂ : Γ ⊢ T
  σ σ₁ σ₂ σ₃ : Sub Γ₁ Γ₂

-- These are abbreviations, not additional constructors or rewrite rules.
-- In particular, lifting is the explicit cons prescribed by Abs, unlike
-- STLC70's primitive opaque lifting. Weakening is a closure, not a
-- constructor of terms as in Wadler's encoding.
_⇑ˢ : Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) (Γ₂ ▷ T)
σ ⇑ˢ = var₀ ∙ˢ (σ ⨟ˢ wkˢ)

_↑ : Γ ⊢ T → (Γ ▷ U) ⊢ T
e ↑ = e [ wkˢ ]ˢ

_[_]₀ : (Γ ▷ T) ⊢ U → Γ ⊢ T → Γ ⊢ U
e [ e₁ ]₀ = e [ e₁ ∙ˢ idˢ ]ˢ

_[_]₁ : ((Γ ▷ U) ▷ V) ⊢ T → Γ ⊢ U → (Γ ▷ V) ⊢ T
e [ e₁ ]₁ = e [ (e₁ ∙ˢ idˢ) ⇑ˢ ]ˢ

-- The type parameters of lam and _∙ˢ_ carry the annotations added in §4.
-- Thus the four changed rules (VarCons, Abs, ShiftCons, Map) preserve
-- the binder/cons type without performing substitution on types.
postulate
  Beta      : app (lam e) e₁                 ≡ e [ e₁ ∙ˢ idˢ ]ˢ
  VarId     : var₀ {Γ} {T} [ idˢ ]ˢ         ≡ var₀
  VarCons   : var₀ [ e ∙ˢ σ ]ˢ              ≡ e
  App       : app e₁ e₂ [ σ ]ˢ              ≡ app (e₁ [ σ ]ˢ) (e₂ [ σ ]ˢ)
  Abs       : lam e [ σ ]ˢ                  ≡ lam (e [ var₀ ∙ˢ (σ ⨟ˢ wkˢ) ]ˢ)
  Clos      : e [ σ₁ ]ˢ [ σ₂ ]ˢ             ≡ e [ σ₁ ⨟ˢ σ₂ ]ˢ
  IdL       : idˢ ⨟ˢ σ                      ≡ σ
  ShiftId   : wkˢ {Γ} {T} ⨟ˢ idˢ            ≡ wkˢ
  ShiftCons : wkˢ ⨟ˢ (e ∙ˢ σ)               ≡ σ
  Map       : (e ∙ˢ σ₁) ⨟ˢ σ₂              ≡ (e [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ˢ σ₂)
  Ass       : (σ₁ ⨟ˢ σ₂) ⨟ˢ σ₃             ≡ σ₁ ⨟ˢ (σ₂ ⨟ˢ σ₃)

  -- The four additions from §3.2, also covered by §4's subject reduction.
  -- VarShift and SCons are substitution η, not function η-reduction.
  Id        : e [ idˢ ]ˢ                    ≡ e
  IdR       : σ ⨟ˢ idˢ                      ≡ σ
  VarShift  : (var₀ {Γ} {T} ∙ˢ wkˢ)         ≡ idˢ
  SCons     : (var₀ [ σ ]ˢ) ∙ˢ (wkˢ ⨟ˢ σ)  ≡ σ

-- no Beta

{-# REWRITE
  VarId VarCons App Abs Clos
  IdL ShiftId ShiftCons Map Ass
  Id IdR VarShift
  SCons
#-}

-- This is the extended system from §3.2. The paper distinguishes local
-- confluence from global confluence with term/substitution metavariables;
-- see its warning on printed p. 17. A local Agda check is not a proof of
-- global confluence or termination of this postulated calculus.

