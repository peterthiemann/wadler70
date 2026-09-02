-- ════════════════════════════════════════════════════════════════════
-- SIMPLY TYPED λ-CALCULUS, intrinsically typed.
--
-- The small running example of the paper's introduction: intrinsically
-- typed syntax, two presentations of its denotational semantics, and a
-- progress theorem for weak-head reduction.  Substitution is defined
-- the textbook way, first, then using σ-calculus.
--
-- ════════════════════════════════════════════════════════════════════
{-# OPTIONS --rewriting #-}
module STLC70 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite public
import Agda.Builtin.Nat as Nat
open import Axiom.Extensionality.Propositional
  using (Extensionality; implicit-extensionality)
open import Relation.Binary.PropositionalEquality
  using (cong; module ≡-Reasoning)

-- As in SystemF, equalities of whole maps use function extensionality.
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

infix 4 _⊢_
infixl 5 _▷_ _⨟ᴿ_ _⨟ˢ_
infixr 7 _⇒_
infix 8 _↑

--! STLC >
--! TypeCtx {
data Type : Set where
  `ℕ   : Type
  _⇒_  : Type → Type → Type

data Ctx : Set where
  ∅    : Ctx
  _▷_  : Ctx → Type → Ctx
--! }

variable
  Γ Γ₁ Γ₂ Γ₃ : Ctx
  T U V : Type
--! Var
data _∋_ : Ctx → Type → Set where
  here   : (Γ ▷ T) ∋ T
  there  : Γ ∋ T → (Γ ▷ U) ∋ T

variable
  x y z : Γ ∋ T

--! Expr
data _⊢_ Γ : Type → Set where
  zero : Γ ⊢ `ℕ
  suc  : Γ ⊢ `ℕ → Γ ⊢ `ℕ
  var  : Γ ∋ T → Γ ⊢ T
  lam  : (Γ ▷ T) ⊢ U → Γ ⊢ (T ⇒ U)
  app  : Γ ⊢ (T ⇒ U) → Γ ⊢ T → Γ ⊢ U

--! Domains {
𝓣⟦_⟧        : Type → Set
𝓣⟦ `ℕ ⟧     = Nat.Nat
𝓣⟦ T ⇒ U ⟧  = 𝓣⟦ T ⟧ → 𝓣⟦ U ⟧
--! }
--! DenotationalA {
data 𝓖⟦_⟧ : Ctx → Set where
  []   : 𝓖⟦ ∅ ⟧
  _▷_  : 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧ → 𝓖⟦ Γ ▷ T ⟧

_◇_ : 𝓖⟦ Γ ⟧ → Γ ∋ T → 𝓣⟦ T ⟧
(_ ▷ v) ◇ here     = v
(γ ▷ _) ◇ there x  = γ ◇ x

𝓔⟦_⟧ : Γ ⊢ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ zero       ⟧ γ = Nat.zero
𝓔⟦ suc e      ⟧ γ = Nat.suc (𝓔⟦ e ⟧ γ)
𝓔⟦ var x      ⟧ γ = γ ◇ x
𝓔⟦ lam e      ⟧ γ = λ v → 𝓔⟦ e ⟧ (γ ▷ v)
𝓔⟦ app e₁ e₂  ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)
--! }
--! DenotationalB {
𝓗⟦_⟧    : Ctx → Set
𝓗⟦ Γ ⟧  = ∀ {T} → Γ ∋ T → 𝓣⟦ T ⟧

_▷▷_ : 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧ → 𝓗⟦ Γ ▷ T ⟧
(γ ▷▷ v) here       = v
(γ ▷▷ v) (there x)  = γ x

𝓔′⟦_⟧ : Γ ⊢ T → 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔′⟦ zero       ⟧ γ  = Nat.zero
𝓔′⟦ suc e      ⟧ γ  = Nat.suc (𝓔′⟦ e ⟧ γ)
𝓔′⟦ var x      ⟧ γ  = γ x
𝓔′⟦ lam e      ⟧ γ  = λ v → 𝓔′⟦ e ⟧ (γ ▷▷ v)
𝓔′⟦ app e₁ e₂  ⟧ γ  = 𝓔′⟦ e₁ ⟧ γ (𝓔′⟦ e₂ ⟧ γ)
--! }

_  : ∅ ⊢ (`ℕ ⇒ `ℕ)
_  = lam zero

_  : ∅ ⊢ (`ℕ ⇒ `ℕ)
_  = lam (var here)

variable
  e e₁ e₂ e′ e₁′ : Γ ⊢ T

-- The textbook substitution machinery, named as in the System F
-- development (SystemF.agda §2 and §5) so that the two can be compared
-- directly: ᴿ marks the renaming world, ˢ the substitution world.
Ren : Ctx → Ctx → Set
Ren Γ₁ Γ₂ = ∀ {T} → Γ₁ ∋ T → Γ₂ ∋ T

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : Ren Γ₁ Γ₂

opaque

  -- weakening, and lifting a renaming under a binder
  wkᴿ : Ren Γ (Γ ▷ T)
  wkᴿ = there

  idᴿ : Ren Γ Γ
  idᴿ x = x

  _∙ᴿ_ : Γ₂ ∋ T → Ren Γ₁ Γ₂ → Ren (Γ₁ ▷ T) Γ₂
  (x ∙ᴿ ρ) here = x
  (x ∙ᴿ ρ) (there y) = ρ y

  -- apply renaming to variable
  _&ᴿ_ : Γ₁ ∋ T → Ren Γ₁ Γ₂ → Γ₂ ∋ T
  x &ᴿ ρ = ρ x

  -- left-to-right composition
  _⨟ᴿ_ : Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
  (ρ₁ ⨟ᴿ ρ₂) x = ρ₂ (ρ₁ x)

  _⇑ᴿ : Ren Γ₁ Γ₂ → Ren (Γ₁ ▷ T) (Γ₂ ▷ T)
  (ρ ⇑ᴿ) here      = here
  (ρ ⇑ᴿ) (there x) = there (ρ x)

_[_]ᴿ : Γ₁ ⊢ T → Ren Γ₁ Γ₂ → Γ₂ ⊢ T
zero       [ ρ ]ᴿ = zero
suc e      [ ρ ]ᴿ = suc (e [ ρ ]ᴿ)
var x      [ ρ ]ᴿ = var (x &ᴿ ρ)
lam e      [ ρ ]ᴿ = lam (e [ ρ ⇑ᴿ ]ᴿ)
app e₁ e₂  [ ρ ]ᴿ = app (e₁ [ ρ ]ᴿ) (e₂ [ ρ ]ᴿ)

-- convenience definitions

_↑ : Γ ⊢ T → (Γ ▷ U) ⊢ T
e ↑ = e [ wkᴿ ]ᴿ

Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = ∀ {T} → Γ₁ ∋ T → Γ₂ ⊢ T

variable
  σ σ′ σ₁ σ₂ σ₃ : Sub Γ₁ Γ₂

opaque

  -- the identity substitution, extension, and lifting under a binder
  ⟨_⟩ : Ren Γ₁ Γ₂ → Sub Γ₁ Γ₂
  ⟨ ρ ⟩ x = var (ρ x)

  _∙ˢ_ : Γ₂ ⊢ T → Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) Γ₂
  (e ∙ˢ σ) here      = e
  (e ∙ˢ σ) (there x) = σ x

  _&ˢ_ : Γ₁ ∋ T → Sub Γ₁ Γ₂ → Γ₂ ⊢ T
  x &ˢ σ = σ x

  _⇑ˢ : Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) (Γ₂ ▷ T)
  (σ ⇑ˢ) here      = var here
  (σ ⇑ˢ) (there x) = (σ x) [ wkᴿ ]ᴿ


idˢ : Sub Γ Γ
idˢ = ⟨ idᴿ ⟩


_[_]ˢ : Γ₁ ⊢ T → Sub Γ₁ Γ₂ → Γ₂ ⊢ T
zero       [ σ ]ˢ = zero
suc e      [ σ ]ˢ = suc (e [ σ ]ˢ)
var x      [ σ ]ˢ = x &ˢ σ
lam e      [ σ ]ˢ = lam (e [ σ ⇑ˢ ]ˢ)
app e₁ e₂  [ σ ]ˢ = app (e₁ [ σ ]ˢ) (e₂ [ σ ]ˢ)

opaque
  _⨟ˢ_ : Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
  (σ₁ ⨟ˢ σ₂) x = (σ₁ x) [ σ₂ ]ˢ

_[_]₀ : (Γ ▷ T) ⊢ U → Γ ⊢ T → Γ ⊢ U
e [ e′ ]₀ = e [ e′ ∙ˢ idˢ ]ˢ

_[_]₁ : ((Γ ▷ U) ▷ V) ⊢ T → Γ ⊢ U → (Γ ▷ V) ⊢ T
e [ e′ ]₁ = e [ (e′ ∙ˢ idˢ) ⇑ˢ ]ˢ

--! SmallStep {
data _⟶_ {Γ} {T} : Γ ⊢ T → Γ ⊢ T → Set where
  β-lam  : app (lam e₁) e₂ ⟶ (e₁ [ e₂ ]₀)
  ξ-app  : e₁ ⟶ e₁′ → app e₁ e₂ ⟶ app e₁′ e₂
--! }

--! Progress {
data Value {Γ} : Γ ⊢ T → Set where
  zero : Value zero
  suc  : (e : Γ ⊢ `ℕ) → Value (suc e)
  lam  : (e : (Γ ▷ T) ⊢ U) → Value (lam e)

data Progress (e : Γ ⊢ T) : Set where
  done  : Value e → Progress e
  step  : e ⟶ e′ → Progress e

progress : (e : ∅ ⊢ T) → Progress e
progress zero     = done zero
progress (suc e)  = done (suc e)
progress (lam e)  = done (lam e)
progress (app e₁ e₂)
  with progress e₁
... | step x        = step (ξ-app x)
... | done (lam e)  = step β-lam
--! }

-- now for something real: postulate the σ-calculus with first-class renamings

-- The registered equalities from SystemF.agda §3, adapted to typed
-- variables and expressions.  Lifting stays first-class and opaque;
-- coincidence is oriented from substitutions to renamings.
-- Explicit equality carriers preserve the implicit type argument of
-- Ren and Sub, so these laws equate the full polymorphic maps.
postulate
  -- Renaming: application, composition, and lifting.
  `beta-id          : x &ᴿ idᴿ                      ≡ x
  `beta-wk          : x &ᴿ wkᴿ                      ≡ there {U = U} x
  `beta-ext-zero    : here &ᴿ (x ∙ᴿ ρ)              ≡ x
  `beta-ext-suc     : there x &ᴿ (y ∙ᴿ ρ)           ≡ x &ᴿ ρ
  `beta-lift-zero   : here {T = T} &ᴿ (ρ ⇑ᴿ)        ≡ here
  `beta-lift-suc    : there {U = U} x &ᴿ (ρ ⇑ᴿ)     ≡ there (x &ᴿ ρ)
  `beta-comp        : x &ᴿ (ρ₁ ⨟ᴿ ρ₂)               ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
  `beta-lift-fusion : (x &ᴿ (ρ₁ ⇑ᴿ)) &ᴿ (ρ₂ ⇑ᴿ)    ≡ x &ᴿ ((ρ₁ ⨟ᴿ ρ₂) ⇑ᴿ)
  `associativity : _≡_ {A = Ren _ _}
    ((ρ₁ ⨟ᴿ ρ₂) ⨟ᴿ ρ₃) (ρ₁ ⨟ᴿ (ρ₂ ⨟ᴿ ρ₃))
  `interact : _≡_ {A = Ren _ _}
    (wkᴿ ⨟ᴿ (x ∙ᴿ ρ)) ρ
  `interact-⨟ : _≡_ {A = Ren _ _}
    (wkᴿ ⨟ᴿ ((x ∙ᴿ ρ) ⨟ᴿ ρ′)) (ρ ⨟ᴿ ρ′)
  `comp-idᵣ : _≡_ {A = Ren _ _}
    (ρ ⨟ᴿ idᴿ) ρ
  `comp-idₗ : _≡_ {A = Ren _ _}
    (idᴿ ⨟ᴿ ρ) ρ
  `lift-id : _≡_ {A = Ren _ _}
    (idᴿ {Γ} ⇑ᴿ) (idᴿ {Γ ▷ T})
  `lift-wk : _≡_ {A = Ren _ _}
    (wkᴿ ⨟ᴿ (ρ ⇑ᴿ)) (ρ ⨟ᴿ wkᴿ {T = T})
  `lift-fusion : _≡_ {A = Ren _ _}
    ((ρ₁ ⇑ᴿ) ⨟ᴿ (ρ₂ ⇑ᴿ)) (_⇑ᴿ {T = T} (ρ₁ ⨟ᴿ ρ₂))
  `lift-wk-⨟ : _≡_ {A = Ren _ _}
    (wkᴿ ⨟ᴿ ((ρ ⇑ᴿ) ⨟ᴿ ρ′)) (ρ ⨟ᴿ (wkᴿ ⨟ᴿ ρ′))
  `lift-fusion-⨟ : _≡_ {A = Ren _ _}
    ((ρ₁ ⇑ᴿ) ⨟ᴿ ((ρ₂ ⇑ᴿ) ⨟ᴿ ρ′)) (((ρ₁ ⨟ᴿ ρ₂) ⇑ᴿ) ⨟ᴿ ρ′)
  identityᵣ        : e [ idᴿ ]ᴿ                    ≡ e
  compositionalityᴿᴿ : (e [ ρ₁ ]ᴿ) [ ρ₂ ]ᴿ         ≡ e [ ρ₁ ⨟ᴿ ρ₂ ]ᴿ

  -- Substitution: application folds into composition.
  beta-ext-zero    : here &ˢ (e ∙ˢ σ)              ≡ e
  beta-ext-suc     : there x &ˢ (e ∙ˢ σ)           ≡ x &ˢ σ
  beta-rename      : x &ˢ ⟨ ρ ⟩                    ≡ var (x &ᴿ ρ)
  beta-lift-zero   : here {T = T} &ˢ (σ ⇑ˢ)        ≡ var here
  beta-lift-suc    : there {U = U} x &ˢ (σ ⇑ˢ)     ≡ x &ˢ (σ ⨟ˢ ⟨ wkᴿ ⟩)
  beta-⟨⟩-⨟        : x &ˢ (⟨ ρ ⟩ ⨟ˢ σ)             ≡ (x &ᴿ ρ) &ˢ σ
  beta-lift-zero-⨟ : here &ˢ ((σ ⇑ˢ) ⨟ˢ σ′)        ≡ here &ˢ σ′
  beta-lift-suc-⨟  : there x &ˢ ((σ ⇑ˢ) ⨟ˢ σ′)     ≡ x &ˢ (σ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ σ′))
  beta-fold        : (x &ˢ σ₁) [ σ₂ ]ˢ             ≡ x &ˢ (σ₁ ⨟ˢ σ₂)
  beta-lift-ren-∙  : (x &ᴿ (ρ ⇑ᴿ)) &ˢ (e ∙ˢ σ)     ≡ x &ˢ (e ∙ˢ (⟨ ρ ⟩ ⨟ˢ σ))
  beta-fold-ˢᴿ     : (x &ˢ σ) [ ρ ]ᴿ               ≡ x &ˢ (σ ⨟ˢ ⟨ ρ ⟩)
  associativity : _≡_ {A = Sub _ _}
    ((σ₁ ⨟ˢ σ₂) ⨟ˢ σ₃) (σ₁ ⨟ˢ (σ₂ ⨟ˢ σ₃))
  distributivity : _≡_ {A = Sub _ _}
    ((e ∙ˢ σ₁) ⨟ˢ σ₂) ((e [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ˢ σ₂))
  interact : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ (e ∙ˢ σ)) σ
  comp-idᵣ : _≡_ {A = Sub _ _}
    (σ ⨟ˢ ⟨ idᴿ ⟩) σ
  comp-idₗ : _≡_ {A = Sub _ _}
    (⟨ idᴿ ⟩ ⨟ˢ σ) σ
  lift-id : _≡_ {A = Sub _ _}
    (⟨ idᴿ {Γ} ⟩ ⇑ˢ) ⟨ idᴿ {Γ ▷ T} ⟩
  lift-wk : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ (σ ⇑ˢ)) (σ ⨟ˢ ⟨ wkᴿ {T = T} ⟩)
  lift-cons : _≡_ {A = Sub _ _}
    ((σ ⇑ˢ) ⨟ˢ (e ∙ˢ σ′)) (e ∙ˢ (σ ⨟ˢ σ′))
  lift-fusion : _≡_ {A = Sub _ _}
    ((σ₁ ⇑ˢ) ⨟ˢ (σ₂ ⇑ˢ)) (_⇑ˢ {T = T} (σ₁ ⨟ˢ σ₂))
  lift-wk-⨟ : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ ((σ ⇑ˢ) ⨟ˢ σ′)) (σ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ σ′))
  lift-fusion-⨟ : _≡_ {A = Sub _ _}
    ((σ₁ ⇑ˢ) ⨟ˢ ((σ₂ ⇑ˢ) ⨟ˢ σ′)) (((σ₁ ⨟ˢ σ₂) ⇑ˢ) ⨟ˢ σ′)
  ⟨⟩-⇑-cons : _≡_ {A = Sub _ _}
    (⟨ ρ ⇑ᴿ ⟩ ⨟ˢ (e ∙ˢ σ)) (e ∙ˢ (⟨ ρ ⟩ ⨟ˢ σ))

  -- Embedding renamings into substitutions and their interaction laws.
  lift-coincidence : _≡_ {A = Sub _ _}
    (⟨ ρ ⟩ ⇑ˢ) ⟨ _⇑ᴿ {T = T} ρ ⟩
  ⟨⟩-comp : _≡_ {A = Sub _ _}
    (⟨ ρ₁ ⟩ ⨟ˢ ⟨ ρ₂ ⟩) ⟨ ρ₁ ⨟ᴿ ρ₂ ⟩
  ⟨⟩-split-⨟ : _≡_ {A = Sub _ _}
    (⟨ ρ₁ ⨟ᴿ ρ₂ ⟩ ⨟ˢ σ) (⟨ ρ₁ ⟩ ⨟ˢ (⟨ ρ₂ ⟩ ⨟ˢ σ))
  ⟨⟩-wk-cons : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ ⟨ x ∙ᴿ ρ ⟩) ⟨ ρ ⟩
  ⟨⟩-wk-cons-⨟ : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ (⟨ x ∙ᴿ ρ ⟩ ⨟ˢ σ)) (⟨ ρ ⟩ ⨟ˢ σ)
  ⟨⟩-wk-lift : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ ⟨ ρ ⇑ᴿ ⟩) (⟨ ρ ⟩ ⨟ˢ ⟨ wkᴿ {T = T} ⟩)
  ⟨⟩-wk-lift-⨟ : _≡_ {A = Sub _ _}
    (⟨ wkᴿ ⟩ ⨟ˢ (⟨ ρ ⇑ᴿ ⟩ ⨟ˢ σ)) (⟨ ρ ⟩ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ σ))
  ⟨⟩-lift-lift : _≡_ {A = Sub _ _}
    (⟨ ρ₁ ⇑ᴿ ⟩ ⨟ˢ ⟨ ρ₂ ⇑ᴿ ⟩) ⟨ _⇑ᴿ {T = T} (ρ₁ ⨟ᴿ ρ₂) ⟩
  ⟨⟩-lift-lift-⨟ : _≡_ {A = Sub _ _}
    (⟨ ρ₁ ⇑ᴿ ⟩ ⨟ˢ (⟨ ρ₂ ⇑ᴿ ⟩ ⨟ˢ σ)) (⟨ (ρ₁ ⨟ᴿ ρ₂) ⇑ᴿ ⟩ ⨟ˢ σ)
  ⟨⟩-lift-RS : _≡_ {A = Sub _ _}
    (⟨ ρ ⇑ᴿ ⟩ ⨟ˢ (σ ⇑ˢ)) (_⇑ˢ {T = T} (⟨ ρ ⟩ ⨟ˢ σ))
  ⟨⟩-lift-RS-⨟ : _≡_ {A = Sub _ _}
    (⟨ ρ ⇑ᴿ ⟩ ⨟ˢ ((σ ⇑ˢ) ⨟ˢ σ′)) (((⟨ ρ ⟩ ⨟ˢ σ) ⇑ˢ) ⨟ˢ σ′)
  ⟨⟩-lift-SR : _≡_ {A = Sub _ _}
    ((σ ⇑ˢ) ⨟ˢ ⟨ ρ ⇑ᴿ ⟩) (_⇑ˢ {T = T} (σ ⨟ˢ ⟨ ρ ⟩))
  ⟨⟩-lift-SR-⨟ : _≡_ {A = Sub _ _}
    ((σ ⇑ˢ) ⨟ˢ (⟨ ρ ⇑ᴿ ⟩ ⨟ˢ σ′)) (((σ ⨟ˢ ⟨ ρ ⟩) ⇑ˢ) ⨟ˢ σ′)
  ⟨⟩-lift-SR-comp : _≡_ {A = Sub _ _}
    ((σ ⇑ˢ) ⨟ˢ ⟨ (ρ ⇑ᴿ) ⨟ᴿ ρ′ ⟩) (((σ ⨟ˢ ⟨ ρ ⟩) ⇑ˢ) ⨟ˢ ⟨ ρ′ ⟩)
  beta-lift-ren-⇑  : (x &ᴿ (ρ ⇑ᴿ)) &ˢ (σ ⇑ˢ)       ≡ x &ˢ ((⟨ ρ ⟩ ⨟ˢ σ) ⇑ˢ)
  beta-lift-ren-⇑-⨟ : (x &ᴿ (ρ ⇑ᴿ)) &ˢ ((σ ⇑ˢ) ⨟ˢ σ′) ≡ x &ˢ (((⟨ ρ ⟩ ⨟ˢ σ) ⇑ˢ) ⨟ˢ σ′)
  compositionalityᴿˢ : (e [ ρ₁ ]ᴿ) [ σ₂ ]ˢ         ≡ e [ ⟨ ρ₁ ⟩ ⨟ˢ σ₂ ]ˢ
  compositionalityˢᴿ : (e [ σ₁ ]ˢ) [ ρ₂ ]ᴿ         ≡ e [ σ₁ ⨟ˢ ⟨ ρ₂ ⟩ ]ˢ
  compositionalityˢˢ : (e [ σ₁ ]ˢ) [ σ₂ ]ˢ         ≡ e [ σ₁ ⨟ˢ σ₂ ]ˢ
  coincidence      : e [ ⟨ ρ ⟩ ]ˢ                 ≡ e [ ρ ]ᴿ

--! <

introduction : (N : Γ ⊢ T) (M : Γ ⊢ U) →
--!! IntroductionStatement
  N ↑ [ M ]₀ ≡ N

introduction {Γ} N M =
--! IntroductionProof {
  begin
    N ↑ [ M ]₀
  ≡⟨⟩
    (N [ wkᴿ ]ᴿ) [ M ∙ˢ ⟨ idᴿ ⟩ ]ˢ
  ≡⟨ compositionalityᴿˢ {e = N} {ρ₁ = wkᴿ} {σ₂ = M ∙ˢ ⟨ idᴿ ⟩} ⟩
    N [ ⟨ wkᴿ ⟩ ⨟ˢ (M ∙ˢ ⟨ idᴿ ⟩) ]ˢ
  ≡⟨ cong (λ (σ : Sub Γ Γ) → N [ σ ]ˢ) interact ⟩
    N [ ⟨ idᴿ ⟩ ]ˢ
  ≡⟨ coincidence {e = N} {ρ = idᴿ} ⟩
    N [ idᴿ ]ᴿ
  ≡⟨ identityᵣ ⟩
    N
  ∎
--! }
  where open ≡-Reasoning


{-# REWRITE
  `beta-id `beta-wk `beta-ext-zero `beta-ext-suc
  `beta-lift-zero `beta-lift-suc `beta-comp `beta-lift-fusion
  `associativity `interact `interact-⨟ `comp-idᵣ `comp-idₗ
  `lift-id `lift-wk `lift-fusion `lift-wk-⨟ `lift-fusion-⨟
  identityᵣ compositionalityᴿᴿ

  beta-ext-zero beta-ext-suc beta-rename
  beta-lift-zero beta-lift-suc beta-⟨⟩-⨟ beta-lift-zero-⨟ beta-lift-suc-⨟ beta-fold
  beta-lift-ren-∙ beta-fold-ˢᴿ
  associativity distributivity interact comp-idᵣ comp-idₗ
  lift-id lift-wk lift-cons lift-fusion lift-wk-⨟ lift-fusion-⨟
  ⟨⟩-⇑-cons

  lift-coincidence ⟨⟩-comp ⟨⟩-split-⨟
  ⟨⟩-wk-cons ⟨⟩-wk-cons-⨟ ⟨⟩-wk-lift ⟨⟩-wk-lift-⨟ ⟨⟩-lift-lift ⟨⟩-lift-lift-⨟
  ⟨⟩-lift-RS ⟨⟩-lift-RS-⨟ ⟨⟩-lift-SR ⟨⟩-lift-SR-⨟ ⟨⟩-lift-SR-comp
  beta-lift-ren-⇑ beta-lift-ren-⇑-⨟
  compositionalityᴿˢ compositionalityˢᴿ compositionalityˢˢ
  coincidence
#-}

-- infixes

infixl 6 _[_]₀ _[_]₁

-- examples

variable
  L M N : Γ ⊢ T

-- Substitution into weakened variable disappears
example1 : (N : Γ ⊢ T) (M : Γ ⊢ U)
  → N ↑ [ M ]₀ ≡ N
example1 N M = refl

-- swapping double substitution
double-subst : N [ M ]₁ [ L ]₀ ≡ N [ L ↑ ]₀ [ M ]₀
double-subst = refl

-- commute double substitution
example2 : (N : Γ ▷ U ▷ V ⊢ T) (M : Γ ▷ U ⊢ V) (L : Γ ⊢ U)
  → N [ M ]₀ [ L ]₀ ≡ N [ L ]₁ [ M [ L ]₀ ]₀
example2 N M L = refl

-- Substitution commutes with η-expansion, preserving the bound variable.
example3 : (N : Γ₁ ⊢ U ⇒ T) (σ : Sub Γ₁ Γ₂)
  → (lam (app (N ↑) (var here))) [ σ ]ˢ
    ≡ lam (app ((N [ σ ]ˢ) ↑) (var here))
example3 N σ = refl

-- Substitution commutes with replacing the newest variable (the β case).
example4 : (N : Γ₁ ▷ U ⊢ T) (M : Γ₁ ⊢ U) (σ : Sub Γ₁ Γ₂)
  → (N [ M ]₀) [ σ ]ˢ ≡ (N [ σ ⇑ˢ ]ˢ) [ M [ σ ]ˢ ]₀
example4 N M σ = refl

-- Weakening commutes with η-expansion (example3 with σ = ⟨ wkᴿ ⟩).
-- With Wadler's explicit weakening constructor, the left side has an
-- outer ↑ and the right side an outer lambda, so they are distinct.
example5 : (N : Γ ⊢ U ⇒ T)
  → _≡_ {A = Γ ▷ V ⊢ U ⇒ T}
      ((lam (app (N ↑) (var here))) ↑)
      (lam (app ((N ↑) ↑) (var here)))
example5 N = refl

opaque
  unfolding _∙ˢ_ _&ˢ_ ⟨_⟩ _⨟ˢ_ wkᴿ idᴿ

  η-id : _≡_ {A = Sub (Γ ▷ U) (Γ ▷ U)}
    (var here ∙ˢ ⟨ wkᴿ ⟩) ⟨ idᴿ ⟩
  η-id = implicit-extensionality fun-ext (fun-ext λ { here → refl ; (there x) → refl })

  η-law : {σ : Sub (Γ₁ ▷ U) Γ₂} → _≡_ {A = Sub (Γ₁ ▷ U) Γ₂}
    ((here &ˢ σ) ∙ˢ (⟨ wkᴿ ⟩ ⨟ˢ σ)) σ
  η-law = implicit-extensionality fun-ext (fun-ext λ { here → refl ; (there x) → refl })

-- Substitution η: keep the newest variable and weaken all older ones.
-- This substitution is the identity, but its η-law is not a rewrite rule,
-- so refl cannot prove this equality for an arbitrary expression N.
counterexample : (N : Γ ▷ U ⊢ T)
  → N [ var here ∙ˢ ⟨ wkᴿ ⟩ ]ˢ ≡ N
counterexample {Γ}{U} N rewrite η-id {Γ}{U} = refl

