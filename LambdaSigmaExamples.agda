{-# OPTIONS --rewriting --local-confluence-check #-}
module LambdaSigmaExamples where

open import LambdaSigma
open import Agda.Builtin.Equality using (_≡_; refl)

--! LS >

-- STLC70.example1 / Weakening.introduction.
--! Introduction {
example1 : (N : Γ ⊢ T) (M : Γ ⊢ U) → N ↑ [ M ]₀ ≡ N
example1 N M = refl
--! }

-- STLC70.example2 / Weakening.commute-subst.
--! CommuteSubst {
example2 : (N : Γ ▷ U ▷ V ⊢ T) (M : Γ ▷ U ⊢ V) (L : Γ ⊢ U)
  → N [ M ]₀ [ L ]₀ ≡ N [ L ]₁ [ M [ L ]₀ ]₀
example2 N M L = refl
--! }

-- STLC70.example3: substitution commutes with term η-expansion.
--! SubstEta {
example3 : (N : Γ₁ ⊢ U ⇒ T) (σ : Sub Γ₁ Γ₂)
  → lam (app (N ↑) var₀) [ σ ]ˢ
    ≡ lam (app ((N [ σ ]ˢ) ↑) var₀)
example3 N σ = refl
--! }

-- STLC70.example4: substitution commutes with single substitution.
--! SubstSingle {
example4 : (N : Γ₁ ▷ U ⊢ T) (M : Γ₁ ⊢ U) (σ : Sub Γ₁ Γ₂)
  → (N [ M ]₀) [ σ ]ˢ ≡ (N [ σ ⇑ˢ ]ˢ) [ M [ σ ]ˢ ]₀
example4 N M σ = refl
--! }

-- STLC70.example5, whose analogue is refuted in WeakeningComparison.
--! WeakeningEta {
example5 : (N : Γ ⊢ U ⇒ T)
  → _≡_ {A = Γ ▷ V ⊢ U ⇒ T}
      (lam (app (N ↑) var₀) ↑)
      (lam (app ((N ↑) ↑) var₀))
example5 N = refl
--! }

-- Unlike WeakeningEta, these are proofs, not definitions of propositions.
-- No function extensionality is needed: VarShift and SCons are rules.
--! EtaId {
η-id : _≡_ {A = Sub (Γ ▷ U) (Γ ▷ U)} (var₀ ∙ˢ wkˢ) idˢ
--! }
--! EtaIdProof {
η-id = refl
--! }

--! EtaLaw {
η-law : (σ : Sub (Γ₁ ▷ U) Γ₂)
  → (var₀ [ σ ]ˢ) ∙ˢ (wkˢ ⨟ˢ σ) ≡ σ
--! }
--! EtaLawProof {
η-law σ = refl
--! }

-- The earlier STLC70 counterexample now also closes with refl alone.
counterexample : (N : Γ ▷ U ⊢ T)
  → N [ var₀ ∙ˢ wkˢ ]ˢ ≡ N
counterexample N = refl

-- Weakening.double-subst, the other single-substitution exercise.
--! DoubleSubst {
double-subst : (N : Γ ▷ U ▷ V ⊢ T) (M : Γ ⊢ U) (L : Γ ⊢ V)
  → N [ M ]₁ [ L ]₀ ≡ N [ L ↑ ]₀ [ M ]₀
double-subst N M L = refl
--! }

-- Wadler's displayed instantiation of the Church-numeral body, with
-- an arbitrary f in place of inc. The ACCL signature has no primitive
-- natural-number operations, so none are added just for this test.
church-instantiation : (f : Γ ⊢ T ⇒ T)
  → lam (app (var₀ ↑) (app (var₀ ↑) var₀)) [ f ]₀
    ≡ lam (app (f ↑) (app (f ↑) var₀))
church-instantiation f = refl

-- The three laws installed as rewrites in Weakening's artifact.
composition : (N : Γ₁ ⊢ T) (σ : Sub Γ₁ Γ₂) (τ : Sub Γ₂ Γ₃)
  → N [ σ ]ˢ [ τ ]ˢ ≡ N [ σ ⨟ˢ τ ]ˢ
composition N σ τ = refl

left-id : (σ : Sub Γ₁ Γ₂) → idˢ ⨟ˢ σ ≡ σ
left-id σ = refl

associativity : (σ : Sub Γ Γ₁) (τ : Sub Γ₁ Γ₂) (υ : Sub Γ₂ Γ₃)
  → (σ ⨟ˢ τ) ⨟ˢ υ ≡ σ ⨟ˢ (τ ⨟ˢ υ)
associativity σ τ υ = refl

-- Beta from §3.1 is included, even though §4's typing presentation S1
-- is stated separately from reduction. No term η rule is assumed.
β-example : (N : Γ ▷ U ⊢ T) (M : Γ ⊢ U)
  → app (lam N) M ≡ N [ M ]₀
β-example N M = Beta

--! <
