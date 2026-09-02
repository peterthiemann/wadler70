# All You Need Is Refl — Almost: Return of the Renamings

Agda development and slides for the Wadler70 talk by Peter Thiemann and
Marius Weidner (Edinburgh, 9 September 2026).  See `abstract.md` for the
abstract and `outline.md` for the outline of the talk.

Three formulations of substitution for an intrinsically typed simply typed
λ-calculus are compared on the same benchmark of substitution equations:

* **EW** — Philip Wadler's *Explicit Weakening* (2024), where weakening is a
  constructor of terms and substitutions are syntax;
* **RoR** — *Return of the Renamings*, our proposal: inductive terms, function
  valued renamings and substitutions, and a confluent selection of σ-calculus
  equations installed as Agda rewrite rules;
* **λσ** — the σ-calculus of Abadi, Cardelli, Curien, and Lévy, realised
  directly as postulates and rewrite rules.

The talk's claim is that EW ⊊ RoR ⊊ λσ with respect to the equations that
hold by `refl`, and that the gap between RoR and λσ is exactly substitution η.

## Agda modules

All modules use `{-# OPTIONS --rewriting #-}` and check with Agda 2.8.0 and
standard-library 2.4.  Check everything with

```bash
agda WeakeningToSTLC70.agda && agda STLC70Notation.agda && agda LambdaSigmaExamples.agda
```

### Return of the Renamings

**`STLC70.agda`** — the main development.

* Intrinsically typed STLC: types `` `ℕ `` and `_⇒_`, snoc-list contexts,
  variables `Γ ∋ T`, and terms `Γ ⊢ T` with `zero`, `suc`, `var`, `lam`, `app`.
* Two presentations of the denotational semantics, with environments as data
  (`𝓖⟦_⟧`) and as functions (`𝓗⟦_⟧`); the running example of the talk's
  introduction.
* Textbook renaming `_[_]ᴿ` and substitution `_[_]ˢ` over function-valued
  `Ren` and `Sub`.  The primitive operations on variables and maps (`wkᴿ`,
  `idᴿ`, `_∙ᴿ_`, `_&ᴿ_`, `_⨟ᴿ_`, `_⇑ᴿ`, `⟨_⟩`, `_∙ˢ_`, `_&ˢ_`, `_⇑ˢ`, `_⨟ˢ_`)
  are `opaque`, so they never compute by themselves.  Derived forms: term
  weakening `_↑`, single substitution `_[_]₀`, and `_[_]₁`.
* Weak-head reduction (`β-lam`, `ξ-app`) and a progress theorem for closed
  terms.
* The σ-calculus with first-class renamings as a block of postulated
  equations: renaming laws, substitution laws, the laws for the embedding
  `⟨_⟩` of renamings into substitutions, compositionality in all four
  renaming/substitution combinations, and coincidence.
* `introduction`: the motivating equation `N ↑ [ M ]₀ ≡ N`, proved by
  equational reasoning from the postulates *before* they are installed as
  rewrite rules.
* The `{-# REWRITE ... #-}` pragma installs the equations.  After it, the
  benchmark equations `example1` – `example5` and `double-subst` hold by
  `refl`.
* Substitution η: `η-id` and `η-law` are provable, but only propositionally
  via function extensionality; `counterexample` shows that they are not part
  of the definitional equality.

**`STLC70Notation.agda`** — presentation-facing surface notation for RoR that
mirrors EW: `●` for `var here`, `ƛ_`, `_·_`, unadorned `_[_]` for
substitution, and `_↑ˢ` / `_▷ˢ_` for weakening and consing substitutions (the
ˢ marker is needed because Agda cannot overload the term-level `_↑` and the
context constructor `_▷_`).  Restates `weaken-by-renaming`, the strictness
witness `weakening-η`, and the two η-laws in that notation.  Re-exports
`STLC70`.

### Explicit Weakening

**`Weakening.lagda.md`** — Wadler's published literate artifact for *Explicit
Weakening*, unchanged except that the module is renamed from `Weaken` to
`Weakening`.  Terms carry an explicit weakening constructor `_↑`,
substitutions `Γ ⊨ Δ` are syntax (`id`, `_↑`, `_▷_`), and instantiation and
composition are defined by recursion with their laws proved by induction.

**`WeakeningExamples.agda`** — the benchmark equations *substitution through
η-expansion* (`example3`) and *substitution through single substitution*
(`example4`) as propositions in EW.  Both hold for identity and cons
substitutions but fail for weakened substitutions, so `example3-unprovable`
and `example4-unprovable` refute any uniform proof.

**`WeakeningComparison.agda`** — the benchmark equation *weakening commutes
with η-expansion* (`example5`) in EW; `example5-impossible` shows that no
propositional proof exists.  This is the witness that EW is strictly weaker
than RoR.

**`WeakeningEta.agda`** — `η-id` and `η-law` as propositions in EW.  Both are
refuted (`η-id-impossible`, `η-law-impossible`), although the cons instance of
η-law holds.

**`WeakeningToSTLC70.agda`** — the translation from EW into RoR (`Ty`, `Cx`,
`Tm`, `Sb`), which preserves types and de Bruijn structure.
`translate-instantiation` and `translate-composition` show that it respects
instantiation and composition, and `preserve-*` / `sound-*` show that every
propositional equality of EW is validated after translation.  This is the
inclusion EW ⊆ RoR.

### σ-calculus

**`LambdaSigma.agda`** — the first-order typed λσ-calculus of Abadi, Cardelli,
Curien, and Lévy.  Only types and contexts are data; terms, substitutions, and
their constructors are postulates whose only computation is rewriting.  The
ten basic σ rules plus `Id`, `IdR`, `VarShift`, and `SCons` are rewrite rules
(Beta is postulated but not rewritten), checked with
`--local-confluence-check`.

**`LambdaSigmaExamples.agda`** — the benchmark equations in λσ, including
`η-id` and `η-law`, all by `refl`.

## Slides

* `wadler70.tex`, `macros.tex` — the beamer slides; `theme/` holds the
  University of Freiburg beamer theme and logos, `EN/` the corporate-design
  sample the theme's word mark comes from, and `return-of-the-renamings.png`
  the closing image.
* Agda snippets are extracted from the sources by `runagdatex`, a wrapper
  around `agdatex.py`.  Regions delimited by `--! Name {` … `--! }` under a
  `--! Prefix >` header become LaTeX macros such as `\RoRWeakeningEta` and
  `\EWEtaEtaLaw`.
* `unicodeletters.tex` maps the Unicode characters of the Agda code to LaTeX
  symbols for pdflatex.  It and `agdatex.py` are local copies from Marius
  Weidner's [Agdasubst](https://github.com/Mari-W/Agdasubst) repository, so
  the build has no dependency outside this directory, Agda, and TeX Live.
* `make snippets` regenerates the snippets; `make` builds `wadler70.pdf` with
  latexmk.

Generated files (`*.agdai`, `latex/`, `agda-generated.tex`,
`agda-macros.txt`, `.agdatex-hashes.json`, the LaTeX auxiliary files,
`wadler70.pdf`, `auto/`, and `tmp/`) are excluded by `.gitignore`.
