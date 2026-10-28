/-
  LD6-1 — the complex-place dictionary at level `Γ₀(N)`: the choice function
  `realize` and the structure `ComplexPlaceDictionary`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_ComplexPlaceDictionary.lean` (49 lines, whole:
  `realize` and the structure's five fields).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ComplexPlaceDictionary.lean

  `realize N x τ` is FLT's `Classical.choose` over a `Σ k : ℤ, ModularForm
  (Gamma0 N) k × ModularForm (Gamma0 N) k` whose two q-expansions realise the
  Laurent series `x` at `τ` with non-vanishing denominator; the `by classical
  exact if H : … then … else 0` *term* is kept verbatim, so that the `Γ`-general
  module's `realizeOf_gamma0` and `ComplexPlaceDictionaryOf.ofGamma0` are `rfl`.
  The structure's `mem_pt_iff` field keeps the `Filter.IsBoundedUnder`
  boundedness shape and `meromorphicOrderAt_realize` the `WithTop ℤ` coercion
  `(((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)`, both verbatim.

  The pin imports `Definitions/Def_AlgebraicCurve_DivisorClassGroup`; **the port
  does not**, and needs no substitute: the wave's audit (SET-LEAVESDEF §0)
  measured that no declaration of this module names anything from it. The
  module sits on `Defs/Fields.lean` (`modularFunctionFieldFull`),
  `Defs/Laurent.lean` (`laurentBaseChange`, `LaurentSeries`) and
  `AlgebraicCurve/Defs/Place.lean` (`Place`, `Place.ord`); `qExpansion`,
  `ModularForm`, `CongruenceSubgroup.Gamma0`, `meromorphicOrderAt` and
  `UpperHalfPlane.ofComplex` are mathlib's.

  `spec-pin:` below names the one pin module transcribed. No `Thm_` wrapper for
  either declaration exists in the pin (`grep -rlw` over `Theorems/` finds
  `realizeOf` only inside leaf-row statements, never as a wrapper of `realize`
  or of the structure), so there is no second `spec-pin:` line.

spec-pin: Definitions/Def_ModularCurve_ComplexPlaceDictionary.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Meromorphic.Order
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.AlgebraicCurve.Defs.Place

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

/-- FLT's `realize`: on `x : LaurentSeries ℂ` at `τ : ℍ`, the ratio
`f.1 τ / f.2 τ` of a chosen pair of `Γ₀(N)`-modular forms whose q-expansions
realise `x` with non-vanishing denominator at `τ`, and `0` when no such pair
exists. -/
def realize (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

/-- FLT's `ComplexPlaceDictionary` at level `Γ₀(N)`: a `ℍ`-indexed family of
places of `laurentBaseChange ℂ (modularFunctionFieldFull N)`, with a positive
ramification index, `Γ₀(N)`-invariance, the boundedness description of the
valuation ring through `realize`, and the order law
`ord (realize x) τ = ramification τ * ord_place x`. -/
structure ComplexPlaceDictionary (N : ℕ) [NeZero N] where

  pt : ℍ → AlgebraicCurve.Place ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N))

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  pt_smul : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), pt ((γ : SL(2, ℤ)) • τ) = pt τ

  mem_pt_iff : ∀ (τ : ℍ) (x : laurentBaseChange ℂ (modularFunctionFieldFull N)),
    x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖)

  meromorphicOrderAt_realize : ∀ (τ : ℍ) (x : laurentBaseChange ℂ (modularFunctionFieldFull N)),
    x ≠ 0 →
      meromorphicOrderAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) =
        (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

end ModularCurve

end
