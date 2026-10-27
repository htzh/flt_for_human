/-
The regular differentials are already a `K`-subspace.

`IsRegularDiff K F ω` says `0 ≤ v.ordDiff ω` at every place, and `regularDiffs K F` is the
`K`-span of those `ω`. This module proves `ω ∈ regularDiffs K F ↔ IsRegularDiff K F ω`,
i.e. the pointwise condition is closed under `0`, `+` and scalar multiplication, so the
span adds nothing: the "regular" differentials are literally the submodule
`regularDiffs K F`. That identification is what lets the other form of the same statement
(the order of `diffCoeff` at a place being nonnegative) be used as a `Submodule` membership.

The prelude is the pin's, and it is the mathematics: `diffCoeff` is additive in `ω` at an
element of nonzero order, `ordDiff` obeys the ultrametric inequality through
`ord` of the coefficient, and the three closure cases. Each of the four ingredients the
proof uses was ported for its own sake — the coefficient laws (`diffCoeff_smul_D`, its
`_of_ord_ne_zero` sibling and the uniqueness form), `ordDiff_zero`, the multiplication law
`ordDiff_smul`, and `Place.min_ord_le_ord_add` — so this module is the span argument
itself and nothing else.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_mem_regularDiffs_iff.lean

spec-pin: Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_mem_regularDiffs_iff.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Differential.Coefficient

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

-- The pin states this file's prelude in a section, so the binder block is the section's;
-- the same here, to keep the checked text identical (the check is textual).
section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
/-- The coefficient is additive in the differential, at an element of nonzero order. -/
theorem diffCoeff_add (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω₁ ω₂ : Ω[F⁄K]) :
    Place.diffCoeff t (ω₁ + ω₂) = Place.diffCoeff t ω₁ + Place.diffCoeff t ω₂ := by
  have h1 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₁
  have h2 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₂
  conv_lhs => rw [← h1, ← h2, ← add_smul]
  exact Place.diffCoeff_smul_D_eq x v ht _

include x in
/-- `ordDiff` obeys the ultrametric inequality, through `ord` of the coefficient. -/
theorem min_ordDiff_le_ordDiff_add (v : Place K F) {ω₁ ω₂ : Ω[F⁄K]} (h₁₂ : ω₁ + ω₂ ≠ 0) :
    min (v.ordDiff ω₁) (v.ordDiff ω₂) ≤ v.ordDiff (ω₁ + ω₂) := by
  rcases eq_or_ne ω₁ 0 with rfl | h₁
  · rw [zero_add]; exact min_le_right _ _
  rcases eq_or_ne ω₂ 0 with rfl | h₂
  · rw [add_zero]; exact min_le_left _ _
  have hu : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩]; exact one_ne_zero
  have hcoe : ∀ ω : Ω[F⁄K], ω ≠ 0 → Place.diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro ω hω h0
    have := Place.diffCoeff_smul_D_of_ord_ne_zero x v hu ω
    rw [h0, zero_smul] at this
    exact hω this.symm
  simp only [Place.ordDiff_def]
  rw [diffCoeff_add x v hu]
  exact v.min_ord_le_ord_add (by rw [← diffCoeff_add x v hu]; exact hcoe _ h₁₂)

include x in
/-- The zero differential is regular. -/
theorem isRegularDiff_zero : IsRegularDiff K F (0 : Ω[F⁄K]) := fun v => by
  rw [Place.ordDiff_zero x v]

include x in
/-- Regular differentials are closed under addition. -/
theorem isRegularDiff_add {ω₁ ω₂ : Ω[F⁄K]} (h₁ : IsRegularDiff K F ω₁) (h₂ : IsRegularDiff K F ω₂) :
    IsRegularDiff K F (ω₁ + ω₂) := by
  intro v
  rcases eq_or_ne (ω₁ + ω₂) 0 with h12 | h12
  · rw [h12, Place.ordDiff_zero x v]
  · exact le_trans (le_min (h₁ v) (h₂ v)) (min_ordDiff_le_ordDiff_add x v h12)

include x in
/-- Regular differentials are closed under scalar multiplication. -/
theorem isRegularDiff_smul (c : K) {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    IsRegularDiff K F (c • ω) := by
  intro v
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]; exact isRegularDiff_zero x v
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [smul_zero]; exact isRegularDiff_zero x v
  rw [← algebraMap_smul F c ω, Place.ordDiff_smul x v ((map_ne_zero _).mpr hc) hω,
    v.ord_algebraMap, zero_add]
  exact h v

end

/-- **The regular differentials form a `K`-subspace.** Verbatim from
`Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean`: membership in the span is the
pointwise condition, the three closure cases supplying the span induction. -/
theorem mem_regularDiffs_iff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (ω : Ω[F⁄K]) :
    ω ∈ AlgebraicCurve.regularDiffs K F ↔ AlgebraicCurve.IsRegularDiff K F ω := by
  refine ⟨fun h => ?_, AlgebraicCurve.mem_regularDiffs_of_isRegularDiff⟩
  induction h using Submodule.span_induction with
  | mem ω hω => exact hω
  | zero => exact isRegularDiff_zero x
  | add ω₁ ω₂ _ _ h₁ h₂ => exact isRegularDiff_add x h₁ h₂
  | smul c ω _ h => exact isRegularDiff_smul x c h

end AlgebraicCurve
