/-
  SET-AF82A consumer: the content bound, spent at `g = 1` and at `F = ℚ`.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/ContentBound.lean` carries the pin's
  `solution` (`S_…:222–331`) as
  `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq`:
  there is a finite set `R` of units of `𝔸_F^fin` such that every `g : GL₂(𝔸_F^fin)` has a
  representative `a ∈ R` and a unit `d` with `v(d) = max (v((g 1 0) · a⁻¹)) (v((g 1 1)))` at every
  finite place `v`, and `contentHomFin a * contentHomFin d ^ 2 = contentHomFin (det g)`.

  **What is concrete here.** The element `g = 1` — the identity matrix, so its `(1,0)`-entry is `0`
  and its `(1,1)`-entry is `1` — and the field `F = ℚ`. Everything else (`R`, `a`, `d`) stays the
  row's own existential data, read out by `obtain`.

  **The readings.**

  * Zone 1 — the content half at `g = 1`: `contentHomFin a * contentHomFin d ^ 2 = 1`, because
    `contentHomFin 1 = 1`.
  * Zone 2 — the same equation read in the class group: `(contentHomFin a)⁻¹` is a square, i.e. it
    lies in the range of the port's `classSq` (`ProductionPinsGeneral.lean`), which is the
    "modulo squares" of the row's title. This is the cross-module reading.
  * Zone 3 — the valuation half at `g = 1`: the `(1,0)`-entry of the identity is `0` and its
    `(1,1)`-entry is `1`, so `max 0 1 = 1` and the correcting unit is integral at every place with
    unit value — `Valued.v (d v) = 1` for all `v`.
  * Zone 4 — the row at `F = ℚ`: the finite set is inhabited (read off the membership of `a`).
  * Zone 5 — the row at `F = ℚ` and `g = 1`, read as a formula for the correction:
    `contentHomFin d ^ 2 = (contentHomFin a)⁻¹`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF82AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.ContentBound

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open AutomorphicForm
open scoped nonZeroDivisors

namespace AutomorphicFormSetAF82AConsumer

/-! ### Zone 1 — the content half of the row at `g = 1` -/

/-- **Zone 1.** At the identity matrix the content of the correction squares away: the row's
equation reads `contentHomFin a * contentHomFin d ^ 2 = 1`. -/
theorem exists_mem_content_mul_sq_eq_one (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((FiniteAdeleRing (𝓞 F) F)ˣ), ∃ a ∈ R, ∃ d : (FiniteAdeleRing (𝓞 F) F)ˣ,
      contentHomFin F a * contentHomFin F d ^ 2 = 1 := by
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq F
  obtain ⟨a, ha, d, -, hcont⟩ := hR 1
  exact ⟨R, a, ha, d, by simpa using hcont⟩

/-! ### Zone 2 — the same equation, read as "the class of `a` is a square up to inversion" -/

/-- **Zone 2.** Cross-module: the inverse of `contentHomFin a` is a square in the class group, i.e.
it lies in the range of `classSq` (`ProductionPinsGeneral.lean`). This is the "modulo squares" that
the row's square is about. -/
theorem exists_mem_inv_content_mem_range_classSq (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((FiniteAdeleRing (𝓞 F) F)ˣ), ∃ a ∈ R,
      (contentHomFin F a)⁻¹ ∈ (classSq F).range := by
  obtain ⟨R, a, ha, c, hc⟩ := exists_mem_content_mul_sq_eq_one F
  exact ⟨R, a, ha, MonoidHom.mem_range.mpr
    ⟨contentHomFin F c, by rw [classSq_apply]; exact eq_inv_of_mul_eq_one_right hc⟩⟩

/-! ### Zone 3 — the valuation half of the row at `g = 1` -/

/-- **Zone 3.** At the identity matrix both entries of the second row are `0` and `1`, so the max is
`1` and the correction `d` is integral of unit value at every finite place. -/
theorem exists_mem_valued_eq_one (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((FiniteAdeleRing (𝓞 F) F)ˣ), ∃ a ∈ R, ∃ d : (FiniteAdeleRing (𝓞 F) F)ˣ,
      ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((d : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq F
  obtain ⟨a, ha, d, hd, -⟩ := hR 1
  refine ⟨R, a, ha, d, fun v => ?_⟩
  have h := hd v
  simp only [Units.val_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq,
    zero_mul, coe_zero_apply, coe_one_apply, map_zero, map_one] at h
  exact h.trans (max_eq_right zero_le)

/-! ### Zone 4 — the row at `F = ℚ` -/

/-- **Zone 4.** The row at `F = ℚ`: the finite set of `(𝔸_ℚ^fin)ˣ` is inhabited, and every `g` still
has its representative in it with the two properties. -/
theorem rat_row :
    ∃ R : Finset ((FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), R.Nonempty := by
  obtain ⟨R, hR⟩ :=
    exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq ℚ
  obtain ⟨a, ha, -⟩ := hR 1
  exact ⟨R, ⟨a, ha⟩⟩

/-! ### Zone 5 — the row at `F = ℚ`, `g = 1`, as a formula for the correction -/

/-- **Zone 5.** At `F = ℚ` and `g = 1` the correction is forced: `contentHomFin d ^ 2` is exactly
the inverse of `contentHomFin a`, so the class of `a` determines `d`'s content up to squares. -/
theorem rat_content_sq :
    ∃ R : Finset ((FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), ∃ a ∈ R, ∃ d : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      contentHomFin ℚ d ^ 2 = (contentHomFin ℚ a)⁻¹ := by
  obtain ⟨R, hR⟩ := exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq ℚ
  obtain ⟨a, ha, d, -, hcont⟩ := hR 1
  exact ⟨R, a, ha, d, by simpa using eq_inv_of_mul_eq_one_right (by simpa using hcont)⟩

end AutomorphicFormSetAF82AConsumer
