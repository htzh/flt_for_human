/-
The residue-field extension of a place is finite, after FLT's
`P2M/Sol/S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean`
(89 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean>).

If `F'/F` is finite and `w` is a place of `F'`, the residue field of the
restriction `w.restrict F` maps finitely into the residue field of `w`: the
`F`-linear independence of a maximal `F`-basis lifts to `F'`-linear
independence of the same elements, bounding the residue degree by `[F' : F]`.

The public headline is the wrapper verbatim; the pin's `S09G2F` helpers are
transcribed `private`.

Mathlib search negatives (recorded): mathlib has no statement bounding the
residue-field extension of a place by the degree of the field extension; the
argument (a lift of a residue-basis through the valuation subring, then
`rank_le` and `Cardinal.natCast_lt_aleph0`) is FLT's. -/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.SetTheory.Cardinal.Basic

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

namespace Place

namespace FiniteResidueAux

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']

open IsLocalRing in

private theorem linearIndependent_lift (w : Place K F') {ι : Type*} [Fintype ι]
    (x : ι → w.toValuationSubring)
    (hx : LinearIndependent (w.restrict F).ResidueField
      fun i => (residue w.toValuationSubring (x i) : w.ResidueField)) :
    LinearIndependent F fun i => ((x i : w.toValuationSubring) : F') := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := not_forall.mp hne
  set O : ValuationSubring F := (w.restrict F).toValuationSubring

  have hne' : (Finset.univ.filter fun i => g i ≠ 0).Nonempty := ⟨i₀, by simpa using hi₀⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image _ (fun i => O.valuation (g i)) hne'
  have hgk : g k ≠ 0 := by simpa using hk

  have hb : ∀ i, g i / g k ∈ O := by
    intro i
    by_cases hi : g i = 0
    · simp [hi]
    · apply O.mem_of_valuation_le_one
      rw [map_div₀]
      have hk0 : (0 : O.ValueGroup) < O.valuation (g k) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hgk
      exact (div_le_one₀ hk0).mpr (hkmax i (by simpa using hi))
  let b : ι → O := fun i => ⟨g i / g k, hb i⟩

  have hrel : ∑ i, Place.restrictInclusion F w (b i) * x i = 0 := by
    apply Subtype.ext
    have hcoe : ((∑ i, Place.restrictInclusion F w (b i) * x i : w.toValuationSubring) : F') =
        ∑ i, algebraMap F F' (g i / g k) * (x i : F') := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, Place.coe_restrictInclusion]
    rw [hcoe]
    have : ∑ i, algebraMap F F' (g i / g k) * (x i : F') =
        algebraMap F F' (g k)⁻¹ * ∑ i, g i • ((x i : w.toValuationSubring) : F') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, div_eq_inv_mul, map_mul, mul_assoc]
    rw [this, hg, mul_zero]
    rfl

  have hres : ∑ i, (residue O (b i) : (w.restrict F).ResidueField) •
      (residue w.toValuationSubring (x i) : w.ResidueField) = 0 := by
    have h := congrArg (residue w.toValuationSubring) hrel
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue,
      map_mul]
  have hk1 := (Fintype.linearIndependent_iff.mp hx) _ hres k

  have hbk : b k = 1 := Subtype.ext (div_self hgk)
  rw [hbk, map_one] at hk1
  exact one_ne_zero hk1

open IsLocalRing in

private theorem finite_residueField (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by
  classical
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := Module.finrank F F') fun s hs => ?_)
    Cardinal.natCast_lt_aleph0

  choose x hx using fun y : s => residue_surjective (R := w.toValuationSubring) (y : w.ResidueField)
  have hs' : LinearIndependent (w.restrict F).ResidueField
      fun i : s => (residue w.toValuationSubring (x i) : w.ResidueField) := by
    simpa only [hx] using hs
  have := linearIndependent_lift (F := F) w x hs'
  simpa [Fintype.card_coe] using this.fintype_card_le_finrank

end FiniteResidueAux

/-- **The residue-field extension of a place is finite.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean`. -/
theorem finite_residueField_of_finiteDimensional {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    (w : Place K F') : Module.Finite (w.restrict F).ResidueField w.ResidueField :=
  FiniteResidueAux.finite_residueField (F := F) w

end Place

end AlgebraicCurve

end
