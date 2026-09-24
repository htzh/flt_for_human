/-
  m5 — the cusp bookkeeping: the `ord_*` values at the two cusps, the
  `IsCusp` split, and the Fricke/`coeffEmb` compatibility.

  These eleven nodes are transcriptions against m2's `QAdicPlace`/`AtkinLehner`/
  `CuspidalClass` vocabulary. Two helpers the pin reaches through wrappers that
  this effort has not yet ported — `order_coeffEmb` and `order_qExpand` (both M4
  glue, m7) — are restated `private` here.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ord_qInftyPlaceBar.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.lean
-/
import FLTForHuman.ModularCurve.Defs.QAdicPlace
import FLTForHuman.ModularCurve.Defs.CuspidalClass
import FLTForHuman.ModularCurve.Defs.AtkinLehner
import FLTForHuman.ModularCurve.Defs.GeometricBaseChange
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

namespace ModularCurve

section Helpers

/-- `coeffEmb` preserves the order. The pin's wrapper `order_coeffEmb` is M4
glue (m7) and is not ported yet. -/
private theorem order_coeffEmb (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) :
    (coeffEmb L x).order = x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have hLx : coeffEmb L x ≠ 0 := by
    intro h0
    have h1 : (coeffEmb L x).coeff x.order = 0 := by rw [h0]; rfl
    rw [coeffEmb_coeff, map_eq_zero_iff _ (algebraMap ℚ L).injective] at h1
    exact HahnSeries.coeff_order_eq_zero.not.mpr hx h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
    (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [coeffEmb_coeff]
    exact fun h => HahnSeries.coeff_order_eq_zero.not.mpr hx
      ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h)
  · intro h
    exact HahnSeries.coeff_order_eq_zero.not.mpr hLx (by rw [coeffEmb_coeff, h, map_zero])

/-- The order of a `q ↦ q ^ N` substitution. The pin's wrapper `order_qExpand`
is M4 glue (m7) and is not ported yet. -/
private theorem order_qExpand {R : Type*} [CommRing R] (N : ℕ) [NeZero N]
    (f : LaurentSeries R) : (qExpand R N f).order = N * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have hc : (qExpand R N f).coeff ((N : ℤ) * f.order) ≠ 0 := by
    rw [qExpand_coeff_mul]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand R N f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  by_cases hdvd : (N : ℤ) ∣ (qExpand R N f).order
  · obtain ⟨m, hm⟩ := hdvd
    rw [hm, qExpand_coeff_mul] at hk
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmlt : m < f.order := by
      rw [hm] at hlt
      exact lt_of_mul_lt_mul_left hlt hNpos.le
    exact hk (HahnSeries.coeff_eq_zero_of_lt_order hmlt)
  · exact hk (qExpand_coeff_of_not_dvd N f hdvd)

end Helpers

/-! ## `ord` at infinity -/

theorem ord_qInftyPlaceBar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)}
    (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : F) :
    (qInftyPlaceBar L F h).ord f = (qSeriesBar L F f).order := by
  obtain ⟨j, hj⟩ := h
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero, qSeriesBar_zero, HahnSeries.order_zero]
  set n : ℤ := (qSeriesBar L F f).order with hn
  have hπ0 : (j⁻¹ : F) ≠ 0 := inv_ne_zero (ne_zero_of_order_eq_neg_one hj)
  have hπn : (j⁻¹ : F) ^ n ≠ 0 := zpow_ne_zero _ hπ0
  have huord : (qSeriesBar L F (f / (j⁻¹) ^ n)).order = 0 := by
    rw [qSeriesBar_div, qSeriesBar_zpow,
      order_div_of_ne_zero_bar (qSeriesBar_ne_zero hf)
        (zpow_ne_zero _ (qSeriesBar_ne_zero hπ0)),
      order_zpow_of_ne_zero_bar (qSeriesBar_ne_zero hπ0), order_inv_of_order_eq_neg_one hj,
      mul_one, ← hn]
    ring
  have humem : f / (j⁻¹) ^ n ∈ qIntegersBar L F := by
    rw [mem_qIntegersBar_iff, huord]
  have hune : f / (j⁻¹) ^ n ≠ 0 := div_ne_zero hf hπn
  have huu : IsUnit (⟨f / (j⁻¹) ^ n, humem⟩ : qIntegersBar L F) :=
    (isUnit_qIntegersBar_iff hune).mpr huord
  have hdecomp : f = ((huu.unit : qIntegersBar L F) : F)
      * (((uniformizerBar hj : qIntegersBar L F) : F) ^ n) := by
    have hcoe : ((huu.unit : qIntegersBar L F) : F) = f / (j⁻¹) ^ n := by
      rw [IsUnit.unit_spec]
    rw [hcoe, coe_uniformizerBar]
    exact (div_mul_cancel₀ f hπn).symm
  rw [hdecomp]
  exact (qInftyPlaceBar L F ⟨j, hj⟩).ord_unit_smul_zpow huu.unit (irreducible_uniformizerBar hj) n

theorem ord_cuspInftyBar (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order :=
  ord_qInftyPlaceBar (AlgebraicClosure ℚ) _ f

/-! ## `ord` at the cusps, on `coeffEmb`-generators -/

theorem ord_cuspInftyBar_coeffEmb_jq (N : ℕ) [NeZero N] :
    (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by
  rw [ord_cuspInftyBar]
  exact order_coeffEmb_jq (AlgebraicClosure ℚ)

theorem ord_cuspInftyBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (d : ℕ) [NeZero d]
    (hd : d ∣ N) : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by
  rw [ord_cuspInftyBar]
  change (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).order = _
  rw [order_coeffEmb, order_qExpand, order_jq, mul_neg, mul_one]

theorem frickeInvolutionBar_coeffEmb_qExpand (N : ℕ) [NeZero N]
    (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a]
    [NeZero b] : frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full N (Dvd.intro b hab))⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by
  rw [frickeInvolutionBar_def]
  refine (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
    (frickeInvolutionFull N) ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩).trans
    (Subtype.ext ?_)
  change coeffEmb (AlgebraicClosure ℚ)
    ((frickeInvolutionFull N ⟨qExpand ℚ a jq, _⟩ : modularFunctionFieldFull N) :
      LaurentSeries ℚ) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq)
  rw [h a b hab ‹NeZero a› ‹NeZero b›]

theorem ord_cuspZeroBar_coeffEmb_qExpand (N : ℕ) [NeZero N]
    (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a]
    [NeZero b] : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by
  rw [cuspZeroBar_def, ← frickeInvolutionBar_coeffEmb_qExpand N h a b hab]
  exact (SemilinearAut.ord_smul (SemilinearAut.ofAlgAut (frickeInvolutionBar N)) (cuspInftyBar N)
    _).trans (ord_cuspInftyBar_coeffEmb_qExpand N a (Dvd.intro b hab))

theorem ord_cuspZeroBar_coeffEmb_jq (N : ℕ) [NeZero N]
    (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -N := by
  have e := ord_cuspZeroBar_coeffEmb_qExpand N h N 1 (mul_one N)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full N (Dvd.intro_left N (mul_one N)))⟩ : modularFunctionFieldBar N) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :=
    Subtype.ext (by simp only [qExpand_one_apply])
  rwa [hj] at e

/-! ## The Fricke compatibility and the cusp split -/

theorem cuspZeroBar_ne_cuspInftyBar (N : ℕ) [NeZero N]
    (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) :
    cuspZeroBar N ≠ cuspInftyBar N := by
  intro e
  have h0 := ord_cuspZeroBar_coeffEmb_jq N h
  rw [e, ord_cuspInftyBar_coeffEmb_jq] at h0
  have : (N : ℤ) = 1 := by linarith
  exact absurd (Nat.cast_eq_one.mp this) hN.ne'

theorem isCusp_iff_ord_neg {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E] (j : E)
    (v : Place K E) : IsCusp j v ↔ v.ord j < 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [isCusp_iff, Place.ord_zero]
    exact ⟨fun h => (h (zero_mem _)).elim, fun h => (lt_irrefl _ h).elim⟩
  · rw [isCusp_iff, v.mem_iff_ord_nonneg hj, not_le]

theorem isCusp_cuspInftyBar (N : ℕ) [NeZero N] :
    IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) (cuspInftyBar N) := by
  rw [isCusp_iff_ord_neg, ord_cuspInftyBar_coeffEmb_jq]
  norm_num

theorem isCusp_cuspZeroBar (N : ℕ) [NeZero N]
    (h : IsFrickeAutFull N (frickeInvolutionFull N)) :
    IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) (cuspZeroBar N) := by
  rw [isCusp_iff_ord_neg, ord_cuspZeroBar_coeffEmb_jq N h, neg_lt_zero, Nat.cast_pos]
  exact Nat.pos_of_ne_zero (NeZero.ne N)

end ModularCurve
