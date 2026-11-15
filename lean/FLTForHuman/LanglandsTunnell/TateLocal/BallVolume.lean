/-
  The real measure of a ball `{x | Valued.v x ≤ exp k}` in a local field: `|𝔭|ᵏ` times the measure of the
  integer ring.

  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp.lean
-/
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell.TateLocal

section Engine

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem ball_eq_smul_integers (k : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ)
          • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hu : Valued.v ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp k := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  have hu' : Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-k) :=
    valued_uniformizerUnit_zpow v k
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hx
    refine ⟨((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x, ?_, ?_⟩
    · rw [map_mul, hu']
      calc WithZero.exp (-k) * Valued.v x ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_right hx _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hu]
    calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul_right hy _
      _ = WithZero.exp k := mul_one _

private theorem main_of_distribHaarChar_uniformizer [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)]
    (hϖ : distribHaarChar (v.adicCompletion K) (uniformizerUnit K v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹)
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hreg : μ.Regular :=
    MeasureTheory.Measure.regular_of_isAddLeftInvariant
      (NumberField.isCompactAdicCompletionIntegers K v)
      (by
        rw [interior_eq_iff_isOpen.mpr (NumberField.isOpenAdicCompletionIntegers K v)]
        exact ⟨0, (v.adicCompletionIntegers K).zero_mem⟩)
      (NumberField.isCompactAdicCompletionIntegers K v).measure_lt_top.ne
  have hN : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hchar : distribHaarChar (v.adicCompletion K) (uniformizerUnit K v ^ (-k))
      = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ k := by
    rw [map_zpow, hϖ, inv_zpow', neg_neg]
  have hμ : μ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k : ℝ≥0) * μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    rw [ball_eq_smul_integers v k, ← distribHaarChar_mul μ, hchar]
  rw [measureReal_def, measureReal_def, hμ, ENNReal.toReal_mul, ENNReal.coe_toReal]
  congr 1

private theorem distribHaarChar_uniformizerUnit [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] :
    distribHaarChar (v.adicCompletion K) (uniformizerUnit K v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have h0 : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := Units.ne_zero _
  have hmod :=
    NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm (x := ((uniformizerUnit K v : v.adicCompletion K)))
  rw [modulus_of_ne_zero h0, Units.mk0_val] at hmod
  rw [hmod, ← NNReal.coe_inj, coe_nnnorm, NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    NumberField.TateGlobal.toNNReal_exp (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (-1 : ℤ), zpow_neg_one]

end Engine

theorem measureReal_setOf_valued_le_exp (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  exact main_of_distribHaarChar_uniformizer v (distribHaarChar_uniformizerUnit v) μ k

end LanglandsTunnell.TateLocal

end
