/-
  The shared prelude of the local twisted integral at a ramified place.

  This module is the **engine** of the `EisensteinGeneral.LocalRam` headlines
  (`LocalRam.lean`) and of the `LocalUnr` pair still to come.  It is the pin's
  `TwistedSmoothLocal` prelude — the block the pin writes twice, byte-identically, at
  `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:24-486` and
  `S_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean:26-488`; writing it once
  is the dedup this module exists for (972 pin lines -> this file).

  The mathematics: for `F` a number field, `v` a finite place and `ϖ` a uniformizer of
  the completion, `untwisted χ s A B` is the local integrand
  `A + charExt χ⁻¹ · modulus^(-(2s+1)) · B(·⁻¹)` split at the integer ring
  `v.adicCompletionIntegers F`; `absChar χ` is the unitary part of `χ`; and the prelude
  proves the four inputs `integrable_dominator` needs: continuity of `charExt`-twists off
  `0` (uniform continuity at the conductor level, `continuousOn_charExt_inv`), continuity
  of a depth-`m` function `B` (`continuous_of_depth`), continuity of the modulus factor
  (`continuousOn_modulus_cpow`), and an `L¹` dominator for `untwisted (absChar χ)` given
  the eigenvalue bound `‖χ ϖ‖·N^(-2s) < 1` (`integrable_dominator`).

  The pin's `p2m` namespace, its `attribute [-instance]`/`[-simp]` preludes and its
  `set_option maxHeartbeats 3200000` are not transcribed.  The pin's `private` becomes
  public (playbook §4(b)): this is the engine the three headlines import.  Three
  declarations the pin proves here are **substituted** by landed port lemmas and not
  repeated: `setOf_valued_sub_le_mem_nhds`/`setOf_valued_sub_lt_mem_nhds`
  (`NumberField.TateGlobal.WeylSmooth`) and `isCompact_integers`
  (`NumberField.TateGlobal.LocalZetaUnramified`); `higherUnitsAt` is imported from the
  definition gate `LanglandsTunnell/TateLocalConstantsAt.lean` and is not re-declared.

  Proof adaptations, all proof-level (no statement changes): the `v4.34.0` drift
  `Set.mem_setOf_eq` -> `Set.mem_ofPred_eq` and `zero_le'` -> `zero_le`; the pin's
  `AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion` is the
  port's `NumberField.TateGlobal.WeylSmooth.integral_smoothWeylIntegrand_adicCompletion`;
  `modulus_adicCompletion_eq_nnnorm` takes `F` and `v` implicitly in the port, so the
  pin's `… F v x` is spelled `… x`; and `absNorm_pos` is proved in term mode from
  `Ideal.finiteQuotientOfFreeOfNeBot`, the pin's `haveI : Finite …` being a
  `linter.style.haveILetI` warning under the port's warning-free gate.
-/
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylSmooth
import FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

namespace EisensteinGeneral

namespace TwistedSmoothLocal

section Prep

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open LanglandsTunnell.TateLocal NumberField.AdelicLevel
open NumberField.TateGlobal NumberField.TateGlobal.WeylSmooth
open NumberField.TateGlobal.LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: valued_uniformizer_exp (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:53)
theorem valued_uniformizer_exp (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
  hϖ

-- pin: valued_uniformizer_pow (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:58)
theorem valued_uniformizer_pow (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℕ) :
    Valued.v ((ϖ : v.adicCompletion F) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, valued_uniformizer_exp ϖ hϖ, ← WithZero.exp_nsmul]
  congr 1
  simp

-- pin: continuous_of_depth (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:65)
theorem continuous_of_depth (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (m : ℕ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    Continuous B := by
  have hz : Valued.v ((ϖ : v.adicCompletion F) ^ m)
      = (Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) :=
    valued_uniformizer_pow ϖ hϖ m
  have hz0 : Valued.v ((ϖ : v.adicCompletion F) ^ m) ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x _ hz0] with y hy
  rw [hz] at hy
  exact (hB x y hy).symm

-- pin: charExt_inv_eq_of_sub_le (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:83)
theorem charExt_inv_eq_of_sub_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) {x y : v.adicCompletion F} (hx : x ≠ 0)
    (hlt : Valued.v (y - x) < Valued.v x)
    (hle : Valued.v (y - x) ≤ Valued.v x * WithZero.exp (-(c : ℤ))) :
    charExt χ⁻¹ y = charExt χ⁻¹ x := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvy : Valued.v y = Valued.v x := Valuation.map_eq_of_sub_lt _ hlt
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hvy
    exact hvx hvy.symm
  set u : (v.adicCompletion F)ˣ := (Units.mk0 x hx)⁻¹ * Units.mk0 y hy0 with hu
  have huval : (u : v.adicCompletion F) = x⁻¹ * y := by simp [hu]
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := by
    rw [huval, map_mul, map_inv₀, hvy, inv_mul_cancel₀ hvx]
  have hu2 : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
    have h1 : (u : v.adicCompletion F) - 1 = x⁻¹ * (y - x) := by
      rw [huval, mul_sub, inv_mul_cancel₀ hx]
    rw [h1, map_mul, map_inv₀]
    calc (Valued.v x)⁻¹ * Valued.v (y - x)
        ≤ (Valued.v x)⁻¹ * (Valued.v x * WithZero.exp (-(c : ℤ))) := by gcongr
      _ = WithZero.exp (-(c : ℤ)) := by rw [← mul_assoc, inv_mul_cancel₀ hvx, one_mul]
  have hmem : u ∈ higherUnitsAt F v c := ⟨hu1, Or.inr hu2⟩
  have hχu : χ u = 1 := hχ u hmem
  have hy' : Units.mk0 y hy0 = Units.mk0 x hx * u := by
    rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hy0, hy', map_mul]
  simp [hχu]

-- pin: continuousOn_charExt_inv (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:112)
theorem continuousOn_charExt_inv (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ContinuousOn (charExt χ⁻¹) {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  have hzv : Valued.v (x * (ϖ : v.adicCompletion F) ^ c) = Valued.v x * WithZero.exp (-(c : ℤ)) := by
    rw [map_mul, valued_uniformizer_pow ϖ hϖ c]
  have hz0 : Valued.v (x * (ϖ : v.adicCompletion F) ^ c) ≠ 0 := by
    rw [hzv]
    exact mul_ne_zero hvx WithZero.coe_ne_zero
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x _ hz0] with y hy
  rw [hzv] at hy
  have hle1 : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hlt : Valued.v (y - x) < Valued.v x :=
    lt_of_lt_of_le hy (mul_le_of_le_one_right' hle1)
  exact (charExt_inv_eq_of_sub_le χ c hχ hx hlt hy.le).symm

-- pin: continuous_addChar_neg_mul (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:135)
theorem continuous_addChar_neg_mul (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Continuous fun x : v.adicCompletion F => ψ (-(ξ * x)) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one]
    exact continuous_const
  have hvξ : Valued.v ξ ≠ 0 := (Valuation.ne_zero_iff _).mpr hξ
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v)
    (WithZero.exp n * (Valued.v ξ)⁻¹)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero WithZero.coe_ne_zero (inv_ne_zero hvξ)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_le_mem_nhds x z hz0] with y hy
  rw [hz] at hy
  have hsmall : Valued.v (ξ * (y - x)) ≤ WithZero.exp n := by
    rw [map_mul]
    calc Valued.v ξ * Valued.v (y - x)
        ≤ Valued.v ξ * (WithZero.exp n * (Valued.v ξ)⁻¹) := by gcongr
      _ = WithZero.exp n := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hvξ, mul_one]
  have h1 : ψ (ξ * (y - x)) = 1 := hψn _ hsmall
  have hsplit : -(ξ * y) = -(ξ * x) + -(ξ * (y - x)) := by ring
  show ψ (-(ξ * x)) = ψ (-(ξ * y))
  rw [hsplit, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (ψ := ψ) (ξ * (y - x)), h1, inv_one,
    mul_one]

-- pin: norm_addChar_of_level (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:164)
theorem norm_addChar_of_level (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (x : v.adicCompletion F) : ‖ψ x‖ = 1 := by
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hvq : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
    have h := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (Ideal.absNorm v.asIdeal : 𝓞 F)).mpr
      (by exact_mod_cast Ideal.absNorm_mem v.asIdeal)
    rw [← valued_algebraMap (K := F) v (Ideal.absNorm v.asIdeal : 𝓞 F)] at h
    simpa only [map_natCast] using h
  obtain ⟨j, hj⟩ : ∃ j : ℕ,
      Valued.v (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x) ≤ WithZero.exp n := by
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [map_mul, hx, mul_zero]; exact zero_le⟩
    · by_cases hq0 : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = 0
      · exact ⟨1, by rw [map_mul, map_pow, hq0, pow_one, zero_mul]; exact zero_le⟩
      · have hql : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)
            = WithZero.exp (WithZero.log (Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F))) :=
          (WithZero.exp_log hq0).symm
        have hxm : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        set l := WithZero.log (Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)) with hl
        set m := WithZero.log (Valued.v x) with hm
        have hl0 : l < 0 := by
          rw [hql, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hvq
          exact hvq
        refine ⟨(m - n).toNat, ?_⟩
        rw [map_mul, map_pow, hql, hxm, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_exp,
          nsmul_eq_mul]
        have h1 : (m - n : ℤ) ≤ ((m - n).toNat : ℤ) := Int.self_le_toNat (m - n)
        have h2 : (0 : ℤ) ≤ ((m - n).toNat : ℤ) := by omega
        have h3 : ((m - n).toNat : ℤ) * l ≤ ((m - n).toNat : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) h2
        linarith
  have h1 : ψ (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x) = 1 := hψn _ hj
  have h2 : ψ (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * x)
      = ψ x ^ (Ideal.absNorm v.asIdeal ^ j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_pow]
  have h3 : ‖ψ x‖ ^ (Ideal.absNorm v.asIdeal ^ j) = 1 := by rw [← norm_pow, ← h2, h1, norm_one]
  have hqj : Ideal.absNorm v.asIdeal ^ j ≠ 0 := pow_ne_zero _ (by omega)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hqj).mp h3

-- pin: untwisted (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:204)
def untwisted (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (A B : v.adicCompletion F → ℂ)
    (x : v.adicCompletion F) : ℂ :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x

-- pin: modulus_eq_of_valued_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:210)
theorem modulus_eq_of_valued_eq {x y : v.adicCompletion F} (h : Valued.v x = Valued.v y) :
    modulus x = modulus y := by
  rw [modulus_adicCompletion_eq_nnnorm x, modulus_adicCompletion_eq_nnnorm y]
  apply NNReal.coe_injective
  simp only [coe_nnnorm]
  exact le_antisymm (Valued.toNormedField.norm_le_iff.mpr h.le) (Valued.toNormedField.norm_le_iff.mpr h.ge)

-- pin: isOpen_integers (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:217)
theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hr : Valued.v.restrict (1 : v.adicCompletion F) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, map_one]
    exact one_ne_zero
  have h := Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  convert h using 1
  ext y
  simp only [SetLike.mem_coe, mem_adicCompletionIntegers, Set.mem_ofPred_eq]
  rw [Valuation.restrict_le_iff, map_one]

-- pin: continuousOn_of_valued_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:231)
theorem continuousOn_of_valued_eq {E : Type} [TopologicalSpace E] (g : v.adicCompletion F → E)
    (hg : ∀ x y : v.adicCompletion F, Valued.v x = Valued.v y → g x = g y) :
    ContinuousOn g {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  apply ContinuousAt.continuousWithinAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [setOf_valued_sub_lt_mem_nhds x x hvx] with y hy
  exact hg x y (Valuation.map_eq_of_sub_lt _ hy).symm

-- pin: continuousOn_modulus_cpow (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:242)
theorem continuousOn_modulus_cpow (w : ℂ) :
    ContinuousOn (fun y : v.adicCompletion F => ((modulus y : ℝ) : ℂ) ^ w) {(0 : v.adicCompletion F)}ᶜ :=
  continuousOn_of_valued_eq _ fun x y h => by rw [modulus_eq_of_valued_eq h]

-- pin: compl_integers_subset (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:246)
theorem compl_integers_subset :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  intro x hx h0
  apply hx
  rw [Set.mem_singleton_iff] at h0
  subst h0
  exact (v.adicCompletionIntegers F).zero_mem

section Measurability

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F))

-- pin: aestronglyMeasurable_untwisted (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:259)
theorem aestronglyMeasurable_untwisted (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) (m : ℕ)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) : AEStronglyMeasurable (untwisted χ s A B) μ := by
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isOpen_integers.measurableSet
  have h1 : AEStronglyMeasurable
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A) μ :=
    (aestronglyMeasurable_indicator_iff hO).mpr hA.aestronglyMeasurable
  have hcont : ContinuousOn (fun y : v.adicCompletion F =>
      charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := by
    have h0 := compl_integers_subset (F := F) (v := v)
    have hB' : ContinuousOn (fun y : v.adicCompletion F => B y⁻¹)
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ :=
      (continuous_of_depth ϖ hϖ m B hB).comp_continuousOn (continuousOn_inv₀.mono h0)
    exact (((continuousOn_charExt_inv ϖ hϖ χ c hχ).mono h0).mul
      ((continuousOn_modulus_cpow _).mono h0)).mul hB'
  have h2 : AEStronglyMeasurable
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => charExt χ⁻¹ y * ((modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹)) μ :=
    (aestronglyMeasurable_indicator_iff hO.compl).mpr (hcont.aestronglyMeasurable hO.compl)
  exact h1.add h2

end Measurability

-- pin: absChar (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:289)
def absChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun u := Units.mk0 ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    (by exact_mod_cast (norm_ne_zero_iff.mpr (χ u).ne_zero))
  map_one' := by
    ext
    simp
  map_mul' u w := by
    ext
    simp

-- pin: absChar_apply (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:299)
theorem absChar_apply (χ : (v.adicCompletion F)ˣ →* ℂˣ) (u : (v.adicCompletion F)ˣ) :
    ((absChar χ u : ℂˣ) : ℂ) = ((‖((χ u : ℂˣ) : ℂ)‖ : ℝ) : ℂ) :=
  rfl

-- pin: absChar_higherUnits (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:303)
theorem absChar_higherUnits (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) :
    ∃ c : ℕ, ∀ u ∈ higherUnitsAt F v c, absChar χ u = 1 := by
  refine ⟨c, fun u hu => ?_⟩
  ext
  rw [absChar_apply, hχ u hu]
  simp

-- pin: norm_charExt_inv_absChar (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:311)
theorem norm_charExt_inv_absChar (χ : (v.adicCompletion F)ˣ →* ℂˣ) (y : v.adicCompletion F) :
    ‖charExt χ⁻¹ y‖ = ‖charExt (absChar χ)⁻¹ y‖ := by
  by_cases hy : y = 0
  · subst hy
    simp
  rw [charExt_of_ne_zero _ hy, charExt_of_ne_zero _ hy]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, absChar_apply]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]

-- pin: depth_norm_add_one (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:320)
theorem depth_norm_add_one (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) →
      (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) y = (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) x := by
  intro x y hxy
  simp only [hB x y hxy]

-- pin: absNorm_pos (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:327)
theorem absNorm_pos : 0 < Ideal.absNorm v.asIdeal :=
  Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff v.asIdeal).mpr
    (Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot))

-- pin: hs_absChar (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:331)
theorem hs_absChar (ϖ : (v.adicCompletion F)ˣ) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ‖((absChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ)))‖ < 1 := by
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos (F := F) (v := v)
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN] at hs ⊢
  rw [absChar_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  convert hs using 3
  simp

-- pin: norm_untwisted_le (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:343)
theorem norm_untwisted_le (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) (A B : v.adicCompletion F → ℂ)
    (x : v.adicCompletion F) :
    ‖untwisted χ s A B x‖
      ≤ ‖untwisted (absChar χ) (s.re : ℂ) (fun z => ((‖A z‖ + 1 : ℝ) : ℂ)) (fun z => ((‖B z‖ + 1 : ℝ) : ℂ)) x‖ := by
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · simp only [untwisted, Set.indicator_of_mem hx, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx),
      add_zero, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    linarith
  · have hx0 : x ≠ 0 := fun h => hx (h ▸ (v.adicCompletionIntegers F).zero_mem)
    have hmod : (0 : ℝ) < (modulus x : ℝ) := by
      rw [modulus_adicCompletion_eq_nnnorm x]
      exact_mod_cast norm_pos_iff.mpr hx0
    simp only [untwisted, Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx), zero_add,
      norm_mul]
    rw [norm_charExt_inv_absChar, Complex.norm_cpow_eq_rpow_re_of_pos hmod,
      Complex.norm_cpow_eq_rpow_re_of_pos hmod]
    have hre : (-(2 * s + 1)).re = (-(2 * (s.re : ℂ) + 1)).re := by simp
    rw [hre]
    gcongr
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

section NormAddOne

variable [MeasurableSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

-- pin: integrableOn_norm_add_one (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:371)
theorem integrableOn_norm_add_one (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ) :
    IntegrableOn (fun z => ((‖A z‖ + 1 : ℝ) : ℂ)) (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ := by
  have hfin : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    (isCompact_integers.measure_lt_top).ne
  exact (hA.norm.add (integrableOn_const hfin)).ofReal

end NormAddOne

-- pin: charExt_absChar_inv_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:380)
theorem charExt_absChar_inv_eq (χ : (v.adicCompletion F)ˣ →* ℂˣ) (x : v.adicCompletion F) :
    charExt (absChar χ)⁻¹ x = ((‖charExt χ⁻¹ x‖ : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    simp
  rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero _ hx]
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, absChar_apply, norm_inv]
  push_cast
  rfl

section Domination

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

-- pin: integrable_dominator (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:395)
theorem integrable_dominator (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    Integrable (untwisted (absChar χ) (s.re : ℂ) (fun z => ((‖A z‖ + 1 : ℝ) : ℂ))
      (fun z => ((‖B z‖ + 1 : ℝ) : ℂ))) μ := by
  set A' : v.adicCompletion F → ℂ := fun z => ((‖A z‖ + 1 : ℝ) : ℂ) with hA'def
  set B' : v.adicCompletion F → ℂ := fun z => ((‖B z‖ + 1 : ℝ) : ℂ) with hB'def
  have hval := NumberField.TateGlobal.WeylSmooth.integral_smoothWeylIntegrand_adicCompletion F v μ ϖ hϖ
    (absChar χ) (absChar_higherUnits χ c hχ) m hm A' (integrableOn_norm_add_one μ A hA) B'
    (depth_norm_add_one m B hB) (s.re : ℂ) (hs_absChar ϖ χ s hs)
  change ∫ x, untwisted (absChar χ) (s.re : ℂ) A' B' x ∂μ = _ at hval
  by_contra hnot
  rw [integral_undef hnot] at hval

  have hfin : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    isCompact_integers.measure_lt_top.ne
  have hpos : 0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    ENNReal.toReal_pos (isOpen_integers.measure_pos μ ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne' hfin
  have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos (F := F) (v := v)

  have hshell : ∀ S : Set (v.adicCompletion F),
      ∃ r : ℝ, 0 ≤ r ∧ ∫ x in S, charExt (absChar χ)⁻¹ x * B' x⁻¹ ∂μ = (r : ℂ) := by
    intro S
    refine ⟨∫ x in S, ‖charExt χ⁻¹ x‖ * (‖B x⁻¹‖ + 1) ∂μ, integral_nonneg fun x => by positivity, ?_⟩
    have heq : (fun x => charExt (absChar χ)⁻¹ x * B' x⁻¹)
        = fun x => ((‖charExt χ⁻¹ x‖ * (‖B x⁻¹‖ + 1) : ℝ) : ℂ) := by
      funext x
      rw [charExt_absChar_inv_eq, hB'def]
      push_cast
      ring
    rw [heq, integral_complex_ofReal]
  have hunit : ∃ r : ℝ, 0 ≤ r ∧
      ∫ u in {u : v.adicCompletion F | Valued.v u = 1}, charExt (absChar χ)⁻¹ u ∂μ = (r : ℂ) := by
    refine ⟨∫ u in {u : v.adicCompletion F | Valued.v u = 1}, ‖charExt χ⁻¹ u‖ ∂μ,
      integral_nonneg fun x => by positivity, ?_⟩
    have heq : (fun u => charExt (absChar χ)⁻¹ u) = fun u => ((‖charExt χ⁻¹ u‖ : ℝ) : ℂ) := by
      funext u
      rw [charExt_absChar_inv_eq]
    rw [heq, integral_complex_ofReal]

  set ra : ℝ := ‖((χ ϖ : ℂˣ) : ℂ)‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) with hra_def
  have hra0 : 0 ≤ ra := by positivity
  have hra1 : ra < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN] at hs
    convert hs using 3
    simp
  have hratio : ((absChar χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ))) = (ra : ℂ) := by
    rw [absChar_apply, hra_def, Complex.ofReal_mul, Complex.ofReal_cpow hN.le]
    push_cast
    ring_nf
  have hcpow : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s.re : ℂ) + 1))
      = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hN.le]
    push_cast
    ring_nf
  have key : ∀ t₁ t₂ t₃ : ℂ,
      μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≤ t₁.re → 0 ≤ t₂.re → 0 ≤ t₃.re →
      (0 : ℂ) = t₁ + t₂ + t₃ → False := by
    intro t₁ t₂ t₃ h₁ h₂ h₃ h
    have := congrArg Complex.re h
    simp only [Complex.zero_re, Complex.add_re] at this
    linarith
  refine key _ _ _ ?_ ?_ ?_ hval
  ·
    have heq : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A' x ∂μ
        = ((∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (‖A x‖ + 1) ∂μ : ℝ) : ℂ) := by
      rw [hA'def]
      exact integral_complex_ofReal
    rw [heq, Complex.ofReal_re]
    have hmono : ∫ _ in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (1 : ℝ) ∂μ
        ≤ ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), (‖A x‖ + 1) ∂μ :=
      integral_mono (integrableOn_const hfin) (hA.norm.add (integrableOn_const hfin))
        fun x => by simp
    rw [setIntegral_const, smul_eq_mul, mul_one] at hmono
    exact hmono
  ·
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    obtain ⟨r, hr0, hr⟩ := hshell {x : v.adicCompletion F | Valued.v x = Multiplicative.ofAdd (k : ℤ)}
    rw [hr, hcpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg (Real.rpow_nonneg hN.le _) k) hr0
  ·
    obtain ⟨r, hr0, hr⟩ := hunit
    rw [hr, hratio, hB'def]
    simp only
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h1 : 0 < 1 - ra := by linarith
    positivity

end Domination

end Prep

end TwistedSmoothLocal

end EisensteinGeneral
