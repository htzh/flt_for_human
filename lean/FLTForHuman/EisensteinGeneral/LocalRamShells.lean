/-
  The shell/set machinery of the local twisted integral at a ramified place.

  This is the **engine** behind the three `EisensteinGeneral.LocalRam` headlines: the
  integrability of the twisted integrand against an additive character
  (`integrable_twisted_aux`), the open/measurable shells `{x | Valued.v x ≤ c}`,
  `{x | Valued.v x < c}`, `{x | Valued.v x = exp k}`, `{x | exp k < Valued.v x}`, the
  bridge `coe_modulus_of_valued_eq` from the valuation to the modulus, and the two
  translation identities that let the large shells be summed: `untwisted_add_eq_of_sphere`
  (the sphere of `x` is stable under translation by a deep enough `t`) and file C's
  `untwisted_add_eq` (the same stability without a sphere hypothesis).

  Sources, pinned `aa2d8b3`:
  `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:490,510-573,583-622` and
  `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean:67-135`.
  The pin's `ofReal_pow_cpow` (A:575) is **not** transcribed: it is public in
  `TateGlobal/WeylShell.lean` (a promotion, WORKORDER-E1 §3) and is used, and imported,
  by the headline module `LocalRam.lean` only.

  `EisensteinGeneral.TwistedSmoothLocal.LocalTwisted` supplies every prelude lemma used
  here (`untwisted`, `charExt_inv_eq_of_sub_le`, `modulus_eq_of_valued_eq`,
  `integrable_dominator`, `norm_untwisted_le`, …); the pin's `private` is public here
  (playbook §4(b)).  The pin's `p2m` prefix, its `attribute [-instance]`/`[-simp]`
  preludes and its `maxHeartbeats` are not transcribed.  One drift adaptation:
  `Set.mem_setOf_eq` -> `Set.mem_ofPred_eq` and `zero_le'` -> `zero_le` (mathlib
  `v4.34.0`); `modulus_adicCompletion_eq_nnnorm` is the port's `(x)`-binder copy in
  `TateGlobal/NormIntegrable.lean`.
-/
import FLTForHuman.EisensteinGeneral.LocalTwisted
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
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

section Domination

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

-- pin: integrable_twisted_aux (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:490)
theorem integrable_twisted_aux (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m) (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1) (ξ : v.adicCompletion F) :
    Integrable (fun x => untwisted χ s A B x * ψ (-(ξ * x))) μ := by
  have hD := (integrable_dominator μ ϖ hϖ χ c hχ m hm A hA B hB s hs).norm
  refine hD.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (aestronglyMeasurable_untwisted μ ϖ hϖ χ c hχ m A hA B hB s).mul
      (continuous_addChar_neg_mul ψ n hψn ξ).aestronglyMeasurable
  · rw [norm_mul, norm_addChar_of_level ψ n hψn, mul_one]
    exact norm_untwisted_le χ s A B x

end Domination

-- pin: isOpen_setOf_valued_le (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:510)
theorem isOpen_setOf_valued_le (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v z} := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have h := Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_le_iff]

-- pin: isOpen_setOf_valued_lt (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:520)
theorem isOpen_setOf_valued_lt (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    IsOpen {x : v.adicCompletion F | Valued.v x < Valued.v z} := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have h := Valued.isOpen_ball (R := v.adicCompletion F) (Valued.v.restrict z)
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff]

section ShellSets

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

-- pin: measurableSet_setOf_valued_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:534)
theorem measurableSet_setOf_valued_eq (k : ℤ) :
    MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp k} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp k)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hset : {x : v.adicCompletion F | Valued.v x = WithZero.exp k}
      = {x : v.adicCompletion F | Valued.v x ≤ Valued.v z}
          ∩ {x : v.adicCompletion F | Valued.v x < Valued.v z}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt, ← hz]
    exact le_antisymm_iff
  rw [hset]
  exact (isOpen_setOf_valued_le z hz0).measurableSet.inter (isOpen_setOf_valued_lt z hz0).measurableSet.compl

-- pin: measurableSet_setOf_exp_lt (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:549)
theorem measurableSet_setOf_exp_lt (k : ℤ) :
    MeasurableSet {x : v.adicCompletion F | WithZero.exp k < Valued.v x} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp k)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hset : {x : v.adicCompletion F | WithZero.exp k < Valued.v x}
      = {x : v.adicCompletion F | Valued.v x ≤ Valued.v z}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le, hz]
  rw [hset]
  exact (isOpen_setOf_valued_le z hz0).measurableSet.compl

end ShellSets

-- pin: toAdd_unzero_exp (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:564)
theorem toAdd_unzero_exp (j : ℤ) (h : WithZero.exp j ≠ 0) :
    (WithZero.unzero h).toAdd = j :=
  congrArg Multiplicative.toAdd (WithZero.unzero_coe (x := Multiplicative.ofAdd j) h)

-- pin: coe_modulus_of_valued_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:568)
theorem coe_modulus_of_valued_eq {x : v.adicCompletion F} {j : ℤ}
    (hx : Valued.v x = WithZero.exp j) :
    ((modulus x : NNReal) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ j := by
  rw [modulus_adicCompletion_eq_nnnorm x, coe_nnnorm, NumberField.FinitePlace.norm_def, hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp, NNReal.coe_zpow]
  norm_cast
-- pin: untwisted_add_eq_of_sphere (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:583)
theorem untwisted_add_eq_of_sphere (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ) (hc : 1 ≤ c)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) (m : ℕ) (hm : 1 ≤ m) (s : ℂ)
    (A B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {t x : v.adicCompletion F} {j : ℤ} (hmj : (m : ℤ) ≤ j) (hx : Valued.v x = WithZero.exp j)
    (ht : Valued.v t ≤ WithZero.exp (j - c)) :
    untwisted χ s A B (t + x) = untwisted χ s A B x := by
  have hvx1 : (1 : WithZero (Multiplicative ℤ)) < Valued.v x := by
    rw [hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hvx1
    exact (not_lt_of_ge zero_le) hvx1
  have htlt : Valued.v t < Valued.v x := by
    rw [hx]
    exact lt_of_le_of_lt ht (WithZero.exp_lt_exp.mpr (by omega))
  have hvtx : Valued.v (t + x) = Valued.v x := Valued.v.map_add_eq_of_lt_right htlt
  have hxO : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show x ∉ v.adicCompletionIntegers F
    rw [mem_adicCompletionIntegers]
    exact not_le_of_gt hvx1
  have htxO : t + x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show t + x ∉ v.adicCompletionIntegers F
    rw [mem_adicCompletionIntegers, hvtx]
    exact not_le_of_gt hvx1
  have hB0 : ∀ y : v.adicCompletion F, Valued.v y = WithZero.exp j → B y⁻¹ = B 0 := by
    intro y hy
    refine hB 0 y⁻¹ ?_
    rw [sub_zero, map_inv₀, hy, ← WithZero.exp_neg]
    show WithZero.exp (-j) ≤ WithZero.exp (-(m : ℤ))
    exact WithZero.exp_le_exp.mpr (by omega)
  have hsub : (t + x) - x = t := add_sub_cancel_right t x
  simp only [untwisted, Set.indicator_of_notMem hxO, Set.indicator_of_notMem htxO,
    Set.indicator_of_mem (Set.mem_compl hxO), Set.indicator_of_mem (Set.mem_compl htxO), zero_add]
  have hchar : charExt χ⁻¹ (t + x) = charExt χ⁻¹ x := by
    refine charExt_inv_eq_of_sub_le χ c hχ hx0 (by rw [hsub]; exact htlt) ?_
    rw [hsub, hx, ← WithZero.exp_add]
    exact ht.trans (WithZero.exp_le_exp.mpr (by omega))
  rw [hchar, modulus_eq_of_valued_eq hvtx, hB0 _ (hvtx.trans hx), hB0 _ hx]

-- pin: untwisted_add_eq (S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean:67)
theorem untwisted_add_eq (χ : (v.adicCompletion F)ˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ higherUnitsAt F v c, χ u = 1) (m : ℕ) (s : ℂ) (A B : v.adicCompletion F → ℂ)
    (hA' : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    {t : v.adicCompletion F} (ht : Valued.v t ≤ WithZero.exp (-((max m c : ℕ) : ℤ))) (x : v.adicCompletion F) :
    untwisted χ s A B (t + x) = untwisted χ s A B x := by
  have htm : Valued.v t ≤ WithZero.exp (-(m : ℤ)) :=
    ht.trans (WithZero.exp_le_exp.mpr (by omega))
  have htc : Valued.v t ≤ WithZero.exp (-(c : ℤ)) :=
    ht.trans (WithZero.exp_le_exp.mpr (by omega))
  have ht1 : Valued.v t ≤ 1 :=
    htm.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hsub : (t + x) - x = t := add_sub_cancel_right t x
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  ·
    have hx' : x ∈ v.adicCompletionIntegers F := hx
    have htx : t + x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      show t + x ∈ v.adicCompletionIntegers F
      rw [mem_adicCompletionIntegers] at hx' ⊢
      exact (Valued.v.map_add t x).trans (max_le ht1 hx')
    simp only [untwisted, Set.indicator_of_mem hx, Set.indicator_of_mem htx,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx), Set.indicator_of_notMem (Set.notMem_compl_iff.mpr htx),
      add_zero]
    exact hA' x (t + x) (by rw [hsub]; exact htm)
  ·
    have hx' : x ∉ v.adicCompletionIntegers F := hx
    have hvx : 1 < Valued.v x := by
      rw [mem_adicCompletionIntegers] at hx'
      exact lt_of_not_ge hx'
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hvx
      exact (not_lt_of_ge zero_le) hvx
    have htlt : Valued.v t < Valued.v x := lt_of_le_of_lt ht1 hvx
    have hvtx : Valued.v (t + x) = Valued.v x := Valued.v.map_add_eq_of_lt_right htlt
    have htx : t + x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      show t + x ∉ v.adicCompletionIntegers F
      rw [mem_adicCompletionIntegers, hvtx]
      exact not_le_of_gt hvx
    have htx0 : t + x ≠ 0 := by
      rintro h
      rw [h, map_zero] at hvtx
      exact ((Valuation.ne_zero_iff _).mpr hx0) hvtx.symm
    simp only [untwisted, Set.indicator_of_notMem hx, Set.indicator_of_notMem htx,
      Set.indicator_of_mem (Set.mem_compl hx), Set.indicator_of_mem (Set.mem_compl htx), zero_add]

    have hchar : charExt χ⁻¹ (t + x) = charExt χ⁻¹ x := by
      refine charExt_inv_eq_of_sub_le χ c hχ hx0 (by rw [hsub]; exact htlt) ?_
      rw [hsub]
      calc Valued.v t ≤ WithZero.exp (-(c : ℤ)) := htc
        _ = 1 * WithZero.exp (-(c : ℤ)) := (one_mul _).symm
        _ ≤ Valued.v x * WithZero.exp (-(c : ℤ)) := by gcongr
    have hmod : modulus (t + x) = modulus x := modulus_eq_of_valued_eq hvtx
    have hBinv : B (t + x)⁻¹ = B x⁻¹ := by
      refine hB x⁻¹ (t + x)⁻¹ ?_

      have hid : (t + x)⁻¹ - x⁻¹ = -(t * ((t + x)⁻¹ * x⁻¹)) := by
        field_simp
        ring
      rw [hid, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hvtx]
      have hinv : (Valued.v x)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (pos_of_gt hvx)]
        exact hvx.le
      calc Valued.v t * ((Valued.v x)⁻¹ * (Valued.v x)⁻¹)
          ≤ Valued.v t * (1 * 1) := by gcongr
        _ = Valued.v t := by rw [mul_one, mul_one]
        _ ≤ Multiplicative.ofAdd (-(m : ℤ)) := htm
    rw [hchar, hmod, hBinv]

end Prep

end TwistedSmoothLocal

end EisensteinGeneral
