/-
  The shell bound: the value of `distribHaarChar`/`ideleNorm` on a uniformizer
  power, the strict inequality `one_lt_absNorm`, the base family `baseFam` and
  its norm/summability/`< 1` estimates, the index map `toNatVec` with its
  injectivity on nonnegative vectors, and the summability criterion
  `summable_of_shell_bound`.

  Transcribed from the pin's `Fold_ShellBound` section
  (`M4aLocalCFT.ShellBound` namespace), declared lines 4859-4963 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  file-scoped `set_option maxHeartbeats 1600000` / `maxSynthPendingDepth 3`
  (A 4841/4843); the declarations elaborate at the low edit cap.  No file-wide
  option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.PlaceSum

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_ShellBound

open NumberField.TateGlobal LanglandsTunnell.TateLocal
open NumberField.TateGlobal.EulerBookkeeping

open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace ShellBound

variable {F : Type} [Field F] [NumberField F]

-- pin: distribHaarChar_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4859)
theorem distribHaarChar_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (unifPow ϖ k)
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-n) := by
  rw [unifPow, Finsupp.prod, Finsupp.prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow, TateGlobal.distribHaarChar_embUnit_eq_local,
    LocalHaarModulus.distribHaarChar_adicCompletion]
  have h1 : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ.ϖ v)) = 1 :=
    ϖ.ordAt_eq_one v
  rw [h1, ← zpow_mul, neg_one_mul]

-- pin: ideleNorm_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4870)
theorem ideleNorm_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ideleNorm F (unifPow ϖ k) = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ)) ^ (-n) := by
  rw [ideleNorm, distribHaarChar_unifPow, Finsupp.prod, Finsupp.prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [NNReal.coe_zpow, NNReal.coe_natCast]

-- pin: one_lt_absNorm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4876)
theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := TateGlobal.absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

-- pin: baseFam (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4883)
def baseFam (F : Type) [Field F] [NumberField F] (σ : ℝ) :
    HeightOneSpectrum (𝓞 F) → ℂ :=
  fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ)

-- pin: norm_baseFam (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4887)
theorem norm_baseFam (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖baseFam F σ v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  rw [baseFam, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

-- pin: summable_norm_baseFam (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4892)
theorem summable_norm_baseFam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ‖baseFam F σ v‖ := by
  refine (TateGlobal.summable_absNorm_rpow_neg hσ).congr fun v => ?_
  rw [norm_baseFam]

-- pin: norm_baseFam_lt_one (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4897)
theorem norm_baseFam_lt_one {σ : ℝ} (hσ : 1 < σ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖baseFam F σ v‖ < 1 := by
  rw [norm_baseFam]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
  exact_mod_cast one_lt_absNorm v

-- pin: norm_mono_baseFam (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4903)
theorem norm_mono_baseFam (σ : ℝ) (m : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    ‖mono (baseFam F σ) m‖ = m.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n := by
  rw [mono, Finsupp.prod, Finsupp.prod, norm_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [norm_pow, norm_baseFam]

-- pin: toNatVec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4909)
def toNatVec (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  k.mapRange Int.toNat rfl

-- pin: mono_baseFam_toNatVec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4912)
theorem mono_baseFam_toNatVec (σ : ℝ) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ‖mono (baseFam F σ) (toNatVec k)‖
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat := by
  rw [norm_mono_baseFam, toNatVec, Finsupp.prod_mapRange_index (fun v => pow_zero _)]

omit [NumberField F] in
-- pin: toNatVec_injOn (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4918)
theorem toNatVec_injOn {k₁ k₂ : HeightOneSpectrum (𝓞 F) →₀ ℤ}
    (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂) (h : toNatVec k₁ = toNatVec k₂) : k₁ = k₂ := by
  ext v
  have hv := congrArg (fun m => m v) h
  simp only [toNatVec, Finsupp.mapRange_apply] at hv
  have hv₁ : 0 ≤ k₁ v := Finsupp.le_def.mp h₁ v
  have hv₂ : 0 ≤ k₂ v := Finsupp.le_def.mp h₂ v
  omega

-- pin: summable_of_shell_bound (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4927)
theorem summable_of_shell_bound {S : Finset (HeightOneSpectrum (𝓞 F))} {σ : ℝ} (hσ : 1 < σ)
    (c : ExpIndex (F := F) S → ℝ) (hc0 : ∀ k, 0 ≤ c k) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k : ExpIndex (F := F) S, 0 ≤ k.1 →
      c k ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat) * M)
    (hz : ∀ k : ExpIndex (F := F) S, ¬ 0 ≤ k.1 → c k = 0) :
    Summable c := by
  classical
  have hEB : Summable fun m : HeightOneSpectrum (𝓞 F) →₀ ℕ => ‖mono (baseFam F σ) m‖ :=
    summable_norm_mono (summable_norm_baseFam hσ) (norm_baseFam_lt_one hσ)
  refine summable_of_sum_le hc0 (c := M * ∑' m, ‖mono (baseFam F σ) m‖) fun u => ?_
  have hsub : ∑ k ∈ u, c k = ∑ k ∈ u.filter (fun k => 0 ≤ k.1), c k := by
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    by_contra hneg
    exact hk (hz k hneg)
  rw [hsub]
  have hstep : ∑ k ∈ u.filter (fun k => 0 ≤ k.1), c k
      ≤ ∑ k ∈ u.filter (fun k => 0 ≤ k.1), ‖mono (baseFam F σ) (toNatVec k.1)‖ * M := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hcone : 0 ≤ k.1 := (Finset.mem_filter.mp hk).2
    calc c k ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat) * M :=
          hb k hcone
      _ = ‖mono (baseFam F σ) (toNatVec k.1)‖ * M := by rw [mono_baseFam_toNatVec]
  refine hstep.trans ?_
  rw [← Finset.sum_mul, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left ?_ hM
  have hinj : Set.InjOn (fun k : ExpIndex (F := F) S => toNatVec k.1)
      ↑(u.filter (fun k => 0 ≤ k.1)) := fun k₁ h₁ k₂ h₂ he =>
    Subtype.ext (toNatVec_injOn (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2 he)
  have himg : ∑ k ∈ u.filter (fun k => 0 ≤ k.1), ‖mono (baseFam F σ) (toNatVec k.1)‖
      = ∑ m ∈ (u.filter (fun k => 0 ≤ k.1)).image (fun k => toNatVec k.1),
          ‖mono (baseFam F σ) m‖ :=
    (Finset.sum_image (f := fun m => ‖mono (baseFam F σ) m‖) hinj).symm
  rw [himg]
  exact hEB.sum_le_tsum _ fun m _ => norm_nonneg _

end ShellBound
end TateGlobal
end NumberField

end

end Fold_ShellBound
