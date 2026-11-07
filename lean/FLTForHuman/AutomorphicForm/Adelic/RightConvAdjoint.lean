/-
  The adjointness of right convolution for the twisted weighted pairing.

  Let `Φ₀` be a fundamental domain for the global-point range inside a determinant window
  `{g | ideleNorm (det g) ∈ Icc α β}`, `ξ` a character of the idele group whose value on `z` has norm
  `ideleNorm z ^ σ`, `u`, `v` two functions that are `ξ`-eigen (an `IsLsXiFunction`), continuous,
  and square-integrable on `Φ₀`, and `g` a continuous compactly supported function. Then, at the
  level of the twisted pairing,

  `∫_{Φ₀} (u * g) x conj (v x) |det x|^-σ
     = ∫_{Φ₀} u x conj ((v * g*) x) |det x|^-σ`,

  where `g* y = conj (g y⁻¹) |det y|^-σ` is the adjoint kernel of `|det|^-σ`-weighted convolution,
  and both sides are again square-integrable on `Φ₀`. This is the right-*convolution* half of the
  pairing calculation whose right-*translation* half is `RightTranslateAdjoint.lean`; the argument
  is Fubini on `Φ₀ × GL₂(𝔸)` together with the change of variables `y ↦ x⁻¹ y` and the character's
  growth law, and it consumes the translation half at the point `x`.

  Transcribed from the pin `S_` file and its `Theorems/` wrapper (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.lean`
  * `Theorems/Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.lean`

  The pin's namespace `WeightedPairingAdjoint` is the subject name and is kept.

  **Visibility follows the pin's**: a `private` prelude and the one public headline.

  **Wiring.** `spec/check_port.py` owns the public declaration here: the wrapper and the `S_` file
  are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateAdjoint
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel
open AutomorphicForm
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace LocalIntertwining

namespace WeightedPairingAdjoint

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume NumberField.AdelicHaar
open MeasureTheory.Measure
open scoped ComplexConjugate ENNReal NNReal

variable (K : Type) [Field K] [NumberField K]

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

private def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

variable {K}

-- The pin's `sigmaFinite_μ` is an `inferInstance` because its `secondCountable_gl` wall is an
-- instance in scope; the port has the second countability of `GL₂(𝔸)` as the public theorem
-- `secondCountableTopology_generalLinearGroup_finTwo`, which is what the `show`/`unfold` exposes.
private theorem sigmaFinite_μ : SigmaFinite (μ K) := by
  have hsc : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  show SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K)
  unfold adelicGLHaar
  infer_instance

private theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')

private theorem wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

private theorem flat_continuous (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) :
    Continuous (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) :=
  (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul (wt_continuous σ)

private theorem flat_hasCompactSupport (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) := by
  have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => g y⁻¹) :=
    hgc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  have h2 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹)) :=
    h1.comp_left (map_zero (starRingEnd ℂ))
  exact h2.mul_right

private theorem isLsXi_translate (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (y : AdelicGL2 (𝓞 K) K) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (fun x => u (x * y)) where
  left_invariant γ x := by simp only [mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [mul_assoc, hu.central_transform]

private theorem kernel_aestronglyMeasurable (u g : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u) (hg : Continuous g)
    (ν₁ ν₂ : Measure (AdelicGL2 (𝓞 K) K)) :
    AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (p.1 * p.2) * g p.2) (ν₁.prod ν₂) := by
  have hsc : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  exact ((hu.comp (continuous_fst.mul continuous_snd)).mul (hg.comp continuous_snd)).aestronglyMeasurable

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private theorem slab_measurableSet (α β : ℝ) : MeasurableSet (slab (K := K) α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem conv_apply (u g : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    rightConv K u g x = ∫ y, u (x * y) * g y ∂(μ K) := rfl

private theorem kernel_integrable (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : AdelicGL2 (𝓞 K) K) : Integrable (fun y => u (x * y) * g y) (μ K) := by
  have hμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  exact ((huc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left

private theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab (K := K) α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurableSet α β))

private theorem ideleNorm_one' : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [mul_one] at h
  exact (mul_right_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h.symm.trans (one_mul _).symm))

private theorem ideleNorm_inv' (c : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K c⁻¹ = (ideleNorm K c)⁻¹ := by
  have h := ideleNorm_mul (F := K) c c⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

section Scaling

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μ K).restrict (slab α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
  (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (huc : Continuous u)
  (hu₂ : MemLp u 2 ((μ K).restrict Φ₀))

include hα hΦ₀ hFD hσ hu huc hu₂

private theorem memLp_translate (y : AdelicGL2 (𝓞 K) K) : MemLp (fun x => u (x * y)) 2 ((μ K).restrict Φ₀) :=
  (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u u hu hu huc huc
    hu₂ hu₂ y).1

private theorem weighted_sq_translate (y : AdelicGL2 (𝓞 K) K) :
    ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) =
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ *
        ∫ x in Φ₀, ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  have h := (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u
    (fun x => u (x * y)) hu (isLsXi_translate ξ u hu y) huc (huc.comp (continuous_id.mul continuous_const)) hu₂
    (memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ y) y).2.2

  have e1 : ∀ x : AdelicGL2 (𝓞 K) K, u (x * y) * conj (u (x * y)) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) =
      ((‖u (x * y)‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
    intro x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have e2 : ∀ x : AdelicGL2 (𝓞 K) K, u x * conj (u (x * y⁻¹ * y)) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) =
      ((‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
    intro x
    rw [inv_mul_cancel_right, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp only [e1, e2] at h
  exact_mod_cast h

private theorem sq_translate_le (y : AdelicGL2 (𝓞 K) K) :
    ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 ∂(μ K) ≤
      (max (α ^ (-σ)) (β ^ (-σ)) / min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K)) *
        ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ := by
  set m : ℝ := min (α ^ (-σ)) (β ^ (-σ)) with hm
  set M : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hM
  by_cases hαβ : α ≤ β
  swap
  ·
    have hempty : Φ₀ = ∅ := by
      refine Set.subset_empty_iff.mp fun x hx => ?_
      exact hαβ ((hΦ₀ hx).1.trans (hΦ₀ hx).2)
    simp [hempty]
  have hm_pos : 0 < m := lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans_le hαβ) _)
  have hdet : 0 ≤ ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ := (Real.rpow_pos_of_pos (ideleNorm_pos _) _).le

  set w : AdelicGL2 (𝓞 K) K → ℝ := fun x => ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) with hw
  have hw_cont : Continuous w := (continuous_ideleNorm_det K).rpow_const fun x => Or.inl (ideleNorm_pos _).ne'
  have hw_ae : ∀ᵐ x ∂((μ K).restrict Φ₀), m ≤ w x ∧ w x ≤ M :=
    (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => wt_bounds α β σ hα x hx
  have hw_bdd : ∀ᵐ x ∂((μ K).restrict Φ₀), ‖w x‖ ≤ M :=
    hw_ae.mono fun x hx => by rw [Real.norm_of_nonneg (wt_pos σ x).le]; exact hx.2

  have hf_cont : Continuous fun x => ‖u (x * y)‖ ^ 2 :=
    ((huc.comp (continuous_id.mul continuous_const)).norm.pow 2)
  have hf_int : Integrable (fun x => ‖u (x * y)‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm
      (huc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable).1
      (memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ y)
  have hu_int : Integrable (fun x => ‖u x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm huc.aestronglyMeasurable).1 hu₂
  have hfw_int : Integrable (fun x => ‖u (x * y)‖ ^ 2 * w x) ((μ K).restrict Φ₀) := by
    simpa only [mul_comm] using hf_int.bdd_mul hw_cont.aestronglyMeasurable hw_bdd
  have huw_int : Integrable (fun x => ‖u x‖ ^ 2 * w x) ((μ K).restrict Φ₀) := by
    simpa only [mul_comm] using hu_int.bdd_mul hw_cont.aestronglyMeasurable hw_bdd

  have h1 : ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 ∂(μ K) ≤ m⁻¹ * ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 * w x ∂(μ K) := by
    rw [← integral_const_mul]
    refine integral_mono_ae hf_int (hfw_int.const_mul _) (hw_ae.mono fun x hx => ?_)
    have hfx : 0 ≤ ‖u (x * y)‖ ^ 2 := by positivity
    calc ‖u (x * y)‖ ^ 2 = m⁻¹ * (‖u (x * y)‖ ^ 2 * m) := by field_simp
      _ ≤ m⁻¹ * (‖u (x * y)‖ ^ 2 * w x) := by gcongr; exact hx.1

  have h2 : ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 * w x ∂(μ K) =
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ * ∫ x in Φ₀, ‖u x‖ ^ 2 * w x ∂(μ K) :=
    weighted_sq_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ y

  have h3 : ∫ x in Φ₀, ‖u x‖ ^ 2 * w x ∂(μ K) ≤ M * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K) := by
    rw [← integral_const_mul]
    refine integral_mono_ae huw_int (hu_int.const_mul _) (hw_ae.mono fun x hx => ?_)
    have hux : 0 ≤ ‖u x‖ ^ 2 := by positivity
    calc ‖u x‖ ^ 2 * w x ≤ ‖u x‖ ^ 2 * M := by gcongr; exact hx.2
      _ = M * ‖u x‖ ^ 2 := mul_comm _ _
  have hu_nn : 0 ≤ ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K) := integral_nonneg fun x => by positivity
  calc ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 ∂(μ K)
      ≤ m⁻¹ * ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 * w x ∂(μ K) := h1
    _ = m⁻¹ * (ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ * ∫ x in Φ₀, ‖u x‖ ^ 2 * w x ∂(μ K)) := by
        rw [h2]
    _ ≤ m⁻¹ * (ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ * (M * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K))) := by
        gcongr
    _ = (M / m * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K)) * ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ := by
        rw [div_eq_mul_inv]; ring

private theorem exists_uniform_bound (S : Set (AdelicGL2 (𝓞 K) K)) (hS : IsCompact S) :
    ∃ C : ℝ, ∀ y ∈ S, ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 ∂(μ K) ≤ C := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').continuousOn
  have hC₀ : 0 ≤ max (α ^ (-σ)) (β ^ (-σ)) / min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K) := by
    by_cases hαβ : α ≤ β
    · have hm : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
        lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans_le hαβ) _)
      have hM : 0 ≤ max (α ^ (-σ)) (β ^ (-σ)) := le_max_of_le_left (Real.rpow_pos_of_pos hα _).le
      exact mul_nonneg (div_nonneg hM hm.le) (integral_nonneg fun x => by positivity)
    · have hempty : Φ₀ = ∅ := Set.subset_empty_iff.mp fun x hx => hαβ ((hΦ₀ hx).1.trans (hΦ₀ hx).2)
      simp [hempty]
  refine ⟨(max (α ^ (-σ)) (β ^ (-σ)) / min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K)) * B,
    fun y hy => (sq_translate_le α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ y).trans ?_⟩
  exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans (hB y hy)) hC₀

end Scaling

private theorem norm_integral_mul_sq_le {ν : Measure (AdelicGL2 (𝓞 K) K)} (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν) (hb₁ : Integrable b ν)
    (hab : Integrable (fun y => ‖a y‖ ^ 2 * ‖b y‖) ν) :
    ‖∫ y, a y * b y ∂ν‖ ^ 2 ≤ (∫ y, ‖b y‖ ∂ν) * ∫ y, ‖a y‖ ^ 2 * ‖b y‖ ∂ν := by
  have hsqrt_m : AEStronglyMeasurable (fun y => Real.sqrt ‖b y‖) ν := (hb.norm.aemeasurable.sqrt).aestronglyMeasurable
  have hf₁m : AEStronglyMeasurable (fun y => ‖a y‖ * Real.sqrt ‖b y‖) ν := ha.norm.mul hsqrt_m
  have e₀ : ∀ y, ‖a y‖ * Real.sqrt ‖b y‖ * Real.sqrt ‖b y‖ = ‖a y‖ * ‖b y‖ := fun y => by
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have e₁ : ∀ y, (‖a y‖ * Real.sqrt ‖b y‖) ^ 2 = ‖a y‖ ^ 2 * ‖b y‖ := fun y => by
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have e₂ : ∀ y, Real.sqrt ‖b y‖ ^ 2 = ‖b y‖ := fun y => Real.sq_sqrt (norm_nonneg _)
  have hf₁L : MemLp (fun y => ‖a y‖ * Real.sqrt ‖b y‖) (ENNReal.ofReal 2) ν := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hf₁m).2 (by simpa only [e₁] using hab)
  have hf₂L : MemLp (fun y => Real.sqrt ‖b y‖) (ENNReal.ofReal 2) ν := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hsqrt_m).2 (by simpa only [e₂] using hb₁.norm)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg (a y)) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun y => Real.sqrt_nonneg ‖b y‖) hf₁L hf₂L
  simp only [Real.rpow_two, e₀, e₁, e₂] at hHolder
  have h1 : ‖∫ y, a y * b y ∂ν‖ ≤ ∫ y, ‖a y‖ * ‖b y‖ ∂ν := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_mul]
  have hI₁ : 0 ≤ ∫ y, ‖a y‖ ^ 2 * ‖b y‖ ∂ν := integral_nonneg fun y => by positivity
  have hI₂ : 0 ≤ ∫ y, ‖b y‖ ∂ν := integral_nonneg fun y => norm_nonneg _
  have h2 : ‖∫ y, a y * b y ∂ν‖ ≤ Real.sqrt (∫ y, ‖a y‖ ^ 2 * ‖b y‖ ∂ν) * Real.sqrt (∫ y, ‖b y‖ ∂ν) := by
    simp only [Real.sqrt_eq_rpow]
    exact h1.trans hHolder
  calc ‖∫ y, a y * b y ∂ν‖ ^ 2
      ≤ (Real.sqrt (∫ y, ‖a y‖ ^ 2 * ‖b y‖ ∂ν) * Real.sqrt (∫ y, ‖b y‖ ∂ν)) ^ 2 := by
        gcongr
    _ = (∫ y, ‖b y‖ ∂ν) * ∫ y, ‖a y‖ ^ 2 * ‖b y‖ ∂ν := by
        rw [mul_pow, Real.sq_sqrt hI₁, Real.sq_sqrt hI₂, mul_comm]

private theorem memLp_rightConv_of_forall (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (u g : AdelicGL2 (𝓞 K) K → ℂ)
    (huc : Continuous u) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hmem : ∀ y, MemLp (fun x => u (x * y)) 2 ((μ K).restrict Φ₀)) (C : ℝ)
    (hC : ∀ y ∈ tsupport g, ∫ x in Φ₀, ‖u (x * y)‖ ^ 2 ∂(μ K) ≤ C) :
    MemLp (rightConv K u g) 2 ((μ K).restrict Φ₀) := by
  have hsc : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hsig : SigmaFinite (μ K) := sigmaFinite_μ (K := K)
  have hμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  set ν : Measure (AdelicGL2 (𝓞 K) K) := (μ K).restrict (tsupport g) with hν
  have hνfin : IsFiniteMeasure ν := ⟨by simpa [hν] using hgc.measure_lt_top⟩
  have hg_ν : Integrable g ν := (hg.integrable_of_hasCompactSupport hgc).restrict
  have hconv : ∀ x, rightConv K u g x = ∫ y, u (x * y) * g y ∂ν := by
    intro x
    rw [conv_apply, hν]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]).symm

  have hker : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (p.1 * p.2) * g p.2)
      (((μ K).restrict Φ₀).prod ν) := kernel_aestronglyMeasurable u g huc hg _ _
  have hconv_meas : AEStronglyMeasurable (rightConv K u g) ((μ K).restrict Φ₀) := by
    rw [show rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂ν from funext hconv]
    exact hker.integral_prod_right'

  set F : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K → ℝ := fun p => ‖u (p.1 * p.2)‖ ^ 2 * ‖g p.2‖ with hF
  have hF_meas : AEStronglyMeasurable F (((μ K).restrict Φ₀).prod ν) :=
    (((huc.comp (continuous_fst.mul continuous_snd)).norm.pow 2).mul (hg.comp continuous_snd).norm)
      |>.aestronglyMeasurable
  have hF_int : Integrable F (((μ K).restrict Φ₀).prod ν) := by
    refine (integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun y => ?_
      have h2 := (memLp_two_iff_integrable_sq_norm
        (huc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable).1 (hmem y)
      simpa only [hF, Function.comp_apply, Pi.mul_apply, id_eq] using h2.mul_const ‖g y‖
    ·
      have hmeas : AEStronglyMeasurable (fun y => ∫ x in Φ₀, ‖F (x, y)‖ ∂(μ K)) ν :=
        hF_meas.norm.prod_swap.integral_prod_right'
      refine Integrable.mono' (hg_ν.norm.const_mul C) hmeas ?_
      refine (ae_restrict_mem (isClosed_tsupport g).measurableSet).mono fun y hy => ?_
      have hnn : 0 ≤ ∫ x in Φ₀, ‖F (x, y)‖ ∂(μ K) := integral_nonneg fun x => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      have hFy : ∀ x, ‖F (x, y)‖ = ‖u (x * y)‖ ^ 2 * ‖g y‖ := fun x => by
        simp only [hF, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u (x * y)‖ ^ 2 * ‖g y‖)]
      simp only [hFy, integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _)
  have hH_int : Integrable (fun x => ∫ y, F (x, y) ∂ν) ((μ K).restrict Φ₀) := hF_int.integral_prod_left

  set G₁ : ℝ := ∫ y, ‖g y‖ ∂ν with hG₁
  have hsq : ∀ x, ‖rightConv K u g x‖ ^ 2 ≤ G₁ * ∫ y, F (x, y) ∂ν := by
    intro x
    rw [hconv]
    refine norm_integral_mul_sq_le (fun y => u (x * y)) g
      (huc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable hg.aestronglyMeasurable hg_ν ?_
    have hcont : Continuous fun y => ‖u (x * y)‖ ^ 2 * ‖g y‖ :=
      ((huc.comp (continuous_const.mul continuous_id)).norm.pow 2).mul hg.norm
    exact (hcont.integrable_of_hasCompactSupport hgc.norm.mul_left).restrict
  have hsq_int : Integrable (fun x => ‖rightConv K u g x‖ ^ 2) ((μ K).restrict Φ₀) :=
    Integrable.mono' (hH_int.const_mul G₁) (hconv_meas.norm.pow 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hsq x)
  exact (memLp_two_iff_integrable_sq_norm hconv_meas).2 hsq_int

private theorem integrable_mul_of_memLp_two {ρ : Measure (AdelicGL2 (𝓞 K) K)} (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ) (ha₂ : MemLp a 2 ρ) (hb₂ : MemLp b 2 ρ) :
    Integrable (fun x => a x * b x) ρ ∧
      ∫ x, ‖a x * b x‖ ∂ρ ≤ ((∫ x, ‖a x‖ ^ 2 ∂ρ) + ∫ x, ‖b x‖ ^ 2 ∂ρ) / 2 := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha).1 ha₂
  have hb' := (memLp_two_iff_integrable_sq_norm hb).1 hb₂
  have hpt : ∀ x, ‖a x * b x‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hint : Integrable (fun x => a x * b x) ρ :=
    Integrable.mono' ((ha'.add hb').div_const 2) (ha.mul hb)
      (Filter.Eventually.of_forall fun x => hpt x)
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖a x * b x‖ ∂ρ ≤ ∫ x, (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 ∂ρ :=
        integral_mono hint.norm ((ha'.add hb').div_const 2) hpt
    _ = ((∫ x, ‖a x‖ ^ 2 ∂ρ) + ∫ x, ‖b x‖ ^ 2 ∂ρ) / 2 := by rw [integral_div, integral_add ha' hb']

private theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact (wt_bounds α β σ hα x hx).2

private theorem wt_inv (σ : ℝ) (y : AdelicGL2 (𝓞 K) K) :
    wt K σ y⁻¹ = ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) := by
  simp only [wt, map_inv, ideleNorm_inv', Real.inv_rpow (ideleNorm_pos _).le, Real.rpow_neg (ideleNorm_pos _).le,
    inv_inv]

private theorem swap_identity (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) (σ : ℝ)
    (A B : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K → ℂ)
    (hA : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => A p.2 p.1)
    (hB : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => B p.2 p.1)
    (g' : AdelicGL2 (𝓞 K) K → ℂ) (hg' : Continuous g') (hg'c : HasCompactSupport g')
    (hA₂ : ∀ y, MemLp (A y) 2 ((μ K).restrict Φ₀)) (hB₂ : ∀ y, MemLp (B y) 2 ((μ K).restrict Φ₀))
    (CA CB : ℝ) (hCA : ∀ y ∈ tsupport g', ∫ x in Φ₀, ‖A y x‖ ^ 2 ∂(μ K) ≤ CA)
    (hCB : ∀ y ∈ tsupport g', ∫ x in Φ₀, ‖B y x‖ ^ 2 ∂(μ K) ≤ CB) :
    ∫ x in Φ₀, (∫ y, A y x * conj (B y x) * g' y ∂(μ K)) * wt K σ x ∂(μ K) =
      ∫ y, g' y * ∫ x in Φ₀, A y x * conj (B y x) * wt K σ x ∂(μ K) ∂(μ K) := by
  have hsc : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hsig : SigmaFinite (μ K) := sigmaFinite_μ (K := K)
  have hμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set ν : Measure (AdelicGL2 (𝓞 K) K) := (μ K).restrict (tsupport g') with hν
  have hνfin : IsFiniteMeasure ν := ⟨by simpa [hν] using hg'c.measure_lt_top⟩
  set M : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hM
  have hwt := wt_ae_bound (K := K) α β σ hα Φ₀ hΦ₀
  have hwt_cont : Continuous (wt K σ) := wt_continuous σ

  have hAy : ∀ y, Continuous (A y) := fun y => hA.comp (Continuous.prodMk continuous_id continuous_const)
  have hBy : ∀ y, Continuous (B y) := fun y => hB.comp (Continuous.prodMk continuous_id continuous_const)
  have hconjB₂ : ∀ y, MemLp (fun x => conj (B y x)) 2 ((μ K).restrict Φ₀) := fun y => by
    have hm : AEStronglyMeasurable (fun x => conj (B y x)) ((μ K).restrict Φ₀) :=
      (Complex.continuous_conj.comp (hBy y)).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    simpa only [Complex.norm_conj] using (memLp_two_iff_integrable_sq_norm (hBy y).aestronglyMeasurable).1 (hB₂ y)

  set Kf : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K → ℂ := fun x y => A y x * conj (B y x) * g' y * wt K σ x with hKf
  have hKf_meas : AEStronglyMeasurable (Function.uncurry Kf) (((μ K).restrict Φ₀).prod ν) := by
    refine Continuous.aestronglyMeasurable ?_
    exact ((hA.mul (Complex.continuous_conj.comp hB)).mul (hg'.comp continuous_snd)).mul (hwt_cont.comp continuous_fst)

  have hslice : ∀ y, Integrable (fun x => Kf x y) ((μ K).restrict Φ₀) ∧
      ∫ x in Φ₀, ‖Kf x y‖ ∂(μ K) ≤ ‖g' y‖ * (M * (((∫ x in Φ₀, ‖A y x‖ ^ 2 ∂(μ K)) +
        ∫ x in Φ₀, ‖B y x‖ ^ 2 ∂(μ K)) / 2)) := by
    intro y
    obtain ⟨hAB_int, hAB_le⟩ := integrable_mul_of_memLp_two (A y) (fun x => conj (B y x))
      (hAy y).aestronglyMeasurable (Complex.continuous_conj.comp (hBy y)).aestronglyMeasurable (hA₂ y) (hconjB₂ y)
    simp only [Complex.norm_conj] at hAB_le
    have hABw : Integrable (fun x => wt K σ x * (A y x * conj (B y x))) ((μ K).restrict Φ₀) :=
      hAB_int.bdd_mul hwt_cont.aestronglyMeasurable hwt
    have hint : Integrable (fun x => Kf x y) ((μ K).restrict Φ₀) := by
      refine (hABw.mul_const (g' y)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hKf]
      ring
    refine ⟨hint, ?_⟩
    have hpt : ∀ᵐ x ∂((μ K).restrict Φ₀), ‖Kf x y‖ ≤ ‖g' y‖ * (M * ‖A y x * conj (B y x)‖) :=
      hwt.mono fun x hx => by
        simp only [hKf, norm_mul]
        have h0 : 0 ≤ ‖A y x‖ * ‖conj (B y x)‖ := by positivity
        calc ‖A y x‖ * ‖conj (B y x)‖ * ‖g' y‖ * ‖wt K σ x‖
            ≤ ‖A y x‖ * ‖conj (B y x)‖ * ‖g' y‖ * M := by gcongr
          _ = ‖g' y‖ * (M * (‖A y x‖ * ‖conj (B y x)‖)) := by ring
    have hM0 : 0 ≤ M := le_max_of_le_left (Real.rpow_pos_of_pos hα _).le
    calc ∫ x in Φ₀, ‖Kf x y‖ ∂(μ K)
        ≤ ∫ x in Φ₀, ‖g' y‖ * (M * ‖A y x * conj (B y x)‖) ∂(μ K) :=
          integral_mono_ae hint.norm ((hAB_int.norm.const_mul M).const_mul ‖g' y‖) hpt
      _ = ‖g' y‖ * (M * ∫ x in Φ₀, ‖A y x * conj (B y x)‖ ∂(μ K)) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ ‖g' y‖ * (M * (((∫ x in Φ₀, ‖A y x‖ ^ 2 ∂(μ K)) + ∫ x in Φ₀, ‖B y x‖ ^ 2 ∂(μ K)) / 2)) := by
          gcongr

  have hKf_int : Integrable (Function.uncurry Kf) (((μ K).restrict Φ₀).prod ν) := by
    refine (integrable_prod_iff' hKf_meas).2 ⟨Filter.Eventually.of_forall fun y => (hslice y).1, ?_⟩
    have hmeas : AEStronglyMeasurable (fun y => ∫ x in Φ₀, ‖Function.uncurry Kf (x, y)‖ ∂(μ K)) ν :=
      hKf_meas.norm.prod_swap.integral_prod_right'
    have hg'_ν : Integrable g' ν := (hg'.integrable_of_hasCompactSupport hg'c).restrict
    refine Integrable.mono' (hg'_ν.norm.mul_const (M * ((CA + CB) / 2))) hmeas ?_
    refine (ae_restrict_mem (isClosed_tsupport g').measurableSet).mono fun y hy => ?_
    have hnn : 0 ≤ ∫ x in Φ₀, ‖Function.uncurry Kf (x, y)‖ ∂(μ K) := integral_nonneg fun x => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    have hM0 : 0 ≤ M := le_max_of_le_left (Real.rpow_pos_of_pos hα _).le
    refine (hslice y).2.trans ?_
    gcongr
    · exact hCA y hy
    · exact hCB y hy

  have houter : ∀ x, (∫ y, A y x * conj (B y x) * g' y ∂(μ K)) = ∫ y, A y x * conj (B y x) * g' y ∂ν := by
    intro x
    rw [hν]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]).symm
  have houter' : (∫ y, g' y * ∫ x in Φ₀, A y x * conj (B y x) * wt K σ x ∂(μ K) ∂(μ K)) =
      ∫ y, g' y * ∫ x in Φ₀, A y x * conj (B y x) * wt K σ x ∂(μ K) ∂ν := by
    rw [hν]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]).symm
  calc ∫ x in Φ₀, (∫ y, A y x * conj (B y x) * g' y ∂(μ K)) * wt K σ x ∂(μ K)
      = ∫ x in Φ₀, ∫ y, Kf x y ∂ν ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [houter, hKf, ← integral_mul_const]
    _ = ∫ y, ∫ x in Φ₀, Kf x y ∂(μ K) ∂ν := integral_integral_swap hKf_int
    _ = ∫ y, g' y * ∫ x in Φ₀, A y x * conj (B y x) * wt K σ x ∂(μ K) ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hKf]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        ring
    _ = ∫ y, g' y * ∫ x in Φ₀, A y x * conj (B y x) * wt K σ x ∂(μ K) ∂(μ K) := houter'.symm

section Identity

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μ K).restrict (slab α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
  (u v : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v)
  (huc : Continuous u) (hvc : Continuous v)
  (hu₂ : MemLp u 2 ((μ K).restrict Φ₀)) (hv₂ : MemLp v 2 ((μ K).restrict Φ₀))
  (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)

include hα hΦ₀ hFD hσ hu hv huc hvc hu₂ hv₂ hg hgc

private theorem lhs_eq :
    ∫ x in Φ₀, rightConv K u g x * conj (v x) * wt K σ x ∂(μ K) =
      ∫ y, g y * (((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) * wt K σ x ∂(μ K)) ∂(μ K) := by
  obtain ⟨CA, hCA⟩ := exists_uniform_bound α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ _ hgc
  have hV := (memLp_two_iff_integrable_sq_norm hvc.aestronglyMeasurable).1 hv₂
  have hswap := swap_identity α β hα Φ₀ hΦ₀ σ (fun y x => u (x * y)) (fun _ x => v x)
    (huc.comp (continuous_fst.mul continuous_snd)) (hvc.comp continuous_fst) g hg hgc
    (fun y => memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ u hu huc hu₂ y) (fun _ => hv₂) CA
    (∫ x in Φ₀, ‖v x‖ ^ 2 ∂(μ K)) hCA (fun _ _ => le_rfl)
  calc ∫ x in Φ₀, rightConv K u g x * conj (v x) * wt K σ x ∂(μ K)
      = ∫ x in Φ₀, (∫ y, u (x * y) * conj (v x) * g y ∂(μ K)) * wt K σ x ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [conv_apply]
        rw [← integral_mul_const]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring
    _ = ∫ y, g y * ∫ x in Φ₀, u (x * y) * conj (v x) * wt K σ x ∂(μ K) ∂(μ K) := hswap
    _ = ∫ y, g y * (((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
          ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) * wt K σ x ∂(μ K)) ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        congr 1
        exact (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u v hu hv huc
          hvc hu₂ hv₂ y).2.2

omit hu in

private theorem rhs_eq :
    ∫ x in Φ₀, u x * conj (rightConv K v (fun y => conj (g y⁻¹) * wt K σ y) x) * wt K σ x ∂(μ K) =
      ∫ y, g y * (((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) * wt K σ x ∂(μ K)) ∂(μ K) := by

  set g' : AdelicGL2 (𝓞 K) K → ℂ :=
    fun y => g y * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) with hg'
  have hc_cont : Continuous fun y : AdelicGL2 (𝓞 K) K =>
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')
  have hg'c : HasCompactSupport g' := hgc.mul_right
  have hg'cont : Continuous g' := hg.mul hc_cont

  obtain ⟨CB, hCB⟩ := exists_uniform_bound α β hα Φ₀ hΦ₀ hFD ξ σ hσ v hv hvc hv₂ (tsupport g')⁻¹
    (hg'c : IsCompact (tsupport g')).inv
  have hswap := swap_identity α β hα Φ₀ hΦ₀ σ (fun _ x => u x) (fun y x => v (x * y⁻¹)) (huc.comp continuous_fst)
    (hvc.comp (continuous_fst.mul continuous_snd.inv)) g' hg'cont hg'c (fun _ => hu₂)
    (fun y => memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ v hv hvc hv₂ y⁻¹) (∫ x in Φ₀, ‖u x‖ ^ 2 ∂(μ K)) CB
    (fun _ _ => le_rfl) (fun y hy => hCB y⁻¹ (Set.inv_mem_inv.mpr hy))

  -- The change of variables `y ↦ y⁻¹` in the `conj`-of-convolution step needs the Haar measure of
  -- `GL₂(𝔸)` to be invariant under inversion. The pin has this as the `scoped instance`
  -- `instInvInvariantμ` (its lines 49–66); here it is a local fact, proved from the pin's own
  -- argument: `μ.inv` is left-invariant, hence a scalar multiple of the regular Haar measure `μ`,
  -- and applying inversion twice shows the scalar squares to `1`.
  have hII : (μ K).IsInvInvariant := by
    have hμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
    have hR : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K
    have hReg : (μ K).Regular := by
      show (adelicGLHaar (Fin 2) (𝓞 K) K).Regular
      unfold adelicGLHaar
      infer_instance
    constructor
    let c : ℝ≥0 := haarScalarFactor (μ K).inv (μ K)
    have hc : (μ K).inv = c • μ K := isMulLeftInvariant_eq_smul_of_regular (μ K).inv (μ K)
    have h2 : map Inv.inv (map Inv.inv (μ K)) = (c * c) • μ K := by
      rw [← inv_def (μ K), hc, Measure.map_smul c (measurable_inv.aemeasurable), ← inv_def (μ K), hc,
        smul_smul]
    have h2' : μ K = (c * c) • μ K := by
      rw [← h2, Measure.map_map measurable_inv measurable_inv]
      simp
    obtain ⟨K', hK, hKmem⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 K) K)
    have hKpos : 0 < μ K K' := Measure.measure_pos_of_mem_nhds (μ := μ K) hKmem
    have hKfin : μ K K' < ⊤ := hK.measure_lt_top
    have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K K' = 1 * μ K K' := by
      rw [one_mul]
      conv_rhs => rw [h2']
      rw [Measure.coe_nnreal_smul_apply]
    have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin.ne).mp h3
    have hcc : c * c = 1 := by exact_mod_cast h4
    have hc1 : c = 1 := by
      rcases lt_trichotomy c 1 with hlt | heq | hgt
      · have h := mul_self_lt_mul_self (zero_le : (0 : ℝ≥0) ≤ c) hlt
        rw [mul_one] at h
        exact absurd hcc h.ne
      · exact heq
      · have h := mul_self_lt_mul_self (zero_le : (0 : ℝ≥0) ≤ 1) hgt
        rw [mul_one] at h
        exact absurd hcc h.ne'
    rw [hc, hc1, one_smul]

  have hinner : ∀ x, conj (rightConv K v (fun y => conj (g y⁻¹) * wt K σ y) x) =
      ∫ y, conj (v (x * y⁻¹)) * g' y ∂(μ K) := by
    intro x
    rw [conv_apply, ← integral_inv_eq_self (fun y => v (x * y) * (conj (g y⁻¹) * wt K σ y)) (μ K),
      ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [inv_inv, wt_inv, hg', map_mul, Complex.conj_conj, Complex.conj_ofReal]

  calc ∫ x in Φ₀, u x * conj (rightConv K v (fun y => conj (g y⁻¹) * wt K σ y) x) * wt K σ x ∂(μ K)
      = ∫ x in Φ₀, (∫ y, u x * conj (v (x * y⁻¹)) * g' y ∂(μ K)) * wt K σ x ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hinner]
        rw [← integral_const_mul]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring
    _ = ∫ y, g' y * ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) * wt K σ x ∂(μ K) ∂(μ K) := hswap
    _ = ∫ y, g y * (((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
          ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) * wt K σ x ∂(μ K)) ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hg']
        ring

end Identity

end WeightedPairingAdjoint

end LocalIntertwining

open LocalIntertwining.WeightedPairingAdjoint NumberField.TateGlobal in
theorem adjoint_rightConv_weightedPairing_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hu : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp (AutomorphicForm.rightConv K u g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, AutomorphicForm.rightConv K u g x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  -- the frozen statement spells the window inline; the helpers take the pin's `slab` form
  have hΦ₀' : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :=
    hΦ₀
  have hFD' : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := hFD
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := exists_uniform_bound α β hα Φ₀ hΦ₀' hFD' ξ σ hσ u hu huc hu₂ _ hgc
    exact memLp_rightConv_of_forall Φ₀ u g huc hg hgc
      (fun y => memLp_translate α β hα Φ₀ hΦ₀' hFD' ξ σ hσ u hu huc hu₂ y) C hC
  · have hgc' := flat_hasCompactSupport σ g hgc
    obtain ⟨C, hC⟩ := exists_uniform_bound α β hα Φ₀ hΦ₀' hFD' ξ σ hσ v hv hvc hv₂ _ hgc'
    exact memLp_rightConv_of_forall Φ₀ v _ hvc
      (flat_continuous σ g hg) hgc'
      (fun y => memLp_translate α β hα Φ₀ hΦ₀' hFD' ξ σ hσ v hv hvc hv₂ y) C hC
  · exact (lhs_eq α β hα Φ₀ hΦ₀' hFD' ξ σ hσ u v hu hv huc hvc hu₂ hv₂ g hg hgc).trans
      (rhs_eq α β hα Φ₀ hΦ₀' hFD' ξ σ hσ u v hv huc hvc hu₂ hv₂ g hg hgc).symm

end AutomorphicForm
