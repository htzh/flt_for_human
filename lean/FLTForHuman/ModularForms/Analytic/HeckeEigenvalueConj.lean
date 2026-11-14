/-
  The Petersson product on cusp forms: positive definiteness, and the conjugacy of a nebentypus
  form's Hecke eigenvalue.

  * `CuspForm.peterssonOn_add_smul_conj`: additivity in the second argument, `ℂ`-homogeneity, and
    Hermitian symmetry `conj ⟪g, f⟫ = ⟪f, g⟫` of the coset-summed Petersson product `peterssonOn`.
  * `CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff`: `⟪f, f⟫` is real and nonnegative,
    and vanishes iff `f = 0` -- the definiteness, from the pointwise density `dens`, the
    fundamental domain `𝒟` and the analytic continuation on the upper half plane.
  * `CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus`: for `g ≠ 0` with nebentypus `ε` and a Hecke
    eigenvalue `λ` at `p ∤ M`, `conj λ = ε⁻¹(p) · λ`.  The proof is the Hermitian symmetry applied
    to `⟪T_p g, g⟫ = λ⟪g, g⟫`, with the adjointness `⟪T_p f, g⟫ = conj ε(p)⟪f, T_p g⟫` (ported) and
    the non-vanishing of `⟪g, g⟫` from the second row.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_peterssonOn_add_smul_conj.lean` (142 lines, 18 declarations),
  `S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.lean` (249 lines, 30 declarations)
  and `S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.lean` (269 lines, 22 declarations), with
  the statements from the wrappers of the same names.  The first two files share a twelve-declaration
  coset-integral prelude (`cosum`, `integrand_eq`, `petersson_add_right`, `petersson_bounded`, ...)
  verbatim; it is written **once**, in the first namespace, and the second reuses it.  The pin's label
  namespaces are rectified: `PetOnIP` -> `Polarization`, `PetOnIP2` -> `SelfPairing`.

  Assumes from earlier modules: `ModularForms/Analytic/Petersson.lean` (`peterssonOn`),
  `ModularForms/Analytic/PeterssonCoset.lean` (the coset integral layer and `dens`),
  `ModularForms/Analytic/PeterssonHeckeTheorems.lean` (the Hecke adjointness),
  `ModularForms/HeckePrelude.lean` and `ModularForms/HeckeQCoeff.lean` (the `T`-periodicity and the
  `q`-coefficient action of `heckeU`/`heckeDiagMatrix`).

  spec-pin: Theorems/Thm_CuspForm_peterssonOn_add_smul_conj.lean
  spec-pin: P2M/Sol/S_CuspForm_peterssonOn_add_smul_conj.lean
  spec-pin: Theorems/Thm_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.lean
  spec-pin: P2M/Sol/S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.lean
  spec-pin: Theorems/Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus.lean
-/
import FLTForHuman.ModularForms.Analytic.PeterssonCoset
import FLTForHuman.ModularForms.Analytic.PeterssonHeckeTheorems
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace SelfPairing

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

local notation "Γᴳᴸ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

scoped instance sl2zContinuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

scoped instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def cosum (Φ : ℍ → ℂ) (x : ℍ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Φ ((q.out⁻¹ : SL(2, ℤ)) • x)

theorem integrand_eq (F G : ℍ → ℂ) :
    CuspForm.peterssonOnIntegrand Γ k F G = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) := by
  funext x
  unfold CuspForm.peterssonOnIntegrand cosum
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_slash_SL k F G _ x

theorem petersson_add_right (F G H : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (G + H) x
      = UpperHalfPlane.petersson k F G x + UpperHalfPlane.petersson k F H x := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply]; ring

theorem petersson_smul_right (F G : ℍ → ℂ) (c : ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (c • G) x = c * UpperHalfPlane.petersson k F G x := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem cosum_add (Φ Ψ : ℍ → ℂ) : cosum (Γ := Γ) (Φ + Ψ) = cosum (Γ := Γ) Φ + cosum (Γ := Γ) Ψ := by
  funext x; simp [cosum, Finset.sum_add_distrib]

theorem cosum_const_mul (c : ℂ) (Φ : ℍ → ℂ) :
    cosum (Γ := Γ) (fun x => c * Φ x) = fun x => c * cosum (Γ := Γ) Φ x := by
  funext x; simp [cosum, Finset.mul_sum]

theorem measurable_smul_SL (γ : SL(2, ℤ)) : Measurable (fun x : ℍ => γ • x) := by
  exact (continuous_const_smul γ).measurable

theorem continuous_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) : Continuous (cosum (Γ := Γ) Φ) := by
  exact continuous_finsetSum _ fun _ _ => hΦ.comp (continuous_const_smul _)

theorem integrable_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) (hbd : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Integrable (cosum (Γ := Γ) Φ) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := hbd
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_cosum hΦ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hC _)

theorem petersson_bounded (f g : CuspForm Γᴳᴸ k) :
    ∃ C, ∀ x, ‖UpperHalfPlane.petersson k ⇑f ⇑g x‖ ≤ C := by
  exact CuspFormClass.petersson_bounded_left k Γᴳᴸ f g

omit [Γ.FiniteIndex] in
theorem petersson_continuous' (f g : CuspForm Γᴳᴸ k) : Continuous (UpperHalfPlane.petersson k ⇑f ⇑g) := by
  exact UpperHalfPlane.petersson_continuous k (CuspFormClass.holo f).continuous
    (CuspFormClass.holo g).continuous

theorem integrable_integrand (f g : CuspForm Γᴳᴸ k) :
    Integrable (CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g) (volume.restrict (𝒟 : Set ℍ)) := by
  rw [integrand_eq]
  exact integrable_cosum (petersson_continuous' f g) (petersson_bounded f g)

def dens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ‖f x‖ ^ 2 * x.im ^ k

omit [Γ.FiniteIndex] in
theorem dens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ dens f x := by
  exact mul_nonneg (sq_nonneg _) (zpow_nonneg x.im_pos.le _)

omit [Γ.FiniteIndex] in
theorem petersson_self_eq_dens (f : CuspForm Γᴳᴸ k) (x : ℍ) :
    UpperHalfPlane.petersson k ⇑f ⇑f x = ((dens f x : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson dens
  rw [Complex.conj_mul' (f x)]
  push_cast
  ring

omit [Γ.FiniteIndex] in
theorem continuous_dens (f : CuspForm Γᴳᴸ k) : Continuous (dens f) := by
  unfold dens
  refine ((continuous_norm.comp (CuspFormClass.holo f).continuous).pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun x => Or.inl (x.im_pos.ne'))

def rdens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ∑ q : SL(2, ℤ) ⧸ Γ, dens f ((q.out⁻¹ : SL(2, ℤ)) • x)

theorem rdens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ rdens f x := by
  exact Finset.sum_nonneg fun _ _ => dens_nonneg f _

theorem continuous_rdens (f : CuspForm Γᴳᴸ k) : Continuous (rdens f) := by
  exact continuous_finsetSum _ fun _ _ => (continuous_dens f).comp (continuous_const_smul _)

theorem integrand_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑f = fun x => ((rdens f x : ℝ) : ℂ) := by
  rw [integrand_eq]
  funext x
  simp only [cosum, rdens, petersson_self_eq_dens, Complex.ofReal_sum]

theorem integrable_rdens (f : CuspForm Γᴳᴸ k) : Integrable (rdens f) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := petersson_bounded f f
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_rdens f).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  have := hC ((q.out⁻¹ : SL(2, ℤ)) • x)
  rwa [petersson_self_eq_dens, Complex.norm_real] at this

theorem peterssonOn_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f f = ((∫ x in (𝒟 : Set ℍ), rdens f x : ℝ) : ℂ) := by
  rw [CuspForm.peterssonOn_def, integrand_self_eq, integral_complex_ofReal]

theorem peterssonOn_self_re_nonneg (f : CuspForm Γᴳᴸ k) : 0 ≤ (CuspForm.peterssonOn Γ k f f).re := by
  rw [peterssonOn_self_eq, Complex.ofReal_re]
  exact setIntegral_nonneg ModularGroup.isClosed_fd.measurableSet fun x _ => rdens_nonneg f x

theorem peterssonOn_self_im (f : CuspForm Γᴳᴸ k) : (CuspForm.peterssonOn Γ k f f).im = 0 := by
  rw [peterssonOn_self_eq, Complex.ofReal_im]

def w₀ : ℍ := ⟨2 * Complex.I, by simp⟩

theorem w₀_mem_fdo : w₀ ∈ 𝒟ᵒ := by
  refine ⟨?_, ?_⟩
  · show 1 < Complex.normSq (2 * Complex.I)
    simp [Complex.normSq_apply]; norm_num
  · show |(2 * Complex.I).re| < 1 / 2
    simp

theorem rdens_eq_zero_of_integral_eq_zero (f : CuspForm Γᴳᴸ k)
    (h : ∫ x in (𝒟 : Set ℍ), rdens f x = 0) {x : ℍ} (hx : x ∈ 𝒟ᵒ) : rdens f x = 0 := by
  have hae : ∀ᵐ y ∂(volume.restrict (𝒟 : Set ℍ)), rdens f y = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (rdens_nonneg f))
      (integrable_rdens f)).mp h
    filter_upwards [this] with y hy using hy
  by_contra hne
  have hpos : 0 < rdens f x := lt_of_le_of_ne (rdens_nonneg f x) (Ne.symm hne)
  set U : Set ℍ := 𝒟ᵒ ∩ {y | rdens f x / 2 < rdens f y} with hU
  have hUopen : IsOpen U :=
    ModularGroup.isOpen_fdo.inter (isOpen_lt continuous_const (continuous_rdens f))
  have hxU : x ∈ U := ⟨hx, by show rdens f x / 2 < rdens f x; linarith⟩
  have hUpos : 0 < volume U := FLT.HyperbolicMeasure.volume_pos_of_isOpen hUopen ⟨x, hxU⟩
  have hUfd : U ⊆ 𝒟 := fun y hy => ModularGroup.fdo_subset_fd hy.1
  have hzero : volume.restrict (𝒟 : Set ℍ) U = 0 := by
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae] with y hy hyU
    have : rdens f x / 2 < rdens f y := hyU.2
    rw [hy] at this
    linarith
  rw [Measure.restrict_apply hUopen.measurableSet, Set.inter_eq_self_of_subset_left hUfd] at hzero
  exact hUpos.ne' hzero

theorem eq_zero_of_peterssonOn_self_eq_zero (f : CuspForm Γᴳᴸ k) (h : CuspForm.peterssonOn Γ k f f = 0) :
    f = 0 := by
  have hint : ∫ x in (𝒟 : Set ℍ), rdens f x = 0 := by
    have := congrArg Complex.re h
    rwa [peterssonOn_self_eq, Complex.ofReal_re, Complex.zero_re] at this
  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk 1 with hq₀
  set σ : SL(2, ℤ) := q₀.out⁻¹ with hσ
  have hvan : ∀ x ∈ 𝒟ᵒ, f (σ • x) = 0 := by
    intro x hx
    have h0 := rdens_eq_zero_of_integral_eq_zero f hint hx
    have hterm : dens f (σ • x) = 0 := by
      have hle : dens f (σ • x) ≤ rdens f x := by
        rw [rdens]
        exact Finset.single_le_sum
          (f := fun q : SL(2, ℤ) ⧸ Γ => dens f ((q.out⁻¹ : SL(2, ℤ)) • x))
          (fun q _ => dens_nonneg f _) (Finset.mem_univ q₀)
      exact le_antisymm (h0 ▸ hle) (dens_nonneg f _)
    have : ‖f (σ • x)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with h1 | h1
      · exact h1
      · exact absurd h1 (zpow_ne_zero _ (σ • x).im_pos.ne')
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  set V : Set ℍ := (fun x : ℍ => σ • x) '' 𝒟ᵒ with hV
  have hVopen : IsOpen V := (Homeomorph.smul σ (α := ℍ)).isOpenMap _ ModularGroup.isOpen_fdo
  have hVne : (σ • w₀) ∈ V := ⟨w₀, w₀_mem_fdo, rfl⟩
  have hfV : ∀ y ∈ V, f y = 0 := by
    rintro _ ⟨x, hx, rfl⟩; exact hvan x hx
  set F : ℂ → ℂ := ⇑f ∘ ofComplex with hF
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} := hFdiff.analyticOnNhd hopen
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((σ • w₀ : ℍ) : ℂ) with hz₀
  have hz₀mem : z₀ ∈ {z : ℂ | 0 < z.im} := (σ • w₀).im_pos
  have hev : F =ᶠ[nhds z₀] 0 := by
    have hWopen : IsOpen (((↑) : ℍ → ℂ) '' V) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hVopen
    have hz₀W : z₀ ∈ ((↑) : ℍ → ℂ) '' V := ⟨σ • w₀, hVne, rfl⟩
    filter_upwards [hWopen.mem_nhds hz₀W] with z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply]
    exact hfV y hy
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀mem hev
  apply DFunLike.ext f 0
  intro y
  have := hzero y.im_pos
  simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
  simpa using this

theorem peterssonOn_self_eq_zero_iff (f : CuspForm Γᴳᴸ k) : CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0 := by
  constructor
  · exact eq_zero_of_peterssonOn_self_eq_zero f
  · rintro rfl
    rw [peterssonOn_self_eq]
    have : rdens (0 : CuspForm Γᴳᴸ k) = fun _ => 0 := by
      funext x; simp [rdens, dens]
    rw [this]
    simp

end SelfPairing

open scoped MatrixGroups

theorem CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (k : ℤ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    0 ≤ (CuspForm.peterssonOn Γ k f f).re ∧ (CuspForm.peterssonOn Γ k f f).im = 0 ∧
    (CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0) := by
  exact ⟨SelfPairing.peterssonOn_self_re_nonneg f, SelfPairing.peterssonOn_self_im f,
    SelfPairing.peterssonOn_self_eq_zero_iff f⟩

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace Polarization

open SelfPairing

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

local notation "Γᴳᴸ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

-- The two `scoped instance`s above are the pin's per-file prelude copy: the pin declares them in
-- both `S_` files, and the port writes them once (in `SelfPairing`), which `open SelfPairing` here
-- makes available.

-- DEVIATION AF63B: the scaffold's `omit [Γ.FiniteIndex] in` was dropped here.
-- Pin P2M/Sol/S_CuspForm_peterssonOn_add_smul_conj.lean:85 keeps the instance
-- (its `integrand_eq`/`integrable_integrand` need it). The declaration text
-- itself is untouched.
theorem peterssonOn_add_right (f g h : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, CuspForm.peterssonOn_def,
    ← integral_add (integrable_integrand f g) (integrable_integrand f h)]
  congr 1
  rw [integrand_eq, integrand_eq, integrand_eq]
  change _ = cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g)
    + cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑h)
  rw [← cosum_add]
  congr 1
  funext x
  exact petersson_add_right _ _ _ x

theorem peterssonOn_smul_right (c : ℂ) (f g : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, ← integral_const_mul]
  congr 1
  rw [integrand_eq, integrand_eq]
  change _ = fun x => c * cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g) x
  rw [← cosum_const_mul]
  congr 1
  funext x
  exact petersson_smul_right _ _ c x

theorem cosum_conj (F G : ℍ → ℂ) (x : ℍ) :
    conj (cosum (Γ := Γ) (UpperHalfPlane.petersson k G F) x)
      = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) x := by
  unfold cosum
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [UpperHalfPlane.petersson_symm k F G, Complex.conj_conj]

theorem integrand_conj (f g : CuspForm Γᴳᴸ k) (x : ℍ) :
    conj (CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f x) = CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g x := by
  rw [integrand_eq, integrand_eq]
  exact cosum_conj ⇑f ⇑g x

theorem peterssonOn_conj_symm (f g : CuspForm Γᴳᴸ k) :
    conj (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def]
  have h := integral_conj (μ := volume.restrict (𝒟 : Set ℍ)) (𝕜 := ℂ)
    (f := CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f)
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integrand_conj f g x)

end Polarization

open scoped MatrixGroups

theorem CuspForm.peterssonOn_add_smul_conj (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by
  exact ⟨Polarization.peterssonOn_add_right f g h, Polarization.peterssonOn_smul_right c f g,
    Polarization.peterssonOn_conj_symm f g⟩

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups ComplexConjugate

noncomputable section

namespace HeckeEigenvalueConj

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Phi

variable {M : ℕ} {k : ℤ} {p : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp

theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  exact pow_mem (T_mem_Gamma1 N) n

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  exact ModularForm.periodic_of_slash_T h

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_slash_heckeMatrix (hp : p ≠ 0) (j : ℕ) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeMatrix p j) := by
  exact hF.slash k (by simp [val_heckeMatrix hp])

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) := by
  exact hF.slash k (by simp [val_heckeDiagMatrix hp])

theorem isBoundedAtImInfty_heckeU (hp : p ≠ 0) {F : ℍ → ℂ} (hF : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact (Filter.zero_zeroAtFilter atImInfty).boundedAtFilter)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (isBoundedAtImInfty_slash_heckeMatrix hp j hF).add ih

theorem mdifferentiable_heckeU {F : ℍ → ℂ}
    (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p F) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hF.slash k _).add ih

theorem periodic_add_smul {F G : ℍ → ℂ} (hF : Periodic (F ∘ ofComplex) 1)
    (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((F + c • G) ∘ ofComplex) 1 := by
  intro w
  have h1 := hF w
  have h2 := hG w
  simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

def phi (k : ℤ) (p : ℕ) (c : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p F + c • (F ∣[k] heckeDiagMatrix p)

variable (F : CuspForm (Γ₁ℝ M) k)

theorem cusp_slash_T_pow (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F := by
  exact SlashInvariantFormClass.slash_action_eq F _
    (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 M n))

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 := by
  exact periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  have hc : IsCusp OnePoint.infty (Γ₁ℝ M) :=
    (Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos h1
  exact (OnePoint.isZeroAt_infty_iff.mp (F.zero_at_cusps' hc)).isBoundedAtImInfty

theorem phi_props (hp : p ≠ 0) (c : ℂ) :
    Periodic (phi k p c ⇑F ∘ ofComplex) 1 ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (phi k p c ⇑F) ∧
    IsBoundedAtImInfty (phi k p c ⇑F) ∧
    ∀ n : ℕ, qCoeff (phi k p c ⇑F) n =
      qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  set U : ℍ → ℂ := heckeU k p (⇑F) with hU
  set D : ℍ → ℂ := (⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  have hUper : Periodic (U ∘ ofComplex) 1 := ModularForm.periodic_heckeU_comp_ofComplex hFper k p
  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp (cusp_slash_T_pow F p)
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    mdifferentiable_heckeU (k := k) (p := p) hFhol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hFhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hp hFbdd
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp hFbdd
  have hφ : phi k p c ⇑F = U + c • D := rfl
  refine ⟨hφ ▸ periodic_add_smul hUper hDper c, hφ ▸ hUhol.add (hDhol.const_smul c),
    hφ ▸ hUbdd.add (hDbdd.smul c), fun n => ?_⟩
  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hancD : AnalyticAt ℂ (cuspFunction 1 (c • D)) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_smul hDper c) (hDhol.const_smul c) (hDbdd.smul c)
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  set G : ℍ → ℂ := fun τ => F (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _) (hDhol.const_smul _)
      (hDbdd.smul _)
  have hqD : qCoeff D n = (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑F) (n / p) else 0) := by
    rw [qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hFper hFhol hFbdd hp n
  have hqU : qCoeff U n = qCoeff (⇑F) (p * n) := by
    rw [hU, UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hp n, coeffHeckeU_apply, mul_comm]
  rw [hφ, qCoeff, qExpansion_add hanU hancD, qExpansion_smul hanD, map_add, map_smul, smul_eq_mul]
  have h1 := hqU
  have h2 := hqD
  simp only [qCoeff] at h1 h2 ⊢
  rw [h1, h2, mul_assoc]

theorem phi_eq_smul_of_qCoeff (hp : p ≠ 0) (c lam : ℂ)
    (hrel : ∀ n : ℕ, qCoeff (⇑F) (p * n) + c * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑F) (n / p) else 0) = lam * qCoeff (⇑F) n) :
    phi k p c ⇑F = lam • (⇑F : ℍ → ℂ) := by
  obtain ⟨hper, hhol, hbdd, hq⟩ := phi_props F hp c
  have hFper := cusp_periodic F
  have hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) := F.holo'
  have hFbdd := cusp_bdd F
  have hang := analyticAt_cuspFunction_zero one_pos hFper hFhol hFbdd
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq hper hhol hbdd (periodic_smul hFper lam)
    (hFhol.const_smul lam) (hFbdd.smul lam) (fun n => ?_)
  rw [hq n, hrel n, qCoeff, qCoeff, qExpansion_smul hang, map_smul, smul_eq_mul]

end Phi

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

local notation "⟪" f ", " g "⟫" => CuspForm.peterssonOn (Gamma1 M) k f g

omit [NeZero M] in
theorem conj_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (a : ZMod M) : conj (ε a) = ε⁻¹ a := by
  have := MulChar.star_apply' ε a
  rwa [RCLike.star_def] at this

theorem petersson_smul_left (f g : CuspForm (Γ₁ℝ M) k) (c : ℂ) :
    ⟪c • ⇑f, ⇑g⟫ = conj c * ⟪⇑f, ⇑g⟫ := by
  obtain ⟨-, h2, -⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k g f f c
  obtain ⟨-, -, h3⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k f g f c
  obtain ⟨-, -, h3'⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k (c • f) g f c
  have h3'' : conj ⟪⇑g, c • ⇑f⟫ = ⟪c • ⇑f, ⇑g⟫ := h3'
  rw [← h3'', h2, map_mul, h3]

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, qCoeff (⇑g) (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑g) (n / p) else 0) =
      lam * qCoeff (⇑g) n) :
    conj lam = ε⁻¹ (p : ZMod M) * lam := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hT : heckeU k p ⇑g + ε (p : ZMod M) • (⇑g ∣[k] heckeDiagMatrix p) = lam • (⇑g : ℍ → ℂ) :=
    phi_eq_smul_of_qCoeff g hp0 (ε (p : ZMod M)) lam heig
  have hadj := CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus M k ε hp hpM g g hg hg
  rw [hT] at hadj
  obtain ⟨-, hlin, -⟩ := CuspForm.peterssonOn_add_smul_conj (Gamma1 M) k g g g lam
  obtain ⟨-, -, hpos⟩ := CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Gamma1 M) k g
  have hne : ⟪⇑g, ⇑g⟫ ≠ 0 := fun h0 => hg0 (hpos.1 h0)
  rw [petersson_smul_left, hlin, conj_dirichlet] at hadj
  have := mul_right_cancel₀ hne (hadj.trans (mul_assoc _ _ _).symm)
  exact this

end Main

end HeckeEigenvalueConj

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (lam : ℂ)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      lam * ModularFormClass.qCoeff g n) :
    starRingEnd ℂ lam = ε⁻¹ (p : ZMod M) * lam := by
  exact HeckeEigenvalueConj.main ε g hg0 hg p hp hpM lam heig

end
