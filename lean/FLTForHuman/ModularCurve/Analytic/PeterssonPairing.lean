/-
  The Petersson pairing is perfect.

  Ported from the two pinned engines
  `P2M/Sol/S_ModularCurve_exists_cuspForm_petersson_eq_gammaH.lean:1–232` and
  `P2M/Sol/S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.lean:1–226`
  (pinned `aa2d8b3`), whose shared Riesz-representation prelude is written **once**
  here, `private`, before either headline. The pin repeats that prelude
  byte-identically in the two `S_` files except for the fundamental-set group:

  * in the `gammaH` engine the set is
    `gammaFundamentalSet (Γ ⊔ Subgroup.zpowers (-1))` while the forms live on `Γ`;
  * in the general engine the set is `gammaFundamentalSet Γ`.

  The prelude therefore carries the fundamental-set group `Λ` as a separate
  explicit parameter (`FS Λ = gammaFundamentalSet Λ`) beside the form group `Γ`;
  each headline instantiates the pair. No mathematics changed: `Λ = Γ` for the
  general headline, `Γ = Γ_H`, `Λ = Γ_H ⊔ ⟨-1⟩` for the `gammaH` one.

  The Riesz step is: `petersson` gives a positive-definite Hermitian form `B` on
  `CuspForm Γ 2`; `B f f = ∫ ‖f‖² im²` over the fundamental set, so `B` is
  nondegenerate (`eq_zero_of_B_self_eq_zero`), its Gram matrix is injective
  (`gram_injective`), hence surjective, and every functional is
  `g ↦ I * B f g` for a unique `f`.

  Proof bodies are adapted to mathlib `v4.34.0` (the pin's `CuspForm.coe_add` /
  `coe_zero` / `coe_smul` are deprecated aliases of `FunLike.coe_add` /
  `FunLike.coe_zero` / `FunLike.coe_smul`; `petersson_bounded_left` and
  `finiteDimensional_of_isArithmetic` now carry arithmeticity/determinant
  hypotheses that are instances for finite-index subgroups). The two public
  headlines are the pin's statements verbatim.
-/
import FLTForHuman.AutomorphicForm.Gamma0FundamentalSet
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.WeightOne.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal. Two section
-- instances (`Γ.FiniteIndex`, `Λ.FiniteIndex`) are carried by the shared prelude
-- but not used by every one of its lemmas.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate Manifold Topology Pointwise

namespace ModularCurve

/-- The weight-two cusp forms on `Γ`; the pin's `S2` abbreviation. -/
private abbrev S2 (Γ : Subgroup SL(2, ℤ)) : Type := CuspForm Γ 2

/-- The fundamental set the pairing integrates over; the pin's `FS` abbreviation,
with the fundamental-set group `Λ` explicit so the two engines share one prelude. -/
private abbrev FS (Λ : Subgroup SL(2, ℤ)) : Set ℍ :=
  FLT.Gamma0FundamentalSet.gammaFundamentalSet Λ

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

private theorem petersson_add_left_apply (k : ℤ) (f f' g : ℍ → ℂ) (τ : ℍ) :
    petersson k (f + f') g τ = petersson k f g τ + petersson k f' g τ := by
  simp only [petersson, Pi.add_apply, map_add]
  ring

private theorem petersson_add_right_apply (k : ℤ) (f g g' : ℍ → ℂ) (τ : ℍ) :
    petersson k f (g + g') τ = petersson k f g τ + petersson k f g' τ := by
  simp only [petersson, Pi.add_apply]
  ring

private theorem petersson_smul_left_apply (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) (τ : ℍ) :
    petersson k (c • f) g τ = conj c * petersson k f g τ := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem petersson_smul_right_apply (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) (τ : ℍ) :
    petersson k f (c • g) τ = c * petersson k f g τ := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul]
  ring

private theorem petersson_two_self_apply (f : ℍ → ℂ) (τ : ℍ) :
    petersson 2 f f τ = ((‖f τ‖ ^ 2 * τ.im ^ 2 : ℝ) : ℂ) := by
  simp only [petersson, Complex.conj_mul', zpow_ofNat]
  push_cast
  ring

variable (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex]

private theorem integrable_petersson (f g : S2 Γ) :
    Integrable (petersson 2 f g) (volume.restrict (FS Λ)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left 2
    ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) f g
  have hcont : Continuous (petersson 2 f g) :=
    petersson_continuous 2 (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous
  haveI : IsFiniteMeasure (volume.restrict (FS Λ)) :=
    isFiniteMeasure_restrict.mpr
      (FLT.Gamma0FundamentalSet.volume_gammaFundamentalSet_lt_top Λ).ne
  exact Integrable.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)

private noncomputable def B (f g : S2 Γ) : ℂ := ∫ τ in FS Λ, petersson 2 f g τ

private theorem B_add_left (f f' g : S2 Γ) : B Λ (f + f') g = B Λ f g + B Λ f' g := by
  unfold B
  rw [← integral_add (integrable_petersson Λ f g) (integrable_petersson Λ f' g)]
  congr 1
  funext τ
  rw [FunLike.coe_add, petersson_add_left_apply]

private theorem B_add_right (f g g' : S2 Γ) : B Λ f (g + g') = B Λ f g + B Λ f g' := by
  unfold B
  rw [← integral_add (integrable_petersson Λ f g) (integrable_petersson Λ f g')]
  congr 1
  funext τ
  rw [FunLike.coe_add, petersson_add_right_apply]

private theorem B_smul_left (c : ℂ) (f g : S2 Γ) : B Λ (c • f) g = conj c * B Λ f g := by
  unfold B
  rw [← integral_const_mul]
  congr 1
  funext τ
  rw [FunLike.coe_smul, petersson_smul_left_apply]

private theorem B_smul_right (c : ℂ) (f g : S2 Γ) : B Λ f (c • g) = c * B Λ f g := by
  unfold B
  rw [← integral_const_mul]
  congr 1
  funext τ
  rw [FunLike.coe_smul, petersson_smul_right_apply]

private theorem B_self_eq (f : S2 Γ) :
    B Λ f f = ((∫ τ in FS Λ, ‖f τ‖ ^ 2 * τ.im ^ 2 : ℝ) : ℂ) := by
  unfold B
  rw [← integral_complex_ofReal]
  congr 1
  funext τ
  exact petersson_two_self_apply f τ

private theorem eq_zero_of_B_self_eq_zero (f : S2 Γ) (h : B Λ f f = 0) : f = 0 := by

  set φ : ℍ → ℝ := fun τ => ‖f τ‖ ^ 2 * τ.im ^ 2 with hφ_def
  have hφ_nonneg : 0 ≤ φ := fun τ => by positivity
  have hfcont : Continuous (⇑f : ℍ → ℂ) := (CuspFormClass.holo f).continuous
  have hφ_cont : Continuous φ := by
    simp only [hφ_def]
    fun_prop
  have hφ_int : Integrable φ (volume.restrict (FS Λ)) := by
    refine (integrable_petersson Λ f f).norm.congr (ae_of_all _ fun τ => ?_)
    simp only [hφ_def]
    rw [petersson_two_self_apply, Complex.norm_of_nonneg (by positivity)]

  have hint0 : ∫ τ in FS Λ, φ τ = 0 := by
    have h' := B_self_eq Λ f
    rw [h] at h'
    exact_mod_cast h'.symm
  have hae : φ =ᵐ[volume.restrict (FS Λ)] 0 :=
    (integral_eq_zero_iff_of_nonneg hφ_nonneg hφ_int).mp hint0

  set q₀ : SL(2, ℤ) ⧸ Λ :=
    QuotientGroup.mk (s := Λ) 1 with hq₀
  set U : Set ℍ := (Quotient.out q₀)⁻¹ • 𝒟ᵒ with hU_def
  have hU_sub : U ⊆ FS Λ :=
    Set.subset_iUnion_of_subset q₀ (Set.smul_set_mono ModularGroup.fdo_subset_fd)
  have hU_open : IsOpen U := ModularGroup.isOpen_fdo.smul _
  have hφU : Set.EqOn φ 0 U :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hU_sub hae) hU_open
      hφ_cont.continuousOn continuousOn_const
  have hfU : ∀ τ ∈ U, f τ = 0 := by
    intro τ hτ
    have h0 : ‖f τ‖ ^ 2 * τ.im ^ 2 = 0 := hφU hτ
    rcases mul_eq_zero.mp h0 with h1 | h1
    · simpa using h1
    · exact absurd h1 (pow_ne_zero 2 τ.im_pos.ne')

  set z₀ : ℍ := ⟨2 * Complex.I, by simp⟩ with hz₀_def
  have hz₀ : z₀ ∈ 𝒟ᵒ := by
    refine ⟨?_, ?_⟩
    · simp only [hz₀_def, Complex.normSq]
      norm_num
    · simp [hz₀_def]
  have hτ₀ : (Quotient.out q₀)⁻¹ • z₀ ∈ U := Set.smul_mem_smul_set hz₀

  have hev : ∀ᶠ z in 𝓝 ((Quotient.out q₀)⁻¹ • z₀), f z = 0 :=
    Filter.eventually_of_mem (hU_open.mem_nhds hτ₀) hfU
  have hzero : (⇑f : ℍ → ℂ) = 0 :=
    UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
      (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact DFunLike.coe_injective (hzero.trans FunLike.coe_zero.symm)

private noncomputable def Bform : S2 Γ →ₗ⋆[ℂ] S2 Γ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun f g => B Λ f g)
    (fun f f' g => B_add_left Λ f f' g)
    (fun c f g => by simpa only [smul_eq_mul] using B_smul_left Λ c f g)
    (fun f g g' => B_add_right Λ f g g')
    (fun c f g => by simpa only [smul_eq_mul, RingHom.id_apply] using B_smul_right Λ c f g)

@[simp] private theorem Bform_apply (f g : S2 Γ) : Bform Λ f g = B Λ f g := rfl

private theorem B_sum_conj_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → S2 Γ)
    (g : S2 Γ) : B Λ (∑ j ∈ s, conj (c j) • v j) g = ∑ j ∈ s, c j * B Λ (v j) g := by
  rw [← Bform_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smulₛₗ, Complex.conj_conj, LinearMap.smul_apply, Bform_apply, smul_eq_mul]

private theorem B_sum_smul_right {ι : Type*} (s : Finset ι) (f : S2 Γ) (a : ι → ℂ) (v : ι → S2 Γ) :
    B Λ f (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i * B Λ f (v i) := by
  rw [← Bform_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, Bform_apply, smul_eq_mul]

private noncomputable def gram {ι : Type*} [Fintype ι] (v : ι → S2 Γ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun c i := ∑ j, c j * B Λ (v j) (v i)
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

private theorem gram_apply {ι : Type*} [Fintype ι] (v : ι → S2 Γ) (c : ι → ℂ) (i : ι) :
    gram Λ v c i = ∑ j, c j * B Λ (v j) (v i) := rfl

private theorem B_conjComb_eq_gram {ι : Type*} [Fintype ι] (v : ι → S2 Γ) (c : ι → ℂ) (i : ι) :
    B Λ (∑ j, conj (c j) • v j) (v i) = gram Λ v c i := by
  rw [gram_apply, B_sum_conj_smul_left]

private theorem gram_injective {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (S2 Γ)) :
    Function.Injective (gram Λ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  set f : S2 Γ := ∑ j, conj (c j) • b j with hf_def
  have hBb : ∀ i, B Λ f (b i) = 0 := fun i => by
    rw [hf_def, B_conjComb_eq_gram, hc, Pi.zero_apply]
  have hBg : ∀ g, B Λ f g = 0 := fun g => by
    rw [← b.sum_repr g, B_sum_smul_right]
    exact Finset.sum_eq_zero fun i _ => by rw [hBb i, mul_zero]
  have hf0 : f = 0 := eq_zero_of_B_self_eq_zero Λ f (hBg f)
  have hc0 : ∀ j, conj (c j) = 0 :=
    Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => conj (c j)) hf0
  funext j
  simpa using congrArg conj (hc0 j)

private theorem main (ℓ : Module.Dual ℂ (S2 Γ)) :
    ∃ f : S2 Γ, ∀ g : S2 Γ, Complex.I * B Λ f g = ℓ g := by
  haveI : FiniteDimensional ℂ (S2 Γ) :=
    CuspForm.finiteDimensional_of_isArithmetic
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2
  let b := Module.finBasis ℂ (S2 Γ)
  have hTs : Function.Surjective (gram Λ b) :=
    LinearMap.injective_iff_surjective.mp (gram_injective Λ b)
  obtain ⟨c, hc⟩ := hTs (fun i => -Complex.I * ℓ (b i))
  refine ⟨∑ j, conj (c j) • b j, fun g => ?_⟩

  have hfun : Complex.I • Bform Λ (∑ j, conj (c j) • b j) = ℓ := by
    refine b.ext fun i => ?_
    rw [LinearMap.smul_apply, Bform_apply, B_conjComb_eq_gram, hc, smul_eq_mul, ← mul_assoc,
      mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have := LinearMap.congr_fun hfun g
  rwa [LinearMap.smul_apply, Bform_apply, smul_eq_mul] at this

theorem exists_cuspForm_petersson_eq_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (ℓ : Module.Dual ℂ (CuspForm Γ 2)) :
    ∃ f : CuspForm Γ 2,
      ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = ℓ g :=
  main Γ ℓ

theorem exists_cuspForm_petersson_eq_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) 2,
      ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = ℓ g := by
  haveI : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
    Subgroup.finiteIndex_of_le
      (K := CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left
  exact main (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ℓ

end ModularCurve
