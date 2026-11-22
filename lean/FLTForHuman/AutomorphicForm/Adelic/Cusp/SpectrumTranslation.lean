/-
  Right translation on the cuspidal-spectrum carrier.

  `Carrier F Φ₀ σ` is the `L²` space of the slab `Φ₀` at the determinant-norm weight `σ`, and its
  subspace `cuspMemberSubmodule F Φ₀ ξ` collects the `ξ`-eigen functions that are cuspidal.

  * `exists_isLift_rightTranslate`: for a character `ξ` of modulus `σ` and every `y : GL₂(𝔸)`, the
    right translations `rightTranslate y` and `rightTranslate y⁻¹` lift to bounded operators `T`,
    `T'` on `Carrier F Φ₀ σ` (`IsLift`), and the two are adjoint up to the character factor:
    `T* = |det y|^σ • T'`, with `‖T‖ ≤ |det y|^(σ/2)`.
  * `exists_isCuspLift_rightTranslate_and_norm_le` is the same statement on the cuspidal
    subcarrier `cuspSubcarrier F hΦ₀ σ ξ`: a bounded `S` with `IsCuspLift … (rightTranslate y) S`
    and the same norm bound.
  * `rightTranslate_mem_cuspMemberSubmodule`: right translation maps the cusp-member submodule
    into itself — `φ ∈ cuspMemberSubmodule F Φ₀ ξ → rightTranslate y φ ∈ cuspMemberSubmodule F Φ₀ ξ`.
  * `exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt`: the carrier map `φ ↦ toCarrier φ` is
    continuous under right translation — for every `x` in the continuous member submodule and every
    `ε > 0` there is a neighbourhood `V` of `1` with `‖toCarrier (rightTranslate y x) - toCarrier x‖ < ε`
    for all `y ∈ V`. Its four engines are `lintegral_enorm_rpow_two_eq` (the `L²` norm of
    `toCarrier φ` as a `lintegral` of `‖φ‖ₑ ^ 2`), `lintegral_enorm_sub_rpow_two_eq` (the same for a
    difference), `enorm_sub_rpow_two_le` (the `2`-power triangle) and `continuous_enorm_rpow_two`.

  Transcribed from the pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt.lean`
    (174 lines, `Ws48RoadP` label dropped; its 4 public engines + the row = the 5 rows of the wire)

  and their three wrappers. The pin's namespace `CuspidalSpectrum` is the subject name and is kept.

  Deltas of the fifth pin, both proof-side except one import:

  * One import is added: `FLTForHuman.MeasureTheory.ParametricIntegral`, for
    `tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` (pin `:122`), which is in the port but
    was **not** in this module's import closure.
  * v4.34 spelling in `lintegral_enorm_rpow_two_eq`: `eLpNorm_eq_lintegral_rpow_enorm_toReal` takes the
    `AEStronglyMeasurable` proof **explicitly** at v4.34 (it was an auto-bound implicit in the pin's
    v4.33), so the rewrite passes `hm.aestronglyMeasurable` (pin `:40`).
  * `haveI` → `have` at the `SecondCountableTopology` binder (pin `:78`), the linter's own suggestion
    (FR-0223).

  Heartbeat probe (gate 7, a measurement — the module carries **no** `set_option maxHeartbeats`):
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop cap 200000 and at
  **N = 65000**, and fails at **N = 62000** (1 error: the landed `exists_isLift_rightTranslate`'s
  `whnf`) and at 61000 (4: that header, one `isDefEq` inside its proof, and the two `unknown constant`
  consequences), at 40000 (4, now also a step of `rightTranslate_mem_cuspMemberSubmodule`), at 12000 /
  8000 / 6000 (4 / 7 / 8: the two landed rows, steps inside them and the new headline's proof). The
  four new engines never appear among the failures down to N = 6000 — the module's floor belongs to
  the landed `exists_isLift_rightTranslate`, not to this pin.

  **Wiring.** `spec/check_port.py` owns the eight public declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumPairing
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumSubrep
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateAdjoint
import FLTForHuman.MeasureTheory.ParametricIntegral
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open Filter Topology
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

theorem exists_isLift_rightTranslate
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ,
      IsLift F hΦ₀ σ ξ (rightTranslate F y) T ∧
      IsLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) • T' ∧
      ‖T‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) := by
  classical
  have hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hw_cont : Continuous fun x : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hrpow : ∀ p : ℝ, Continuous fun x : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ p :=
    fun p => hw_cont.rpow_const fun x => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hcpos : ∀ w : AdelicGL2 (𝓞 F) F,
      0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) :=
    fun w => NumberField.TateGlobal.ideleNorm_pos _

  have hmaps : ∀ (w : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ),
      φ ∈ contMemberSubmodule F Φ₀ ξ → rightTranslate F w φ ∈ contMemberSubmodule F Φ₀ ξ := by
    intro w φ hφ
    obtain ⟨hlx, h2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
    have hT := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos
      Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ hlx hlx hφ.2 hφ.2 h2 h2 w
    refine ⟨(mem_memberSubmodule_iff' F Φ₀ ξ _).mpr ⟨⟨fun γ x => ?_, fun z x => ?_⟩, hT.1⟩,
      hφ.2.comp (continuous_id.mul continuous_const)⟩
    · show φ (globalPoints (𝓞 F) F γ * x * w) = φ (x * w)
      rw [mul_assoc]; exact hlx.left_invariant γ (x * w)
    · show φ (centralScalar (𝓞 F) F ((z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F)ˣ) * x * w) =
        ((ξ z : ℂˣ) : ℂ) * φ (x * w)
      rw [mul_assoc]; exact hlx.central_transform z (x * w)

  let Nc : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := contMemberSubmodule F Φ₀ ξ
  let ι : ↥Nc →ₗ[ℂ] ↥(memberSubmodule F Φ₀ ξ) := Submodule.inclusion (fun _ h => h.1)
  let L0 : ↥Nc →ₗ[ℂ] Carrier F Φ₀ σ := (toCarrier F hΦ₀ σ ξ).comp ι
  have hL0 : ∀ ψ : ↥Nc,
      L0 ψ = toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩ := fun ψ => rfl
  obtain ⟨Mbar, hMbar⟩ :
      ∃ Mbar : Submodule ℂ (Carrier F Φ₀ σ), (LinearMap.range L0).topologicalClosure = Mbar := ⟨_, rfl⟩
  have hMbar_closed : IsClosed (Mbar : Set (Carrier F Φ₀ σ)) := by
    rw [← hMbar]; exact Submodule.isClosed_topologicalClosure _
  have hMbar_complete : CompleteSpace ↥Mbar := hMbar_closed.completeSpace_coe
  have hL0mem : ∀ ψ : ↥Nc, L0 ψ ∈ Mbar := fun ψ => by
    rw [← hMbar]; exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self L0 ψ)
  let e : ↥Nc →ₗ[ℂ] ↥Mbar := L0.codRestrict Mbar hL0mem
  have he_coe : ∀ ψ : ↥Nc, ((e ψ : ↥Mbar) : Carrier F Φ₀ σ) = L0 ψ := fun ψ => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((LinearMap.range L0 : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe, hMbar]; exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, rfl⟩
    exact ⟨e ψ, ⟨ψ, rfl⟩, rfl⟩
  let P : Carrier F Φ₀ σ →L[ℂ] ↥Mbar := Mbar.orthogonalProjectionOnto

  have hw_nonneg : ∀ x : AdelicGL2 (𝓞 F) F,
      0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
    fun x => Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  have inner_toCarrier : ∀ (a b : AdelicGL2 (𝓞 F) F → ℂ) (ha : a ∈ memberSubmodule F Φ₀ ξ)
      (hb : b ∈ memberSubmodule F Φ₀ ξ),
      ⟪toCarrier F hΦ₀ σ ξ ⟨a, ha⟩, toCarrier F hΦ₀ σ ξ ⟨b, hb⟩⟫_ℂ =
        ∫ x in Φ₀, b x * conj (a x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro a b ha hb
    rw [MeasureTheory.L2.inner_def]
    have hae_a : (toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] a :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ ha)
    have hae_b : (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] b :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hb)
    have h1 : ∫ x, ⟪(toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) x,
          (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) x⟫_ℂ
          ∂(weightedMeasure F Φ₀ σ) = ∫ x, b x * conj (a x) ∂(weightedMeasure F Φ₀ σ) := by
      apply integral_congr_ae
      filter_upwards [hae_a, hae_b] with x hxa hxb
      rw [hxa, hxb, RCLike.inner_apply]
    rw [h1]
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul]
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (ENNReal.ofReal (weight F σ x)).toReal • (b x * conj (a x)) = b x * conj (a x) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
      rw [weight_def, ENNReal.toReal_ofReal (hw_nonneg x), Complex.real_smul]
      ring
    · exact ((hrpow (-σ)).measurable).ennreal_ofReal
    · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

  have hpair : ∀ (w : AdelicGL2 (𝓞 F) F) (ψ θ : ↥Nc),
      ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩,
          toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w θ, (hmaps w θ θ.2).1⟩⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ : ℝ) : ℂ) *
          ⟪toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w⁻¹ ψ, (hmaps w⁻¹ ψ ψ.2).1⟩,
            toCarrier F hΦ₀ σ ξ ⟨(θ : AdelicGL2 (𝓞 F) F → ℂ), θ.2.1⟩⟫_ℂ := by
    intro w ψ θ
    obtain ⟨hψlx, hψ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ (ψ : AdelicGL2 (𝓞 F) F → ℂ)).mp ψ.2.1
    obtain ⟨hθlx, hθ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ (θ : AdelicGL2 (𝓞 F) F → ℂ)).mp θ.2.1
    have hT := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos
      Φ₀ hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ (θ : AdelicGL2 (𝓞 F) F → ℂ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ) hθlx hψlx θ.2.2 ψ.2.2 hθ2 hψ2 w
    rw [inner_toCarrier, inner_toCarrier]
    exact hT.2.2
  have hnormsq : ∀ (w : AdelicGL2 (𝓞 F) F) (ψ : ↥Nc),
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩‖ ^ 2 =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ *
          ‖toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩‖ ^ 2 := by
    intro w ψ
    have h := hpair w ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ ψ
    have hback : rightTranslate F w⁻¹ (rightTranslate F w (ψ : AdelicGL2 (𝓞 F) F → ℂ)) = ψ := by
      funext x
      simp only [rightTranslate_apply]
      group
    have h' : ⟪toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩,
        toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ : ℝ) : ℂ) *
          ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩,
            toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩⟫_ℂ := by
      rw [h]
      have hsub : (⟨rightTranslate F w⁻¹ (rightTranslate F w (ψ : AdelicGL2 (𝓞 F) F → ℂ)),
          (hmaps w⁻¹ _ (hmaps w ψ ψ.2)).1⟩ : ↥(memberSubmodule F Φ₀ ξ)) =
          ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩ :=
        Subtype.ext hback
      rw [hsub]
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h', RCLike.re_to_complex,
      RCLike.re_to_complex, Complex.re_ofReal_mul]

  have build : ∀ w : AdelicGL2 (𝓞 F) F,
      ∃ (Sw : ↥Mbar →L[ℂ] Carrier F Φ₀ σ),
        (∀ v, Sw v ∈ Mbar) ∧
        (∀ ψ : ↥Nc, Sw (e ψ) = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩) ∧
        (∀ v, ‖Sw v‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖v‖) ∧
        IsLift F hΦ₀ σ ξ (rightTranslate F w) (Sw.comp P) := by
    intro w
    let fw : ↥Nc →ₗ[ℂ] Carrier F Φ₀ σ :=
      { toFun := fun ψ => L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩
        map_add' := fun ψ θ => by
          rw [← map_add]; congr 1
        map_smul' := fun c ψ => by
          rw [RingHom.id_apply, ← map_smul]; congr 1 }
    have hfw : ∀ ψ : ↥Nc, fw ψ = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ := fun ψ => rfl
    have hbound : ∀ ψ : ↥Nc,
        ‖fw ψ‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) *
          ‖e ψ‖ := by
      intro ψ
      rw [hfw, hL0]
      have hsq := hnormsq w ψ
      have h0 : 0 ≤ ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩‖ := norm_nonneg _
      have h1 : 0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) *
          ‖e ψ‖ := mul_nonneg (Real.rpow_nonneg (hcpos w).le _) (norm_nonneg _)
      refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).mp (le_of_eq ?_)
      have hc2 : (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2)) ^ (2 : ℕ) =
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hcpos w).le]
        norm_num
      rw [hsq, mul_pow, hc2]
      rfl
    let Sw : ↥Mbar →L[ℂ] Carrier F Φ₀ σ := fw.extendOfNorm e
    have hSw_e : ∀ ψ : ↥Nc, Sw (e ψ) = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ := fun ψ =>
      LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ ψ
    have hSw_norm : ∀ v,
        ‖Sw v‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖v‖ :=
      fun v => LinearMap.norm_extendOfNorm_apply_le hdense _ hbound v
    have hSw_mem : ∀ v, Sw v ∈ Mbar := by
      intro v
      refine hdense.induction_on v (p := fun v => Sw v ∈ Mbar) ?_ ?_
      · exact hMbar_closed.preimage Sw.continuous
      · intro ψ
        rw [hSw_e]
        exact hL0mem _
    refine ⟨Sw, hSw_mem, hSw_e, hSw_norm, ⟨hmaps w, ?_⟩⟩
    intro φ hφ
    have hPe : P (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩) = e ⟨φ, hφ⟩ := by
      have hcoe : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = ((e ⟨φ, hφ⟩ : ↥Mbar) : Carrier F Φ₀ σ) := rfl
      rw [hcoe]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [ContinuousLinearMap.comp_apply, hPe, hSw_e]
    rfl

  obtain ⟨Sy, hSy_mem, hSy_e, hSy_norm, hlift⟩ := build y
  obtain ⟨Si, hSi_mem, hSi_e, _, hlift'⟩ := build y⁻¹
  refine ⟨Sy.comp P, Si.comp P, hlift, hlift', ?_, ?_⟩
  · have hcore_e : ∀ ψ θ : ↥Nc,
        ⟪((e ψ : ↥Mbar) : Carrier F Φ₀ σ), Sy (e θ)⟫_ℂ =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
            ⟪Si (e ψ), ((e θ : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ := by
      intro ψ θ
      rw [hSy_e, hSi_e, he_coe, he_coe, hL0, hL0, hL0, hL0]
      exact hpair y ψ θ
    have hcore : ∀ a b : ↥Mbar,
        ⟪(a : Carrier F Φ₀ σ), Sy b⟫_ℂ =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
            ⟪Si a, (b : Carrier F Φ₀ σ)⟫_ℂ := by
      intro a b
      refine hdense.induction_on₂ (p := fun (a b : ↥Mbar) =>
        ⟪(a : Carrier F Φ₀ σ), Sy b⟫_ℂ =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
            ⟪Si a, (b : Carrier F Φ₀ σ)⟫_ℂ) ?_ hcore_e a b
      exact isClosed_eq ((continuous_subtype_val.comp continuous_fst).inner
        (Sy.continuous.comp continuous_snd))
        (continuous_const.mul ((Si.continuous.comp continuous_fst).inner
          (continuous_subtype_val.comp continuous_snd)))
    refine ((ContinuousLinearMap.eq_adjoint_iff
      (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) • Si.comp P)
      (Sy.comp P)).mpr ?_).symm
    intro x v
    rw [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_smul_left, Complex.conj_ofReal]
    have h1 : ⟪Si (P x), v⟫_ℂ = ⟪Si (P x), ((P v : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ := by
      have hsub : v - ((P v : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ :=
        Submodule.sub_starProjection_mem_orthogonal v
      have := Submodule.inner_right_of_mem_orthogonal (hSi_mem (P x)) hsub
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : ⟪x, Sy (P v)⟫_ℂ = ⟪((P x : ↥Mbar) : Carrier F Φ₀ σ), Sy (P v)⟫_ℂ := by
      have hsub : x - ((P x : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ :=
        Submodule.sub_starProjection_mem_orthogonal x
      have := Submodule.inner_left_of_mem_orthogonal (hSy_mem (P v)) hsub
      rw [inner_sub_left, sub_eq_zero] at this
      exact this
    rw [h1, h2]
    exact (hcore (P x) (P v)).symm
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (hcpos y).le _) fun v => ?_
    rw [ContinuousLinearMap.comp_apply]
    refine (hSy_norm (P v)).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hcpos y).le _))
    exact Submodule.norm_orthogonalProjectionOnto_apply_le Mbar v

theorem rightTranslate_mem_cuspMemberSubmodule
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (y : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightTranslate F y φ ∈ cuspMemberSubmodule F Φ₀ ξ := by
  obtain ⟨⟨⟨hmemb, hcusp⟩, hKf⟩, hcont⟩ := hφ
  obtain ⟨hLs, hL2⟩ := (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hmemb
  obtain ⟨hleft, hcentral⟩ := hLs

  have hcont' : Continuous (rightTranslate F y φ) := by
    show Continuous fun x => φ (x * y)
    exact hcont.comp (continuous_id.mul continuous_const)

  have hLs' : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightTranslate F y φ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 F) F γ * g * y) = φ (g * y)
      rw [mul_assoc, hleft]
    · show φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * y) = ((ξ z : ℂˣ) : ℂ) * φ (g * y)
      rw [mul_assoc, hcentral]

  have hL2' : MemLp (rightTranslate F y φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    by_cases h0 : φ = 0
    · subst h0
      exact MemLp.zero'
    · obtain ⟨σ, hσ⟩ :=
        AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F Φ₀ ξ φ
          hmemb hcont h0
      exact (AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀
        hΦ₀.subset hΦ₀.isFundamentalDomain ξ σ hσ φ φ ⟨hleft, hcentral⟩ ⟨hleft, hcentral⟩ hcont hcont
        hL2 hL2 y).1
  have hmemb' : IsAutomorphicFnAt F (fdPins F Φ₀) ξ (rightTranslate F y φ) :=
    (isAutomorphicFnAt_fdPins_iff F Φ₀ ξ _).mpr ⟨hLs', hL2'⟩

  have hcusp' : @IsCuspidalFn _ (fdPins F Φ₀).nS _ _ (fdPins F Φ₀).ν unipotentGL2 (rightTranslate F y φ) :=
    @IsCuspidalFn.rightTranslate _ (fdPins F Φ₀).nS _ _ _ _ _ hcusp y

  have hKf' : IsKfSmooth F (rightTranslate F y φ) := by
    set K : Subgroup (AdelicGL2 (𝓞 F) F) := finiteAdelicGL2Subgroup F with hK
    have hKn : K.Normal := by
      rw [hK]
      unfold finiteAdelicGL2Subgroup
      infer_instance

    have hmemc : ∀ k : K, y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y ∈ K := fun k => by
      simpa using hKn.conj_mem (k : AdelicGL2 (𝓞 F) F) k.2 y⁻¹
    let c : K → K := fun k => ⟨y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y, hmemc k⟩
    have hc : Continuous c :=
      (((continuous_const.mul continuous_subtype_val).mul continuous_const)).subtype_mk _
    have hopen : IsOpen ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K) := hKf
    show IsOpen ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk (rightTranslate F y φ) :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)
    have hsub : c ⁻¹' ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)
        ⊆ ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk (rightTranslate F y φ) :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K) := by
      intro k hk
      simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hk ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * y)) hk
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 ⊢
      show φ (x * (k : AdelicGL2 (𝓞 F) F) * y) = φ (x * y)
      have hstep : x * y * (y⁻¹ * (k : AdelicGL2 (𝓞 F) F) * y) = x * (k : AdelicGL2 (𝓞 F) F) * y := by
        group
      rw [hstep] at h1
      exact h1

    have hH : IsOpen (c ⁻¹' ((MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) : Subgroup K) : Set K)) :=
      hopen.preimage hc

    let chom : K →* K :=
      { toFun := c
        map_one' := by
          refine Subtype.ext ?_
          show y⁻¹ * ((1 : K) : AdelicGL2 (𝓞 F) F) * y = ((1 : K) : AdelicGL2 (𝓞 F) F)
          simp
        map_mul' := fun a b => by
          refine Subtype.ext ?_
          show y⁻¹ * ((a * b : K) : AdelicGL2 (𝓞 F) F) * y
            = (y⁻¹ * (a : AdelicGL2 (𝓞 F) F) * y) * (y⁻¹ * (b : AdelicGL2 (𝓞 F) F) * y)
          simp only [Subgroup.coe_mul]
          group }
    refine Subgroup.isOpen_mono (H₁ := (MulAction.stabilizer K
        (FLT.SmoothVectors.RightTranslationFn.mk φ :
          FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)).comap chom) ?_ ?_
    · intro k hk
      exact hsub hk
    · exact hH
  exact ⟨⟨⟨hmemb', hcusp'⟩, hKf'⟩, hcont'⟩

theorem exists_isCuspLift_rightTranslate_and_norm_le
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) S ∧
        ‖S‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) := by
  obtain ⟨T, T', hT, -, -, hTn⟩ :=
    exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y

  have hAmap : ∀ a ∈ Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)),
      T a ∈ Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) := by
    rintro _ ⟨φm, hφm, rfl⟩
    have hc : (φm : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φm.2, hφm.2⟩
    have hRy : rightTranslate F y φm ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ y φm hφm
    refine ⟨⟨rightTranslate F y φm, hRy.1.1.1⟩, hRy, ?_⟩
    exact (hT.comm φm hc).symm

  have hCmap : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) :
          Set (Carrier F Φ₀ σ))) := by
      rw [← Submodule.topologicalClosure_coe]; exact hv
    have hTv := map_mem_closure T.continuous hv' hAmap
    rw [← Submodule.topologicalClosure_coe] at hTv
    exact hTv
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ)
    (fun v => hCmap v v.2), fun φ h => ?_, ?_⟩
  · apply Subtype.ext
    show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ)
      = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F y φ, h⟩ : Carrier F Φ₀ σ)
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) ⟨φ.2.1.1.1, φ.2.2⟩
  · refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun v => ?_) hTn
    show ‖T (v : Carrier F Φ₀ σ)‖ ≤ ‖T‖ * ‖v‖
    exact (T.le_opNorm (v : Carrier F Φ₀ σ)).trans_eq (by rw [Submodule.norm_coe])

end CuspidalSpectrum

end AutomorphicForm

namespace AutomorphicForm

namespace CuspidalSpectrum

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_enorm_rpow_two_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ memberSubmodule F Φ₀ ξ) :
    ∫⁻ g, ‖φ g‖ₑ ^ (2:ℝ) ∂(weightedMeasure F Φ₀ σ) = ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ ^ (2:ℝ) := by
  have hm := memLp_weightedMeasure_of_mem F hΦ₀ σ hφ
  have h1 : toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ = hm.toLp φ := rfl
  rw [h1, Lp.norm_toLp, ENNReal.ofReal_toReal hm.eLpNorm_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_enorm_sub_rpow_two_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ memberSubmodule F Φ₀ ξ) (hψ : ψ ∈ memberSubmodule F Φ₀ ξ) :
    ∫⁻ g, ‖φ g - ψ g‖ₑ ^ (2:ℝ) ∂(weightedMeasure F Φ₀ σ) =
      ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ - toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩‖ ^ (2:ℝ) := by
  have hsub : φ - ψ ∈ memberSubmodule F Φ₀ ξ := sub_mem hφ hψ
  have hdiff : toCarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ - toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ = toCarrier F hΦ₀ σ ξ ⟨φ - ψ, hsub⟩ := by
    rw [← map_sub]; rfl
  rw [hdiff, ← lintegral_enorm_rpow_two_eq hΦ₀ σ ξ (φ - ψ) hsub]
  rfl

theorem enorm_sub_rpow_two_le (a b : ℂ) :
    ‖a - b‖ₑ ^ (2:ℝ) ≤ 2 * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) := by
  calc ‖a - b‖ₑ ^ (2:ℝ) ≤ (‖a‖ₑ + ‖b‖ₑ) ^ (2:ℝ) := by gcongr; exact enorm_sub_le
    _ ≤ (2:ℝ≥0∞) ^ ((2:ℝ) - 1) * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
    _ = 2 * (‖a‖ₑ ^ (2:ℝ) + ‖b‖ₑ ^ (2:ℝ)) := by norm_num

theorem continuous_enorm_rpow_two {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f) :
    Continuous fun g => ‖f g‖ₑ ^ (2:ℝ) :=
  ENNReal.continuous_rpow_const.comp hf.enorm

theorem exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ contMemberSubmodule F Φ₀ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ y ∈ V, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ < ε := by
  classical
  have : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set κ : Measure (AdelicGL2 (𝓞 F) F) := weightedMeasure F Φ₀ σ with hκ

  let N : AdelicGL2 (𝓞 F) F → ℝ := fun y => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)
  have hN : Continuous N := NumberField.TateGlobal.continuous_ideleNorm_det F
  have hNpos : ∀ y, 0 < N y := fun y => NumberField.TateGlobal.ideleNorm_pos _
  have hN1 : N 1 = 1 := by simp [N, NumberField.TateGlobal.ideleNorm]

  have key : ∀ y : AdelicGL2 (𝓞 F) F, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩‖ ≤ N y ^ (σ / 2) * ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ := by
    intro y
    obtain ⟨T, T', hT, -, -, hTn⟩ := exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y
    refine ⟨hT.mapsTo x hx, ?_⟩
    rw [← hT.comm x hx]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))
  choose hy hbound using key

  set c : ℝ := ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ with hc
  let Fy : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun y g => ‖x (g * y) - x g‖ₑ ^ (2:ℝ)
  let Gy : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℝ≥0∞ :=
    fun y g => 2 * (‖x (g * y)‖ₑ ^ (2:ℝ) + ‖x g‖ₑ ^ (2:ℝ))
  let glim : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => 2 * (‖x g‖ₑ ^ (2:ℝ) + ‖x g‖ₑ ^ (2:ℝ))
  have hxc : Continuous x := hx.2
  have hxyc : ∀ y, Continuous fun g => x (g * y) := fun y => hxc.comp (continuous_id.mul continuous_const)
  have hIx : ∫⁻ g, ‖x g‖ₑ ^ (2:ℝ) ∂κ = ENNReal.ofReal c ^ (2:ℝ) := lintegral_enorm_rpow_two_eq hΦ₀ σ ξ x hx.1
  have hIxy : ∀ y, ∫⁻ g, ‖x (g * y)‖ₑ ^ (2:ℝ) ∂κ ≤ ENNReal.ofReal (N y ^ (σ / 2) * c) ^ (2:ℝ) := by
    intro y
    have h := lintegral_enorm_rpow_two_eq hΦ₀ σ ξ (rightTranslate F y x) (hy y).1
    simp only [rightTranslate_apply] at h
    rw [h]
    gcongr
    exact hbound y
  have hmeas2 : ∀ y, Measurable fun g => ‖x (g * y)‖ₑ ^ (2:ℝ) := fun y => (continuous_enorm_rpow_two (hxyc y)).measurable
  have hmeas1 : Measurable fun g => ‖x g‖ₑ ^ (2:ℝ) := (continuous_enorm_rpow_two hxc).measurable
  have hGint : ∀ y, ∫⁻ g, Gy y g ∂κ = 2 * (∫⁻ g, ‖x (g * y)‖ₑ ^ (2:ℝ) ∂κ + ∫⁻ g, ‖x g‖ₑ ^ (2:ℝ) ∂κ) := by
    intro y
    simp only [Gy]
    rw [lintegral_const_mul _ ((hmeas2 y).fun_add hmeas1), lintegral_add_left (hmeas2 y)]
  have hglim : ∫⁻ g, glim g ∂κ = 2 * (ENNReal.ofReal c ^ (2:ℝ) + ENNReal.ofReal c ^ (2:ℝ)) := by
    simp only [glim]
    rw [lintegral_const_mul _ (hmeas1.fun_add hmeas1), lintegral_add_left hmeas1, hIx]

  have hlim0 : Tendsto (fun y => ∫⁻ g, Fy y g ∂κ) (𝓝 1) (𝓝 0) := by
    refine tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le Fy Gy glim ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro y
      exact (continuous_enorm_rpow_two ((hxyc y).sub hxc)).measurable.aemeasurable
    · intro y
      exact (((hmeas2 y).add hmeas1).const_mul _).aemeasurable
    · intro y
      exact ae_of_all _ fun g => enorm_sub_rpow_two_le _ _
    · refine ae_of_all _ fun g => ?_
      have hc' : Continuous fun y => Fy y g :=
        continuous_enorm_rpow_two (f := fun y => x (g * y) - x g) ((hxc.comp (continuous_const_mul g)).sub continuous_const)
      have h0 : Fy 1 g = 0 := by
        simp only [Fy, mul_one, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos two_pos]
      convert hc'.tendsto 1 using 2
      exact h0.symm
    · refine ae_of_all _ fun g => ?_
      have hc' : Continuous fun y => Gy y g :=
        (ENNReal.continuous_const_mul ENNReal.ofNat_ne_top).comp
          ((continuous_enorm_rpow_two (f := fun y => x (g * y)) (hxc.comp (continuous_const_mul g))).add
            continuous_const)
      convert hc'.tendsto 1 using 2
      simp only [Gy, glim, mul_one]
    · rw [hglim]
      have h : ENNReal.ofReal c ^ (2:ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg two_pos.le ENNReal.ofReal_ne_top
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨h, h⟩)
    ·
      let B : AdelicGL2 (𝓞 F) F → ℝ≥0∞ :=
        fun y => 2 * (ENNReal.ofReal (N y ^ (σ / 2) * c) ^ (2:ℝ) + ENNReal.ofReal c ^ (2:ℝ))
      have hGB : ∀ y, ∫⁻ g, Gy y g ∂κ ≤ B y := by
        intro y
        rw [hGint y, hIx]
        simp only [B]
        gcongr
        exact hIxy y
      have hBc : Continuous B := by
        refine (ENNReal.continuous_const_mul ENNReal.ofNat_ne_top).comp ?_
        refine (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp ?_)).add continuous_const
        exact (hN.rpow_const fun y => Or.inl (hNpos y).ne').mul continuous_const
      have hB1 : B 1 = ∫⁻ g, glim g ∂κ := by
        rw [hglim]
        simp only [B, hN1, Real.one_rpow, one_mul]
      calc limsup (fun y => ∫⁻ g, Gy y g ∂κ) (𝓝 1) ≤ limsup B (𝓝 1) :=
            limsup_le_limsup (Eventually.of_forall hGB)
        _ = B 1 := (hBc.tendsto 1).limsup_eq
        _ = ∫⁻ g, glim g ∂κ := hB1

  have hε2 : (0:ℝ≥0∞) < ENNReal.ofReal ε ^ (2:ℝ) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hε) ENNReal.ofReal_ne_top
  refine ⟨_, hlim0 (Iio_mem_nhds hε2), fun y hyV => ⟨hy y, ?_⟩⟩
  have hlt : ENNReal.ofReal ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, (hy y).1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ ^ (2:ℝ)
      < ENNReal.ofReal ε ^ (2:ℝ) := by
    rw [← lintegral_enorm_sub_rpow_two_eq hΦ₀ σ ξ (rightTranslate F y x) x (hy y).1 hx.1]
    simpa only [rightTranslate_apply, Set.mem_preimage, Set.mem_Iio] using hyV
  exact not_le.1 fun h => (not_lt.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) two_pos.le)) hlt

end CuspidalSpectrum

end AutomorphicForm
