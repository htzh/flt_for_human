/-
  Averaging cusp lifts over a compact subgroup.

  Fix a slab fundamental domain `Φ₀`, a character `ξ` of modulus `σ`, and a family of *cusp lifts*
  `u ↦ S u` — bounded operators on the cuspidal subcarrier `cuspSubcarrier F hΦ₀ σ ξ` that lift the
  right translations `rightTranslate u`. For a finite measure on the compact group and a continuous
  weight `c`, integrating the orbit of a cusp member against these lifts lands back on the subcarrier:

    `∫ u, c u • S u (toCuspSubcarrier φ) = toCuspSubcarrier (fun x => ∫ u, c u * φ (x * u))`,

  and the averaged function `x ↦ ∫ u, c u * φ (x * u)` is again a **cusp member** — which is the
  content of `exists` in both statements: the membership of the average is proved, not assumed.

  Two groups are covered:

  * `integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact`:
    a compact subgroup `U ≤ finiteAdelicGL2Subgroup F` (the finite, level side);
  * `integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate`: the
    product of the archimedean row-isometry groups, included through `adelicArchGLIncl ∘ ι` (the
    archimedean side).

  The two arguments are the same: Bochner integration of a continuous family of bounded operators on
  a Hilbert space, the `L²` bound from the lifts' norm bound, and the cusp-membership of the average
  from the cusp-membership of `φ` (a compact group average of right translates stays in the
  submodule, `rightTranslate_mem_cuspMemberSubmodule`). The pin copies the whole prelude into both of
  its `S_` files; here it is written **once**, publicly, at the pin's names.

  Transcribed from the pin's two `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.lean`
  * `P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate.lean`

  The pin's `AvgLiftFin` namespace is the finite group's half; its archimedean twin carries a
  pipeline label, dropped here (`AvgLiftArch`).

  **Drifts from the pin** (each recorded in `spec/decl_markers.tsv` where it touches a statement):

  * `eLpNorm_two_pow_two` (`S_…isCompact.lean:76`) is stated with an `AEStronglyMeasurable`
    hypothesis. mathlib v4.34 defines `eLpNorm` to be `⊤` off the a.e. strongly measurable
    functions (`MemLp f p μ` is now exactly `eLpNorm f p μ < ∞`), so the pin's unconditional
    identity is false on this line; every pin use discharges the hypothesis from continuity or from
    `Lp.aestronglyMeasurable`. Matching `own:` row in `spec/decl_markers.tsv`.
  * The pin's local `KK` abbrev is a compressed name and is not carried; `continuous_iota` writes
    the type out as `∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion` (second `own:` row).
  * `Adelic/ArchApproxIdentity/ArchInfra.lean` is imported for the pin's
    `secondCountableTopology_KK` (the port's
    `ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀`), which the skeleton's
    eleven imports did not reach.
  * The pin's `set_option synthInstance.maxHeartbeats 400000 in set_option maxHeartbeats 1600000 in`
    above the finite `solution` is **not** transcribed: both headlines elaborate under the port's
    `-DmaxHeartbeats=200000` (the finite one at the first try).

  **Wiring.** `spec/check_port.py` owns the public declarations here: the shared prelude is the pin's
  (public in both `S_` files) and the two headlines are the wrappers'.
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumPairing
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumSubrep
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.TestFnNearIdentity
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace ENNReal ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

/-! ### The shared prelude

  Both pin `S_` files open with the same seven declarations (`S_…isCompact:30–115` and
  `S_…rightTranslate:30–115`, identical text). They are written **once** here, publicly, at the
  pin's names, in the helper namespace `AvgLift` (the pin's `AvgLiftFin` and its pipeline-labelled
  archimedean twin folded into one).

  Three of the seven are already in the port and are **imported**, not re-proved:

  * `continuous_adelicArchGLIncl'` → `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl`
    (`Adelic/TestFnNearIdentity.lean`);
  * `eq_of_glArch_eq_of_glFin_eq` → `AutomorphicForm.gl_ext` (`Adelic/MaximalCompactFactors.lean`);
  * `secondCountableTopology_KK` →
    `ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀`
    (`Adelic/ArchApproxIdentity/ArchInfra.lean`).

  The pin's local `KK` abbrev is a compressed name and is not carried: `continuous_iota` spells its
  type out (`spec/decl_markers.tsv`, `own:` row for this one declaration). -/

namespace AvgLift

variable {F : Type} [Field F] [NumberField F]

-- The pin states this over its local `KK` abbrev (`S_…isCompact.lean:27`); that abbrev is a compressed
-- name and is not carried (SET-AF19 §3), so the type is written out here.
-- own: pin's `KK F` abbrev is not carried; the type is written out, so no hash-identical pin copy exists
omit [NumberField F] in
theorem continuous_iota
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →*
      GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) =
        ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    Continuous ι := by
  have hentry : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (i j : Fin 2)
      (w : InfinitePlace F),
      ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
        = (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j := by
    intro κ i j w
    rw [← NumberField.AdelicLevel.archComponent_apply (K := F) w (ι κ) i j, hι]
  have hval : Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => continuous_pi fun w => ?_
    simp only [hentry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem commute_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ finiteAdelicGL2Subgroup F) (a : GL (Fin 2) (InfiniteAdeleRing F)) :
    u * adelicArchGLIncl F a = adelicArchGLIncl F a * u := by
  have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu
  refine gl_ext F ?_ ?_
  · rw [map_mul, map_mul, hu1, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicArchGLIncl, one_mul, mul_one]

-- The pin (`S_…isCompact.lean:76`) states this with no measurability hypothesis, which mathlib v4.34
-- makes false: `eLpNorm` is now `⊤` for a function that is not a.e. strongly measurable. Every pin use
-- discharges the hypothesis from continuity (or from `Lp.aestronglyMeasurable`).
-- own: mathlib v4.34's `eLpNorm` is `⊤` off the a.e. strongly measurable functions, so the pin's unconditional form is false; the `AEStronglyMeasurable` hypothesis is carried instead
theorem eLpNorm_two_pow_two {X : Type*} [MeasurableSpace X] (ν : Measure X) {φ : X → ℂ}
    (hφ : AEStronglyMeasurable φ ν) :
    eLpNorm φ 2 ν ^ 2 = ∫⁻ a, ‖φ a‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hφ,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_sq_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {g : X → ℝ≥0∞}
    (hg : AEMeasurable g ν) :
    (∫⁻ x, g x ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ x, g x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two) hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h2 : (∫⁻ x, g x ∂ν) ^ 2 ≤
      ((∫⁻ x, g x ^ (2:ℝ) ∂ν) ^ ((1:ℝ)/2) * (ν Set.univ) ^ ((1:ℝ)/2)) ^ 2 := by
    gcongr
  have h3 : ((∫⁻ x, g x ^ (2:ℝ) ∂ν) ^ ((1:ℝ)/2) * (ν Set.univ) ^ ((1:ℝ)/2)) ^ 2 =
      (∫⁻ x, g x ^ (2:ℝ) ∂ν) * ν Set.univ := by
    rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ x, g x ^ (2:ℝ) ∂ν) ^ ((1:ℝ)/2)),
      ← ENNReal.rpow_natCast ((ν Set.univ) ^ ((1:ℝ)/2)), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  have h4 : (∫⁻ x, g x ^ (2:ℝ) ∂ν) = ∫⁻ x, g x ^ 2 ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_natCast]
    norm_num
  rw [h3, h4, mul_comm] at h2
  exact h2

theorem isKfSmooth_integral_mul_apply_mul
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    [MeasurableSpace ↥U] (μ : Measure ↥U)
    (c : ↥U → ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    IsKfSmooth F (fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ) := by
  classical

  set Sφ : Subgroup ↥(finiteAdelicGL2Subgroup F) :=
    MulAction.stabilizer ↥(finiteAdelicGL2Subgroup F) (FLT.SmoothVectors.RightTranslationFn.mk φ)
      with hSφ
  have hSo : IsOpen (Sφ : Set ↥(finiteAdelicGL2Subgroup F)) := hφ
  have hfixφ : ∀ s ∈ Sφ, ∀ z : AdelicGL2 (𝓞 F) F, φ (z * (s : AdelicGL2 (𝓞 F) F)) = φ z := by
    intro s hs z
    rw [MulAction.mem_stabilizer_iff] at hs
    have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f z) hs
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
      FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1
    exact h1

  let e : ↥U → ↥(finiteAdelicGL2Subgroup F) := fun u => ⟨(u : AdelicGL2 (𝓞 F) F), hUf u.2⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have : CompactSpace ↥U := isCompact_iff_compactSpace.mp hU

  let conj' : ↥U × ↥(finiteAdelicGL2Subgroup F) → ↥(finiteAdelicGL2Subgroup F) :=
    fun p => (e p.1)⁻¹ * p.2 * e p.1
  have hconj : Continuous conj' :=
    ((he.comp continuous_fst).inv.mul continuous_snd).mul (he.comp continuous_fst)
  have hpre : IsOpen (conj' ⁻¹' (Sφ : Set ↥(finiteAdelicGL2Subgroup F))) := hSo.preimage hconj
  have hsub : (Set.univ : Set ↥U) ×ˢ ({1} : Set ↥(finiteAdelicGL2Subgroup F)) ⊆
      conj' ⁻¹' (Sφ : Set _) := by
    rintro ⟨u, v⟩ ⟨-, hv⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    show (e u)⁻¹ * 1 * e u ∈ Sφ
    rw [mul_one, inv_mul_cancel]
    exact one_mem _
  obtain ⟨A, B, hA, hB, hUA, h1B, hAB⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hpre hsub
  have h1 : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ B := h1B (Set.mem_singleton 1)

  have hfix : ∀ v ∈ B, ∀ x : AdelicGL2 (𝓞 F) F,
      (∫ u, c u * φ (x * (v : AdelicGL2 (𝓞 F) F) * (u : AdelicGL2 (𝓞 F) F)) ∂μ) =
        ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ := by
    intro v hv x
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    have hm : conj' (u, v) ∈ Sφ := hAB (Set.mk_mem_prod (hUA (Set.mem_univ u)) hv)
    have h2 := hfixφ _ hm (x * (u : AdelicGL2 (𝓞 F) F))
    show c u * φ (x * (v : AdelicGL2 (𝓞 F) F) * (u : AdelicGL2 (𝓞 F) F)) =
      c u * φ (x * (u : AdelicGL2 (𝓞 F) F))
    rw [← h2]
    congr 2
    show x * (v : AdelicGL2 (𝓞 F) F) * (u : AdelicGL2 (𝓞 F) F) = x * (u : AdelicGL2 (𝓞 F) F) *
      ((u : AdelicGL2 (𝓞 F) F)⁻¹ * (v : AdelicGL2 (𝓞 F) F) * (u : AdelicGL2 (𝓞 F) F))
    group

  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hB.mem_nhds h1) fun v hv => ?_)
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
  simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk]
  exact hfix v hv x

end AvgLift

open AvgLift in
theorem integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    [MeasurableSpace ↥U] [BorelSpace ↥U] (μ : Measure ↥U) [IsFiniteMeasure μ]
    (S : ↥U → (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hS : ∀ u : ↥U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (S u))
    (hSc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : ↥U => S u v)
    (c : ↥U → ℂ) (hc : Continuous c)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      ∫ u, c u • S u (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ, h⟩ := by
  classical

  have : CompactSpace ↥U := isCompact_iff_compactSpace.mp hU
  have : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have : SecondCountableTopology ↥U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  have : SFinite ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := inferInstance
  have hμlf : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨Set.univ, Filter.univ_mem, measure_lt_top μ _⟩⟩
  have hμsf : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  have hμs : SFinite μ := inferInstance
  set y : ↥U → AdelicGL2 (𝓞 F) F :=
    fun κ => ((κ : ↥U) : AdelicGL2 (𝓞 F) F) with hy
  have hyc : Continuous y := continuous_subtype_val
  have hR : ∀ κ, rightTranslate F (y κ) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun κ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (y κ) φ hφ
  have hSR : ∀ κ, S κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) =
      toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y κ) φ, hR κ⟩ := fun κ => hS κ ⟨φ, hφ⟩ (hR κ)
  have hφc : Continuous φ := hφ.2
  have hjoint : Continuous fun p : AdelicGL2 (𝓞 F) F × ↥U =>
      φ (p.1 * y p.2) := hφc.comp (continuous_fst.mul (hyc.comp continuous_snd))
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun x => ∫ κ, c κ * φ (x * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ
    with hψdef

  have hψc : Continuous ψ := by
    have h := continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun (x : AdelicGL2 (𝓞 F) F) (κ : ↥U) => c κ * φ (x * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)))
      ((hc.comp continuous_snd).mul hjoint) isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hφx : IsLsXiFunction (𝓞 F) F ⊤ ξ φ := ((mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1.1.1).1
  have hψx : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show (∫ κ, c κ * φ (globalPoints (𝓞 F) F γ * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ) =
        ∫ κ, c κ * φ (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ
      refine integral_congr_ae (ae_of_all _ fun κ => ?_)
      show c κ * φ (globalPoints (𝓞 F) F γ * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) =
        c κ * φ (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F))
      rw [mul_assoc, hφx.left_invariant]
    · show (∫ κ, c κ * φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g *
          ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ) =
        ((ξ z : ℂˣ) : ℂ) * ∫ κ, c κ * φ (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun κ => ?_)
      show c κ * φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g *
          ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) =
        ((ξ z : ℂˣ) : ℂ) * (c κ * φ (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)))
      rw [mul_assoc, hφx.central_transform]
      ring

  obtain ⟨κc, -, hκc⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (hc.norm.continuousOn)
  have hC : ∀ κ, ‖c κ‖ ≤ ‖c κc‖ := fun κ => hκc (Set.mem_univ κ)
  have hC0 : 0 ≤ ‖c κc‖ := norm_nonneg _
  obtain ⟨κb, -, hκb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((hSc (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)).norm.continuousOn)
  set B : ℝ := ‖S κb (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ with hBdef
  have hBκ : ∀ κ, ‖S κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ ≤ B := fun κ => hκb (Set.mem_univ κ)
  have hB0 : 0 ≤ B := norm_nonneg _
  have hnormR : ∀ κ, eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ) ≤ ENNReal.ofReal B := by
    intro κ
    have hmem := memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1
    have h1 : ‖S κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ =
        (eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)).toReal := by
      rw [hSR κ]
      change ‖((toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y κ) φ, hR κ⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
        Carrier F Φ₀ σ)‖ = _
      rw [toCuspSubcarrier_apply_coe]
      exact Lp.norm_toLp _ hmem
    calc eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)
        = ENNReal.ofReal ((eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)).toReal) :=
          (ENNReal.ofReal_toReal hmem.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (h1 ▸ hBκ κ)

  set m : ℝ := min (α ^ (-σ)) (β ^ (-σ)) with hmdef
  have hm0 : 0 < m := lt_min (Real.rpow_pos_of_pos hΦ₀.pos _) (Real.rpow_pos_of_pos hΦ₀.pos_right _)
  have hlow : ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞,
      ∫⁻ x, f x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ≤
        (ENNReal.ofReal m)⁻¹ * ∫⁻ x, f x ∂(weightedMeasure F Φ₀ σ) := by
    intro f
    set μ₀ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ₀
    have hres : μ₀.restrict Φ₀ = (μ₀.restrict (detNormSlab F α β)).restrict Φ₀ := by
      rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet,
        Set.inter_eq_left.mpr hΦ₀.subset]
    have hae0 : ∀ᵐ x ∂(μ₀.restrict Φ₀), x ∈ Φ₀ := by
      rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
    have hwlow : ∀ x ∈ Φ₀, m ≤ weight F σ x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hΦ₀.subset hx
      unfold weight
      rcases le_or_gt 0 (-σ) with hs | hs
      · exact (min_le_left _ _).trans (Real.rpow_le_rpow hΦ₀.pos.le h1 hs)
      · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos
          (lt_of_lt_of_le hΦ₀.pos h1) h2 hs.le)
    have hle : (ENNReal.ofReal m) • μ₀.restrict Φ₀ ≤ weightedMeasure F Φ₀ σ := by
      unfold weightedMeasure
      rw [← withDensity_const]
      exact withDensity_mono (hae0.mono fun x hx => ENNReal.ofReal_le_ofReal (hwlow x hx))
    have h := lintegral_mono' hle (le_refl f)
    rw [lintegral_smul_measure] at h
    exact (ENNReal.mul_le_iff_le_inv (by simp [hm0]) ENNReal.ofReal_ne_top).mp h
  have hψL2 : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    have : SecondCountableTopologyEither (AdelicGL2 (𝓞 F) F) (↥U) := secondCountableTopologyEither_of_left _ _
    have : OpensMeasurableSpace (AdelicGL2 (𝓞 F) F × ↥U) := Prod.opensMeasurableSpace
    have hmeas2 : Measurable fun p : AdelicGL2 (𝓞 F) F × ↥U => ‖φ (p.1 * y p.2)‖ₑ ^ 2 :=
      (hjoint.measurable.enorm.pow_const 2)
    set K : ℝ≥0∞ := ENNReal.ofReal ‖c κc‖ ^ 2 * μ Set.univ with hK

    have hpt : ∀ x, ‖ψ x‖ₑ ^ 2 ≤ K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ := by
      intro x
      have hmx : AEMeasurable (fun κ => ‖φ (x * y κ)‖ₑ) μ :=
        (hφc.comp (continuous_const.mul hyc)).measurable.enorm.aemeasurable
      have h1 : ‖ψ x‖ₑ ≤ ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ := by
        calc ‖ψ x‖ₑ ≤ ∫⁻ κ, ‖c κ * φ (x * ((κ : ↥U) : AdelicGL2 (𝓞 F) F))‖ₑ ∂μ :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ κ, ENNReal.ofReal ‖c κc‖ * ‖φ (x * y κ)‖ₑ ∂μ := by
              refine lintegral_mono fun κ => ?_
              rw [enorm_mul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hC κ)
          _ = ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ := by
              rw [lintegral_const_mul'' _ hmx]
      calc ‖ψ x‖ₑ ^ 2 ≤ (ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ) ^ 2 := by gcongr
        _ = ENNReal.ofReal ‖c κc‖ ^ 2 * (∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ) ^ 2 := mul_pow _ _ _
        _ ≤ ENNReal.ofReal ‖c κc‖ ^ 2 * (μ Set.univ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ) := by
            gcongr
            exact lintegral_sq_le μ hmx
        _ = K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ := by rw [hK, mul_assoc]
    have hsq : eLpNorm ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ^ 2 < ⊤ := by
      rw [eLpNorm_two_pow_two (hφ := hψc.aestronglyMeasurable)]
      calc ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)
          ≤ ∫⁻ x, K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
            lintegral_mono fun x => hpt x
        _ = K * ∫⁻ x, ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
            rw [lintegral_const_mul'' _ (hmeas2.lintegral_prod_right'.aemeasurable)]
        _ = K * ∫⁻ κ, ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ∂μ := by
            rw [lintegral_lintegral_swap hmeas2.aemeasurable]
        _ ≤ K * ∫⁻ κ, (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 ∂μ := by
            gcongr with κ
            calc ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)
                ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂(weightedMeasure F Φ₀ σ) :=
                  hlow _
              _ = (ENNReal.ofReal m)⁻¹ *
                    eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ) ^ 2 := by
                  rw [eLpNorm_two_pow_two (φ := rightTranslate F (y κ) φ)
                    (hφ := (hφc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)]
                  rfl
              _ ≤ (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 := by
                  gcongr
                  exact hnormR κ
        _ = K * ((ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 * μ Set.univ) := by rw [lintegral_const]
        _ < ⊤ := by
            refine ENNReal.mul_lt_top ?_ ?_
            · exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top μ _)
            · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_
                (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (measure_lt_top μ _)
              exact ENNReal.inv_lt_top.mpr (by simp [hm0])
    exact lt_of_le_of_ne le_top fun htop => by
      rw [htop] at hsq
      exact absurd hsq (by simp)
  have hψcusp : @IsCuspidalFn _ (fdPins F Φ₀).nS _ _ (fdPins F Φ₀).ν unipotentGL2 ψ := by
    let mA : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
    have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    have hO1 : OpensMeasurableSpace (AdeleRing (𝓞 F) F) := inferInstance
    have hO2 : OpensMeasurableSpace (↥U) := inferInstance
    have := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

    obtain ⟨Cb, hCb, hsubb⟩ := exists_isCompact_adelicBox_subset F
    have hbox_top : adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hsubb) hCb.measure_lt_top).ne
    have hνprob : IsProbabilityMeasure (fdPins F Φ₀).ν := by
      show IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (adelicAddHaar_adelicBox_pos F).ne'
        hbox_top
    intro g
    have h0 := fun κ : ↥U => hφ.1.1.2 (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F))
    unfold constantTerm at h0 ⊢

    have hint : Integrable (Function.uncurry fun (q : AdeleRing (𝓞 F) F) (κ : ↥U) =>
        c κ * φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)))
        (((fdPins F Φ₀).ν).prod μ) := by
      have : SecondCountableTopologyEither (AdeleRing (𝓞 F) F) (↥U) :=
        secondCountableTopologyEither_of_right _ _
      have : OpensMeasurableSpace (AdeleRing (𝓞 F) F × ↥U) := Prod.opensMeasurableSpace
      have hG : Continuous (Function.uncurry fun (q : AdeleRing (𝓞 F) F) (κ : ↥U) =>
          c κ * φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F))) :=
        (hc.comp continuous_snd).mul (hφc.comp
          ((((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).comp continuous_fst).mul
            continuous_const).mul (hyc.comp continuous_snd)))

      obtain ⟨B, hB⟩ := (hCb.prod isCompact_univ).exists_bound_of_continuousOn
        (s := Cb ×ˢ (Set.univ : Set (↥U))) hG.continuousOn
      have hae : ∀ᵐ p ∂(((fdPins F Φ₀).ν).prod μ), p.1 ∈ adelicBox F := by
        rw [ae_iff]
        have hset : {p : AdeleRing (𝓞 F) F × ↥U | ¬ p.1 ∈ adelicBox F} =
            (adelicBox F)ᶜ ×ˢ (Set.univ : Set (↥U)) := by
          ext p; simp
        rw [hset, Measure.prod_prod]
        have hν0 : (fdPins F Φ₀).ν (adelicBox F)ᶜ = 0 := by
          show ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) (adelicBox F)ᶜ = 0
          rw [ProbabilityTheory.cond_apply (measurableSet_adelicBox F), Set.inter_compl_self,
            measure_empty, mul_zero]
        rw [hν0, zero_mul]
      refine Integrable.mono' (integrable_const B) hG.aestronglyMeasurable ?_
      filter_upwards [hae] with p hp
      exact hB p ⟨hsubb hp, Set.mem_univ _⟩
    have hswap := integral_integral_swap hint
    have hlhs : (fun q => constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) ψ g q) =
        fun q => ∫ κ, c κ * φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ := by
      funext q
      show (∫ κ, c κ * φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂μ) = _
      rfl
    rw [hlhs, hswap]
    have hin : ∀ κ : ↥U, (∫ q, c κ * φ (unipotentGL2 q * g *
        ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) ∂(fdPins F Φ₀).ν) = 0 := by
      intro κ
      rw [integral_const_mul]
      have : (fun q => φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F))) =
          constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ
            (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) := by
        funext q
        show φ (unipotentGL2 q * g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)) =
          φ (unipotentGL2 q * (g * ((κ : ↥U) : AdelicGL2 (𝓞 F) F)))
        rw [mul_assoc]
      rw [this, h0 κ, mul_zero]
    simp only [hin, integral_zero]
  have hψsm : IsKfSmooth F ψ :=
    AvgLift.isKfSmooth_integral_mul_apply_mul U hU hUf μ c φ hφ.1.2
  have hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    ⟨⟨⟨(isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mpr ⟨hψx, hψL2⟩, hψcusp⟩, hψsm⟩, hψc⟩
  refine ⟨hψm, ?_⟩

  set w := weightedMeasure F Φ₀ σ with hwdef
  have : SecondCountableTopologyEither (AdelicGL2 (𝓞 F) F) (↥U) := secondCountableTopologyEither_of_left _ _
  have : OpensMeasurableSpace (AdelicGL2 (𝓞 F) F × ↥U) := Prod.opensMeasurableSpace
  have : SFinite w := by rw [hwdef]; unfold weightedMeasure; infer_instance
  have : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  set G : ↥U → ↥(cuspSubcarrier F hΦ₀ σ ξ) := fun κ => c κ • S κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
    with hGdef
  have hGc : Continuous G := hc.smul (hSc _)
  have hGint : Integrable G μ := by
    obtain ⟨κm, -, hκm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hGc.norm.continuousOn
    exact Integrable.mono' (integrable_const ‖G κm‖) hGc.aestronglyMeasurable
      (ae_of_all _ fun κ => hκm (Set.mem_univ κ))
  have hGcoe : ∀ κ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) =
      c κ • (memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1).toLp (rightTranslate F (y κ) φ) := by
    intro κ
    show ((c κ • S κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
      Carrier F Φ₀ σ) = _
    rw [hSR κ, Submodule.coe_smul, toCuspSubcarrier_apply_coe]
    rfl

  apply Subtype.ext
  show ((∫ κ, G κ ∂μ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) =
    ((toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)
  rw [toCuspSubcarrier_apply_coe]
  have hL := ((cuspSubcarrier F hΦ₀ σ ξ).subtypeL.integral_comp_comm hGint).symm
  simp only [Submodule.subtypeL_apply] at hL
  rw [hL]
  change ∫ κ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∂μ =
    (memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).toLp ψ
  have hGint' : Integrable (fun κ => ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)) μ :=
    (cuspSubcarrier F hΦ₀ σ ξ).subtypeL.integrable_comp hGint

  refine ext_inner_left ℂ fun θ => ?_
  rw [← integral_inner hGint' θ]

  have hlhs : ∀ κ, ⟪θ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)⟫_ℂ =
      ∫ x, (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ)) ∂w := by
    intro κ
    rw [hGcoe κ, inner_smul_right, MeasureTheory.L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1).coeFn_toLp] with x hx
    rw [hx, rightTranslate_apply, RCLike.inner_apply]
    ring
  have hrhs : ⟪θ, (memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).toLp ψ⟫_ℂ =
      ∫ x, ∫ κ, (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ)) ∂μ ∂w := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, mul_comm, integral_const_mul]
  simp_rw [hlhs]
  rw [hrhs]

  have hH : Integrable (Function.uncurry fun (x : AdelicGL2 (𝓞 F) F) (κ : ↥U) =>
      (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ))) (w.prod μ) := by

    have hθm : AEStronglyMeasurable
        (fun p : AdelicGL2 (𝓞 F) F × ↥U => (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) (w.prod μ) :=
      (Lp.aestronglyMeasurable θ).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := w) (ν := μ))
    have hθ2 : MemLp (fun p : AdelicGL2 (𝓞 F) F × ↥U => (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) 2
        (w.prod μ) := by
      have hsq : eLpNorm (fun p : AdelicGL2 (𝓞 F) F × ↥U =>
          (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) 2 (w.prod μ) ^ 2 < ⊤ := by
        rw [eLpNorm_two_pow_two (hφ := hθm), lintegral_prod _ (hθm.aemeasurable.enorm.pow_const 2)]
        simp only [lintegral_const]
        rw [lintegral_mul_const'' _ ((Lp.aestronglyMeasurable θ).aemeasurable.enorm.pow_const 2),
          ← eLpNorm_two_pow_two (φ := (θ : AdelicGL2 (𝓞 F) F → ℂ))
            (hφ := Lp.aestronglyMeasurable θ)]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (Lp.memLp θ).eLpNorm_lt_top) (measure_lt_top μ _)
      exact lt_of_le_of_ne le_top fun htop => by
        rw [htop] at hsq
        exact absurd hsq (by simp)
    have hθ2' : MemLp (fun p : AdelicGL2 (𝓞 F) F × ↥U =>
        (starRingEnd ℂ) ((θ : AdelicGL2 (𝓞 F) F → ℂ) p.1)) 2 (w.prod μ) :=
      hθ2.star

    have hΦc : Continuous fun p : AdelicGL2 (𝓞 F) F × ↥U => c p.2 * φ (p.1 * y p.2) :=
      (hc.comp continuous_snd).mul hjoint
    have hΦ2 : MemLp (fun p : AdelicGL2 (𝓞 F) F × ↥U => c p.2 * φ (p.1 * y p.2)) 2 (w.prod μ) := by
      have hmeas : Measurable fun p : AdelicGL2 (𝓞 F) F × ↥U => ‖c p.2 * φ (p.1 * y p.2)‖ₑ ^ 2 :=
        hΦc.measurable.enorm.pow_const 2
      have hsq : eLpNorm (fun p : AdelicGL2 (𝓞 F) F × ↥U => c p.2 * φ (p.1 * y p.2)) 2
          (w.prod μ) ^ 2 < ⊤ := by
        rw [eLpNorm_two_pow_two (hφ := hΦc.aestronglyMeasurable), lintegral_prod _ hmeas.aemeasurable,
          lintegral_lintegral_swap hmeas.aemeasurable]
        calc ∫⁻ κ, ∫⁻ x, ‖c κ * φ (x * y κ)‖ₑ ^ 2 ∂w ∂μ
            = ∫⁻ κ, ‖c κ‖ₑ ^ 2 * ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂w ∂μ := by
              refine lintegral_congr fun κ => ?_
              rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
              refine lintegral_congr fun x => ?_
              rw [enorm_mul, mul_pow]
          _ ≤ ∫⁻ κ, ENNReal.ofReal ‖c κc‖ ^ 2 * ENNReal.ofReal B ^ 2 ∂μ := by
              refine lintegral_mono fun κ => ?_
              gcongr
              · rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hC κ)
              · calc ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂w =
                    eLpNorm (rightTranslate F (y κ) φ) 2 w ^ 2 := by
                      rw [eLpNorm_two_pow_two (φ := rightTranslate F (y κ) φ) (hφ :=
                        (hφc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)]
                      rfl
                  _ ≤ ENNReal.ofReal B ^ 2 := by gcongr; exact hnormR κ
          _ = ENNReal.ofReal ‖c κc‖ ^ 2 * ENNReal.ofReal B ^ 2 * μ Set.univ := lintegral_const _
          _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
              (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (measure_lt_top μ _)
      exact lt_of_le_of_ne le_top fun htop => by
        rw [htop] at hsq
        exact absurd hsq (by simp)

    have hprod := hθ2'.fun_mul hΦ2 (r := 1)
    have hint1 := memLp_one_iff_integrable.mp hprod
    exact hint1
  exact (integral_integral_swap hH).symm

open AvgLift in
theorem integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) [IsFiniteMeasure μ]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (π : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →
      (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hπ : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (ι κ))) (π κ))
    (hπc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ),
      Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => π κ v)
    (c : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (hc : Continuous c)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      ∫ κ, c κ • π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ =
        toCuspSubcarrier F hΦ₀ σ ξ
          ⟨fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ, h⟩ := by
  classical

  have : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  have : CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.compactSpace
  have : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have : SecondCountableTopology (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
    ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ F
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  have : SFinite ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := inferInstance
  have hμlf : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨Set.univ, Filter.univ_mem, measure_lt_top μ _⟩⟩
  have hμsf : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  have hμs : SFinite μ := inferInstance
  set y : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → AdelicGL2 (𝓞 F) F :=
    fun κ => adelicArchGLIncl F (ι κ) with hy
  have hyc : Continuous y :=
    (TestFnNearIdentity.continuous_adelicArchGLIncl F).comp (continuous_iota ι hι)
  have hR : ∀ κ, rightTranslate F (y κ) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun κ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (y κ) φ hφ
  have hπR : ∀ κ, π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) =
      toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y κ) φ, hR κ⟩ := fun κ => hπ κ ⟨φ, hφ⟩ (hR κ)
  have hφc : Continuous φ := hφ.2
  have hjoint : Continuous fun p : AdelicGL2 (𝓞 F) F ×
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      φ (p.1 * y p.2) := hφc.comp (continuous_fst.mul (hyc.comp continuous_snd))
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ
    with hψdef

  have hψc : Continuous ψ := by
    have h := continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun (x : AdelicGL2 (𝓞 F) F) (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) =>
        c κ * φ (x * adelicArchGLIncl F (ι κ)))
      ((hc.comp continuous_snd).mul hjoint) isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hφx : IsLsXiFunction (𝓞 F) F ⊤ ξ φ := ((mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1.1.1).1
  have hψx : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show (∫ κ, c κ * φ (globalPoints (𝓞 F) F γ * g * adelicArchGLIncl F (ι κ)) ∂μ) =
        ∫ κ, c κ * φ (g * adelicArchGLIncl F (ι κ)) ∂μ
      refine integral_congr_ae (ae_of_all _ fun κ => ?_)
      show c κ * φ (globalPoints (𝓞 F) F γ * g * adelicArchGLIncl F (ι κ)) =
        c κ * φ (g * adelicArchGLIncl F (ι κ))
      rw [mul_assoc, hφx.left_invariant]
    · show (∫ κ, c κ * φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g *
          adelicArchGLIncl F (ι κ)) ∂μ) =
        ((ξ z : ℂˣ) : ℂ) * ∫ κ, c κ * φ (g * adelicArchGLIncl F (ι κ)) ∂μ
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun κ => ?_)
      show c κ * φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g *
          adelicArchGLIncl F (ι κ)) =
        ((ξ z : ℂˣ) : ℂ) * (c κ * φ (g * adelicArchGLIncl F (ι κ)))
      rw [mul_assoc, hφx.central_transform]
      ring

  obtain ⟨κc, -, hκc⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (hc.norm.continuousOn)
  have hC : ∀ κ, ‖c κ‖ ≤ ‖c κc‖ := fun κ => hκc (Set.mem_univ κ)
  have hC0 : 0 ≤ ‖c κc‖ := norm_nonneg _
  obtain ⟨κb, -, hκb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((hπc (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)).norm.continuousOn)
  set B : ℝ := ‖π κb (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ with hBdef
  have hBκ : ∀ κ, ‖π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ ≤ B := fun κ => hκb (Set.mem_univ κ)
  have hB0 : 0 ≤ B := norm_nonneg _
  have hnormR : ∀ κ, eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ) ≤
      ENNReal.ofReal B := by
    intro κ
    have hmem := memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1
    have h1 : ‖π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ =
        (eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)).toReal := by
      rw [hπR κ]
      change ‖((toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y κ) φ, hR κ⟩ :
        ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)‖ = _
      rw [toCuspSubcarrier_apply_coe]
      exact Lp.norm_toLp _ hmem
    calc eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)
        = ENNReal.ofReal ((eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ)).toReal) :=
          (ENNReal.ofReal_toReal hmem.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (h1 ▸ hBκ κ)

  set m : ℝ := min (α ^ (-σ)) (β ^ (-σ)) with hmdef
  have hm0 : 0 < m := lt_min (Real.rpow_pos_of_pos hΦ₀.pos _) (Real.rpow_pos_of_pos hΦ₀.pos_right _)
  have hlow : ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞,
      ∫⁻ x, f x ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ≤
        (ENNReal.ofReal m)⁻¹ * ∫⁻ x, f x ∂(weightedMeasure F Φ₀ σ) := by
    intro f
    set μ₀ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ₀
    have hres : μ₀.restrict Φ₀ = (μ₀.restrict (detNormSlab F α β)).restrict Φ₀ := by
      rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet,
        Set.inter_eq_left.mpr hΦ₀.subset]
    have hae0 : ∀ᵐ x ∂(μ₀.restrict Φ₀), x ∈ Φ₀ := by
      rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
    have hwlow : ∀ x ∈ Φ₀, m ≤ weight F σ x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hΦ₀.subset hx
      unfold weight
      rcases le_or_gt 0 (-σ) with hs | hs
      · exact (min_le_left _ _).trans (Real.rpow_le_rpow hΦ₀.pos.le h1 hs)
      · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos
          (lt_of_lt_of_le hΦ₀.pos h1) h2 hs.le)
    have hle : (ENNReal.ofReal m) • μ₀.restrict Φ₀ ≤ weightedMeasure F Φ₀ σ := by
      unfold weightedMeasure
      rw [← withDensity_const]
      exact withDensity_mono (hae0.mono fun x hx => ENNReal.ofReal_le_ofReal (hwlow x hx))
    have h := lintegral_mono' hle (le_refl f)
    rw [lintegral_smul_measure] at h
    exact (ENNReal.mul_le_iff_le_inv (by simp [hm0]) ENNReal.ofReal_ne_top).mp h
  have hψL2 : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    have : SecondCountableTopologyEither (AdelicGL2 (𝓞 F) F)
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      secondCountableTopologyEither_of_left _ _
    have : OpensMeasurableSpace (AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) := Prod.opensMeasurableSpace
    have hmeas2 : Measurable fun p : AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => ‖φ (p.1 * y p.2)‖ₑ ^ 2 :=
      (hjoint.measurable.enorm.pow_const 2)
    set K : ℝ≥0∞ := ENNReal.ofReal ‖c κc‖ ^ 2 * μ Set.univ with hK

    have hpt : ∀ x, ‖ψ x‖ₑ ^ 2 ≤ K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ := by
      intro x
      have hmx : AEMeasurable (fun κ => ‖φ (x * y κ)‖ₑ) μ :=
        (hφc.comp (continuous_const.mul hyc)).measurable.enorm.aemeasurable
      have h1 : ‖ψ x‖ₑ ≤ ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ := by
        calc ‖ψ x‖ₑ ≤ ∫⁻ κ, ‖c κ * φ (x * adelicArchGLIncl F (ι κ))‖ₑ ∂μ :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ κ, ENNReal.ofReal ‖c κc‖ * ‖φ (x * y κ)‖ₑ ∂μ := by
              refine lintegral_mono fun κ => ?_
              rw [enorm_mul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hC κ)
          _ = ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ := by
              rw [lintegral_const_mul'' _ hmx]
      calc ‖ψ x‖ₑ ^ 2 ≤ (ENNReal.ofReal ‖c κc‖ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ) ^ 2 := by gcongr
        _ = ENNReal.ofReal ‖c κc‖ ^ 2 * (∫⁻ κ, ‖φ (x * y κ)‖ₑ ∂μ) ^ 2 := mul_pow _ _ _
        _ ≤ ENNReal.ofReal ‖c κc‖ ^ 2 * (μ Set.univ * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ) := by
            gcongr
            exact lintegral_sq_le μ hmx
        _ = K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ := by rw [hK, mul_assoc]
    have hsq : eLpNorm ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ^ 2 < ⊤ := by
      rw [eLpNorm_two_pow_two (hφ := hψc.aestronglyMeasurable)]
      calc ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)
          ≤ ∫⁻ x, K * ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
            lintegral_mono fun x => hpt x
        _ = K * ∫⁻ x, ∫⁻ κ, ‖φ (x * y κ)‖ₑ ^ 2 ∂μ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
            rw [lintegral_const_mul'' _ (hmeas2.lintegral_prod_right'.aemeasurable)]
        _ = K * ∫⁻ κ, ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ∂μ := by
            rw [lintegral_lintegral_swap hmeas2.aemeasurable]
        _ ≤ K * ∫⁻ κ, (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 ∂μ := by
            gcongr with κ
            calc ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)
                ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂(weightedMeasure F Φ₀ σ) :=
                  hlow _
              _ = (ENNReal.ofReal m)⁻¹ *
                    eLpNorm (rightTranslate F (y κ) φ) 2 (weightedMeasure F Φ₀ σ) ^ 2 := by
                  rw [eLpNorm_two_pow_two (φ := rightTranslate F (y κ) φ)
                    (hφ := (hφc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)]
                  rfl
              _ ≤ (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 := by
                  gcongr
                  exact hnormR κ
        _ = K * ((ENNReal.ofReal m)⁻¹ * ENNReal.ofReal B ^ 2 * μ Set.univ) := by rw [lintegral_const]
        _ < ⊤ := by
            refine ENNReal.mul_lt_top ?_ ?_
            · exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top μ _)
            · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_
                (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (measure_lt_top μ _)
              exact ENNReal.inv_lt_top.mpr (by simp [hm0])
    exact lt_of_le_of_ne le_top fun htop => by
      rw [htop] at hsq
      exact absurd hsq (by simp)
  have hψcusp : @IsCuspidalFn _ (fdPins F Φ₀).nS _ _ (fdPins F Φ₀).ν unipotentGL2 ψ := by
    let mA : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
    have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
    have hO1 : OpensMeasurableSpace (AdeleRing (𝓞 F) F) := inferInstance
    have hO2 : OpensMeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      inferInstance
    have := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

    obtain ⟨Cb, hCb, hsubb⟩ := exists_isCompact_adelicBox_subset F
    have hbox_top : adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hsubb) hCb.measure_lt_top).ne
    have hνprob : IsProbabilityMeasure (fdPins F Φ₀).ν := by
      show IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite (adelicAddHaar_adelicBox_pos F).ne'
        hbox_top
    intro g
    have h0 := fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      hφ.1.1.2 (g * adelicArchGLIncl F (ι κ))
    unfold constantTerm at h0 ⊢

    have hint : Integrable (Function.uncurry fun (q : AdeleRing (𝓞 F) F)
        (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) =>
        c κ * φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ)))
        (((fdPins F Φ₀).ν).prod μ) := by
      have : SecondCountableTopologyEither (AdeleRing (𝓞 F) F)
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
        secondCountableTopologyEither_of_right _ _
      have : OpensMeasurableSpace (AdeleRing (𝓞 F) F ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) := Prod.opensMeasurableSpace
      have hG : Continuous (Function.uncurry fun (q : AdeleRing (𝓞 F) F)
          (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) =>
          c κ * φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ))) :=
        (hc.comp continuous_snd).mul (hφc.comp
          ((((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).comp continuous_fst).mul
            continuous_const).mul (hyc.comp continuous_snd)))

      obtain ⟨B, hB⟩ := (hCb.prod isCompact_univ).exists_bound_of_continuousOn
        (s := Cb ×ˢ (Set.univ : Set (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)))
        hG.continuousOn
      have hae : ∀ᵐ p ∂(((fdPins F Φ₀).ν).prod μ), p.1 ∈ adelicBox F := by
        rw [ae_iff]
        have hset : {p : AdeleRing (𝓞 F) F ×
            (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) | ¬ p.1 ∈ adelicBox F} =
            (adelicBox F)ᶜ ×ˢ
              (Set.univ : Set (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) := by
          ext p; simp
        rw [hset, Measure.prod_prod]
        have hν0 : (fdPins F Φ₀).ν (adelicBox F)ᶜ = 0 := by
          show ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) (adelicBox F)ᶜ = 0
          rw [ProbabilityTheory.cond_apply (measurableSet_adelicBox F), Set.inter_compl_self,
            measure_empty, mul_zero]
        rw [hν0, zero_mul]
      refine Integrable.mono' (integrable_const B) hG.aestronglyMeasurable ?_
      filter_upwards [hae] with p hp
      exact hB p ⟨hsubb hp, Set.mem_univ _⟩
    have hswap := integral_integral_swap hint
    have hlhs : (fun q => constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) ψ g q) =
        fun q => ∫ κ, c κ * φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ)) ∂μ := by
      funext q
      show (∫ κ, c κ * φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ)) ∂μ) = _
      rfl
    rw [hlhs, hswap]
    have hin : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∫ q, c κ * φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ)) ∂(fdPins F Φ₀).ν) = 0 := by
      intro κ
      rw [integral_const_mul]
      have : (fun q => φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ))) =
          constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ
            (g * adelicArchGLIncl F (ι κ)) := by
        funext q
        show φ (unipotentGL2 q * g * adelicArchGLIncl F (ι κ)) =
          φ (unipotentGL2 q * (g * adelicArchGLIncl F (ι κ)))
        rw [mul_assoc]
      rw [this, h0 κ, mul_zero]
    simp only [hin, integral_zero]
  have hψsm : IsKfSmooth F ψ := by
    refine Subgroup.isOpen_mono ?_ hφ.1.2
    intro u hua
    rw [MulAction.mem_stabilizer_iff] at hua ⊢
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    have h1 := fun x' : AdelicGL2 (𝓞 F) F =>
      congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x') hua
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
      FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 ⊢
    show (∫ κ, c κ * φ (x * ↑u * adelicArchGLIncl F (ι κ)) ∂μ) =
      ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ
    refine integral_congr_ae (ae_of_all _ fun κ => ?_)
    show c κ * φ (x * ↑u * adelicArchGLIncl F (ι κ)) = c κ * φ (x * adelicArchGLIncl F (ι κ))
    rw [mul_assoc, commute_of_mem_finiteAdelicGL2Subgroup (u : finiteAdelicGL2Subgroup F).2 (ι κ),
      ← mul_assoc, h1]
  have hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    ⟨⟨⟨(isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mpr ⟨hψx, hψL2⟩, hψcusp⟩, hψsm⟩, hψc⟩
  refine ⟨hψm, ?_⟩

  set w := weightedMeasure F Φ₀ σ with hwdef
  have : SecondCountableTopologyEither (AdelicGL2 (𝓞 F) F)
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
    secondCountableTopologyEither_of_left _ _
  have : OpensMeasurableSpace (AdelicGL2 (𝓞 F) F ×
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) := Prod.opensMeasurableSpace
  have : SFinite w := by rw [hwdef]; unfold weightedMeasure; infer_instance
  have : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  set G : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →
      ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    fun κ => c κ • π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) with hGdef
  have hGc : Continuous G := hc.smul (hπc _)
  have hGint : Integrable G μ := by
    obtain ⟨κm, -, hκm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hGc.norm.continuousOn
    exact Integrable.mono' (integrable_const ‖G κm‖) hGc.aestronglyMeasurable
      (ae_of_all _ fun κ => hκm (Set.mem_univ κ))
  have hGcoe : ∀ κ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) =
      c κ • (memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1).toLp (rightTranslate F (y κ) φ) := by
    intro κ
    show ((c κ • π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
      Carrier F Φ₀ σ) = _
    rw [hπR κ, Submodule.coe_smul, toCuspSubcarrier_apply_coe]
    rfl

  apply Subtype.ext
  show ((∫ κ, G κ ∂μ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) =
    ((toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)
  rw [toCuspSubcarrier_apply_coe]
  have hL := ((cuspSubcarrier F hΦ₀ σ ξ).subtypeL.integral_comp_comm hGint).symm
  simp only [Submodule.subtypeL_apply] at hL
  rw [hL]
  change ∫ κ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∂μ =
    (memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).toLp ψ
  have hGint' : Integrable (fun κ => ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)) μ :=
    (cuspSubcarrier F hΦ₀ σ ξ).subtypeL.integrable_comp hGint

  refine ext_inner_left ℂ fun θ => ?_
  rw [← integral_inner hGint' θ]

  have hlhs : ∀ κ, ⟪θ, ((G κ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ)⟫_ℂ =
      ∫ x, (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ)) ∂w := by
    intro κ
    rw [hGcoe κ, inner_smul_right, MeasureTheory.L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_weightedMeasure_of_mem F hΦ₀ σ (hR κ).1.1.1).coeFn_toLp] with x hx
    rw [hx, rightTranslate_apply, RCLike.inner_apply]
    ring
  have hrhs : ⟪θ, (memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).toLp ψ⟫_ℂ =
      ∫ x, ∫ κ, (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ)) ∂μ ∂w := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_weightedMeasure_of_mem F hΦ₀ σ hψm.1.1.1).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, mul_comm, integral_const_mul]
  simp_rw [hlhs]
  rw [hrhs]

  have hH : Integrable (Function.uncurry fun (x : AdelicGL2 (𝓞 F) F)
      (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) =>
      (starRingEnd ℂ) (θ x) * (c κ * φ (x * y κ))) (w.prod μ) := by

    have hθm : AEStronglyMeasurable
        (fun p : AdelicGL2 (𝓞 F) F ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
          (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) (w.prod μ) :=
      (Lp.aestronglyMeasurable θ).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := w) (ν := μ))
    have hθ2 : MemLp (fun p : AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) 2 (w.prod μ) := by
      have hsq : eLpNorm (fun p : AdelicGL2 (𝓞 F) F ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
          (θ : AdelicGL2 (𝓞 F) F → ℂ) p.1) 2 (w.prod μ) ^ 2 < ⊤ := by
        rw [eLpNorm_two_pow_two (hφ := hθm), lintegral_prod _ (hθm.aemeasurable.enorm.pow_const 2)]
        simp only [lintegral_const]
        rw [lintegral_mul_const'' _ ((Lp.aestronglyMeasurable θ).aemeasurable.enorm.pow_const 2),
          ← eLpNorm_two_pow_two (φ := (θ : AdelicGL2 (𝓞 F) F → ℂ))
            (hφ := Lp.aestronglyMeasurable θ)]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (Lp.memLp θ).eLpNorm_lt_top) (measure_lt_top μ _)
      exact lt_of_le_of_ne le_top fun htop => by
        rw [htop] at hsq
        exact absurd hsq (by simp)
    have hθ2' : MemLp (fun p : AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        (starRingEnd ℂ) ((θ : AdelicGL2 (𝓞 F) F → ℂ) p.1)) 2 (w.prod μ) :=
      hθ2.star

    have hΦc : Continuous fun p : AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => c p.2 * φ (p.1 * y p.2) :=
      (hc.comp continuous_snd).mul hjoint
    have hΦ2 : MemLp (fun p : AdelicGL2 (𝓞 F) F ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        c p.2 * φ (p.1 * y p.2)) 2 (w.prod μ) := by
      have hmeas : Measurable fun p : AdelicGL2 (𝓞 F) F ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => ‖c p.2 * φ (p.1 * y p.2)‖ₑ ^ 2 :=
        hΦc.measurable.enorm.pow_const 2
      have hsq : eLpNorm (fun p : AdelicGL2 (𝓞 F) F ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
          c p.2 * φ (p.1 * y p.2)) 2 (w.prod μ) ^ 2 < ⊤ := by
        rw [eLpNorm_two_pow_two (hφ := hΦc.aestronglyMeasurable), lintegral_prod _ hmeas.aemeasurable,
          lintegral_lintegral_swap hmeas.aemeasurable]
        calc ∫⁻ κ, ∫⁻ x, ‖c κ * φ (x * y κ)‖ₑ ^ 2 ∂w ∂μ
            = ∫⁻ κ, ‖c κ‖ₑ ^ 2 * ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂w ∂μ := by
              refine lintegral_congr fun κ => ?_
              rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
              refine lintegral_congr fun x => ?_
              rw [enorm_mul, mul_pow]
          _ ≤ ∫⁻ κ, ENNReal.ofReal ‖c κc‖ ^ 2 * ENNReal.ofReal B ^ 2 ∂μ := by
              refine lintegral_mono fun κ => ?_
              gcongr
              · rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hC κ)
              · calc ∫⁻ x, ‖φ (x * y κ)‖ₑ ^ 2 ∂w =
                    eLpNorm (rightTranslate F (y κ) φ) 2 w ^ 2 := by
                      rw [eLpNorm_two_pow_two (φ := rightTranslate F (y κ) φ) (hφ :=
                        (hφc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)]
                      rfl
                  _ ≤ ENNReal.ofReal B ^ 2 := by gcongr; exact hnormR κ
          _ = ENNReal.ofReal ‖c κc‖ ^ 2 * ENNReal.ofReal B ^ 2 * μ Set.univ := lintegral_const _
          _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
              (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (measure_lt_top μ _)
      exact lt_of_le_of_ne le_top fun htop => by
        rw [htop] at hsq
        exact absurd hsq (by simp)

    have hprod := hθ2'.fun_mul hΦ2 (r := 1)
    have hint1 := memLp_one_iff_integrable.mp hprod
    exact hint1
  exact (integral_integral_swap hH).symm

end CuspidalSpectrum

end AutomorphicForm
