/-
  The level-spherical flat approximate identity on the cuspidal spectrum.

  Two rows on the limits `rightConv y (f n) g → y g` of a sequence `f` of *flat*, level-spherical,
  factorizable test functions:

  * `exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional`: for a finite-dimensional
    space `Y` of continuous functions invariant under a level subgroup
    `levelOne N ⊓ finiteAdelicGL2Subgroup` and inside an archimedean cut `archCutSubmodule tys`, there is
    such a sequence `f` (each `f n` factorizable, level-spherical of type `tys` at the level, and fixed by
    the flat twist `flat σ`) whose right convolutions converge pointwise to the identity on `Y`;
  * `exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact`: the same
    with the level subgroup given as `U = O ⊓ finiteAdelicGL2Subgroup` for a compact `U` and an open `O`.

  It is the approximate-identity statement the level-spherical argument spends: the flat test functions
  act as the identity on a finite-dimensional, uniformly continuous, level-invariant space.

  Transcribed from the two `S_` files below (pinned `aa2d8b3`, 860 + 935 lines). The two pins share 45
  declarations (≈474 lines): the level-spherical prelude is transcribed once, and the two rows differ in
  the level they quantify over.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.lean

  ## Port deltas

  **Premise imports, measured by BFS over this module's own import closure (FR-0229), not by memory.**
  Seven of the ten premises were already in the closure (182 modules). Five were not, and the
  `import` lines below were added for them; the first pin line is the use site that needs the name:

  * `isCompact_rowIsometrySubgroup_detOne` → `AutomorphicForm/Adelic/MaximalCompactFactors.lean`,
    this row's pin `S_..._finiteDimensional.lean:362` (`isCompact_rowIsometrySubgroup₀`, used through
    `compactSpace_Kw` at `:378`);
  * `continuous_and_hasCompactSupport_of_isFactorizableTestFn` → `AutomorphicForm/Adelic/TestFnTop.lean`,
    pin `:635`;
  * `exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq`
    → `AutomorphicForm/Adelic/RightConvProductIntegral.lean`, pin `:762–764`;
  * `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule`
    → `AutomorphicForm/Adelic/ArchCutReproducer.lean`, pin `:729–731`;
  * `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat`
    → `AutomorphicForm/Adelic/ArchPeterssonPairing.lean`, pin `:753–754`.

  The other five were in the closure as delivered: the Haar-invariance premise
  `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing`
  (`NumberTheory/AdelicHaar/ProductMeasure.lean`), `finiteDimensional_span_translates_of_mem_archCutSubmodule`
  (`AutomorphicForm/Adelic/ArchCutSpan.lean`), `TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult`
  (`AutomorphicForm/Adelic/IdeleNormDetGlue.lean`), `TateGlobal.continuous_ideleNorm_det`
  (`NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean`),
  `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat`
  (`AutomorphicForm/Adelic/Siegel/CentreCutCover.lean`) and
  `isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule`
  (`AutomorphicForm/Adelic/ArchApproximation.lean`).

  ## Renames and drops versus the pin

  The statements are the pins' verbatim; only the pipeline-label namespaces move.

  * `P2MW.S_<row>` (the search-stage label) goes; the declarations sit in the module's own
    `AutomorphicForm`, with the pin's inner namespaces renamed to subject names:
    `C2ABridge` → `FiniteLevelImage` (the image of the level subgroup under `glFin`),
    `R5bC` → `ArchLocalCompactness`, `R5bK` → `ArchRowIsometryHaar`. `ApproxIdentity` keeps its name.
    Since all four are only search-stage labels, no `spec/decl_markers.tsv` row is needed: the checker
    matches last names and the statements carry no qualified names.
  * `AutomorphicForm.C2ABridge.ideleNorm_det_eq_one_of_isCompact_of_mem`
    (pin `..._of_isCompact.lean:114`) is **not** transcribed: it is already ported as
    `NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem`
    (`NumberTheory/NumberField/TateGlobalIdeleNormDet.lean:43`), which is in the import closure and is
    the name both rows' proofs use (a `scaffold_audit.py` "satisfied by the import closure" row).
  * the pin's nine `private` declarations `rowIsoSet`, `mem_rowIsoSet_iff`, `continuous_entry`,
    `isClosed_rowIsoSet`, `norm_entry_le_one`, `isCompact_rowIsoSet`, `toUnit`, `continuous_toUnit`,
    `range_toUnit`, `isCompact_rowIsometrySubgroup₀` (pin `..._finiteDimensional.lean:283–366`) are
    **dropped**: they prove the general `[ProperSpace K]` statement, and the premise
    `isCompact_rowIsometrySubgroup_detOne F w` is that statement at `w.Completion`, the only instance
    the argument uses. Nothing else changes shape: `compactSpace_Kw` consumes the premise directly.
  * the pin's `private` declarations `inclAdelic` (`:393`), `inclAdelic_apply` (`:398`),
    `inclAdelic_mulSingle` (`:405`), `continuous_inclAdelic` (`:473`), `integral_mul_right_muK` (`:528`)
    and `integral_mul_left_muK` (`:533`) are **dropped as unreferenced**: the proofs use `inclArch` and
    `continuous_adelicArchGLIncl` directly, never their `inclAdelic` composite. (`move_dead.py` reads
    a transcribed copy of them as dead, and it is right.)
  * the pin's `private` `secondCountableTopology_placeGL` (`:233`), `secondCountableTopology_rowIsometrySubgroup₀`
    (`:243`), `secondCountableTopology_piRowIsometrySubgroup₀` (`:249`) and `isTopologicalGroup_archGL`
    (`:256`) are **dropped as unreferenced in this environment**: they are fed to the pin only through
    its `attribute [local instance]` preamble, and this port elaborates without them — the module is
    silent with the three remaining entries of that attribute line and with the four declarations
    deleted (`move_dead.py`: 4 declarations / 30 lines -> 0 / 0). The port keeps
    `t2Space_archMatrix'`, `locallyCompactSpace_archMatrix`, `locallyCompactSpace_archGL` and
    `secondCountableTopology_archGL`, which are referenced from the rows' proofs as well.

  **Proof-side substitutions** (no statement touched): the `haveI`/`letI` sites of the pin's proofs are
  written `have`/`let`, the linter's own suggestion and the always-safe direction (FR-0223). The pin's
  `attribute [-instance]`/`p2m_open`/`p2m_reactivate`/`attribute [-simp]` header and its
  `set_option maxHeartbeats 800000` are not carried: the pin's environment supplies instances and a
  simp set this one does not need, and no module carries a heartbeat floor (FR-0225).

  **Heartbeat probe** (gate 6, recorded, never installed — FR-0225): the module is silent in the edit
  loop at `-DmaxHeartbeats=200000` (the playbook cap) and still silent at 100000; at 50000 both rows
  abort at `whnf`, at the `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat`
  application in `havg` — so the margin is 2x and the cost sits in the two row proofs, not in a frozen
  statement. No `set_option maxHeartbeats` is installed.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalTestFn
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CarrierWindowMonotonicity
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.NumberTheory.AdelicHaar.ProductMeasure
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet
-- port deltas: the five premises that lay outside the delivered import closure
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.RightConvProductIntegral
import FLTForHuman.AutomorphicForm.Adelic.ArchCutReproducer
import FLTForHuman.AutomorphicForm.Adelic.ArchPeterssonPairing

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped Classical ENNReal NNReal ComplexConjugate InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

/-! ## The finite half: the level subgroup inside `GL₂(𝔸_f)` -/

namespace FiniteLevelImage

variable (F : Type) [Field F] [NumberField F]

def adelicFinGLIncl : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing F)) (MonoidHom.id _)

theorem glArch_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (adelicFinGLIncl F k) = 1 := by
  ext i j
  rfl

theorem glFin_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (adelicFinGLIncl F k) = k := by
  ext i j
  rfl

theorem adelicFinGLIncl_mem_finiteAdelicGL2Subgroup (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    adelicFinGLIncl F k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).2 (glArch_adelicFinGLIncl F k)

theorem continuous_adelicFinGLIncl : Continuous (adelicFinGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      ((adelicFinGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem adelicFinGLIncl_glFin_of_glArch_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glArch (𝓞 F) F g = 1) :
    adelicFinGLIncl F (glFin (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext ?_ rfl
  exact (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
    hg).symm

theorem adelicArchGLIncl_glArch_of_glFin_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glFin (𝓞 F) F g = 1) :
    adelicArchGLIncl F (glArch (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext rfl ?_
  exact (congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hg).symm

theorem image_glFin_eq_preimage (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F) :
    (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (U : Set (AdelicGL2 (𝓞 F) F)) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    show adelicFinGLIncl F (glFin (𝓞 F) F g) ∈ (U : Set (AdelicGL2 (𝓞 F) F))
    rw [adelicFinGLIncl_glFin_of_glArch_eq_one F g ((mem_finiteAdelicGL2Subgroup_iff F g).1 (hUf hg))]
    exact hg
  · intro hm
    exact ⟨adelicFinGLIncl F m, hm, glFin_adelicFinGLIncl F m⟩

theorem image_glFin_levelOne_inf (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.1
  · intro hm
    refine ⟨adelicFinGLIncl F m, ⟨?_, ?_⟩, glFin_adelicFinGLIncl F m⟩
    · show glFin (𝓞 F) F (adelicFinGLIncl F m) ∈ finiteLevelOne (𝓞 F) F N
      rw [glFin_adelicFinGLIncl]
      exact hm
    · exact (mem_finiteAdelicGL2Subgroup_iff F _).2 (glArch_adelicFinGLIncl F m)

theorem isOpen_image_glFin (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))) :
    IsOpen ((glFin (𝓞 F) F) '' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_eq_preimage F _ inf_le_right]
  have h : adelicFinGLIncl F ⁻¹' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (O : Set (AdelicGL2 (𝓞 F) F)) := by
    ext m
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, adelicFinGLIncl_mem_finiteAdelicGL2Subgroup F m⟩⟩
  rw [h]
  exact hO.preimage (continuous_adelicFinGLIncl F)

theorem isOpen_image_glFin_levelOne_inf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen ((glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_levelOne_inf]
  exact isOpen_finiteLevelOne (𝓞 F) F hN

theorem isClosed_image_glFin_levelOne_inf (N : Ideal (𝓞 F)) :
    IsClosed ((glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_levelOne_inf]
  exact isClosed_finiteLevelOne (𝓞 F) F N

theorem isCompact_image_glFin (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) :=
  hU.image (continuous_glFin (𝓞 F) F)

theorem isCompact_image_glFin_levelOne_inf (N : Ideal (𝓞 F)) :
    IsCompact ((glFin (𝓞 F) F) '' (↑(levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_levelOne_inf]
  exact isCompact_finiteLevelOne (𝓞 F) F N

end FiniteLevelImage

/-! ## Approximate identities on a locally compact group -/

namespace ApproxIdentity

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
variable (ν : Measure H) [IsFiniteMeasureOnCompacts ν] (x₀ : H)

theorem tendsto_integral_mul
    {ψ : ℕ → H → ℝ} (hcont : ∀ n, Continuous (ψ n))
    (hcs : ∀ n, HasCompactSupport (ψ n)) (hnn : ∀ n g, 0 ≤ ψ n g)
    (hint : ∀ n, (∫ g, ψ n g ∂ν) = 1)
    (hsupp : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U)
    {φ : H → ℂ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ g, φ g * (ψ n g : ℂ) ∂ν) atTop (𝓝 (φ x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV : φ ⁻¹' Metric.ball (φ x₀) (ε / 2) ∈ 𝓝 x₀ :=
    hφ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsupp _ hV)
  refine ⟨n₀, fun n hn => ?_⟩
  have hsub := hn₀ n hn
  have hψc : Continuous fun g => (ψ n g : ℂ) := Complex.continuous_ofReal.comp (hcont n)
  have hψcs : HasCompactSupport fun g => (ψ n g : ℂ) :=
    (hcs n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi₁ : Integrable (fun g => φ g * (ψ n g : ℂ)) ν :=
    (hφ.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have hi₂ : Integrable (fun g => φ x₀ * (ψ n g : ℂ)) ν :=
    (continuous_const.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have h1 : (∫ g, φ x₀ * (ψ n g : ℂ) ∂ν) = φ x₀ := by
    calc (∫ g, φ x₀ * (ψ n g : ℂ) ∂ν) = φ x₀ * ∫ g, (ψ n g : ℂ) ∂ν := integral_const_mul _ _
      _ = φ x₀ * ((∫ g, ψ n g ∂ν : ℝ) : ℂ) := by rw [integral_complex_ofReal]
      _ = φ x₀ := by rw [hint n, Complex.ofReal_one, mul_one]
  have hdiff : (∫ g, φ g * (ψ n g : ℂ) ∂ν) - φ x₀ = ∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν := by
    calc (∫ g, φ g * (ψ n g : ℂ) ∂ν) - φ x₀
        = (∫ g, φ g * (ψ n g : ℂ) ∂ν) - ∫ g, φ x₀ * (ψ n g : ℂ) ∂ν := by rw [h1]
      _ = ∫ g, (φ g * (ψ n g : ℂ) - φ x₀ * (ψ n g : ℂ)) ∂ν := (integral_sub hi₁ hi₂).symm
      _ = ∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν := by simp only [sub_mul]
  have hbound : ∀ g, ‖(φ g - φ x₀) * (ψ n g : ℂ)‖ ≤ ε / 2 * ψ n g := by
    intro g
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn n g)]
    by_cases hg : g ∈ tsupport (ψ n)
    · have hlt : ‖φ g - φ x₀‖ < ε / 2 := by
        have h := Metric.mem_ball.mp (hsub hg)
        rwa [dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_right hlt.le (hnn n g)
    · simp [image_eq_zero_of_notMem_tsupport hg]
  have hi₃ : Integrable (fun g => ‖(φ g - φ x₀) * (ψ n g : ℂ)‖) ν :=
    (((hφ.sub continuous_const).mul hψc).integrable_of_hasCompactSupport hψcs.mul_left).norm
  have hi₄ : Integrable (fun g => ε / 2 * ψ n g) ν :=
    (continuous_const.mul (hcont n)).integrable_of_hasCompactSupport (hcs n).mul_left
  rw [dist_eq_norm, hdiff]
  calc ‖∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν‖
      ≤ ∫ g, ‖(φ g - φ x₀) * (ψ n g : ℂ)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ε / 2 * ψ n g ∂ν := integral_mono hi₃ hi₄ hbound
    _ = ε / 2 * ∫ g, ψ n g ∂ν := integral_const_mul _ _
    _ = ε / 2 := by rw [hint n, mul_one]
    _ < ε := half_lt_self hε

theorem integral_pos [ν.IsOpenPosMeasure]
    {ψ : H → ℝ} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ) (hnn : ∀ g, 0 ≤ ψ g) (h0 : 0 < ψ x₀) :
    0 < ∫ g, ψ g ∂ν :=
  hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun g => hnn g) h0.ne'

theorem tendsto_inv_integral_mul_integral_mul [ν.IsOpenPosMeasure]
    {ψ : ℕ → H → ℝ} (hcont : ∀ n, Continuous (ψ n))
    (hcs : ∀ n, HasCompactSupport (ψ n)) (hnn : ∀ n g, 0 ≤ ψ n g) (h0 : ∀ n, 0 < ψ n x₀)
    (hsupp : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U)
    {φ : H → ℂ} (hφ : Continuous φ) :
    Tendsto (fun n => (∫ g, (ψ n g : ℂ) ∂ν)⁻¹ * ∫ g, φ g * (ψ n g : ℂ) ∂ν) atTop (𝓝 (φ x₀)) := by
  have hI : ∀ n, 0 < ∫ g, ψ n g ∂ν := fun n => integral_pos ν x₀ (hcont n) (hcs n) (hnn n) (h0 n)
  let ψ' : ℕ → H → ℝ := fun n g => ψ n g / ∫ g, ψ n g ∂ν
  have hcont' : ∀ n, Continuous (ψ' n) := fun n => (hcont n).div_const _
  have hcs' : ∀ n, HasCompactSupport (ψ' n) := fun n => by
    show HasCompactSupport fun g => ψ n g / ∫ g, ψ n g ∂ν
    simp_rw [div_eq_mul_inv]
    exact (hcs n).mul_right
  have hnn' : ∀ n g, 0 ≤ ψ' n g := fun n g => div_nonneg (hnn n g) (hI n).le
  have hint' : ∀ n, (∫ g, ψ' n g ∂ν) = 1 := fun n => by
    show (∫ g, ψ n g / ∫ g, ψ n g ∂ν ∂ν) = 1
    rw [integral_div, div_self (hI n).ne']
  have hsupp' : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ' n) ⊆ U := fun U hU =>
    (hsupp U hU).mono fun n hn => by
      refine Set.Subset.trans ?_ hn
      show tsupport (fun g => ψ n g / ∫ g, ψ n g ∂ν) ⊆ tsupport (ψ n)
      simp_rw [div_eq_mul_inv]
      exact tsupport_mul_subset_left
  have hlim := tendsto_integral_mul ν x₀ hcont' hcs' hnn' hint' hsupp' hφ
  refine hlim.congr fun n => ?_
  have hIc : ((∫ g, (ψ n g : ℂ) ∂ν)) = ((∫ g, ψ n g ∂ν : ℝ) : ℂ) := integral_complex_ofReal
  have hne : ((∫ g, ψ n g ∂ν : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hI n).ne'
  rw [hIc, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show φ g * ((ψ n g / ∫ g, ψ n g ∂ν : ℝ) : ℂ) = ((∫ g, ψ n g ∂ν : ℝ) : ℂ)⁻¹ * (φ g * (ψ n g : ℂ))
  push_cast
  field_simp

end ApproxIdentity

/-! ## Second countability and local compactness of the archimedean `GL₂` -/

namespace ArchLocalCompactness

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) := by
  have : ∀ w : InfinitePlace F, ProperSpace w.Completion :=
    fun w => NumberField.AdelicBox.properSpace_completion (K := F) w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

private theorem secondCountableTopology_archMatrix :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  have := secondCountableTopology_infiniteAdeleRing F
  exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))

omit [NumberField F] in
private theorem t2Space_archMatrix' : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := by
  have := secondCountableTopology_archMatrix F

  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_archMatrix :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem locallyCompactSpace_archGL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
  have := t2Space_archMatrix' F
  have := locallyCompactSpace_archMatrix F
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end ArchLocalCompactness

/-! ## The compact product over the archimedean places and its Haar measure -/

namespace ArchRowIsometryHaar

attribute [local instance] ArchLocalCompactness.t2Space_archMatrix' ArchLocalCompactness.locallyCompactSpace_archMatrix
  ArchLocalCompactness.locallyCompactSpace_archGL ArchLocalCompactness.secondCountableTopology_archGL

section Setting

variable (F : Type) [Field F] [NumberField F]

private abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

private abbrev Kprod : Type := Π w : InfinitePlace F, Kw F w

private instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (Kw F w) :=
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup_detOne F w)

omit [NumberField F] in
private theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w) (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

private def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F)
    (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

variable {F}

private theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

private theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

private theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

private theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem
      i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

end Setting

section HaarKprod

open MeasureTheory TopologicalSpace

variable (F : Type) [Field F] [NumberField F]

private abbrev KprodMeasurableSpace : MeasurableSpace (Kprod F) := borel (Kprod F)

attribute [local instance] KprodMeasurableSpace

omit [NumberField F] in
private theorem KprodBorelSpace : BorelSpace (Kprod F) := ⟨rfl⟩

attribute [local instance] KprodBorelSpace

private def KprodTop : PositiveCompacts (Kprod F) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by
    rw [interior_univ]
    exact ⟨1, Set.mem_univ 1⟩

private def muK : Measure (Kprod F) := Measure.haarMeasure (KprodTop F)

private theorem muK_univ : muK F Set.univ = 1 :=
  Measure.haarMeasure_self (K₀ := KprodTop F)

private instance isProbabilityMeasure_muK : IsProbabilityMeasure (muK F) := ⟨muK_univ F⟩

private instance isMulLeftInvariant_muK : (muK F).IsMulLeftInvariant := by
  unfold muK
  infer_instance

private instance isHaarMeasure_muK : (muK F).IsHaarMeasure := by
  unfold muK
  infer_instance

private theorem isMulRightInvariant_muK : (muK F).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable fun κ : Kprod F => κ * g := (continuous_mul_const g).measurable
  have : IsFiniteMeasureOnCompacts (Measure.map (· * g) (muK F)) := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (Measure.map (· * g) (muK F)).haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F))
      (muK F) (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ, muK_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F)) (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

end HaarKprod

section Inv

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] KprodMeasurableSpace KprodBorelSpace

private theorem isInvInvariant_muK : (muK F).IsInvInvariant := by
  have := isMulRightInvariant_muK F
  refine ⟨?_⟩
  have : IsFiniteMeasureOnCompacts (muK F).inv := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (muK F).inv.haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (muK F).inv (muK F)
      (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.inv_apply, Set.inv_univ, muK_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (muK F).inv (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

end Inv

end ArchRowIsometryHaar

/-! ## The rows -/

open NumberField.TateGlobal in
/-- **The finite-dimensional level.** A finite-dimensional uniformly continuous level-invariant space
inside an archimedean cut is the identity limit of flat level-spherical factorizable test functions. -/
theorem exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by
  classical
  have : FiniteDimensional ℂ ↥Y := hY
  set U : Subgroup (AdelicGL2 (𝓞 F) F) := levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F with hU

  have hUf : U ≤ finiteAdelicGL2Subgroup F := inf_le_right
  have hS : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = ↑(U.map (glFin (𝓞 F) F)) :=
    (Subgroup.coe_map _ _).symm
  have hSinv : ∀ z : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F z ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      glFin (𝓞 F) F z⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    intro z hz
    rw [hS, SetLike.mem_coe] at hz ⊢
    rw [map_inv]
    exact inv_mem hz
  have hSint : ∀ z : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F z ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      glFin (𝓞 F) F z ∈ finiteIntegralGL2 (𝓞 F) F := by
    rintro z ⟨u, hu, huz⟩
    rw [← huz]
    have hu1 : glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N := (mem_levelOne_iff.mp (inf_le_left (a := levelOne (𝓞 F) F N) hu))
    have hu0 := finiteLevelOne_le_finiteLevelZero (𝓞 F) F N hu1
    exact (mem_finiteIntegralGL2_iff).mpr ⟨hu0.1.integral, hu0.2.integral⟩
  have hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
    exact FiniteLevelImage.isOpen_image_glFin_levelOne_inf F hN
  have hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
    exact FiniteLevelImage.isCompact_image_glFin_levelOne_inf F N

  have : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  have : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Units.isEmbedding_embedProduct.t2Space
  have hcl : IsClosed ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := hUc.isClosed
  have hfin : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
    refine ⟨?_, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · exact ⟨_, hUo, hx, fun x' hx' => by rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun x' hx' => by
        rw [Set.indicator_of_notMem (show x' ∉ _ from hx'), Set.indicator_of_notMem hx]⟩
  have h1S : ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      glFin (𝓞 F) F (adelicArchGLIncl F x) ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
    fun x => ⟨1, U.one_mem, by rw [map_one, glFin_adelicArchGLIncl]⟩
  have hTcont : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ → Continuous ψ := by
    intro ψ hψ
    have hF := (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F
      (fun g => ψ (glArch (𝓞 F) F g) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g))
      ⟨ψ, _, hψ, hfin, fun g => rfl⟩).1
    have heq : ψ = fun x => ψ (glArch (𝓞 F) F (adelicArchGLIncl F x)) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
          (glFin (𝓞 F) F (adelicArchGLIncl F x)) := by
      funext x
      simp only [glArch_adelicArchGLIncl, Set.indicator_of_mem (h1S x), mul_one]
    rw [heq]
    exact hF.comp ArchRowIsometryHaar.continuous_adelicArchGLIncl

  let : MeasurableSpace (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.KprodMeasurableSpace F
  have : BorelSpace (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.KprodBorelSpace F
  let μ : Measure (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.muK F
  have : IsProbabilityMeasure μ := ArchRowIsometryHaar.isProbabilityMeasure_muK F
  have : μ.IsMulLeftInvariant := ArchRowIsometryHaar.isMulLeftInvariant_muK F
  have : μ.IsMulRightInvariant := ArchRowIsometryHaar.isMulRightInvariant_muK F
  have : μ.IsInvInvariant := ArchRowIsometryHaar.isInvInvariant_muK F
  let ι : ArchRowIsometryHaar.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) := ArchRowIsometryHaar.inclArch F
  have hιc : Continuous ι := ArchRowIsometryHaar.continuous_inclArch
  have hι : ∀ (κ : ArchRowIsometryHaar.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
    fun κ w => ArchRowIsometryHaar.archComponent_inclArch κ w

  have := ArchLocalCompactness.t2Space_archMatrix' F
  have := ArchLocalCompactness.locallyCompactSpace_archGL F
  have := ArchLocalCompactness.secondCountableTopology_archGL F
  let : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  have : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (GL (Fin 2) (InfiniteAdeleRing F))))
  let μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haarMeasure K₀
  have : μa.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  have : μa.Regular := Measure.regular_haarMeasure
  have : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  obtain ⟨E, hEfd, hYE, hEc, hEt, hEK⟩ : ∃ E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ ↥E ∧ Y ≤ E ∧ (∀ v ∈ E, Continuous v) ∧ E ≤ archCutSubmodule F tys ∧
      ∀ v ∈ E, ∀ κ : ArchRowIsometryHaar.Kprod F, (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E := by
    let X := AdelicGL2 (𝓞 F) F
    let Sp : (X → ℂ) → Submodule ℂ (X → ℂ) := fun x =>
      Submodule.span ℂ (Set.range fun κ : ArchRowIsometryHaar.Kprod F => fun g : X => x (g * adelicArchGLIncl F (ι κ)))
    have hSp : ∀ x : X → ℂ, Continuous x → x ∈ archCutSubmodule F tys →
        FiniteDimensional ℂ ↥(Sp x) ∧ (∀ v ∈ Sp x, Continuous v) ∧ Sp x ≤ archCutSubmodule F tys ∧
        ∀ v ∈ Sp x, ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ Sp x :=
      fun x hxc hxt => AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F ι hι tys x hxc hxt
    let b := Module.finBasis ℂ ↥Y
    let yv : Fin (Module.finrank ℂ ↥Y) → (X → ℂ) := fun i => (b i : X → ℂ)
    have hyvc : ∀ i, Continuous (yv i) := fun i => hYc _ (b i).2
    have hyvt : ∀ i, yv i ∈ archCutSubmodule F tys := fun i => hYt (b i).2
    let E : Submodule ℂ (X → ℂ) := ⨆ i, Sp (yv i)
    have : ∀ i, FiniteDimensional ℂ ↥(Sp (yv i)) := fun i => (hSp (yv i) (hyvc i) (hyvt i)).1
    have hEfd : FiniteDimensional ℂ ↥E := inferInstance
    let T : Submodule ℂ (X → ℂ) :=
      { carrier := {v | Continuous v ∧ v ∈ archCutSubmodule F tys ∧
          ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E}
        add_mem' := by
          rintro v w ⟨hvc, hvt, hvs⟩ ⟨hwc, hwt, hws⟩
          exact ⟨hvc.add hwc, Submodule.add_mem _ hvt hwt, fun κ => by
            have h__af := E.add_mem (hvs κ) (hws κ)
            simp only [Pi.add_apply] at h__af ⊢
            exact h__af⟩
        zero_mem' := ⟨continuous_zero, Submodule.zero_mem _, fun κ => by
          have h__af := E.zero_mem
          simp only [Pi.zero_apply] at h__af ⊢
          exact h__af⟩
        smul_mem' := by
          rintro a v ⟨hvc, hvt, hvs⟩
          exact ⟨hvc.const_smul a, Submodule.smul_mem _ a hvt, fun κ => by
            have h__af := E.smul_mem a (hvs κ)
            simp only [Pi.smul_apply] at h__af ⊢
            exact h__af⟩ }
    have hET : E ≤ T := by
      refine iSup_le fun i => ?_
      intro v hv
      obtain ⟨-, hc, ht, hs⟩ := hSp (yv i) (hyvc i) (hyvt i)
      exact ⟨hc v hv, ht hv, fun κ => (le_iSup (fun i => Sp (yv i)) i) (hs v hv κ)⟩
    have hind : ∀ v ∈ E, Continuous v ∧ v ∈ archCutSubmodule F tys ∧
        ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E :=
      fun v hv => hET hv
    have hyvE : ∀ i, yv i ∈ E := fun i =>
      (le_iSup (fun i => Sp (yv i)) i) (Submodule.subset_span ⟨1, by
        funext g
        show yv i (g * adelicArchGLIncl F (ι 1)) = yv i g
        rw [map_one, map_one, mul_one]⟩)
    refine ⟨E, hEfd, fun y hy => ?_, fun v hv => (hind v hv).1, fun v hv => (hind v hv).2.1,
      fun v hv κ => (hind v hv).2.2 κ⟩
    have hyeq : y = ∑ i, (b.repr ⟨y, hy⟩ i) • yv i := by
      have h0 := congrArg (fun z : ↥Y => (z : X → ℂ)) (b.sum_repr ⟨y, hy⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h0.symm
    rw [hyeq]
    exact E.sum_mem fun i _ => E.smul_mem _ (hyvE i)

  obtain ⟨e, heC, hecl, hefl, hedual, hety, hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μ ι hι tys E hEfd hEc hEt hEK

  obtain ⟨V, hV⟩ := (nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))).exists_antitone_basis
  have hVmem : ∀ n, V n ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)) := fun n => hV.mem n
  have hVshrink : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop, V n ⊆ W :=
    fun W hW => hV.eventually_subset hW
  choose h hh using fun n =>
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ (V n) (hVmem n)

  let avg : (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun ψ y =>
    ∫ p : ArchRowIsometryHaar.Kprod F × ArchRowIsometryHaar.Kprod F, e p.1 * e p.2 * ψ ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)
  have havg : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ →
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        ψ (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = ψ x) →
      (∀ x : GL (Fin 2) (InfiniteAdeleRing F), ψ x = conj (ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) →
      IsArchSphericalOfType F tys (avg ψ) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), avg ψ x = conj (avg ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
    intro ψ hψt hψc hψf
    have hA := AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μ ι hι tys e e heC heC ψ hψt
    have hB := AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μ ι hι σ e hecl hefl ψ hψc hψf
    exact ⟨⟨hA.1, hA.2 hedual hety, hB.1⟩, hB.2⟩
  let fa₁ : ℕ → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun n => avg (h n)
  have hsph : ∀ n, IsArchSphericalOfType F tys (fa₁ n) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), fa₁ n x = conj (fa₁ n x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) :=
    fun n => havg (h n) (hh n).1 (hh n).2.2.2.2.1 (hh n).2.2.2.2.2

  obtain ⟨C, hC, hbridge⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μ ι hιc hι μa U hUf hUo hUc

  have hψc : ∀ n, Continuous fun a => (h n a).re := fun n => Complex.continuous_re.comp (hTcont _ (hh n).1)
  have hψK : ∀ n, HasCompactSupport fun a => (h n a).re := fun n => (hh n).1.2.comp_left Complex.zero_re
  have hψ0 : ∀ n a, 0 ≤ (h n a).re := fun n a => ((hh n).2.1 a).2
  have hψ1 : ∀ n, 0 < (h n 1).re := fun n => (hh n).2.2.1
  have hψV : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop,
      tsupport (fun a => (h n a).re) ⊆ W := fun W hW =>
    (hVshrink W hW).mono fun n hn =>
      ((closure_mono (Function.support_comp_subset Complex.zero_re (h n))).trans (hh n).2.2.2.1).trans hn
  let I : ℕ → ℝ := fun n => ∫ a, (h n a).re ∂μa
  have hI : ∀ n, 0 < I n := fun n => ApproxIdentity.integral_pos μa 1 (hψc n) (hψK n) (hψ0 n) (hψ1 n)
  let c : ℕ → ℝ := fun n => C⁻¹ * (I n)⁻¹

  let f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ) := fun n g =>
    ((c n : ℂ) * fa₁ n (glArch (𝓞 F) F g)) *
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g)

  have hfaT : ∀ n, IsArchTestFactor F (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨⟨Φ, hΦ, hΦe⟩, hK⟩ := (hsph n).1.1
    exact ⟨⟨fun m => (c n : ℂ) * Φ m, contDiff_const.mul hΦ, fun g => by
      show (c n : ℂ) * fa₁ n g = (c n : ℂ) * Φ (archEntries F g)
      rw [hΦe]⟩, hK.mul_left⟩
  have hfaB : ∀ n, IsArchFactorBiFinite F tys (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨h1, h2⟩ := (hsph n).1.2.1
    exact ⟨(archFactorCutSubmodule F tys).smul_mem (c n : ℂ) h1,
      (archFactorDualCutSubmodule F tys).smul_mem (c n : ℂ) h2⟩
  have hfaC : ∀ n (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (fun x => (c n : ℂ) * fa₁ n x) (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) =
        (fun x => (c n : ℂ) * fa₁ n x) x := by
    intro n w k x
    show (c n : ℂ) * fa₁ n _ = (c n : ℂ) * fa₁ n x
    rw [(hsph n).1.2.2 w k x]

  have hNdet : ∀ y : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      ideleNorm F (Matrix.GeneralLinearGroup.det y) =
        ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F y))) := by
    intro y hy
    rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult y (hSint y hy),
      ideleNorm_det_eq_prod_archDetNorm_pow_mult _ (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
    simp only [NumberField.AdelicVolume.archDetNorm, glArch_adelicArchGLIncl]
  refine ⟨f, fun n => ⟨?_, ?_, ?_⟩, fun y hy g => ?_⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, _, hfaT n, hfin, fun g => rfl⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, hfaT n, hfaB n, hfaC n, fun g => rfl⟩
  ·
    funext y
    show conj (f n y⁻¹) * ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) = f n y
    by_cases hy : glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · have hy' := hSinv y hy
      have hy'' : (glFin (𝓞 F) F y)⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        simpa only [map_inv] using hy'
      simp only [f, map_inv, Set.indicator_of_mem hy, Set.indicator_of_mem hy'', mul_one, map_mul,
        Complex.conj_ofReal]
      rw [(hsph n).2 (glArch (𝓞 F) F y), ← hNdet y hy]
      ring
    · have hy' : glFin (𝓞 F) F y⁻¹ ∉ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
        fun h' => hy (by simpa only [inv_inv] using hSinv y⁻¹ h')
      simp only [f, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero, map_zero, zero_mul]
  ·
    have hyc : Continuous y := hYc y hy
    have hyU' : ∀ g' : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (g' * u) = y g' := fun g' u hu => hYU y hy g' u hu
    have hrep' : ∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * y (z * adelicArchGLIncl F (ι κ)) ∂μ = y z :=
      fun z => hrep y (hYE hy) z
    have hφ : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing F) => y (g * adelicArchGLIncl F a) :=
      hyc.comp ((continuous_const_mul g).comp ArchRowIsometryHaar.continuous_adelicArchGLIncl)
    have hstep1 : ∀ n, rightConv F y (f n) g =
        (c n : ℂ) * rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g := by
      intro n
      simp only [rightConv, f]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    have hstep2 : ∀ n, rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g =
        C * ∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa :=
      fun n => hbridge e heC (h n) (hTcont _ (hh n).1) (hh n).1.2 (hh n).2.2.2.2.1 y hyc hyU' hrep' g
    have hstep3 : ∀ n, (∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa) =
        ∫ a, y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ) ∂μa :=
      fun n => integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show y (g * adelicArchGLIncl F a) * h n a = y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ)
        rw [((hh n).2.1 a).1])
    have hlim := ApproxIdentity.tendsto_inv_integral_mul_integral_mul μa (1 : GL (Fin 2) (InfiniteAdeleRing F))
      hψc hψK hψ0 hψ1 hψV hφ
    simp only [map_one, mul_one] at hlim
    refine hlim.congr fun n => ?_
    have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    have hI0 : ((I n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hI n).ne'
    have hIc : (∫ a, ((h n a).re : ℂ) ∂μa) = ((I n : ℝ) : ℂ) := integral_complex_ofReal
    rw [hstep1, hstep2, hstep3, hIc]
    show ((I n : ℝ) : ℂ)⁻¹ * _ = ((C⁻¹ * (I n)⁻¹ : ℝ) : ℂ) * ((C : ℂ) * _)
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv, mul_mul_mul_comm, inv_mul_cancel₀ hC0, one_mul]

open NumberField.TateGlobal in
/-- **The compact level.** The same for a level subgroup written as `U = O ⊓ finiteAdelicGL2Subgroup`
with `U` compact and `O` open. -/
theorem exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys U (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by
  classical
  have : FiniteDimensional ℂ ↥Y := hY

  have hUf : U ≤ finiteAdelicGL2Subgroup F := hUO ▸ inf_le_right
  have hS : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = ↑(U.map (glFin (𝓞 F) F)) :=
    (Subgroup.coe_map _ _).symm
  have hSinv : ∀ z : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F z ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      glFin (𝓞 F) F z⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    intro z hz
    rw [hS, SetLike.mem_coe] at hz ⊢
    rw [map_inv]
    exact inv_mem hz
  have hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
    rw [hUO]
    exact FiniteLevelImage.isOpen_image_glFin F O hO
  have hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) :=
    FiniteLevelImage.isCompact_image_glFin F U hU

  have : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  have : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Units.isEmbedding_embedProduct.t2Space
  have hcl : IsClosed ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := hUc.isClosed
  have hfin : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
    refine ⟨?_, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · exact ⟨_, hUo, hx, fun x' hx' => by rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun x' hx' => by
        rw [Set.indicator_of_notMem (show x' ∉ _ from hx'), Set.indicator_of_notMem hx]⟩
  have h1S : ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      glFin (𝓞 F) F (adelicArchGLIncl F x) ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
    fun x => ⟨1, U.one_mem, by rw [map_one, glFin_adelicArchGLIncl]⟩
  have hTcont : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ → Continuous ψ := by
    intro ψ hψ
    have hF := (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F
      (fun g => ψ (glArch (𝓞 F) F g) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g))
      ⟨ψ, _, hψ, hfin, fun g => rfl⟩).1
    have heq : ψ = fun x => ψ (glArch (𝓞 F) F (adelicArchGLIncl F x)) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
          (glFin (𝓞 F) F (adelicArchGLIncl F x)) := by
      funext x
      simp only [glArch_adelicArchGLIncl, Set.indicator_of_mem (h1S x), mul_one]
    rw [heq]
    exact hF.comp ArchRowIsometryHaar.continuous_adelicArchGLIncl

  let : MeasurableSpace (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.KprodMeasurableSpace F
  have : BorelSpace (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.KprodBorelSpace F
  let μ : Measure (ArchRowIsometryHaar.Kprod F) := ArchRowIsometryHaar.muK F
  have : IsProbabilityMeasure μ := ArchRowIsometryHaar.isProbabilityMeasure_muK F
  have : μ.IsMulLeftInvariant := ArchRowIsometryHaar.isMulLeftInvariant_muK F
  have : μ.IsMulRightInvariant := ArchRowIsometryHaar.isMulRightInvariant_muK F
  have : μ.IsInvInvariant := ArchRowIsometryHaar.isInvInvariant_muK F
  let ι : ArchRowIsometryHaar.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) := ArchRowIsometryHaar.inclArch F
  have hιc : Continuous ι := ArchRowIsometryHaar.continuous_inclArch
  have hι : ∀ (κ : ArchRowIsometryHaar.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
    fun κ w => ArchRowIsometryHaar.archComponent_inclArch κ w

  have := ArchLocalCompactness.t2Space_archMatrix' F
  have := ArchLocalCompactness.locallyCompactSpace_archGL F
  have := ArchLocalCompactness.secondCountableTopology_archGL F
  let : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  have : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (GL (Fin 2) (InfiniteAdeleRing F))))
  let μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haarMeasure K₀
  have : μa.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  have : μa.Regular := Measure.regular_haarMeasure
  have : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  obtain ⟨E, hEfd, hYE, hEc, hEt, hEK⟩ : ∃ E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ ↥E ∧ Y ≤ E ∧ (∀ v ∈ E, Continuous v) ∧ E ≤ archCutSubmodule F tys ∧
      ∀ v ∈ E, ∀ κ : ArchRowIsometryHaar.Kprod F, (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E := by
    let X := AdelicGL2 (𝓞 F) F
    let Sp : (X → ℂ) → Submodule ℂ (X → ℂ) := fun x =>
      Submodule.span ℂ (Set.range fun κ : ArchRowIsometryHaar.Kprod F => fun g : X => x (g * adelicArchGLIncl F (ι κ)))
    have hSp : ∀ x : X → ℂ, Continuous x → x ∈ archCutSubmodule F tys →
        FiniteDimensional ℂ ↥(Sp x) ∧ (∀ v ∈ Sp x, Continuous v) ∧ Sp x ≤ archCutSubmodule F tys ∧
        ∀ v ∈ Sp x, ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ Sp x :=
      fun x hxc hxt => AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F ι hι tys x hxc hxt
    let b := Module.finBasis ℂ ↥Y
    let yv : Fin (Module.finrank ℂ ↥Y) → (X → ℂ) := fun i => (b i : X → ℂ)
    have hyvc : ∀ i, Continuous (yv i) := fun i => hYc _ (b i).2
    have hyvt : ∀ i, yv i ∈ archCutSubmodule F tys := fun i => hYt (b i).2
    let E : Submodule ℂ (X → ℂ) := ⨆ i, Sp (yv i)
    have : ∀ i, FiniteDimensional ℂ ↥(Sp (yv i)) := fun i => (hSp (yv i) (hyvc i) (hyvt i)).1
    have hEfd : FiniteDimensional ℂ ↥E := inferInstance
    let T : Submodule ℂ (X → ℂ) :=
      { carrier := {v | Continuous v ∧ v ∈ archCutSubmodule F tys ∧
          ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E}
        add_mem' := by
          rintro v w ⟨hvc, hvt, hvs⟩ ⟨hwc, hwt, hws⟩
          exact ⟨hvc.add hwc, Submodule.add_mem _ hvt hwt, fun κ => by
            have h__af := E.add_mem (hvs κ) (hws κ)
            simp only [Pi.add_apply] at h__af ⊢
            exact h__af⟩
        zero_mem' := ⟨continuous_zero, Submodule.zero_mem _, fun κ => by
          have h__af := E.zero_mem
          simp only [Pi.zero_apply] at h__af ⊢
          exact h__af⟩
        smul_mem' := by
          rintro a v ⟨hvc, hvt, hvs⟩
          exact ⟨hvc.const_smul a, Submodule.smul_mem _ a hvt, fun κ => by
            have h__af := E.smul_mem a (hvs κ)
            simp only [Pi.smul_apply] at h__af ⊢
            exact h__af⟩ }
    have hET : E ≤ T := by
      refine iSup_le fun i => ?_
      intro v hv
      obtain ⟨-, hc, ht, hs⟩ := hSp (yv i) (hyvc i) (hyvt i)
      exact ⟨hc v hv, ht hv, fun κ => (le_iSup (fun i => Sp (yv i)) i) (hs v hv κ)⟩
    have hind : ∀ v ∈ E, Continuous v ∧ v ∈ archCutSubmodule F tys ∧
        ∀ κ : ArchRowIsometryHaar.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E :=
      fun v hv => hET hv
    have hyvE : ∀ i, yv i ∈ E := fun i =>
      (le_iSup (fun i => Sp (yv i)) i) (Submodule.subset_span ⟨1, by
        funext g
        show yv i (g * adelicArchGLIncl F (ι 1)) = yv i g
        rw [map_one, map_one, mul_one]⟩)
    refine ⟨E, hEfd, fun y hy => ?_, fun v hv => (hind v hv).1, fun v hv => (hind v hv).2.1,
      fun v hv κ => (hind v hv).2.2 κ⟩
    have hyeq : y = ∑ i, (b.repr ⟨y, hy⟩ i) • yv i := by
      have h0 := congrArg (fun z : ↥Y => (z : X → ℂ)) (b.sum_repr ⟨y, hy⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h0.symm
    rw [hyeq]
    exact E.sum_mem fun i _ => E.smul_mem _ (hyvE i)

  obtain ⟨e, heC, hecl, hefl, hedual, hety, hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μ ι hι tys E hEfd hEc hEt hEK

  obtain ⟨V, hV⟩ := (nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))).exists_antitone_basis
  have hVmem : ∀ n, V n ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)) := fun n => hV.mem n
  have hVshrink : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop, V n ⊆ W :=
    fun W hW => hV.eventually_subset hW
  choose h hh using fun n =>
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ (V n) (hVmem n)

  let avg : (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun ψ y =>
    ∫ p : ArchRowIsometryHaar.Kprod F × ArchRowIsometryHaar.Kprod F, e p.1 * e p.2 * ψ ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)
  have havg : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ →
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        ψ (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = ψ x) →
      (∀ x : GL (Fin 2) (InfiniteAdeleRing F), ψ x = conj (ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) →
      IsArchSphericalOfType F tys (avg ψ) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), avg ψ x = conj (avg ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
    intro ψ hψt hψc hψf
    have hA := AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μ ι hι tys e e heC heC ψ hψt
    have hB := AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μ ι hι σ e hecl hefl ψ hψc hψf
    exact ⟨⟨hA.1, hA.2 hedual hety, hB.1⟩, hB.2⟩
  let fa₁ : ℕ → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun n => avg (h n)
  have hsph : ∀ n, IsArchSphericalOfType F tys (fa₁ n) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), fa₁ n x = conj (fa₁ n x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) :=
    fun n => havg (h n) (hh n).1 (hh n).2.2.2.2.1 (hh n).2.2.2.2.2

  obtain ⟨C, hC, hbridge⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μ ι hιc hι μa U hUf hUo hUc

  have hψc : ∀ n, Continuous fun a => (h n a).re := fun n => Complex.continuous_re.comp (hTcont _ (hh n).1)
  have hψK : ∀ n, HasCompactSupport fun a => (h n a).re := fun n => (hh n).1.2.comp_left Complex.zero_re
  have hψ0 : ∀ n a, 0 ≤ (h n a).re := fun n a => ((hh n).2.1 a).2
  have hψ1 : ∀ n, 0 < (h n 1).re := fun n => (hh n).2.2.1
  have hψV : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop,
      tsupport (fun a => (h n a).re) ⊆ W := fun W hW =>
    (hVshrink W hW).mono fun n hn =>
      ((closure_mono (Function.support_comp_subset Complex.zero_re (h n))).trans (hh n).2.2.2.1).trans hn
  let I : ℕ → ℝ := fun n => ∫ a, (h n a).re ∂μa
  have hI : ∀ n, 0 < I n := fun n => ApproxIdentity.integral_pos μa 1 (hψc n) (hψK n) (hψ0 n) (hψ1 n)
  let c : ℕ → ℝ := fun n => C⁻¹ * (I n)⁻¹

  let f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ) := fun n g =>
    ((c n : ℂ) * fa₁ n (glArch (𝓞 F) F g)) *
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g)

  have hfaT : ∀ n, IsArchTestFactor F (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨⟨Φ, hΦ, hΦe⟩, hK⟩ := (hsph n).1.1
    exact ⟨⟨fun m => (c n : ℂ) * Φ m, contDiff_const.mul hΦ, fun g => by
      show (c n : ℂ) * fa₁ n g = (c n : ℂ) * Φ (archEntries F g)
      rw [hΦe]⟩, hK.mul_left⟩
  have hfaB : ∀ n, IsArchFactorBiFinite F tys (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨h1, h2⟩ := (hsph n).1.2.1
    exact ⟨(archFactorCutSubmodule F tys).smul_mem (c n : ℂ) h1,
      (archFactorDualCutSubmodule F tys).smul_mem (c n : ℂ) h2⟩
  have hfaC : ∀ n (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (fun x => (c n : ℂ) * fa₁ n x) (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) =
        (fun x => (c n : ℂ) * fa₁ n x) x := by
    intro n w k x
    show (c n : ℂ) * fa₁ n _ = (c n : ℂ) * fa₁ n x
    rw [(hsph n).1.2.2 w k x]

  have hNdet : ∀ y : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      ideleNorm F (Matrix.GeneralLinearGroup.det y) =
        ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F y))) := by
    rintro y ⟨u, hu, huy⟩
    have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).1 (hUf hu)
    have ha : adelicArchGLIncl F (glArch (𝓞 F) F y) = y * u⁻¹ := by
      have h := FiniteLevelImage.adelicArchGLIncl_glArch_of_glFin_eq_one F (y * u⁻¹)
        (by rw [map_mul, map_inv, huy, mul_inv_cancel])
      rwa [map_mul, map_inv, hu1, inv_one, mul_one] at h
    have hdu : ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 :=
      NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F U hU u hu
    conv_lhs => rw [show y = adelicArchGLIncl F (glArch (𝓞 F) F y) * u by rw [ha, inv_mul_cancel_right]]
    rw [map_mul, ideleNorm_mul, hdu, mul_one]
  refine ⟨f, fun n => ⟨?_, ?_, ?_⟩, fun y hy g => ?_⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, _, hfaT n, hfin, fun g => rfl⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, hfaT n, hfaB n, hfaC n, fun g => rfl⟩
  ·
    funext y
    show conj (f n y⁻¹) * ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) = f n y
    by_cases hy : glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · have hy' := hSinv y hy
      have hy'' : (glFin (𝓞 F) F y)⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        simpa only [map_inv] using hy'
      simp only [f, map_inv, Set.indicator_of_mem hy, Set.indicator_of_mem hy'', mul_one, map_mul,
        Complex.conj_ofReal]
      rw [(hsph n).2 (glArch (𝓞 F) F y), ← hNdet y hy]
      ring
    · have hy' : glFin (𝓞 F) F y⁻¹ ∉ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
        fun h' => hy (by simpa only [inv_inv] using hSinv y⁻¹ h')
      simp only [f, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero, map_zero, zero_mul]
  ·
    have hyc : Continuous y := hYc y hy
    have hyU' : ∀ g' : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (g' * u) = y g' := fun g' u hu => hYU y hy g' u hu
    have hrep' : ∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * y (z * adelicArchGLIncl F (ι κ)) ∂μ = y z :=
      fun z => hrep y (hYE hy) z
    have hφ : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing F) => y (g * adelicArchGLIncl F a) :=
      hyc.comp ((continuous_const_mul g).comp ArchRowIsometryHaar.continuous_adelicArchGLIncl)
    have hstep1 : ∀ n, rightConv F y (f n) g =
        (c n : ℂ) * rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g := by
      intro n
      simp only [rightConv, f]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    have hstep2 : ∀ n, rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g =
        C * ∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa :=
      fun n => hbridge e heC (h n) (hTcont _ (hh n).1) (hh n).1.2 (hh n).2.2.2.2.1 y hyc hyU' hrep' g
    have hstep3 : ∀ n, (∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa) =
        ∫ a, y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ) ∂μa :=
      fun n => integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show y (g * adelicArchGLIncl F a) * h n a = y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ)
        rw [((hh n).2.1 a).1])
    have hlim := ApproxIdentity.tendsto_inv_integral_mul_integral_mul μa (1 : GL (Fin 2) (InfiniteAdeleRing F))
      hψc hψK hψ0 hψ1 hψV hφ
    simp only [map_one, mul_one] at hlim
    refine hlim.congr fun n => ?_
    have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    have hI0 : ((I n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hI n).ne'
    have hIc : (∫ a, ((h n a).re : ℂ) ∂μa) = ((I n : ℝ) : ℂ) := integral_complex_ofReal
    rw [hstep1, hstep2, hstep3, hIc]
    show ((I n : ℝ) : ℂ)⁻¹ * _ = ((C⁻¹ * (I n)⁻¹ : ℝ) : ℂ) * ((C : ℂ) * _)
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv, mul_mul_mul_comm, inv_mul_cancel₀ hC0, one_mul]

end AutomorphicForm
