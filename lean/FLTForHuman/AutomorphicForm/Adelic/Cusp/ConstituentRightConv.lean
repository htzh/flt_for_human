/-
  Right convolution on a cuspidal constituent: injectivity and invariance.

  The rows here are the test-function side of `IsCuspConstituent`: a cuspidal constituent is a
  subrepresentation of the cuspidal `K`-finite span, closed under right convolution by
  factorizable arch-bi-finite test functions, and the facts below say what that closure buys.

  * `exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv` — the reflexion
    convolution `f' * (x ↦ f x⁻¹)` of two factorizable arch-bi-finite test functions is again
    factorizable and arch-bi-finite;
  * `exists_rightConv_injOn_of_finiteDimensional_of_le` and
    `..._of_forall_apply_mul_eq` — a finite-dimensional, uniformly continuous, level-invariant
    space inside an archimedean cut admits a level-spherical factorizable test function fixed
    by the flat twist whose right convolution is injective on it (the second with the level
    written as `U = O ⊓ finiteAdelicGL2Subgroup` for compact `U` and open `O`);
  * `continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` —
    the cuspidal `K`-finite span consists of continuous functions and is stable under right
    translation in the smooth cusp automorphic class;
  * `forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` — a constituent with one
    nonzero real-archimedean-unipotent-invariant vector is invariant under the whole real
    `GL₂⁺`;
  * `isCuspConstituent_productionPinsOf_mono` — cuspidality is monotone in the compact set
    `D` of the production pins.

  Build record (AF89C).

  * Step 1 transcribed the pins' remaining declarations at their last names, under subject
    sub-namespaces (the pins' `FACT`/`IsArchTestFactor` → `ArchTestFactor`, `InvSub22` →
    `RealInvariant`, `C8Mono` → `Mono`): `scaffold_audit` went from 6 declared / 9 satisfied by
    the import closure to `complete`, and step 2 discharges every proof obligation.
  * The two pins' engines named `main` (`…_mem_cuspKFiniteSubmodule.lean:119`,
    `…_of_isCuspConstituent_of_exists.lean:110`) are not separate declarations: each pin's
    `solution` statement *is* its `main` statement, `scaffold_audit` already credits the last
    name `main` through the import closure, and the two proofs are inlined in the rows.
  * The only pin-`private` helper is `IsArchTestFactor.continuous` (pin 1 `:42`), transcribed
    `private` as `ArchTestFactor.continuous`.
  * Two statement-neutral substitutions inside proofs: `continuous_mul_left` →
    `continuous_const_mul` (FR-0231's rename family) and the pins' `letI`/`haveI` → `let`/`have`
    (FR-0223). No heartbeat floor and no linter option is installed (FR-0225).
  * Heartbeat probe (never installed), read with
    `lake env lean -DautoImplicit=false -DmaxHeartbeats=N <module>`: silent at `N = 10000`,
    fails at `N / 2 = 5000` (`…ConstituentRightConv.lean:108:0: (deterministic) timeout at
    whnf`, the C1 row); at `7500` the first failure is the C2 row (`:174:6`), so the natural
    per-declaration cost of the two heaviest rows sits just below `10000`. Silent at the
    edit-loop cap `200000`, where the gates below were read.

  ## Port deltas

  * No `import` line was added: the scaffold's seven imports carry every premise (C2/C3 in
    `Cusp/LevelSphericalLimit`; C1's reflexion engine in `RightTranslateSpan`; the arch/finite
    measure split in `AdelicHaar/ArchFiniteFactorization`; the injectivity engine in
    `Analysis/Normed/Operator/CompactFiniteDimensional`; `TestFactorIntegral`/`TestFnTop`).
  * One non-import delta: `Classical` added to the file's `open scoped` line. The archimedean
    `ContDiff`-on-`archEntries` lemmas of C1 need
    `NormedAddCommGroup (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)`, whose instance search
    needs the classical decidability instances (FR-0224 trap 2). Statement text is unchanged —
    `check_port` reads 24 ok / 0 mismatch / 0 missing with and without it.
  * No pin wire line was added or re-spelled.

  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalLimit
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateSpan
import FLTForHuman.Analysis.Normed.Operator.CompactFiniteDimensional
import FLTForHuman.AutomorphicForm.Adelic.TestFactorIntegral
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.NumberTheory.AdelicHaar.ArchFiniteFactorization

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Manifold Classical

namespace AutomorphicForm.CuspidalConstituent

/-! ## C1 — the reflexion convolution of two factorizable test functions -/

namespace ArchTestFactor

variable (F : Type) [Field F] [NumberField F]

private theorem continuous {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have hΦa : fa = Φ ∘ archEntries F := funext hfa
  rw [hΦa]
  exact hΦ.continuous.comp (continuous_archEntries F)

theorem const_mul {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (fun x => c * fa x) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩ := h
  refine ⟨⟨fun M => c * Φ M, contDiff_const.mul hΦ, fun x => ?_⟩, ?_⟩
  · show c * fa x = c * Φ (archEntries F x)
    rw [hfa]
  · exact hsupp.mul_left

end ArchTestFactor

theorem exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hf' : IsFactorizableTestFn F f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F,
      IsFactorizableTestFn F (rightConv F f' (fun x => f x⁻¹)) ∧
      IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨hfc', hfs'⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f' hf'
  obtain ⟨tys'', hb⟩ := exists_isArchBiFinite_rightConv_comp_inv F f f' tys tys' hfc hfs hbf hfc' hfs' hbf'
  refine ⟨tys'', ?_, hb⟩
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  obtain ⟨fa', ff', hfa', hff', hf'eq⟩ := hf'
  let : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  have : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  have : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  have : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K₀a⟩ :=
    (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (GL (Fin 2) (InfiniteAdeleRing F))))
  let μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haarMeasure K₀a
  have : μa.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀a
  have : μa.Regular := Measure.regular_haarMeasure
  let : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := borel _
  have : BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := ⟨rfl⟩
  have : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  have : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  have : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K₀f⟩ :=
    (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
  let μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Measure.haarMeasure K₀f
  have : μf.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀f
  have : μf.Regular := Measure.regular_haarMeasure
  obtain ⟨c, hc, hsplit⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral F μa μf
  let Ca : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun x => ∫ a, fa' (x * a) * fa a⁻¹ ∂μa
  let Cf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ := fun x => ∫ b, ff' (x * b) * ff b⁻¹ ∂μf
  have hconv : rightConv F f' (fun x => f x⁻¹) =
      fun z => ((c : ℂ) * Ca (glArch (𝓞 F) F z)) * Cf (glFin (𝓞 F) F z) := by
    funext z
    have hint : (fun y => f' (z * y) * f y⁻¹) =
        fun y => (fun a => fa' (glArch (𝓞 F) F z * a) * fa a⁻¹) (glArch (𝓞 F) F y) *
          (fun b => ff' (glFin (𝓞 F) F z * b) * ff b⁻¹) (glFin (𝓞 F) F y) := by
      funext y
      simp only [hf'eq, hfeq, map_mul, map_inv]
      ring
    rw [rightConv_apply]
    show (∫ y, f' (z * y) * f y⁻¹ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = _
    rw [hint]
    have hs := hsplit (fun a => fa' (glArch (𝓞 F) F z * a) * fa a⁻¹)
      (fun b => ff' (glFin (𝓞 F) F z * b) * ff b⁻¹)
    rw [hs]
    show (c : ℂ) * ((∫ a, fa' (glArch (𝓞 F) F z * a) * fa a⁻¹ ∂μa) *
      ∫ b, ff' (glFin (𝓞 F) F z * b) * ff b⁻¹ ∂μf) = _
    ring
  rw [hconv]
  refine ⟨fun x => (c : ℂ) * Ca x, Cf, ?_, ?_, fun z => rfl⟩
  · have h1 := AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport F μa fa'
      (fun a => fa a⁻¹) hfa' ((ArchTestFactor.continuous F hfa).comp continuous_inv)
      (hfa.2.comp_homeomorph (Homeomorph.inv _))
    exact ArchTestFactor.const_mul F h1 c
  · exact AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport F μf ff'
      (fun b => ff b⁻¹) hff' (hff.2.comp_homeomorph (Homeomorph.inv _))

/-! ## C2, C3 — injectivity of the right convolution on a finite-dimensional cut -/

theorem exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys U f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by
  have hYfd : FiniteDimensional ℂ ↥Y := hY
  obtain ⟨f, hf, hlim⟩ :=
    AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
      F U hU O hO hUO tys σ Y hY hYc hYU hYt
  let : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ n, ∀ y : AdelicGL2 (𝓞 F) F → ℂ, Continuous y → ∀ g : AdelicGL2 (𝓞 F) F,
      Integrable (fun x => y (g * x) * f n x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro n y hy g
    obtain ⟨hfc, hfK⟩ :=
      AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F (f n) (hf n).1
    refine Continuous.integrable_of_hasCompactSupport ((hy.comp (continuous_const_mul g)).mul hfc) ?_
    exact hfK.mul_left
  have hadd : ∀ n (y₁ y₂ : AdelicGL2 (𝓞 F) F → ℂ), Continuous y₁ → Continuous y₂ →
      rightConv F (y₁ + y₂) (f n) = rightConv F y₁ (f n) + rightConv F y₂ (f n) := by
    intro n y₁ y₂ h₁ h₂
    funext g
    simp only [rightConv, Pi.add_apply, add_mul]
    exact integral_add (hint n y₁ h₁ g) (hint n y₂ h₂ g)
  have hsmul : ∀ n (c : ℂ) (y : AdelicGL2 (𝓞 F) F → ℂ),
      rightConv F (c • y) (f n) = c • rightConv F y (f n) := by
    intro n c y
    funext g
    simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  let T : ℕ → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) := fun n =>
    { toFun := fun y => rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) (f n)
      map_add' := fun y₁ y₂ => by
        simpa only [Submodule.coe_add] using hadd n _ _ (hYc _ y₁.2) (hYc _ y₂.2)
      map_smul' := fun c y => by
        simpa only [Submodule.coe_smul, RingHom.id_apply] using hsmul n c _ }
  have hT : ∀ (y : ↥Y) (x : AdelicGL2 (𝓞 F) F),
      Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : AdelicGL2 (𝓞 F) F → ℂ) x)) :=
    fun y x => hlim y y.2 x
  obtain ⟨n, hn⟩ := LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional Y T hT
  refine ⟨f n, (hf n).1, (hf n).2.1, (hf n).2.2, fun y hy h0 => ?_⟩
  have := hn ⟨y, hy⟩ h0
  exact congrArg Subtype.val this

theorem exists_rightConv_injOn_of_finiteDimensional_of_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : Y ≤ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f ∧
      flat F σ f = f ∧
      ∀ y ∈ Y, rightConv F y f = 0 → y = 0 := by
  have hYfd : FiniteDimensional ℂ ↥Y := hY
  obtain ⟨f, hf, hlim⟩ :=
    AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional F N hN tys σ Y
      hY hYc (fun y hy g k hk => hYU hy g k hk) hYt
  let : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ n, ∀ y : AdelicGL2 (𝓞 F) F → ℂ, Continuous y → ∀ g : AdelicGL2 (𝓞 F) F,
      Integrable (fun x => y (g * x) * f n x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro n y hy g
    obtain ⟨hfc, hfK⟩ :=
      AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F (f n) (hf n).1
    refine Continuous.integrable_of_hasCompactSupport ((hy.comp (continuous_const_mul g)).mul hfc) ?_
    exact hfK.mul_left
  have hadd : ∀ n (y₁ y₂ : AdelicGL2 (𝓞 F) F → ℂ), Continuous y₁ → Continuous y₂ →
      rightConv F (y₁ + y₂) (f n) = rightConv F y₁ (f n) + rightConv F y₂ (f n) := by
    intro n y₁ y₂ h₁ h₂
    funext g
    simp only [rightConv, Pi.add_apply, add_mul]
    exact integral_add (hint n y₁ h₁ g) (hint n y₂ h₂ g)
  have hsmul : ∀ n (c : ℂ) (y : AdelicGL2 (𝓞 F) F → ℂ),
      rightConv F (c • y) (f n) = c • rightConv F y (f n) := by
    intro n c y
    funext g
    simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  let T : ℕ → (↥Y →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) := fun n =>
    { toFun := fun y => rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) (f n)
      map_add' := fun y₁ y₂ => by
        simpa only [Submodule.coe_add] using hadd n _ _ (hYc _ y₁.2) (hYc _ y₂.2)
      map_smul' := fun c y => by
        simpa only [Submodule.coe_smul, RingHom.id_apply] using hsmul n c _ }
  have hT : ∀ (y : ↥Y) (x : AdelicGL2 (𝓞 F) F),
      Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : AdelicGL2 (𝓞 F) F → ℂ) x)) :=
    fun y x => hlim y y.2 x
  obtain ⟨n, hn⟩ := LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional Y T hT
  refine ⟨f n, (hf n).1, (hf n).2.1, (hf n).2.2, fun y hy h0 => ?_⟩
  have := hn ⟨y, hy⟩ h0
  exact congrArg Subtype.val this

/-! ## C4 — continuity and smooth cusp membership of the `K`-finite span -/

section CuspSpan

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem integrable_slice_cond_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hcont : Continuous (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) :=
    hφ.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)
  have h1 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) C
      (adelicAddHaar (𝓞 F) F) :=
    hcont.continuousOn.integrableOn_compact hC
  have h2 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := h1.mono_set hBC
  unfold ProbabilityTheory.cond
  exact h2.integrable.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

end CuspSpan

theorem continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ cuspKFiniteSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ (rightTranslate K g x) := by
  refine Submodule.span_induction
    (p := fun φ _ => Continuous φ ∧
      ∀ g : AdelicGL2 (𝓞 K) K, IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ
        (rightTranslate K g φ))
    ?_ ?_ ?_ ?_ hx
  · intro φ hφ
    exact ⟨hφ.2.1, hφ.1⟩
  · refine ⟨continuous_const, fun g => ?_⟩
    rw [rightTranslate_zero]
    exact isSmoothCuspAutomorphicFnAt_zero K (productionPinsOf K D U gen (adelicBox K)) ξ
  · intro u w _ _ hu hw
    refine ⟨hu.1.add hw.1, fun g => ?_⟩
    rw [rightTranslate_add]
    exact AutomorphicForm.IsotypicSpanForms.isSmoothCuspAutomorphicFnAt_add D U gen ξ
      (hu.1.comp (continuous_id.mul continuous_const)) (hw.1.comp (continuous_id.mul continuous_const))
      (hu.2 g) (hw.2 g)
  · intro c u _ hu
    refine ⟨hu.1.const_smul c, fun g => ?_⟩
    rw [rightTranslate_smul]
    exact AutomorphicForm.IsotypicSpanForms.isSmoothCuspAutomorphicFnAt_smul D U gen ξ c (hu.2 g)

/-! ## C5 — archimedean `GL₂⁺`-invariance from one invariant vector -/

namespace RealInvariant

variable {F : Type} [Field F] [NumberField F]
variable {w : InfinitePlace F} (hw : w.IsReal)

omit [NumberField F] in
theorem glArch_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have hpt := congrFun (congrFun (congrArg
    (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion)) (H v)) i) j
  rwa [archComponent_apply, archComponent_apply] at hpt

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

open NumberField.InfinitePlace.Completion in
theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

open NumberField.InfinitePlace.Completion in
theorem archComponent_archRealGLAt_self (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_archRealGLAt_of_ne {v : InfinitePlace F} (hv : v ≠ w) (m : GL (Fin 2) ℝ) :
    archComponent F v (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hv]

open NumberField.InfinitePlace.Completion in
theorem symm_apply_proj (y : AdelicGL2 (𝓞 F) F) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw y) = archComponent F w (glArch (𝓞 F) F y) := by
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (archComponent F w (glArch (𝓞 F) F y))) = _
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

theorem archRealGLAt_mul (h : GL (Fin 2) ℝ) (y : AdelicGL2 (𝓞 F) F) :
    archRealGLAt hw h * y = y * archRealGLAt hw ((archRealProjAt hw y)⁻¹ * h * archRealProjAt hw y) := by
  refine eq_of_glArch_eq_of_glFin_eq F (glArch_ext fun v => ?_) ?_
  · simp only [map_mul, map_inv]
    by_cases hv : v = w
    · subst hv
      simp only [archComponent_archRealGLAt_self, symm_apply_proj]
      rw [mul_assoc, mul_inv_cancel_left]
    · simp only [archComponent_archRealGLAt_of_ne hw hv, inv_one, one_mul, mul_one]
  · simp only [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul, mul_one]

theorem det_conj (h a : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    Matrix.GeneralLinearGroup.det (a⁻¹ * h * a) = 1 := by
  rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel]

omit [NumberField F] in
open NumberField.InfinitePlace.Completion in
theorem det_glEquiv_eq_one (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)) = 1 := by
  have hd := ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  change (RingEquiv.mapMatrix (m := Fin 2) (ringEquivRealOfIsReal hw)
    ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)).det = 1
  rw [← RingEquiv.map_det, hd, map_one]

def W (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {x | x ∈ V ∧ ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ),
    Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g}
  zero_mem' := ⟨V.zero_mem, fun _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun g h hh => by
    simp only [Pi.add_apply, ha.2 g h hh, hb.2 g h hh]⟩
  smul_mem' := fun c {a} ha => ⟨V.smul_mem c ha.1, fun g h hh => by
    simp only [Pi.smul_apply, ha.2 g h hh]⟩

theorem mem_W {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} {x : AdelicGL2 (𝓞 F) F → ℂ} :
    x ∈ W hw V ↔ x ∈ V ∧ ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ),
      Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g := Iff.rfl

theorem isCuspSubrep_W (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F pins ξ V) : IsCuspSubrep F pins ξ (W hw V) where
  le := fun x hx => hV.le hx.1
  rightTranslate_fin_mem := fun g hg x hx => ⟨hV.rightTranslate_fin_mem g hg x hx.1, fun y h hh => by
    rw [rightTranslate_apply, rightTranslate_apply, mul_assoc,
      archRealGLAt_mul_comm_of_glArch_eq_one hw h ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg), ← mul_assoc,
      hx.2 _ h hh]⟩
  rightTranslate_arch_mem := fun v k x hx => ⟨hV.rightTranslate_arch_mem v k x hx.1, fun y h hh => by
    rw [rightTranslate_apply, rightTranslate_apply, rowIsometryInclAt₀_apply]
    by_cases hv : v = w
    · subst hv
      rw [← archRealGLAt_glEquivOfRingEquiv hw, mul_assoc, ← map_mul,
        hx.2 _ _ (by rw [map_mul, hh, one_mul, det_glEquiv_eq_one hw k]), hx.2 _ _ (det_glEquiv_eq_one hw k)]
    · have hcomm : archRealGLAt hw h * adelicArchGLInclAt F v (k : GL (Fin 2) v.Completion)
          = adelicArchGLInclAt F v (k : GL (Fin 2) v.Completion) * archRealGLAt hw h :=
        (commute_adelicArchGLInclAt_of_ne F (Ne.symm hv) _ _).eq
      rw [mul_assoc, hcomm, ← mul_assoc, hx.2 _ h hh]⟩
  rightConv_mem := fun f tys hf hbf x hx => ⟨hV.rightConv_mem f tys hf hbf x hx.1, fun g h hh => by
    rw [rightConv_apply, rightConv_apply]
    congr 1
    funext y
    rw [mul_assoc, archRealGLAt_mul hw h y, ← mul_assoc, hx.2 _ _ (det_conj h _ hh)]⟩

end RealInvariant

theorem forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F pins ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by
  obtain ⟨hsub, _, hmin⟩ := hV
  have hW := RealInvariant.isCuspSubrep_W hw pins ξ V hsub
  have hle : RealInvariant.W hw V ≤ V := fun x hx => hx.1
  rcases hmin (RealInvariant.W hw V) hW hle with hbot | heq
  · exfalso
    apply hne
    have hmem : x₀ ∈ RealInvariant.W hw V := ⟨hx₀, hinv⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · have hmem : x ∈ RealInvariant.W hw V := by rw [heq]; exact hx
    exact hmem.2 g h hh

/-! ## C6 — monotonicity of cuspidality in the production compact set -/

namespace Mono

variable {F : Type} [Field F] [NumberField F]

noncomputable abbrev stdPins (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) B

theorem isSmoothCuspAutomorphicFnAt_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) {ξ : (stdPins D B).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (stdPins D B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D' B) ξ φ := by
  let mG : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := h
  have hA' := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D B).Z ξ D φ).mp hA
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D B).Z ξ D' φ).mpr
    ⟨hA'.1, hA'.2.mono_measure (Measure.restrict_mono hD le_rfl)⟩, hcusp⟩, hsm⟩

theorem cuspKFiniteSubmodule_antitone {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) (ξ : (stdPins D B).Z →* ℂˣ) :
    cuspKFiniteSubmodule F (stdPins D B) ξ ≤ cuspKFiniteSubmodule F (stdPins D' B) ξ := by
  refine Submodule.span_mono ?_
  rintro φ ⟨hsat, hcont, tys, htys⟩
  exact ⟨fun g => isSmoothCuspAutomorphicFnAt_mono hD B (hsat g), hcont, tys, htys⟩

theorem isCuspSubrep_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    (B : Set (AdeleRing (𝓞 F) F)) {ξ : (stdPins D B).Z →* ℂˣ} {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (h : IsCuspSubrep F (stdPins D B) ξ V) : IsCuspSubrep F (stdPins D' B) ξ V := by
  exact ⟨h.le.trans (cuspKFiniteSubmodule_antitone hD B ξ), h.rightTranslate_fin_mem,
    h.rightTranslate_arch_mem, h.rightConv_mem⟩

end Mono

theorem isCuspConstituent_productionPinsOf_mono
    (F : Type) [Field F] [NumberField F]
    (D D' : Set (AdelicGL2 (𝓞 F) F)) (hD : D' ⊆ D) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V := by
  refine ⟨Mono.isCuspSubrep_mono hD B hV.1, hV.2.1, fun W hW hWV => hV.2.2 W ?_ hWV⟩
  exact ⟨hWV.trans hV.1.le, hW.rightTranslate_fin_mem, hW.rightTranslate_arch_mem, hW.rightConv_mem⟩

end AutomorphicForm.CuspidalConstituent

end
