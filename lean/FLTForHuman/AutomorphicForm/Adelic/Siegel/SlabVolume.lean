/-
  The finite volume of a determinant-norm slab.

  `AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain`: for a
  set `Φ₀` that is a fundamental domain for the left action of the global points `GL₂(K)` on the slab
  `{g | ideleNorm (det g) ∈ Icc α β}` against the restricted Haar measure `adelicGLHaar`, the measure of
  `Φ₀ ∩ slab` is finite. This is the finiteness the weighted-Petersson and Rankin–Selberg slab
  integrals consume: the slab has finite volume, read through any fundamental domain.

  The argument is the finite Siegel cover: the centre-cut Siegel set has finite measure under
  `adelicGLHaar` (so do its right translates, and finite unions of them), the slab cover of
  `exists_finset_slab_covering_of_coversModCentre` puts the slab inside such a finite union, and the
  fundamental-domain property moves the measure along the `K`-points of `GL₂(K)`.

  The two engine lemmas are public, as in the pin: the measure of a right translate of the centre-cut
  Siegel set is finite, and so is that of a finite union of translates. They are stated with the pin's
  section variable `K` and are useful on their own (the covering arguments of the windowed-Siegel
  layer need precisely this bound).

  Transcribed from the pin `S_` file below (pinned `aa2d8b3`, 119 lines), its label namespace
  `SlabFDFinite` replaced by the subject namespace `SlabVolume`.

  Port deltas (all proof-side; no statement moves):

  * `open scoped Pointwise` is added: the pin gets the pointwise set action `γ • D'` from its own
    `open scoped … Pointwise` (`:20`), the scaffold's open list did not carry it and the pin's proof
    cannot elaborate without it (`Set.smulSet` is `scoped[Pointwise]`).
  * The pin's five `scoped instance` countable declarations (`:31–43`: `Countable K`, `Mˣ`,
    `Matrix`, `GL (Fin 2) K`, `(globalPoints …).range`) are **not** transcribed as declarations: they
    are engine-side instance plumbing, and five new public names would put `own` entries on the
    module's checker line. The row establishes the same four-step chain locally, as `have` binders in
    its proof (`Countable K` → `Matrix` → `GL (Fin 2) K` → `Γ`) — a class-typed `have` is still an
    instance (FR-0223).
  * `haveI` → `have` at every instance binder, the linter's own suggestion (FR-0223); the two
    `haveI : BorelSpace …` lines of the pin (`:48`, `:72`) are dropped as the module's
    `attribute [local instance] … borelSpace_glBorel` already supplies that instance.
  * `measure_centreCutSiegelSet_lt_top` is qualified `NumberField.SiegelVolume.…` (the pin writes it
    bare under its own `open`); the declaration is in this module's import closure but not in its
    `open` list.
  * The row's hypothesis `hαβ : α < β` is not consumed by the pin's argument either; it is named
    once (`have hαβ' : α < β := hαβ; clear hαβ'`) so the unused-variable linter stays silent without
    a `set_option`.

  Heartbeat probe (gate 6, a measurement — the module carries **no** `set_option maxHeartbeats`):
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop cap 200000 and at
  **N = 10000**, and fails at **N = 9000** (timeout at `whnf` on the row's own declaration) and at
  8500/8000 (`isDefEq` inside the row's `calc`). The floor is the row, not the engines: at N = 2000
  the only failure is still the row, so both engine lemmas elaborate below that.

  spec-pin: P2M/Sol/S_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.FiniteCover
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabCoveringTheorems
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace SlabVolume

variable (K : Type) [Field K] [NumberField K]

local notation "G" => AdelicGL2 (𝓞 K) K
local notation "μH" => adelicGLHaar (Fin 2) (𝓞 K) K

/-- A right translate of a centre-cut Siegel set has finite `adelicGLHaar`-measure. -/
theorem measure_image_mul_right_centreCutSiegelSet_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ}
    (hd₁ : 0 < d₁) (d₂ : ℝ) (x : G) :
    μH ((· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [Set.image_mul_right, ← Measure.map_apply (measurable_mul_const x⁻¹)
    (measurableSet_centreCutSiegelSet c u d₁ d₂)]
  exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top _ hc u hd₁ d₂

/-- A finite union of right translates of a centre-cut Siegel set has finite `adelicGLHaar`-measure. -/
theorem measure_biUnion_lt_top {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset G) :
    μH (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
  refine (measure_biUnion_finset_le T _).trans_lt ?_
  exact ENNReal.sum_lt_top.mpr fun x _ => measure_image_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x

end SlabVolume

theorem adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Φ₀ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) < ⊤ := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  -- the row's hypothesis `hαβ : α < β` is not consumed by the pin's argument: it is referenced
  -- once here so that the unused-variable linter stays silent (the binder is the pin's own).
  have hαβ' : α < β := hαβ
  clear hαβ'
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set slab : Set (AdelicGL2 (𝓞 K) K) :=
    {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hslab_def
  have hslab : MeasurableSet slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  set Γ := (globalPoints (𝓞 K) K).range with hΓ
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  have : Countable (GL (Fin 2) K) :=
    Function.Injective.countable (f := (Units.val : GL (Fin 2) K → Matrix (Fin 2) (Fin 2) K))
      (fun a b h => Units.ext h)
  have : Countable Γ := (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable
  set ν := μ.restrict slab with hν

  obtain ⟨T, c, hc, u, hcovall⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hcovall 1 2 two_pos (by norm_num)
  obtain ⟨T', hT'⟩ := exists_finset_slab_covering_of_coversModCentre K c u 1 2 T (by norm_num) hcov α β hα
  set D' : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ T', (· * x) '' centreCutSiegelSet K c u 1 2 with hD'
  have hD'fin : μ D' < ⊤ := SlabVolume.measure_biUnion_lt_top K hc u one_pos 2 T'

  have hslab_smul : ∀ (γ : Γ) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ slab ↔ x ∈ slab := by
    rintro ⟨_, γ, rfl⟩ x
    show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x))
        ∈ Set.Icc α β ↔ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

  have : MeasurableConstSMul Γ (AdelicGL2 (𝓞 K) K) :=
    ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩
  have : SMulInvariantMeasure Γ (AdelicGL2 (𝓞 K) K) ν := by
    refine ⟨fun γ s hs => ?_⟩
    have hpre : MeasurableSet ((fun x => γ • x) ⁻¹' s) := hs.preimage (measurable_const_smul γ)
    rw [hν, Measure.restrict_apply hpre, Measure.restrict_apply hs]
    have : (fun x => γ • x) ⁻¹' s ∩ slab = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact and_congr_right fun _ => (hslab_smul γ x).symm
    rw [this, measure_preimage_mul]

  have hcover : Φ₀ ∩ slab ⊆ ⋃ γ : Γ, γ • D' := by
    rintro g ⟨-, hg⟩
    obtain ⟨γ, hγ⟩ := hT' g hg
    refine Set.mem_iUnion.2 ⟨(⟨globalPoints (𝓞 K) K γ, γ, rfl⟩ : Γ)⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  calc μ (Φ₀ ∩ slab)
      ≤ μ ((⋃ γ : Γ, γ • D') ∩ Φ₀ ∩ slab) := measure_mono fun g hg =>
          ⟨⟨hcover hg, hg.1⟩, hg.2⟩
    _ = ν ((⋃ γ : Γ, γ • D') ∩ Φ₀) := (Measure.restrict_apply' hslab).symm
    _ = ν (⋃ γ : Γ, γ • D' ∩ Φ₀) := by rw [Set.iUnion_inter]
    _ ≤ ∑' γ : Γ, ν (γ • D' ∩ Φ₀) := measure_iUnion_le _
    _ = ν D' := (hΦ₀.measure_eq_tsum D').symm
    _ ≤ μ D' := Measure.restrict_le_self _
    _ < ⊤ := hD'fin

end AutomorphicForm
