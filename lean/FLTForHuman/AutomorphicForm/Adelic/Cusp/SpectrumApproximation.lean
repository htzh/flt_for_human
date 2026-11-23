/-
The cuspidal spectrum approximated by translates of one flat level-spherical test function.

Four rows of the approximation argument that identifies the cuspidal spectrum with the closure of the
`archCut`/level-invariant vectors:

* `exists_norm_toCarrier_sub_lt` — for `x` cuspidal, `U(N)`-invariant and `archCut`-flat, and any
  `ε > 0`, there is a **factorizable** test function `f`, level-spherical of type `tys` for `U(N)` and
  flat of modulus `σ`, such that `rightConv x f` is cuspidal and its carrier class is within `ε` of
  `x`'s;
* `exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq` — the same
  with the level subgroup an arbitrary compact open `U` inside the finite integral group and the
  invariance hypothesis given pointwise (`∀ g u ∈ U, x (g * u) = x g`);
* `exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous` — the cusp lift
  `x ↦ x ⋆ f` is a continuous monoid homomorphism of the cuspidal submodule, and
  `exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact` — its
  `isCompact` variant with the coercion and the norm equation.

The subject is the same in all four: the carrier is the closure of the translates of one flat
level-spherical vector, which is what makes the cuspidal spectrum a limit of finite-dimensional
`archCut` pieces.  They consume the archimedean approximation/`archCut` machinery
(`Adelic/{ArchApproximation,ArchCutReproducer,ArchCutSpan,ArchPeterssonPairing}.lean`), the carrier's
convolution action (`Cusp/{SpectrumTranslation,SpectrumConvAction}.lean`), the Petersson parametric
integral floor (`MeasureTheory/ParametricIntegral.lean`) and the idèle-norm façade
(`Adelic/IdeleNormDetGlue.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_sub_lt.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact.lean>

spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_sub_lt.lean
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq.lean
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous.lean
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_sub_lt.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact.lean

## The engine (48 pin rows) and how each row is accounted for

Two of the four pins are **almost entirely `private`** (1 public row each), so `check_port` is a *weak*
gate on this order: it sees the 8 public declarations below and nothing else. The completeness gate
is the pin-vs-module declaration diff (`statement_db`), which must — and does — account for all **48**
pin rows (16 + 15 + 14 + 3, FR-0277). `check_port`'s 8 is therefore **not** the order's size.

| pin `S_` file (lines) | pin rows | substituted by import | declared here |
|---|---:|---:|---:|
| `exists_norm_toCarrier_sub_lt` (446) | 16 | 9 | 7 |
| `exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq` (428) | 15 | 9 | 6 |
| `exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous` (294) | 14 | 9 | 5 |
| `exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact` (174) | 3 | 0 | 3 |
| **total** | **48** | **27** | **21** |

The 21 declared row-instances are **15 declarations** (the two approximation pins share their whole
private prelude verbatim, and the two cusp-lift pins share both of their non-headline rows), with the
pins' `private`/`public` split kept: **7 `private`** in `ArchTestApprox` (`norm_toCarrier_sub`,
`eLpNorm_sub_lt_top`, `IsArchTestFactor.const_mul'`, `glFin_image_fdPins_U`,
`ideleNorm_det_eq_of_glFin_mem_finiteLevelOne`, `ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2`,
`isFinTestFactor_indicator`) and **8 public** (`RowIsometryMonoidHom.{eq_inclArch,
ideleNorm_det_eq_one}`, `CuspSubcarrierDense.{exists_mem_norm_sub_lt, eq_of_isCuspLift}`, and the
four headlines at the wrappers' statements and published names).

The pin's label namespaces come off for subject namespaces (`T6Assembly` → `ArchTestApprox`,
`SirProof`/`IsoRepU` → `RowIsometryMonoidHom` + `CuspSubcarrierDense`), all search-stage labels.

### Substituted (imported, not re-proved) — `port once`

| pin row(s) | port home |
|---|---|
| `iota`, `iota_apply_val` | `AutomorphicForm.ArchInfra.inclArch`, `…inclArch_entry` |
| `archComponent_iota` | `AutomorphicForm.ArchInfra.archComponent_inclArch` |
| `continuous_iota` (both pins) / `continuous_inclArch` (pin 294) | `AutomorphicForm.ArchInfra.continuous_inclArch` |
| `inclArch`, `inclArch_mulSingle`, `inclArch_entry`, `Kw`, `Kprod`, `commute_archRowIsometryInclAt₀` | `AutomorphicForm.ArchInfra` (same names) |
| `continuous_adelicArchGLIncl'` (pins 446/428), `continuous_adelicArchGLIncl` (pin 294) | `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl` |
| `eq_of_isMulLeftInvariant_of_isProbabilityMeasure` | `IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure` |
| `continuous_archEntries` | `AutomorphicForm.continuous_archEntries` |
| `continuous'` (`IsArchTestFactor.continuous'`) | `AutomorphicForm.continuous_of_isArchTestFactor` |
| `eLpNorm_two_pow_two` | `AutomorphicForm.CuspidalSpectrum.AvgLift.eLpNorm_two_pow_two`, **with** an `AEStronglyMeasurable` hypothesis |

The last one is a statement drift, not a re-proof: mathlib v4.34's `eLpNorm` is `⊤` off the a.e.
strongly measurable functions, so the pin's unconditional identity is false on this line. Every pin
use here discharges the hypothesis from `memLp_weightedMeasure_of_mem` (the `own:` row for the
public copy is recorded in `spec/decl_markers.tsv` against `Cusp/SpectrumIntegration.lean`).

Two port-side shape differences are absorbed, not drifted: `RowIsometryMonoidHom.eq_inclArch` /
`…ideleNorm_det_eq_one` are stated over the pin's bare `Kprod` / `inclArch` (the module opens
`ArchInfra`, so the pin's statement text is preserved and both rows read `ok` by hash), and the
port's `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule`,
`isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule` and
`lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` take the same
`(F, μ, ι, hι, …)` argument prefix the pins pass.

### Gates

* `check_port --force` → **8 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* edit loop (`lake env lean -DautoImplicit=false`) → **silent**, no `sorry`.
* `lake build FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumApproximation` → 0 warning lines from
  this file.
* `#print axioms` on all 8 public declarations → `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.
* `dedup.py --within --module '*Cusp/SpectrumApproximation*'` → **0 clusters** (15 declarations).
  There is no pin `main`↔`solution` pair to excuse here: the two approximation pins' `solution`s are
  the two distinct headlines, and the cusp-lift pins' shared two helpers are written **once**.
* `move_dead.py --dry-run` → **0 declarations, 0 lines**.
* heartbeat probe pair, **recorded and never installed** (FR-0225): with
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` the module is **silent at N = 160 000** and
  **fails at N = 130 000**. The two sites that fail first are the cusp-lift headlines: the statement
  elaboration of `exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous` (a `whnf`
  timeout, the `ContinuousLinearMap` op-norm instance) and the `‖v - a‖` rewriting step of the
  `isCompact` row (`isDefEq`). At 100 000 the two approximation rows fail too (their `hkey` step).
  No `set_option maxHeartbeats` is in this module.
* collision probe (`tmp/af103/collision-probe.lean`): the reduced form over the three modules of this
  set that were built when this one landed
  (`tmp/af103/collision-C.lean`: `SpectrumApproximation`, `ConstituentSpine`,
  `ValuationSubringValuedField`) prints nothing; the set-level probe needs `ModularCurve/Reduction/`
  and `ModularCurve/X1/JqRamification`, which were not built yet (see `tmp/af103/AF103C-REPORT.md`).

Imports added to the scaffold's list: `Cusp/SpectrumIntegration` (for
`AvgLift.eLpNorm_two_pow_two`) and `MeasureTheory/IsotypicConvolution` (for
`IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure`); everything else the four
proofs use was already in the closure.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.ArchCutReproducer
import FLTForHuman.AutomorphicForm.Adelic.ArchCutSpan
import FLTForHuman.AutomorphicForm.Adelic.ArchPeterssonPairing
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConvAction
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumIntegration
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDetGlue
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.RightConvProductIntegral
import FLTForHuman.AutomorphicForm.Adelic.Siegel.CentreCutCover
import FLTForHuman.MeasureTheory.IsotypicConvolution
import FLTForHuman.MeasureTheory.ParametricIntegral
import FLTForHuman.NumberTheory.AdelicHaar.ProductMeasure
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet

set_option autoImplicit false

-- The pins' `letI normedInst` / `letI mK` bindings are proof-local typeclass assumptions that
-- mathlib's style linter would like as `let`; they are kept as instances (the pin's text) and the
-- style linter is off, as in the rest of the port's transcription of these pins.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Topology

namespace AutomorphicForm.CuspidalSpectrum

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-! ## The row-isometry product is the canonical archimedean monoid homomorphism

Pin `S_…_monoidHom_…_and_norm_eq_and_continuous.lean:24–132` opens with an `Incl` section that builds
the monoid homomorphism `Kprod F →* GL (Fin 2) (InfiniteAdeleRing F)` out of the row-isometry
inclusions.  Nine of its declarations are **already public in the port**, at the same statements, in
`AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` (`ArchInfra.Kw`, `ArchInfra.Kprod`,
`ArchInfra.commute_archRowIsometryInclAt₀`, `ArchInfra.inclArch`, `ArchInfra.inclArch_mulSingle`,
`ArchInfra.inclArch_entry`, `ArchInfra.archComponent_inclArch`, `ArchInfra.continuous_inclArch`) and
`AutomorphicForm/Adelic/TestFnNearIdentity.lean`
(`AutomorphicForm.continuous_adelicArchGLIncl`); they are **imported, not re-proved** (`port once`).
Only the two that no port module carries are transcribed below. -/

namespace RowIsometryMonoidHom

-- The pin's two remaining declarations are stated over its own `Kprod` / `inclArch`, which the port
-- carries in `ArchInfra`; opening that namespace is what keeps the pin's statement text.
open ArchInfra

variable (F : Type) [Field F] [NumberField F]

/-- **The row-isometry product is unique.** A monoid homomorphism out of `Kprod F` whose `w`-th
archimedean component is the row-isometry inclusion is `ArchInfra.inclArch F`.  Pin
`S_…_and_norm_eq_and_continuous.lean:110`. -/
theorem eq_inclArch (ι : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ι = inclArch F := by
  refine MonoidHom.ext fun κ => Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  have h1 := AdelicLevel.archComponent_apply (K := F) w (ι κ) i j
  have h2 := AdelicLevel.archComponent_apply (K := F) w (ArchInfra.inclArch F κ) i j
  rw [← h1, ← h2, hι, ArchInfra.archComponent_inclArch]

/-- **The row-isometry inclusion has idèle norm one.**  Pin
`S_…_and_norm_eq_and_continuous.lean:119`. -/
theorem ideleNorm_det_eq_one (ι : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (κ : Kprod F) :
    NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
  have hX : glFin (𝓞 F) F (adelicArchGLIncl F (ι κ)) ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [glFin_adelicArchGLIncl]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F := F) _ hX]
  refine Finset.prod_eq_one fun w _ => ?_
  have h1 : NumberField.AdelicVolume.archDetNorm w (adelicArchGLIncl F (ι κ)) = 1 := by
    unfold NumberField.AdelicVolume.archDetNorm
    rw [glArch_adelicArchGLIncl, hι,
      ((mem_rowIsometrySubgroup₀_iff w.Completion).mp (κ w).2).1, norm_one]
  rw [h1, one_pow]

end RowIsometryMonoidHom

/-! ## A cusp lift is determined on a dense set

Pins `S_…_monoidHom_…_and_norm_eq_and_continuous.lean:134–187` (its `Dense` section) and
`S_…_of_isCompact.lean:24–79` (its `Dense` section) share both of the following two declarations
verbatim; they are written **once** here, publicly, at the pin's names.  The pin's inner namespace
labels (`SirProof`, `IsoRepU`) are search-stage pipeline labels and are dropped for the subject
namespace `CuspSubcarrierDense`. -/

namespace CuspSubcarrierDense

variable (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
  (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

/-- **Cusp members are dense in the cuspidal subcarrier.**  Pin
`S_…_and_norm_eq_and_continuous.lean:139`. -/
theorem exists_mem_norm_sub_lt (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ < ε := by
  have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) :
        Set (Carrier F Φ₀ σ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact v.2
  obtain ⟨a, haA, hav⟩ := Metric.mem_closure_iff.mp hv ε hε
  obtain ⟨φm, hφm, rfl⟩ := haA
  refine ⟨φm, hφm, ?_⟩
  rw [← Submodule.norm_coe, Submodule.coe_sub, toCuspSubcarrier_apply_coe, ← dist_eq_norm]
  exact hav

variable {F hΦ₀ σ ξ}

/-- **A cusp lift is determined by its values on cusp members.**  Two bounded operators lifting the
same operation agree, because the cusp members are dense and both are bounded.  Pin
`S_…_and_norm_eq_and_continuous.lean:153`. -/
theorem eq_of_isCuspLift {op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hop : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    {S S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (hS : IsCuspLift F hΦ₀ σ ξ op S) (hS' : IsCuspLift F hΦ₀ σ ξ op S') : S = S' := by
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  refine ContinuousLinearMap.ext fun v => ?_

  have key : ∀ ε : ℝ, 0 < ε → ‖S v - S' v‖ ≤ (‖S‖ + ‖S'‖) * ε := by
    intro ε hε
    obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v ε hε
    have hSa : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = S' (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [hS ⟨φ, hφ⟩ (hop φ hφ), hS' ⟨φ, hφ⟩ (hop φ hφ)]
    have hdec : S v - S' v = S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) -
        S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [map_sub, map_sub, hSa]; abel
    rw [hdec]
    calc ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) - S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖
        ≤ ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ +
          ‖S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ +
          ‖S'‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ :=
          add_le_add (S.le_opNorm _) (S'.le_opNorm _)
      _ ≤ ‖S‖ * ε + ‖S'‖ * ε := add_le_add (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S))
          (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S'))
      _ = (‖S‖ + ‖S'‖) * ε := by ring
  have h0 : ‖S v - S' v‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < ‖S‖ + ‖S'‖ + 1 := by positivity
    have := key (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) (by positivity)
    have hlt : (‖S‖ + ‖S'‖) * (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) < ‖S v - S' v‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg S, norm_nonneg S']
    exact absurd (this.trans_lt hlt) (lt_irrefl _)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end CuspSubcarrierDense

/-! ## The private prelude of the two approximation rows

Pins `S_…_norm_toCarrier_sub_lt.lean:44–199` and
`S_…_of_forall_apply_mul_eq.lean:42–185` open with the same `private` prelude (the pin's
`T6Assembly` namespace, a search-stage label, dropped for the subject name `ArchTestApprox`).
Fourteen declarations are shared verbatim; the two rows then differ in the level subgroup only.

Nine of them are **already public in the port** and are imported rather than re-proved
(`port once`, `port_advise`'s substitute list):

| pin (`private`) | port home |
|---|---|
| `iota` / `iota_apply_val` | `ArchInfra.inclArch` / `ArchInfra.inclArch_entry` |
| `archComponent_iota` | `ArchInfra.archComponent_inclArch` |
| `continuous_iota` | `ArchInfra.continuous_inclArch` |
| `eq_of_isMulLeftInvariant_of_isProbabilityMeasure` | `IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure` |
| `continuous_adelicArchGLIncl'` | `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl` |
| `continuous_archEntries` | `AutomorphicForm.continuous_archEntries` |
| `continuous'` (`IsArchTestFactor.continuous'`) | `AutomorphicForm.continuous_of_isArchTestFactor` |
| `eLpNorm_two_pow_two` | `AvgLift.eLpNorm_two_pow_two`, **with** an `AEStronglyMeasurable` hypothesis |

The `eLpNorm_two_pow_two` substitution is a statement drift, not a re-proof: mathlib v4.34 defines
`eLpNorm` to be `⊤` off the a.e. strongly measurable functions, so the pin's unconditional identity
is false on this line (`spec/decl_markers.tsv`'s `own:` row in `Cusp/SpectrumIntegration.lean`).  Every
pin use here discharges the hypothesis, from `memLp_weightedMeasure_of_mem`.

The seven declarations below are the rest of the prelude, `private` as in the pins.  The level-`N`
one (`glFin_image_fdPins_U`, `ideleNorm_det_eq_of_glFin_mem_finiteLevelOne`) is the first pin's
only; the second pin has `ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2` instead. -/

namespace ArchTestApprox

variable {F : Type} [Field F] [NumberField F]

/-- The `L²` norm of a difference of carrier vectors is the `eLpNorm` of the difference.  Pin
`S_…_norm_toCarrier_sub_lt.lean:98` / `S_…_of_forall_apply_mul_eq.lean:96`. -/
private theorem norm_toCarrier_sub {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (a b : AdelicGL2 (𝓞 F) F → ℂ)
    (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ) :
    ‖toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ - toCarrier F hΦ₀ σ ξ ⟨b, hb⟩‖ =
      (eLpNorm (a - b) 2 (weightedMeasure F Φ₀ σ)).toReal := by
  rw [← map_sub]
  have : (⟨a, ha⟩ - ⟨b, hb⟩ : ↥(memberSubmodule F Φ₀ ξ)) =
      ⟨a - b, (memberSubmodule F Φ₀ ξ).sub_mem ha hb⟩ := rfl
  rw [this]
  exact Lp.norm_toLp (a - b)
    (memLp_weightedMeasure_of_mem F hΦ₀ σ ((memberSubmodule F Φ₀ ξ).sub_mem ha hb))

/-- A difference of carrier vectors is in `L²`.  Pin `S_…_norm_toCarrier_sub_lt.lean:107` /
`S_…_of_forall_apply_mul_eq.lean:105`. -/
private theorem eLpNorm_sub_lt_top {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {a b : AdelicGL2 (𝓞 F) F → ℂ}
    (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ) :
    eLpNorm (a - b) 2 (weightedMeasure F Φ₀ σ) < ⊤ :=
  (memLp_weightedMeasure_of_mem F hΦ₀ σ ((memberSubmodule F Φ₀ ξ).sub_mem ha hb)).eLpNorm_lt_top

open scoped Classical in
/-- An archimedean test factor is stable under a constant multiplier.  Pin
`S_…_norm_toCarrier_sub_lt.lean:152` / `S_…_of_forall_apply_mul_eq.lean:150`. -/
private theorem IsArchTestFactor.const_mul' {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (fun y => c * fa y) := by
  obtain ⟨⟨Φ, hΦ, heq⟩, hK⟩ := h
  exact ⟨⟨fun A => c * Φ A, contDiff_const.mul hΦ, fun g => by
      show c * fa g = c * Φ (archEntries F g); rw [heq]⟩, hK.mul_left⟩

/-- The image of the level-`N` pin subgroup under the finite projection.  Pin
`S_…_norm_toCarrier_sub_lt.lean:157`. -/
private theorem glFin_image_fdPins_U (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext k
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (Subgroup.mem_inf.mp hu).1
  · intro hk
    refine ⟨AdelicDock.finEmbed (𝓞 F) F k, ?_, ?_⟩
    · exact Subgroup.mem_inf.mpr ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F k).mpr hk,
        (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F k)⟩
    · exact AdelicDock.glFin_finEmbed (𝓞 F) F k

/-- The idèle norm of the determinant depends only on the finite part, for a level-`N` matrix.  Pin
`S_…_norm_toCarrier_sub_lt.lean:170`. -/
private theorem ideleNorm_det_eq_of_glFin_mem_finiteLevelOne (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) (hg : glFin (𝓞 F) F g ∈ finiteLevelOne (𝓞 F) F N) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
      = NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F := F) g
      (mem_finiteIntegralGL2_iff.mpr ⟨hg.1.integral, hg.2.integral⟩),
    NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F := F)
      (adelicArchGLIncl F (glArch (𝓞 F) F g)) (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold NumberField.AdelicVolume.archDetNorm
  rw [glArch_adelicArchGLIncl]

/-- The same for a matrix in the finite integral group.  Pin
`S_…_of_forall_apply_mul_eq.lean:155`. -/
private theorem ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2 (g : AdelicGL2 (𝓞 F) F)
    (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
      = NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F := F) g hg,
    NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (F := F)
      (adelicArchGLIncl F (glArch (𝓞 F) F g)) (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold NumberField.AdelicVolume.archDetNorm
  rw [glArch_adelicArchGLIncl]

/-- The indicator of a compact open set is a finite test factor.  Pin
`S_…_norm_toCarrier_sub_lt.lean:182` / `S_…_of_forall_apply_mul_eq.lean:166`. -/
private theorem isFinTestFactor_indicator
    {S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hSo : IsOpen S) (hSc : IsCompact S) :
    IsFinTestFactor F (S.indicator fun _ => (1 : ℂ)) := by
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  have hScl : IsClosed S := hSc.isClosed
  refine ⟨fun s => ?_, HasCompactSupport.intro hSc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_univ
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = S := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hSo
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Sᶜ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hScl.isOpen_compl
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_empty

end ArchTestApprox

open ArchTestApprox in
theorem exists_norm_toCarrier_sub_lt
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hxU : x ∈ levelInvariantSubmodule F (fdPins F Φ₀) N) (hxt : x ∈ archCutSubmodule F tys)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys ((fdPins F Φ₀).U N) f ∧
      flat F σ f = f ∧
      ∃ hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ,
        ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hx⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf⟩‖ < ε 
:= by
  classical

  haveI hBorelA : BorelSpace (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  haveI : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  haveI : CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.compactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance
  letI mK : MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩
  haveI : Nonempty (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨1⟩
  set μK : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
    Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) with hμK
  haveI hKprob : IsProbabilityMeasure μK :=
    ⟨by rw [hμK, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  haveI hKright : μK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : IsProbabilityMeasure (μK.map (· * g)) :=
      Measure.isProbabilityMeasure_map_iff (measurable_mul_const g).aemeasurable |>.mpr inferInstance
    exact IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure (μK.map (· * g)) μK
  haveI hKinv : μK.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure μK.inv := by
      rw [Measure.inv_def]
      exact Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable |>.mpr inferInstance
    exact IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure μK.inv μK

  letI mA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  set μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haar with hμa
  haveI : μa.Regular := by rw [hμa]; infer_instance
  haveI hAright : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  have hxc : Continuous x := hx.2
  obtain ⟨hEfd, hEc, hEt, hEK⟩ :=
    AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F
      (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys x hxc hxt
  set E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
    (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ArchInfra.inclArch F κ))) with hE
  have hxE : x ∈ E := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g
    simp only [map_one, mul_one]
  obtain ⟨e, he, hecl, hefl, het, het', hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys E hEfd hEc hEt hEK

  have hxcm : x ∈ contMemberSubmodule F Φ₀ ξ := ⟨hx.1.1.1, hx.2⟩
  obtain ⟨V, hV, hVest⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt F hΦ₀ σ ξ hσ x hxcm (ε / 2)
      (half_pos hε)
  have hinclc : Continuous (adelicArchGLIncl F) :=
    AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl F
  have hVinf : (adelicArchGLIncl F) ⁻¹' V ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    refine hinclc.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨h₀, hh₀t, hh₀re, hh₀1, hh₀V, hh₀c, hh₀f⟩ :=
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ _ hVinf

  have hUimg : (glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))
      = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    glFin_image_fdPins_U Φ₀ N
  have hUo : IsOpen ((glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))) := by
    rw [hUimg]; exact isOpen_finiteLevelOne (𝓞 F) F hN
  have hUc : IsCompact ((glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))) := by
    rw [hUimg]; exact isCompact_finiteLevelOne (𝓞 F) F N
  obtain ⟨C, hCpos, hC⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μK (ArchInfra.inclArch F) (ArchInfra.continuous_inclArch (F := F))
      (ArchInfra.archComponent_inclArch (F := F)) μa ((fdPins F Φ₀).U N) inf_le_right hUo hUc

  set I₀ : ℝ := ∫ a, (h₀ a).re ∂μa with hI₀
  have hh₀cont : Continuous h₀ := AutomorphicForm.continuous_of_isArchTestFactor F hh₀t
  have hh₀K : HasCompactSupport h₀ := hh₀t.2
  have hI₀pos : 0 < I₀ := by
    have hre : Continuous fun a => (h₀ a).re := Complex.continuous_re.comp hh₀cont
    have hreK : HasCompactSupport fun a => (h₀ a).re := hh₀t.2.comp_left Complex.zero_re
    exact hre.integral_pos_of_hasCompactSupport_nonneg_nonzero hreK (fun a => (hh₀re a).2) hh₀1.ne'
  set c : ℝ := (C * I₀)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (mul_pos hCpos hI₀pos)
  set h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun a => (c : ℂ) * h₀ a with hh
  have hht : IsArchTestFactor F h := IsArchTestFactor.const_mul' hh₀t (c : ℂ)
  have hhcont : Continuous h := continuous_const.mul hh₀cont
  have hhK : HasCompactSupport h := hh₀K.mul_left
  have hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y := fun w k y => by
    simp only [hh, hh₀c w k y]
  have hhf : ∀ y : GL (Fin 2) (InfiniteAdeleRing F), h y = conj (h y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ) := by
    intro y
    simp only [hh, map_mul, Complex.conj_ofReal, mul_assoc]
    rw [← hh₀f y]

  set fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      e p.1 * e p.2 * h ((ArchInfra.inclArch F p.1)⁻¹ * y * (ArchInfra.inclArch F p.2)⁻¹) ∂(μK.prod μK) with hfa
  set f : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa (glArch (𝓞 F) F g) *
      Set.indicator ((glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g) with hfdef
  obtain ⟨hfa_t, hfa_bf⟩ :=
    AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys e e he he h hht
  have hfa_bf' : IsArchFactorBiFinite F tys fa := hfa_bf het het'
  obtain ⟨hfa_c, hfa_f⟩ :=
    AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) σ e hecl hefl h hhc hhf
  have hsph : IsLevelSphericalOfType F tys ((fdPins F Φ₀).U N) f :=
    ⟨fa, hfa_t, hfa_bf', fun w k y => hfa_c w k y, fun g => rfl⟩
  have hff : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) :=
    isFinTestFactor_indicator hUo hUc
  have hftest : IsFactorizableTestFn F f := ⟨fa, _, hfa_t, hff, fun g => rfl⟩
  have hflat : flat F σ f = f := by
    funext g
    show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ) = f g
    simp only [hfdef, map_inv]
    by_cases hg : glFin (𝓞 F) F g ∈ (glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F))
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∈ (glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact inv_mem hg
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg', mul_one, mul_one]
      have hgl : glFin (𝓞 F) F g ∈ finiteLevelOne (𝓞 F) F N := by rw [hUimg] at hg; exact hg
      rw [ideleNorm_det_eq_of_glFin_mem_finiteLevelOne N g hgl]
      exact (hfa_f (glArch (𝓞 F) F g)).symm
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∉ (glFin (𝓞 F) F) '' ((fdPins F Φ₀).U N : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact fun h => hg (by simpa using inv_mem h)
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', mul_zero, mul_zero, map_zero, zero_mul]
  have hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hftest x hx

  have hxU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, x (g * u) = x g := hxU
  have hconv : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = C * ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa :=
    hC e he h hhcont hhK hhc x hxc hxU (fun z => hrep x hxE z)
  set p : GL (Fin 2) (InfiniteAdeleRing F) → ℝ := fun a => (h₀ a).re / I₀ with hp
  have hconv' : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa := by
    intro g
    rw [hconv g]
    have h1 : ∀ a, x (g * adelicArchGLIncl F a) * h a = (c : ℂ) * (x (g * adelicArchGLIncl F a) * h₀ a) := fun a => by
      simp only [hh]; ring
    have h2 : ∀ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) = (x (g * adelicArchGLIncl F a) * h₀ a) * ((I₀ : ℂ))⁻¹ := by
      intro a
      simp only [hp, Complex.ofReal_div]
      rw [(hh₀re a).1]
      ring
    simp_rw [h1, h2, integral_const_mul, integral_mul_const]
    have hCc : (C : ℂ) * (c : ℂ) = ((I₀ : ℂ))⁻¹ := by
      simp only [hc, Complex.ofReal_inv, Complex.ofReal_mul]
      field_simp [Complex.ofReal_ne_zero.mpr hCpos.ne', Complex.ofReal_ne_zero.mpr hI₀pos.ne']
    rw [← mul_assoc, hCc, mul_comm]

  refine ⟨f, hftest, hsph, hflat, hxf, ?_⟩

  have hnorm : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ‖v‖ = ‖(v : Carrier F Φ₀ σ)‖ := fun v => rfl
  rw [hnorm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  have hkey : ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1.1.1⟩ -
        toCarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf.1.1.1⟩‖
      = (eLpNorm (x - rightConv F x f) 2 (weightedMeasure F Φ₀ σ)).toReal :=
    norm_toCarrier_sub hΦ₀ σ ξ x (rightConv F x f) hx.1.1.1 hxf.1.1.1
  rw [hkey]
  set ν : Measure (AdelicGL2 (𝓞 F) F) := weightedMeasure F Φ₀ σ with hν

  suffices hmain : eLpNorm (x - rightConv F x f) 2 ν ^ 2 ≤ ENNReal.ofReal (ε / 2) ^ 2 by
    have h1 : eLpNorm (x - rightConv F x f) 2 ν ≤ ENNReal.ofReal (ε / 2) :=
      (ENNReal.pow_le_pow_left_iff two_ne_zero).mp hmain
    calc (eLpNorm (x - rightConv F x f) 2 ν).toReal ≤ ε / 2 :=
          ENNReal.toReal_le_of_le_ofReal (half_pos hε).le h1
      _ < ε := half_lt_self hε

  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    infer_instance
  haveI : SFinite ν := by rw [hν, weightedMeasure]; infer_instance
  haveI : SFinite μa := by
    haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => properSpace_completion v
    haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
      inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := Units.isEmbedding_embedProduct.secondCountableTopology
    infer_instance

  have hpc : Continuous p := (Complex.continuous_re.comp hh₀cont).div_const _
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hh₀re a).2 hI₀pos.le
  have hp1 : ∫ a, p a ∂μa = 1 := by
    simp only [hp, integral_div]
    exact div_self hI₀pos.ne'
  have hpK : HasCompactSupport p := by
    have : p = (fun r : ℝ => r / I₀) ∘ (fun a => (h₀ a).re) := rfl
    rw [this]
    exact (hh₀t.2.comp_left Complex.zero_re).comp_left (zero_div _)
  have hU : Measurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) :=
    (hxc.comp (continuous_fst.mul (hinclc.comp continuous_snd))).measurable
  have hint : ∀ g : AdelicGL2 (𝓞 F) F, Integrable (fun a => x (g * adelicArchGLIncl F a) * (p a : ℂ)) μa := fun g =>
    ((hxc.comp (continuous_const.mul hinclc)).mul (Complex.continuous_ofReal.comp hpc)).integrable_of_hasCompactSupport
      ((hpK.comp_left Complex.ofReal_zero).mul_left)
  have hJ := MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq ν μa p hpc.measurable
    hp0 hp1 x hxc.measurable (fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) hU hint

  have hL : eLpNorm (x - rightConv F x f) 2 ν ^ 2 = ∫⁻ g, ‖x g - ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa‖ₑ ^ 2 ∂ν := by
    rw [AvgLift.eLpNorm_two_pow_two ν
      (memLp_weightedMeasure_of_mem F hΦ₀ σ
        ((memberSubmodule F Φ₀ ξ).sub_mem hx.1.1.1 hxf.1.1.1)).aestronglyMeasurable]
    refine lintegral_congr fun g => ?_
    rw [Pi.sub_apply, hconv' g]
  rw [hL]
  refine hJ.trans ?_

  have hpt : ∀ a, p a ≠ 0 → adelicArchGLIncl F a ∈ V := by
    intro a ha
    have : a ∈ tsupport h₀ := by
      refine subset_tsupport _ ?_
      intro h0; apply ha; simp only [hp, h0, Complex.zero_re, zero_div]
    exact hh₀V this
  have hB : ∀ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
      ≤ ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 := by
    intro a
    by_cases ha : p a = 0
    · simp [ha]
    obtain ⟨hy, hlt⟩ := hVest _ (hpt a ha)
    refine mul_le_mul_right ?_ _
    have heq : ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
        = eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν ^ 2 := by
      rw [AvgLift.eLpNorm_two_pow_two ν
        (memLp_weightedMeasure_of_mem F hΦ₀ σ
          ((memberSubmodule F Φ₀ ξ).sub_mem hy.1 hx.1.1.1)).aestronglyMeasurable]
      refine lintegral_congr fun g => ?_
      rw [Pi.sub_apply, rightTranslate_apply, enorm_sub_rev]
    rw [heq]
    have hlt' : eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν < ENNReal.ofReal (ε / 2) := by
      rw [norm_toCarrier_sub hΦ₀ σ ξ] at hlt
      exact (ENNReal.lt_ofReal_iff_toReal_lt (eLpNorm_sub_lt_top hΦ₀ σ hy.1 hx.1.1.1).ne).mpr hlt
    exact pow_le_pow_left' hlt'.le 2
  calc ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν ∂μa
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 ∂μa := lintegral_mono hB
    _ = (∫⁻ a, ENNReal.ofReal (p a) ∂μa) * ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [lintegral_mul_const _ hpc.measurable.ennreal_ofReal]
    _ = ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hpc.integrable_of_hasCompactSupport hpK) (ae_of_all _ hp0), hp1,
          ENNReal.ofReal_one, one_mul]


open ArchTestApprox in
theorem exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUi : (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hxU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g) (hxt : x ∈ archCutSubmodule F tys)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys U f ∧
      flat F σ f = f ∧
      ∃ hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ,
        ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hx⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf⟩‖ < ε 
:= by
  classical

  haveI hBorelA : BorelSpace (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  haveI : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  haveI : CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.compactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance
  letI mK : MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩
  haveI : Nonempty (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨1⟩
  set μK : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
    Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) with hμK
  haveI hKprob : IsProbabilityMeasure μK :=
    ⟨by rw [hμK, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  haveI hKright : μK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : IsProbabilityMeasure (μK.map (· * g)) :=
      Measure.isProbabilityMeasure_map_iff (measurable_mul_const g).aemeasurable |>.mpr inferInstance
    exact IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure (μK.map (· * g)) μK
  haveI hKinv : μK.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure μK.inv := by
      rw [Measure.inv_def]
      exact Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable |>.mpr inferInstance
    exact IsotypicProjection.eq_of_isMulLeftInvariant_of_isProbabilityMeasure μK.inv μK

  letI mA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  set μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haar with hμa
  haveI : μa.Regular := by rw [hμa]; infer_instance
  haveI hAright : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  have hxc : Continuous x := hx.2
  obtain ⟨hEfd, hEc, hEt, hEK⟩ :=
    AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F
      (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys x hxc hxt
  set E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
    (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ArchInfra.inclArch F κ))) with hE
  have hxE : x ∈ E := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g
    simp only [map_one, mul_one]
  obtain ⟨e, he, hecl, hefl, het, het', hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys E hEfd hEc hEt hEK

  have hxcm : x ∈ contMemberSubmodule F Φ₀ ξ := ⟨hx.1.1.1, hx.2⟩
  obtain ⟨V, hV, hVest⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt F hΦ₀ σ ξ hσ x hxcm (ε / 2)
      (half_pos hε)
  have hinclc : Continuous (adelicArchGLIncl F) :=
    AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl F
  have hVinf : (adelicArchGLIncl F) ⁻¹' V ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    refine hinclc.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨h₀, hh₀t, hh₀re, hh₀1, hh₀V, hh₀c, hh₀f⟩ :=
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ _ hVinf

  have hUimg : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) =
      ((U.map (glFin (𝓞 F) F) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :
        Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    (Subgroup.coe_map (glFin (𝓞 F) F) U).symm
  obtain ⟨C, hCpos, hC⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μK (ArchInfra.inclArch F) (ArchInfra.continuous_inclArch (F := F))
      (ArchInfra.archComponent_inclArch (F := F)) μa U hUf hUo hUc

  set I₀ : ℝ := ∫ a, (h₀ a).re ∂μa with hI₀
  have hh₀cont : Continuous h₀ := AutomorphicForm.continuous_of_isArchTestFactor F hh₀t
  have hh₀K : HasCompactSupport h₀ := hh₀t.2
  have hI₀pos : 0 < I₀ := by
    have hre : Continuous fun a => (h₀ a).re := Complex.continuous_re.comp hh₀cont
    have hreK : HasCompactSupport fun a => (h₀ a).re := hh₀t.2.comp_left Complex.zero_re
    exact hre.integral_pos_of_hasCompactSupport_nonneg_nonzero hreK (fun a => (hh₀re a).2) hh₀1.ne'
  set c : ℝ := (C * I₀)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (mul_pos hCpos hI₀pos)
  set h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun a => (c : ℂ) * h₀ a with hh
  have hht : IsArchTestFactor F h := IsArchTestFactor.const_mul' hh₀t (c : ℂ)
  have hhcont : Continuous h := continuous_const.mul hh₀cont
  have hhK : HasCompactSupport h := hh₀K.mul_left
  have hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y := fun w k y => by
    simp only [hh, hh₀c w k y]
  have hhf : ∀ y : GL (Fin 2) (InfiniteAdeleRing F), h y = conj (h y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ) := by
    intro y
    simp only [hh, map_mul, Complex.conj_ofReal, mul_assoc]
    rw [← hh₀f y]

  set fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      e p.1 * e p.2 * h ((ArchInfra.inclArch F p.1)⁻¹ * y * (ArchInfra.inclArch F p.2)⁻¹) ∂(μK.prod μK) with hfa
  set f : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa (glArch (𝓞 F) F g) *
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g) with hfdef
  obtain ⟨hfa_t, hfa_bf⟩ :=
    AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) tys e e he he h hht
  have hfa_bf' : IsArchFactorBiFinite F tys fa := hfa_bf het het'
  obtain ⟨hfa_c, hfa_f⟩ :=
    AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μK (ArchInfra.inclArch F) (ArchInfra.archComponent_inclArch (F := F)) σ e hecl hefl h hhc hhf
  have hsph : IsLevelSphericalOfType F tys U f :=
    ⟨fa, hfa_t, hfa_bf', fun w k y => hfa_c w k y, fun g => rfl⟩
  have hff : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) :=
    isFinTestFactor_indicator hUo hUc
  have hftest : IsFactorizableTestFn F f := ⟨fa, _, hfa_t, hff, fun g => rfl⟩
  have hflat : flat F σ f = f := by
    funext g
    show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ) = f g
    simp only [hfdef, map_inv]
    by_cases hg : glFin (𝓞 F) F g ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact inv_mem hg
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg', mul_one, mul_one]
      rw [ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2 g (SetLike.mem_coe.mp (hUi hg))]
      exact (hfa_f (glArch (𝓞 F) F g)).symm
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∉ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact fun h => hg (by simpa using inv_mem h)
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', mul_zero, mul_zero, map_zero, zero_mul]
  have hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hftest x hx

  have hconv : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = C * ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa :=
    hC e he h hhcont hhK hhc x hxc hxU (fun z => hrep x hxE z)
  set p : GL (Fin 2) (InfiniteAdeleRing F) → ℝ := fun a => (h₀ a).re / I₀ with hp
  have hconv' : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa := by
    intro g
    rw [hconv g]
    have h1 : ∀ a, x (g * adelicArchGLIncl F a) * h a = (c : ℂ) * (x (g * adelicArchGLIncl F a) * h₀ a) := fun a => by
      simp only [hh]; ring
    have h2 : ∀ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) = (x (g * adelicArchGLIncl F a) * h₀ a) * ((I₀ : ℂ))⁻¹ := by
      intro a
      simp only [hp, Complex.ofReal_div]
      rw [(hh₀re a).1]
      ring
    simp_rw [h1, h2, integral_const_mul, integral_mul_const]
    have hCc : (C : ℂ) * (c : ℂ) = ((I₀ : ℂ))⁻¹ := by
      simp only [hc, Complex.ofReal_inv, Complex.ofReal_mul]
      field_simp [Complex.ofReal_ne_zero.mpr hCpos.ne', Complex.ofReal_ne_zero.mpr hI₀pos.ne']
    rw [← mul_assoc, hCc, mul_comm]

  refine ⟨f, hftest, hsph, hflat, hxf, ?_⟩

  have hnorm : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ‖v‖ = ‖(v : Carrier F Φ₀ σ)‖ := fun v => rfl
  rw [hnorm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  have hkey : ‖toCarrier F hΦ₀ σ ξ ⟨x, hx.1.1.1⟩ -
        toCarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf.1.1.1⟩‖
      = (eLpNorm (x - rightConv F x f) 2 (weightedMeasure F Φ₀ σ)).toReal :=
    norm_toCarrier_sub hΦ₀ σ ξ x (rightConv F x f) hx.1.1.1 hxf.1.1.1
  rw [hkey]
  set ν : Measure (AdelicGL2 (𝓞 F) F) := weightedMeasure F Φ₀ σ with hν

  suffices hmain : eLpNorm (x - rightConv F x f) 2 ν ^ 2 ≤ ENNReal.ofReal (ε / 2) ^ 2 by
    have h1 : eLpNorm (x - rightConv F x f) 2 ν ≤ ENNReal.ofReal (ε / 2) :=
      (ENNReal.pow_le_pow_left_iff two_ne_zero).mp hmain
    calc (eLpNorm (x - rightConv F x f) 2 ν).toReal ≤ ε / 2 :=
          ENNReal.toReal_le_of_le_ofReal (half_pos hε).le h1
      _ < ε := half_lt_self hε

  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    infer_instance
  haveI : SFinite ν := by rw [hν, weightedMeasure]; infer_instance
  haveI : SFinite μa := by
    haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => properSpace_completion v
    haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
      inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := Units.isEmbedding_embedProduct.secondCountableTopology
    infer_instance

  have hpc : Continuous p := (Complex.continuous_re.comp hh₀cont).div_const _
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hh₀re a).2 hI₀pos.le
  have hp1 : ∫ a, p a ∂μa = 1 := by
    simp only [hp, integral_div]
    exact div_self hI₀pos.ne'
  have hpK : HasCompactSupport p := by
    have : p = (fun r : ℝ => r / I₀) ∘ (fun a => (h₀ a).re) := rfl
    rw [this]
    exact (hh₀t.2.comp_left Complex.zero_re).comp_left (zero_div _)
  have hU : Measurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) :=
    (hxc.comp (continuous_fst.mul (hinclc.comp continuous_snd))).measurable
  have hint : ∀ g : AdelicGL2 (𝓞 F) F, Integrable (fun a => x (g * adelicArchGLIncl F a) * (p a : ℂ)) μa := fun g =>
    ((hxc.comp (continuous_const.mul hinclc)).mul (Complex.continuous_ofReal.comp hpc)).integrable_of_hasCompactSupport
      ((hpK.comp_left Complex.ofReal_zero).mul_left)
  have hJ := MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq ν μa p hpc.measurable
    hp0 hp1 x hxc.measurable (fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) hU hint

  have hL : eLpNorm (x - rightConv F x f) 2 ν ^ 2 = ∫⁻ g, ‖x g - ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa‖ₑ ^ 2 ∂ν := by
    rw [AvgLift.eLpNorm_two_pow_two ν
      (memLp_weightedMeasure_of_mem F hΦ₀ σ
        ((memberSubmodule F Φ₀ ξ).sub_mem hx.1.1.1 hxf.1.1.1)).aestronglyMeasurable]
    refine lintegral_congr fun g => ?_
    rw [Pi.sub_apply, hconv' g]
  rw [hL]
  refine hJ.trans ?_

  have hpt : ∀ a, p a ≠ 0 → adelicArchGLIncl F a ∈ V := by
    intro a ha
    have : a ∈ tsupport h₀ := by
      refine subset_tsupport _ ?_
      intro h0; apply ha; simp only [hp, h0, Complex.zero_re, zero_div]
    exact hh₀V this
  have hB : ∀ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
      ≤ ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 := by
    intro a
    by_cases ha : p a = 0
    · simp [ha]
    obtain ⟨hy, hlt⟩ := hVest _ (hpt a ha)
    refine mul_le_mul_right ?_ _
    have heq : ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
        = eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν ^ 2 := by
      rw [AvgLift.eLpNorm_two_pow_two ν
        (memLp_weightedMeasure_of_mem F hΦ₀ σ
          ((memberSubmodule F Φ₀ ξ).sub_mem hy.1 hx.1.1.1)).aestronglyMeasurable]
      refine lintegral_congr fun g => ?_
      rw [Pi.sub_apply, rightTranslate_apply, enorm_sub_rev]
    rw [heq]
    have hlt' : eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν < ENNReal.ofReal (ε / 2) := by
      rw [norm_toCarrier_sub hΦ₀ σ ξ] at hlt
      exact (ENNReal.lt_ofReal_iff_toReal_lt (eLpNorm_sub_lt_top hΦ₀ σ hy.1 hx.1.1.1).ne).mpr hlt
    exact pow_le_pow_left' hlt'.le 2
  calc ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν ∂μa
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 ∂μa := lintegral_mono hB
    _ = (∫⁻ a, ENNReal.ofReal (p a) ∂μa) * ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [lintegral_mul_const _ hpc.measurable.ennreal_ofReal]
    _ = ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hpc.integrable_of_hasCompactSupport hpK) (ae_of_all _ hp0), hp1,
          ENNReal.ofReal_one, one_mul]



open CuspSubcarrierDense in
theorem exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ∃ π : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (ι κ))) (π κ)) ∧
      (∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π κ v‖ = ‖v‖) ∧
      (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => π κ v) 
:= by
  classical

  have hιeq : ι = ArchInfra.inclArch F := RowIsometryMonoidHom.eq_inclArch F ι hι
  have hιc : Continuous ι := by rw [hιeq]; exact ArchInfra.continuous_inclArch (F := F)

  let y : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F :=
    (adelicArchGLIncl F).comp ι
  have hy : ∀ κ, y κ = adelicArchGLIncl F (ι κ) := fun _ => rfl
  have hyc : Continuous y := (AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl F).comp hιc
  have hN : ∀ κ, NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (y κ)) = 1 :=
    fun κ => RowIsometryMonoidHom.ideleNorm_det_eq_one F ι hι κ
  have hmem : ∀ (κ) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (y κ) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun κ φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (y κ) φ hφ

  choose π₀ hπ₀ using fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
    AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ (y κ)
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hnorm : ∀ κ, ‖π₀ κ‖ ≤ 1 := fun κ => by
    have h := (hπ₀ κ).2
    rwa [hN κ, Real.one_rpow] at h

  have hone : π₀ 1 = 1 := by
    refine eq_of_isCuspLift (hmem 1) (hπ₀ 1).1 fun φ h => ?_
    have hR : rightTranslate F (y 1) φ = φ := by
      funext x; rw [map_one, rightTranslate_apply, mul_one]
    rw [one_apply_eq_self]
    congr 1
    exact Subtype.ext hR.symm
  have hmul : ∀ a b, π₀ (a * b) = π₀ a * π₀ b := by
    intro a b
    refine eq_of_isCuspLift (hmem (a * b)) (hπ₀ (a * b)).1 fun φ h => ?_
    have hb : rightTranslate F (y b) φ ∈ cuspMemberSubmodule F Φ₀ ξ := hmem b φ φ.2
    have hab : rightTranslate F (y a) (rightTranslate F (y b) φ) ∈ cuspMemberSubmodule F Φ₀ ξ :=
      hmem a _ hb
    rw [mul_apply_eq_comp, (hπ₀ b).1 φ hb, (hπ₀ a).1 ⟨_, hb⟩ hab]
    congr 1
    apply Subtype.ext
    show rightTranslate F (y a) (rightTranslate F (y b) φ) = rightTranslate F (y (a * b)) φ
    rw [rightTranslate_rightTranslate, map_mul]
  let π : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →*
      (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    { toFun := π₀, map_one' := hone, map_mul' := hmul }
  have hπ : ∀ κ, π κ = π₀ κ := fun _ => rfl

  have hiso : ∀ (κ) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π κ v‖ = ‖v‖ := by
    intro κ v
    apply le_antisymm
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [hπ]; nlinarith [hnorm κ, norm_nonneg v])
    · have hinv : π κ⁻¹ (π κ v) = v := by
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
      calc ‖v‖ = ‖π κ⁻¹ (π κ v)‖ := by rw [hinv]
        _ ≤ ‖π κ⁻¹‖ * ‖π κ v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖π κ v‖ := mul_le_mul_of_nonneg_right (hnorm κ⁻¹) (norm_nonneg _)
        _ = ‖π κ v‖ := one_mul _
  refine ⟨π, fun κ => (hπ₀ κ).1, hiso, fun v => ?_⟩

  refine continuous_iff_continuousAt.mpr fun κ₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v (ε / 3) hε3
  set a : ↥(cuspSubcarrier F hΦ₀ σ ξ) := toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ with ha

  obtain ⟨V, hV, hVlt⟩ := AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    F hΦ₀ σ ξ hσ φ ⟨hφ.1.1.1, hφ.2⟩ (ε / 3) hε3
  have hf : Continuous fun κ => y (κ₀⁻¹ * κ) := hyc.comp (continuous_const.mul continuous_id)
  have hf0 : (fun κ => y (κ₀⁻¹ * κ)) κ₀ = 1 := by simp
  have hpre : (fun κ => y (κ₀⁻¹ * κ)) ⁻¹' V ∈ 𝓝 κ₀ :=
    hf.continuousAt.preimage_mem_nhds (by rw [inv_mul_cancel, map_one]; exact hV)
  refine Filter.eventually_of_mem hpre fun κ hκ => ?_
  obtain ⟨hy', hlt⟩ := hVlt _ hκ

  have hmid : ‖π κ a - π κ₀ a‖ < ε / 3 := by
    have hκeq : π κ = π κ₀ * π (κ₀⁻¹ * κ) := by rw [← map_mul, mul_inv_cancel_left]
    have h1 : π κ a - π κ₀ a = π κ₀ (π (κ₀⁻¹ * κ) a - a) := by
      rw [map_sub, hκeq, mul_apply_eq_comp]
    rw [h1, hiso]
    have hlift : π (κ₀⁻¹ * κ) a = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y (κ₀⁻¹ * κ)) φ, hmem _ φ hφ⟩ :=
      (hπ₀ (κ₀⁻¹ * κ)).1 ⟨φ, hφ⟩ (hmem _ φ hφ)
    rw [hlift, ha, ← Submodule.norm_coe, Submodule.coe_sub, toCuspSubcarrier_apply_coe,
      toCuspSubcarrier_apply_coe]
    exact hlt

  rw [dist_eq_norm]
  have hsplit : π κ v - π κ₀ v = π κ (v - a) + (π κ a - π κ₀ a) + π κ₀ (a - v) := by
    simp only [map_sub]; abel
  calc ‖π κ v - π κ₀ v‖ = ‖π κ (v - a) + (π κ a - π κ₀ a) + π κ₀ (a - v)‖ := by rw [hsplit]
    _ ≤ ‖π κ (v - a)‖ + ‖π κ a - π κ₀ a‖ + ‖π κ₀ (a - v)‖ := norm_add₃_le
    _ = ‖v - a‖ + ‖π κ a - π κ₀ a‖ + ‖a - v‖ := by rw [hiso, hiso]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h2 : ‖a - v‖ < ε / 3 := by rw [norm_sub_rev]; exact hva
        linarith
    _ = ε := by ring

open CuspSubcarrierDense in
theorem exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    ∃ π : U →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ u : U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (π u)) ∧
      (∀ (u : U) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π u v‖ = ‖v‖) ∧
      (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : U => π u v) 
:= by
  classical

  let y : ↥U →* AdelicGL2 (𝓞 F) F := U.subtype
  have hy : ∀ u : ↥U, y u = (u : AdelicGL2 (𝓞 F) F) := fun _ => rfl
  have hyc : Continuous y := continuous_subtype_val
  have hN : ∀ u : ↥U, NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (y u)) = 1 :=
    fun u => NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F U hU
      (u : AdelicGL2 (𝓞 F) F) u.2
  have hmem : ∀ (u : ↥U) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (y u) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun u φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (y u) φ hφ

  choose π₀ hπ₀ using fun u : ↥U =>
    AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ (y u)
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hnorm : ∀ u, ‖π₀ u‖ ≤ 1 := fun u => by
    have h := (hπ₀ u).2
    rwa [hN u, Real.one_rpow] at h

  have hone : π₀ 1 = 1 := by
    refine eq_of_isCuspLift (hmem 1) (hπ₀ 1).1 fun φ h => ?_
    have hR : rightTranslate F (y 1) φ = φ := by
      funext x; rw [map_one, rightTranslate_apply, mul_one]
    rw [one_apply_eq_self]
    congr 1
    exact Subtype.ext hR.symm
  have hmul : ∀ a b, π₀ (a * b) = π₀ a * π₀ b := by
    intro a b
    refine eq_of_isCuspLift (hmem (a * b)) (hπ₀ (a * b)).1 fun φ h => ?_
    have hb : rightTranslate F (y b) φ ∈ cuspMemberSubmodule F Φ₀ ξ := hmem b φ φ.2
    have hab : rightTranslate F (y a) (rightTranslate F (y b) φ) ∈ cuspMemberSubmodule F Φ₀ ξ :=
      hmem a _ hb
    rw [mul_apply_eq_comp, (hπ₀ b).1 φ hb, (hπ₀ a).1 ⟨_, hb⟩ hab]
    congr 1
    apply Subtype.ext
    show rightTranslate F (y a) (rightTranslate F (y b) φ) = rightTranslate F (y (a * b)) φ
    rw [rightTranslate_rightTranslate, map_mul]
  let π : ↥U →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    { toFun := π₀, map_one' := hone, map_mul' := hmul }
  have hπ : ∀ u, π u = π₀ u := fun _ => rfl

  have hiso : ∀ (u) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π u v‖ = ‖v‖ := by
    intro u v
    apply le_antisymm
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [hπ]; nlinarith [hnorm u, norm_nonneg v])
    · have hinv : π u⁻¹ (π u v) = v := by
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
      calc ‖v‖ = ‖π u⁻¹ (π u v)‖ := by rw [hinv]
        _ ≤ ‖π u⁻¹‖ * ‖π u v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖π u v‖ := mul_le_mul_of_nonneg_right (hnorm u⁻¹) (norm_nonneg _)
        _ = ‖π u v‖ := one_mul _
  refine ⟨π, fun u => (hπ₀ u).1, hiso, fun v => ?_⟩

  refine continuous_iff_continuousAt.mpr fun u₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v (ε / 3) hε3
  set a : ↥(cuspSubcarrier F hΦ₀ σ ξ) := toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ with ha
  obtain ⟨V, hV, hVlt⟩ := AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    F hΦ₀ σ ξ hσ φ ⟨hφ.1.1.1, hφ.2⟩ (ε / 3) hε3
  have hf : Continuous fun u : ↥U => y (u₀⁻¹ * u) := hyc.comp (continuous_const.mul continuous_id)
  have hpre : (fun u : ↥U => y (u₀⁻¹ * u)) ⁻¹' V ∈ 𝓝 u₀ :=
    hf.continuousAt.preimage_mem_nhds (by rw [inv_mul_cancel, map_one]; exact hV)
  refine Filter.eventually_of_mem hpre fun u hu => ?_
  obtain ⟨hy', hlt⟩ := hVlt _ hu
  have hmid : ‖π u a - π u₀ a‖ < ε / 3 := by
    have hκeq : π u = π u₀ * π (u₀⁻¹ * u) := by rw [← map_mul, mul_inv_cancel_left]
    have h1 : π u a - π u₀ a = π u₀ (π (u₀⁻¹ * u) a - a) := by
      rw [map_sub, hκeq, mul_apply_eq_comp]
    rw [h1, hiso]
    have hlift : π (u₀⁻¹ * u) a = toCuspSubcarrier F hΦ₀ σ ξ
        ⟨rightTranslate F (y (u₀⁻¹ * u)) φ, hmem _ φ hφ⟩ :=
      (hπ₀ (u₀⁻¹ * u)).1 ⟨φ, hφ⟩ (hmem _ φ hφ)
    rw [hlift, ha, ← Submodule.norm_coe, Submodule.coe_sub, toCuspSubcarrier_apply_coe,
      toCuspSubcarrier_apply_coe]
    exact hlt
  rw [dist_eq_norm]
  have hsplit : π u v - π u₀ v = π u (v - a) + (π u a - π u₀ a) + π u₀ (a - v) := by
    simp only [map_sub]; abel
  calc ‖π u v - π u₀ v‖ = ‖π u (v - a) + (π u a - π u₀ a) + π u₀ (a - v)‖ := by rw [hsplit]
    _ ≤ ‖π u (v - a)‖ + ‖π u a - π u₀ a‖ + ‖π u₀ (a - v)‖ := norm_add₃_le
    _ = ‖v - a‖ + ‖π u a - π u₀ a‖ + ‖a - v‖ := by rw [hiso, hiso]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h2 : ‖a - v‖ < ε / 3 := by rw [norm_sub_rev]; exact hva
        linarith
    _ = ε := by ring


end AutomorphicForm.CuspidalSpectrum
