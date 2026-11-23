/-
The constituent spine: the cuspidal constituent of a cusp subrepresentation inside the intersection of
its level-invariant and archimedean-cut pieces.

Two rows of the "cuspidal constituent" spine, differing only in how the finite-level invariance is
spelled:

* `iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le` — for a cusp
  subrepresentation `V` of the production pins and a Hecke-stable `archCut` piece `M`, the
  intersection of all `IsCuspSubrep` submodules of `M ∩ levelInvariantSubmodule N ∩ archCutSubmodule`
  is `V`;
* `…_inf_invariants_…` — the same with the level hypothesis moved to the invariants of the subgroup.

They are the containment half of the spine that makes the cuspidal spectrum's constituents
irreducible (`Cusp/SpectrumConstituentClosure.lean` is their sibling), and they consume the test
function calculus (`Adelic/{TestFnInvariance,TestFnTop,RightConvIntegral,RightConvRegularity}.lean`),
the archimedean approximation (`Adelic/ArchApproximation.lean`) and the spectrum integration
(`Cusp/SpectrumIntegration.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le.lean>

spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le.lean

Measurements (order AF103D, measured at landing, not estimated; pin `aa2d8b3`, 595 lines):

* `spec/check_port.py --force` → **10 ok / 0 mismatch / 0 missing / 0 own / 0 kw**, every declaration
  `ok` — the eight distinct public engine rows and the two headlines.
* the pin-vs-module declaration diff (`statement_db`, over the module's four `spec-pin` wires):
  **31 pin rows** (the 15 + 14 `S_` rows — every second-pin engine row is the first pin's by name —
  plus the two `Theorems/` headlines) against **18 module declarations**: **16 by hash, 0 by name,
  2 unaccounted** (`prodPins`, `spine_le`, the two invented helpers, both `private`).
* `dedup.py --within` → **0 duplicate clusters** (18 declarations, 0 removable lines);
  `move_dead.py --dry-run` → **0 declarations, 0 lines**.
* `#print axioms` on all **10** public declarations → `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.
* heartbeat probe pair (**recorded, never installed** — the module carries no `set_option
  maxHeartbeats`): `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop
  cap **N = 200000** and down to **N = 20000**; it first fails at **N = 15000** (one `(kernel)
  deterministic timeout` inside `spine_le`, plus the two downstream `unknown constant` errors on the
  headlines), and at **N = 12000** (a `whnf` timeout and a tactic-execution timeout at the
  `exists_integral_rightTranslate_eq_inv_card_mul_sum` step).

Why 10 `ok` and not the order's ≈20: the two `S_` pins carry the **same** fourteen-declaration engine
verbatim, so the second pin's public `S_` rows are the first's by name and every engine row matches
twice over the wire (`hash-ok (2 pin rows)`). The estimate's "18 public engine rows" is nine per pin,
of which one is that pin's own `solution` — its copy of its headline, `statement_db`-hash-equal to its
`Theorems/` row. The distinct declarations are therefore 8 public engine rows + 2 headlines = **10**,
written once (substitute-first; a second engine copy would also be a `dedup --within` cluster).

Substitutions and the `levelAvg` decision (imported or called, never re-proved):

* `commute_of_glArch_eq_one_of_glFin_eq_one` — public in the port at
  `AutomorphicForm/Adelic/RightConvIntegral.lean:72`; restated here at the pin's own statement with the
  port's proof in one line. `glFin_eq_one_of_mem_iSup_range` — public at
  `AutomorphicForm/Adelic/TestFnInvariance.lean:164`, also one line.
* the pin's 26-line compactness derivation of `pins.U N` inside `solution` is replaced by the port's
  `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` (`Adelic/LevelCompactness.lean:150`) — a proof step,
  not a row.
* the rows' **premises** are imported at the pins' own calls: `isCuspSubrep_span_cyclic_and_mem_and_le`,
  `exists_linearMap_archCutProjector`, `exists_integral_rightTranslate_eq_inv_card_mul_sum`,
  `exists_integral_rightConv_eq_rightConv`, `isFactorizableTestFn_comp_inv_mul`,
  `continuous_and_hasCompactSupport_of_isFactorizableTestFn`,
  `continuous_rightConv_of_continuous_of_hasCompactSupport`.
* **`levelAvg`**: `port_advise`'s `levelAvg → AutomorphicForm.ArchCxGL.conjFn` is a type-only false
  positive (FR-0266) — `conjFn φ = fun g => starRingEnd ℂ (φ g)` is complex conjugation
  (`ArchCasimirComplex.lean:795`), not a level average, and `rg` finds no `levelAvg`/`subgroupProb`
  anywhere in the port. `subgroupProb`, `levelAvg` and the four `levelAvg_*` rows are transcribed.
  `rightConv_comp_mul_left_eq` is `private` in `ArchApproximation.lean:596` (not importable) and is
  transcribed as the pin's public row; `rightTranslate_mem_{of_mem_iSup_range,
  archCutSubmodule_of_mem_iSup_range,archCutSubmodule_of_mem_finiteAdelic}` and
  `continuous_of_mem_cuspKFiniteSubmodule` are `private` in the port's siblings (`ArchApproximation`,
  `SpectrumLift`, `SpectrumConstituentClosure`/`CutWeightDecomposition`) and stay `private` here, as
  the pins have them.

Structure: the engine is one copy in the subject namespace `CuspidalConstituent.Spine` (the pins'
`F4CutWords` label dropped); no other module in the port carries this engine — the private
`CuspidalConstituent.ArchSplit` engine of `Cusp/IrreducibleSpine.lean` belongs to the *other* pair of
constituent pins (the `exists_inf_…_isIrreducible` pair) and shares with it only
`continuous_of_mem_cuspKFiniteSubmodule`, which this pin states `private`, so it is restated here.
The two rows differ only in the two hypotheses of the shared `private theorem spine_le`: `hLmem`
(membership in `L` is right-`U`-invariance) and `hLarch` (a right translate by an archimedean element
preserves `L`) — the first row instantiates `L := levelInvariantSubmodule F pins N` with `Iff.rfl` and
the pin's own `rightTranslate_mem_levelInvariantSubmodule_of_glFin_eq_one`, the second
`L := Representation.invariants` with the two-line invariant spellings. FR-0274: every public name
here is either the scaffold's headline or lives in `CuspidalConstituent.Spine`, which no other module
uses; the private `continuous_of_mem_cuspKFiniteSubmodule` does not clash with the port's public
`CuspidalConstituent.continuous_of_mem_cuspKFiniteSubmodule` — the two elaborate together
(`tmp/af103/collision-D.lean`, silent).
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConstituentClosure
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumIntegration
import FLTForHuman.AutomorphicForm.Adelic.RightConvIntegral
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.TestFnInvariance
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop

set_option autoImplicit false

-- The two pins write `letI`/`haveI` at their instance binders; the module keeps the pins' proof text,
-- so the v4.34 style rule that would rewrite them to `let`/`have` is off for the file (the same option
-- 350 other ported modules carry).
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

namespace AutomorphicForm.CuspidalConstituent

/-! The shared engine of the two rows. The two `S_` pins carry the *same* fourteen-declaration engine
verbatim — every engine row of the second pin is the first pin's by name — so it is written **once**
here, in a subject namespace of its own, and neither headline re-proves it. The two rows differ only in
the last helper (`levelInvariantSubmodule` against `Representation.invariants`), and that difference is
carried by the two hypotheses `hLmem`/`hLarch` of the shared argument `spine_le`.

No other module carries this engine: the port's nearest twin is one row of it,
`continuous_of_mem_cuspKFiniteSubmodule`, which the two `S_…_exists_inf_…_isIrreducible_of_isCuspSubrep`
pins also carry — ported privately in `Cusp/IrreducibleSpine.lean` as `CuspidalConstituent.ArchSplit`
and publicly in that file's `CuspidalConstituent` block. This pin states the row `private`, so it is
restated `private` here and the two copies coexist (FR-0274). -/
namespace Spine

variable (F : Type) [Field F] [NumberField F]

/-- The production pins of both rows, as one abbreviation (the pins term is written out in the two
checked headlines, which are the pins' own statements). -/
private abbrev prodPins (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

/-- Port has this publicly (`AutomorphicForm/Adelic/RightConvIntegral.lean`); the row is restated here
at the pin's own statement with the port's proof in one line. -/
theorem commute_of_glArch_eq_one_of_glFin_eq_one {g k : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hk : glFin (𝓞 F) F k = 1) : Commute g k :=
  AutomorphicForm.commute_of_glArch_eq_one_of_glFin_eq_one F hg hk

variable (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))

/-- Normalised Haar measure of a compact open level subgroup. -/
def subgroupProb : @Measure U (borel U) :=
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  Measure.haarMeasure ⊤

/-- Averaging over the compact open level subgroup. -/
def levelAvg (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun x => ∫ u, φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂(subgroupProb F U hU)

theorem levelAvg_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    levelAvg F U hU (φ + ψ) = levelAvg F U hU φ + levelAvg F U hU ψ := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  funext x
  simp only [levelAvg, Pi.add_apply]
  have hi : ∀ {θ : AdelicGL2 (𝓞 F) F → ℂ}, Continuous θ →
      Integrable (fun u : U => θ (x * (u : AdelicGL2 (𝓞 F) F))) (subgroupProb F U hU) := fun hθ =>
    (hθ.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_add (hi hφ) (hi hψ)

theorem levelAvg_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    levelAvg F U hU (c • φ) = c • levelAvg F U hU φ := by
  funext x
  simp only [levelAvg, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem levelAvg_eq_self {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x) : levelAvg F U hU φ = φ := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  haveI : IsProbabilityMeasure (subgroupProb F U hU) :=
    ⟨by rw [subgroupProb, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  funext x
  simp only [levelAvg]
  rw [show (fun u : U => φ (x * (u : AdelicGL2 (𝓞 F) F))) = fun _ => φ x from funext fun u => hφ x u u.2]
  simp

theorem levelAvg_apply_mul (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ U) : levelAvg F U hU φ (x * u) = levelAvg F U hU φ x := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  simp only [levelAvg]
  have h := integral_mul_left_eq_self (μ := subgroupProb F U hU)
    (fun v : U => φ (x * (v : AdelicGL2 (𝓞 F) F))) ⟨u, hu⟩
  simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
  rw [subgroupProb] at h ⊢
  exact h

theorem rightConv_comp_mul_left_eq (ψ f : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    rightConv F ψ (fun z => f (h⁻¹ * z)) = rightTranslate F h (rightConv F ψ f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  show (∫ z, ψ (x * z) * f (h⁻¹ * z) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * h * z) * f z ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
  rw [← MeasureTheory.integral_mul_left_eq_self (fun z => ψ (x * z) * f (h⁻¹ * z)) h]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem glFin_eq_one_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    glFin (𝓞 F) F k = 1 :=
  AutomorphicForm.glFin_eq_one_of_mem_iSup_range F hk

private theorem rightTranslate_mem_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hM : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ M, rightTranslate F k φ ∈ M := by
  refine Subgroup.iSup_induction _ (C := fun k => ∀ φ ∈ M, rightTranslate F k φ ∈ M) hk ?_ ?_ ?_
  · rintro w k ⟨k', rfl⟩; exact hM w k'
  · intro φ hφ
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rwa [this]
  · intro a b ha hb φ hφ
    rw [← rightTranslate_rightTranslate]
    exact ha _ (hb _ hφ)

private theorem rightTranslate_mem_archCutSubmodule_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    (tys : ArchTypeFamily F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F k φ ∈ archCutSubmodule F tys :=
  rightTranslate_mem_of_mem_iSup_range F _
    (fun w k _φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) hk

private theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic (F : Type) [Field F] [NumberField F]
    (tys : ArchTypeFamily F) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F g φ ∈ archCutSubmodule F tys := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun φ => rightTranslate F g φ ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hφ w) ?_ ?_ ?_
  · intro i f hfi
    refine Submodule.mem_iSup_of_mem i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
      commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg)
        (glFin_rowIsometryInclAt₀ F w k')
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

private theorem rightTranslate_mem_levelInvariantSubmodule_of_glFin_eq_one (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (N : Ideal (𝓞 F)) (hU : pins.U N ≤ finiteAdelicGL2Subgroup F)
    {k : AdelicGL2 (𝓞 F) F} (hk : glFin (𝓞 F) F k = 1) :
    ∀ φ ∈ levelInvariantSubmodule F pins N, rightTranslate F k φ ∈ levelInvariantSubmodule F pins N := by
  intro φ hφ x u hu
  show φ (x * u * k) = φ (x * k)
  have hc : Commute u k :=
    commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F u).mp (hU hu)) hk
  rw [mul_assoc, hc.eq, ← mul_assoc]
  exact hφ (x * k) u hu

private theorem continuous_of_mem_cuspKFiniteSubmodule (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hc, -⟩; exact hc
  · exact continuous_const
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha; exact ha.const_smul c

/-- The containment argument, once, for both rows. `V` is the cusp subrepresentation, `L` the level
piece (`levelInvariantSubmodule F pins N` in the first row, `Representation.invariants` of the compact
open level subgroup in the second), `M` the Hecke-stable archimedean piece. The only things the argument
needs to know about `L` are its two hypotheses: membership is right-`U`-invariance (`hLmem`), and a
right translate by an archimedean element preserves it (`hLarch`). -/
private theorem spine_le
    (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUc : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (prodPins F D) ξ V)
    (L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hLmem : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ L ↔ ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x)
    (hLarch : ∀ (k : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F k = 1 → ∀ φ ∈ L, rightTranslate F k φ ∈ L)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ M ⊓ L, (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (u * x) = f x ∧ f (x * u) = f x) → ∀ φ ∈ M, rightConv F φ f ∈ M) :
    (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspSubrep F (prodPins F D) ξ W ∧ V ⊓ L ⊓ archCutSubmodule F tys ⊓ M ≤ W), W)
      ⊓ L ⊓ archCutSubmodule F tys ≤ M := by
  classical
  set pins := prodPins F D with hpins
  set A : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := archCutSubmodule F tys with hA
  set Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ L ⊓ A ⊓ M with hY
  let C : (AdelicGL2 (𝓞 F) F → ℂ) → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun Ψ => Submodule.span ℂ
      {φ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        φ = rightTranslate F (g * k) Ψ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          φ = rightTranslate F (g * k) (rightConv F Ψ f)}
  set S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨆ y : Y, C (y : AdelicGL2 (𝓞 F) F → ℂ) with hS_def

  have hC : ∀ y : Y, IsCuspSubrep F pins ξ (C y) ∧ (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ C y ∧ C y ≤ V := by
    intro y
    have hyV : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ V := y.2.1.1.1
    obtain ⟨h1, h2, h3, -⟩ := AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le F D
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)
      ξ V hV (y : AdelicGL2 (𝓞 F) F → ℂ) hyV
    exact ⟨h1, h2, h3⟩
  have hSV : S ≤ V := iSup_le fun y => (hC y).2.2
  have hVc : ∀ φ ∈ V, Continuous φ := fun φ hφ =>
    continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.le hφ)

  have hS : IsCuspSubrep F pins ξ S := by
    refine ⟨iSup_le fun y => (hC y).1.le, ?_, ?_, ?_⟩
    · intro g hg φ hφ
      refine Submodule.iSup_induction (motive := fun φ => rightTranslate F g φ ∈ S) _ hφ ?_ ?_ ?_
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightTranslate_fin_mem g hg φ hφy)
      · show rightTranslate F _ 0 ∈ S
        rw [rightTranslate_zero]; exact Submodule.zero_mem _
      · intro a b ha hb
        show rightTranslate F _ (a + b) ∈ S
        rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb
    · intro w k φ hφ
      refine Submodule.iSup_induction (motive := fun φ => rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ S) _ hφ ?_ ?_ ?_
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightTranslate_arch_mem w k φ hφy)
      · show rightTranslate F _ 0 ∈ S
        rw [rightTranslate_zero]; exact Submodule.zero_mem _
      · intro a b ha hb
        show rightTranslate F _ (a + b) ∈ S
        rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb
    · intro f tys' hf hbf φ hφ
      obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
      refine Submodule.iSup_induction' _ (motive := fun φ _ => rightConv F φ f ∈ S) ?_ ?_ ?_ hφ
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightConv_mem f tys' hf hbf φ hφy)
      · show rightConv F 0 f ∈ S
        rw [show (0 : AdelicGL2 (𝓞 F) F → ℂ) = fun _ => 0 from rfl, rightConv_zero_left]
        exact Submodule.zero_mem _
      · intro a b ha hb ha' hb'
        show rightConv F (a + b) f ∈ S
        rw [rightConv_add_left F (hVc a (hSV ha)) (hVc b (hSV hb)) hfc hfs]
        exact Submodule.add_mem _ ha' hb'
  have hYS : Y ≤ S := by
    intro y hy
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : Y) (hC ⟨y, hy⟩).2.1

  have hW₀S : (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : IsCuspSubrep F pins ξ W ∧ V ⊓ L ⊓ A ⊓ M ≤ W), W) ≤ S :=
    iInf₂_le S ⟨hS, hYS⟩

  letI : MeasurableSpace U := borel _
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  haveI : (subgroupProb F U hUc).IsHaarMeasure := by unfold subgroupProb; infer_instance
  haveI : IsProbabilityMeasure (subgroupProb F U hUc) :=
    ⟨by rw [subgroupProb, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

  obtain ⟨Q, hQid, -, hQconv⟩ := AutomorphicForm.exists_linearMap_archCutProjector F tys

  let Cont : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    { carrier := {φ | Continuous φ}
      zero_mem' := continuous_const
      add_mem' := fun {a b} ha hb => Continuous.add ha hb
      smul_mem' := fun c {a} ha => Continuous.const_smul ha c }
  let PN : Cont →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun φ => levelAvg F U hUc φ
      map_add' := fun a b => levelAvg_add F U hUc a.2 b.2
      map_smul' := fun c a => levelAvg_smul F U hUc c a }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend PN
  have hΛ' : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ), Continuous φ → Λ φ = levelAvg F U hUc φ := by
    intro φ hφ
    have := LinearMap.congr_fun hΛ ⟨φ, hφ⟩
    exact this

  have hP : ∃ P : V →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : V, (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ L ⊓ A → P φ = φ) ∧
      (∀ y ∈ Y, ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ∀ hv : rightTranslate F (g * k) y ∈ V, P ⟨_, hv⟩ ∈ M) ∧
      (∀ y ∈ Y, ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys' : ArchTypeFamily F), IsFactorizableTestFn F f → IsArchBiFinite F tys' f →
        ∀ hv : rightTranslate F (g * k) (rightConv F y f) ∈ V, P ⟨_, hv⟩ ∈ M) := by
    refine ⟨Λ ∘ₗ Q ∘ₗ V.subtype, ?_, ?_, ?_⟩
    ·
      rintro φ ⟨hφL, hφA⟩
      show Λ (Q (φ : AdelicGL2 (𝓞 F) F → ℂ)) = φ
      rw [hQid _ (hVc _ φ.2) hφA, hΛ' _ (hVc _ φ.2)]
      exact levelAvg_eq_self F U hUc ((hLmem _).mp hφL)
    ·
      intro y hy g hg k hk hv
      have hyV : y ∈ V := hy.1.1.1
      have hyL : y ∈ L := hy.1.1.2
      have hyA : y ∈ A := hy.1.2
      have hyM : y ∈ M := hy.2
      have hkfin : glFin (𝓞 F) F k = 1 := glFin_eq_one_of_mem_iSup_range F hk
      have hy'M : rightTranslate F k y ∈ M := rightTranslate_mem_of_mem_iSup_range F M hMk hk y hyM
      have hy'L : rightTranslate F k y ∈ L := hLarch k hkfin y hyL
      have hy'A : rightTranslate F k y ∈ A := rightTranslate_mem_archCutSubmodule_of_mem_iSup_range F tys hk y hyA
      have hsplit : rightTranslate F (g * k) y = rightTranslate F g (rightTranslate F k y) :=
        (rightTranslate_rightTranslate F k g y).symm
      have hvA : rightTranslate F (g * k) y ∈ A := by
        rw [hsplit]; exact rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic F tys hg _ hy'A
      show Λ (Q (rightTranslate F (g * k) y)) ∈ M
      rw [hQid _ (hVc _ hv) hvA, hΛ' _ (hVc _ hv), hsplit]
      obtain ⟨n, reps, h1, h2, h3, _, heq⟩ :=
        AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum F U hUc
          O hO hUO (subgroupProb F U hUc) ((hLmem _).mp hy'L) hg
      have hsum : levelAvg F U hUc (rightTranslate F g (rightTranslate F k y)) =
          (n : ℂ)⁻¹ • fun x => ∑ i, rightTranslate F k y (x * reps i) := by
        funext x
        exact heq x
      rw [hsum]
      exact M.smul_mem _ (hMhecke g hg n reps h1 h2 h3 _ ⟨hy'M, hy'L⟩)
    ·
      intro y hy g hg k hk f tys' hf hbf hv
      have hyV : y ∈ V := hy.1.1.1
      have hyL : y ∈ L := hy.1.1.2
      have hyA : y ∈ A := hy.1.2
      have hyM : y ∈ M := hy.2
      have hyc : Continuous y := hVc y hyV
      have hc1 : rightTranslate F (g * k) (rightConv F y f) = rightConv F y (fun z => f ((g * k)⁻¹ * z)) :=
        (rightConv_comp_mul_left_eq F y f (g * k)).symm
      obtain ⟨hf1, hbf1⟩ := AutomorphicForm.isFactorizableTestFn_comp_inv_mul F tys' hf hbf hg hk
      obtain ⟨f', hf', hbf', hQeq⟩ := hQconv y hyc hyA _ tys' hf1 hbf1
      show Λ (Q (rightTranslate F (g * k) (rightConv F y f))) ∈ M
      rw [hc1, hQeq]
      obtain ⟨hf'c, hf's⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f' hf'
      have hcont : Continuous (rightConv F y f') :=
        AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F y hyc f' hf'c hf's
      rw [hΛ' _ hcont]
      obtain ⟨f'', hf'', hbf'', hinv'', heq''⟩ :=
        AutomorphicForm.exists_integral_rightConv_eq_rightConv F U hUc
          O hO hUO (subgroupProb F U hUc) tys hyc ((hLmem _).mp hyL) hf' hbf'
      have havg : levelAvg F U hUc (rightConv F y f') = rightConv F y f'' := funext heq''
      rw [havg]
      exact hMconv f'' hf'' hbf'' hinv'' y hyM

  have hmain : S ⊓ L ⊓ A ≤ M := by
    obtain ⟨P, hPid, hPgen, hPconv⟩ := hP
    rintro φ ⟨⟨hφS, hφL⟩, hφA⟩
    have hφV : φ ∈ V := hSV hφS
    have hfix : P ⟨φ, hφV⟩ = φ := hPid ⟨φ, hφV⟩ ⟨hφL, hφA⟩
    rw [← hfix]

    have key : ∀ ψ (hψ : ψ ∈ S), P ⟨ψ, hSV hψ⟩ ∈ M := by
      intro ψ hψ
      refine Submodule.iSup_induction' _
        (motive := fun ψ hψ => P ⟨ψ, hSV hψ⟩ ∈ M) ?_ ?_ ?_ hψ
      · rintro ⟨y, hy⟩ ψ hψC
        have hCV : C y ≤ V := (hC ⟨y, hy⟩).2.2
        suffices h : ∀ hv : ψ ∈ V, P ⟨ψ, hv⟩ ∈ M from h _
        refine Submodule.span_induction
          (p := fun ψ _ => ∀ hv : ψ ∈ V, P ⟨ψ, hv⟩ ∈ M) ?_ ?_ ?_ ?_ hψC
        · rintro χ ⟨g, hg, k, hk, hχ⟩ hv
          rcases hχ with rfl | ⟨f, tys', hf, hbf, rfl⟩
          · exact hPgen y hy g hg k hk hv
          · exact hPconv y hy g hg k hk f tys' hf hbf hv
        · intro hv
          have : (⟨0, hv⟩ : V) = 0 := rfl
          rw [this, map_zero]; exact M.zero_mem
        · intro a b ha hb iha ihb hv
          have : (⟨a + b, hv⟩ : V) = ⟨a, hCV ha⟩ + ⟨b, hCV hb⟩ := rfl
          rw [this, map_add]; exact M.add_mem (iha _) (ihb _)
        · intro c a ha iha hv
          have : (⟨c • a, hv⟩ : V) = c • ⟨a, hCV ha⟩ := rfl
          rw [this, map_smul]; exact M.smul_mem c (iha _)
      · show P ⟨0, hSV (Submodule.zero_mem _)⟩ ∈ M
        have : (⟨0, hSV (Submodule.zero_mem _)⟩ : V) = 0 := rfl
        rw [this, map_zero]; exact M.zero_mem
      · intro a b ha hb iha ihb
        show P ⟨a + b, hSV (Submodule.add_mem _ ha hb)⟩ ∈ M
        have : (⟨a + b, hSV (Submodule.add_mem _ ha hb)⟩ : V) = ⟨a, hSV ha⟩ + ⟨b, hSV hb⟩ := rfl
        rw [this, map_add]; exact M.add_mem iha ihb
    exact key φ hφS
  intro φ hφ
  rcases hφ with ⟨⟨hφW, hφL⟩, hφA⟩
  exact hmain ⟨⟨hW₀S hφW, hφL⟩, hφA⟩

end Spine
theorem iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
        ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j) →
      ∀ φ ∈ M ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N,
        (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, f (u * x) = f x ∧ f (x * u) = f x) →
      ∀ φ ∈ M, rightConv F φ f ∈ M) :
    (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧
          V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M ≤ W), W)
      ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := by
  classical
  set pins := productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hpins
  have hUO : pins.U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
  have hUf : pins.U N ≤ finiteAdelicGL2Subgroup F := by rw [hUO]; exact inf_le_right
  have hUc : IsCompact ((pins.U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [hUO]; exact isCompact_levelOne_inf_finiteAdelicGL2Subgroup F N
  exact Spine.spine_le F D ξ (pins.U N) hUc (levelOne (𝓞 F) F N) (isOpen_levelOne (𝓞 F) F hN) hUO
    tys V hV (levelInvariantSubmodule F pins N) (fun _ => Iff.rfl)
    (fun k hk φ hφ =>
      Spine.rightTranslate_mem_levelInvariantSubmodule_of_glFin_eq_one F pins N hUf hk φ hφ)
    M hMk hMhecke hMconv

theorem iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ M ⊓ Representation.invariants ((rightRegular F).comp U.subtype), (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (u * x) = f x ∧ f (x * u) = f x) → ∀ φ ∈ M, rightConv F φ f ∈ M) :
    (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧ V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ⊓ M ≤ W), W)
      ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ≤ M := by
  classical
  set L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Representation.invariants ((rightRegular F).comp U.subtype) with hL
  have hLmem : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      φ ∈ L ↔ ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := by
    intro φ
    rw [hL, Representation.mem_invariants]
    constructor
    · intro h x u hu
      exact congrFun (h ⟨u, hu⟩) x
    · intro h u
      funext x
      exact h x u u.2
  have hLarch : ∀ (k : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F k = 1 → ∀ φ ∈ L, rightTranslate F k φ ∈ L := by
    intro k hk φ hφ
    have hUf : U ≤ finiteAdelicGL2Subgroup F := by rw [hUO]; exact inf_le_right
    refine (hLmem _).mpr fun x u hu => ?_
    show φ (x * u * k) = φ (x * k)
    have hc : Commute u k :=
      Spine.commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F u).mp (hUf hu)) hk
    rw [mul_assoc, hc.eq, ← mul_assoc]
    exact (hLmem _).mp hφ (x * k) u hu
  exact Spine.spine_le F D ξ U hU O hO hUO tys V hV L hLmem hLarch M hMk hMhecke hMconv

end AutomorphicForm.CuspidalConstituent
