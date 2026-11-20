/-
  Compactness of the integral subgroup `GL₂(ℤ_[p])`.

  `LocalGL2.integralSubgroup R K` (`RepTheory/LocalLanglands/IntegralSubgroup.lean`) is the image
  of `GL₂(R) → GL₂(K)` under the coefficient map, so it is compact whenever the coefficient ring
  `R` is: `GL₂(R)` is the unit group of the compact topological ring `M₂(R)`, which embeds as a
  closed subspace of `M₂(R) × M₂(R)ᵐᵒᵖ`, and the structure map `GL₂(R) → GL₂(K)` is continuous as
  soon as `algebraMap R K` is. The module states that in the three shapes the local Langlands
  side consumes — the abstract `R`/`K` form, the `ℤ_[p]`/`ℚ_[p]` instance, and the bundled
  `CompactSpace` on the subgroup itself. Downstream (`NumberTheory/LocalNewvector/`) this is what
  turns a sum over the open compact `GL₂(ℤ_[p])` into a finite sum, which is the point of the
  fixed-vector and conductor bounds `ConductorDatum` is stated with.

  Transcribed from `Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean` (pinned
  `aa2d8b3`, 40 lines / 5 declarations): all five are here at the pin's names, statements, and
  visibility. `instCompactSpaceMatrix` is the pin's `instance` body and all (the `Matrix` compact
  space is the `m → n → R` product one); `gl2_compactSpace` is the pin's `inferInstance`;
  `isCompact_coe_integralSubgroup` is the pin's proof, with the pin's `Matrix.GeneralLinearGroup.map`
  unfolding and its `simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range]` closing move.

  spec-pin: Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean

  ## Port deltas

  - `import Mathlib` replaced by the five specific mathlib modules the proofs use:
    `Topology.Algebra.Group.Units` (`CompactSpace αˣ` from `[T1Space α] [ContinuousMul α]
    [CompactSpace α]`, via `isClosedEmbedding_embedProduct.compactSpace` — the instance
    `gl2_compactSpace`'s `inferInstance` lands on), `Topology.Algebra.Monoid`
    (`Continuous.units_map`),
    `Topology.Compactness.Compact` (`Pi.compactSpace`, `isCompact_range`,
    `isCompact_iff_compactSpace`), `Topology.Instances.Matrix` (`continuous_matrix`) and
    `NumberTheory.Padics.ProperSpace` (`PadicInt.compactSpace`). This is the port's standing
    substitution (cf. `RepTheory/LocalLanglands/IntegralSubgroup.lean`), and it is what keeps the
    module inside the silence gate's time budget: a bare `import Mathlib` here loads a 6.1 GB
    olean closure on a 7 GB machine and takes over 100 s per run.
  - `haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R` is written `have` (one site, in
    `isCompact_coe_integralSubgroup`): at mathlib `v4.34` the `haveI`/`letI` style linter fires on a
    `Prop`-valued binding and would break the silence gate. The substitution is statement-neutral
    and the local hypothesis still serves as the instance (FR-0223's class).

  ## Deferred pin surface

  None. The pin is 40 lines / 5 declarations and the module declares exactly those five;
  `move_dead.py` reads 0 declarations / 0 lines, and `dedup.py --within` reads 0 clusters.

  ## Gates

  - `check_port --force` — 5 ok, 0 mismatch, 0 missing, 0 own, 0 kw (tier 2, wired).
  - `scaffold_audit` — **complete**: 5 pin public on the wire, 5 declared here, 0 satisfied from
    the import closure (no last-name collision to lean on).
  - `lake env lean -DautoImplicit=false` — no output at all (project cap `maxHeartbeats = 4000000`).
  - `lake build FLTForHuman.RepTheory.LocalLanglands.IntegralSubgroupCompact` under the lock — ok.
  - `#print axioms` on all five —
    `[propext, Classical.choice, Quot.sound]` for each, with no proof hole (probe:
    `lean/tmp/af96/probe_isc.lean`).
  - `dedup --within` — 0 clusters. `move_dead --dry-run` — 0 declarations, 0 lines.
  - Heartbeat probe (stated, never installed, FR-0225): silent at `-DmaxHeartbeats=1000`, first
    failure at `500` (deterministic timeout at `whnf`, in `isCompact_coe_integralSubgroup`), so the
    heaviest declaration costs about 0.5–1 million heartbeats — the `IsTopologicalRing`/`T2Space`
    instance search on `Matrix (Fin 2) (Fin 2) R`, not the argument. No `set_option maxHeartbeats`
    is carried.
-/

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.NumberTheory.Padics.ProperSpace
import FLTForHuman.RepTheory.LocalLanglands.IntegralSubgroup

set_option autoImplicit false

noncomputable section


namespace FLT.SpectralSide


instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (Matrix m n R) :=
  inferInstanceAs <| CompactSpace (m → n → R)

theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K))) := by
  have : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

theorem isCompact_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) :=
  isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val

theorem compactSpace_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    CompactSpace (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :=
  isCompact_iff_compactSpace.mp (isCompact_coe_integralSubgroup_padic p)

end FLT.SpectralSide

end
