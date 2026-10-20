# The D-S cone's leaf families — wave 2 (groups D–F), landed; the front closes

**Status: closed 2026-10-20.** Three coding groups, **29 new modules on top of phase 1's 18**, **417
statement-checked declarations**, 9,874 port lines, no existing module edited, nothing promoted, nothing
registered. Checker **2434 → 2851 ok** (+417, exactly the wired count), 0 mismatched / 0 missing / 4 own
over **107 modules**; axioms `[propext, Classical.choice, Quot.sound]`; 0 warnings; **no
`set_option maxHeartbeats` anywhere**. **44 of the 49 dispatched nodes landed** (8,504 pin lines including
the 99-line gate); 5 are deferred on missing definition gates, each recorded in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). The frontier falls **1,360 → 1,285 nodes** and **505,110 →
489,200 raw `S_` lines** across the whole session. Order:
[topics/deligneSerre/WORKORDER-MG3-ds-leaf-families.md](../topics/deligneSerre/WORKORDER-MG3-ds-leaf-families.md) §10;
scope criterion (and why phase 2 overshot it):
[topics/deligneSerre/TOPIC-ds-leaf-families.md](../topics/deligneSerre/TOPIC-ds-leaf-families.md) §8.

> **On the name.** This front was filed as *mathlib-small-families* for its first day, and that was a
> misnomer on both counts: the wave took every ready leaf in a one-to-three-node family of the D-S cone,
> which included nodes of 1,111 and 797 pin lines, and subjects that are FLT-flavoured however clean their
> imports (`PeriodPair`'s ℘-torsion, `LocalNewvector`, `RatIdele`). It is now **the D-S cone's leaf
> families**, and the four tests a "small supplement" actually has to pass are §8 of
> [TOPIC-ds-leaf-families.md](../../topics/deligneSerre/TOPIC-ds-leaf-families.md); the re-scoped cut that
> passes them is [TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md).

Build-time issues left open by this wave — the owed `ResidueSumQExpansion` shape rework,
the parked `ZLattice` draft, the tree's olean gaps and the lock/memory rules — are in
[build-time-issues.md](build-time-issues.md).

## 1. What landed

| group | modules | port lines | wired | pin lines | nodes |
|---|---|---:|---:|---:|---|
| **D** — `PeriodPair` (3), `MulAction` (2), `jacobiTheta_two_eq_tprod`, `AddAut` (+ the 99-line compat gate), `ClassGroup`, `IsAddCyclic` | 7 | 3,463 | 209 | 3,063 | 9 / 9 |
| **E** — `Function` (3), `LSeries` (2), `BrauerNesbitt`, `LinearEquiv`, `HexagonalLattice` | 6 | 2,714 | 95 | 2,246 | 8 / 10 |
| **F** — the small tail: `LaurentSeries`, torsion/valuation, compact-operator/finite-dimension, `StarSubalgebra` integral, decay estimates, `VectorFourier`+`SchwartzMap`+`AddChar`, `Complex` pair, adjoin degree, exact fundamental domain, `IsLocalRing`, `IsLocallyConstant`, `CuspFormClass`, `WittVector`, `ZSpan`, `integralClosure`, `LocalGL2` Iwasawa | 16 | 3,697 | 113 | 3,096 | 26 / 30 |
| **total** | **29** | **9,874** | **417** | **8,504** | **44 / 49** |

Grouping followed §5: a sub-80-line leaf rode with the neighbouring family of the same area (torsion pair,
compact-operator pair, decay/integrability pair, the `PiFourier` prelude shared by `VectorFourier` and
`SchwartzMap`, adjoin pair, `IsLocalRing` pair, `IsLocallyConstant` pair, `CuspFormClass` pair); each large
family got its own module. Two one-liners that do not share a subject (`ClassGroup` support vs squarefree
cardinality) stayed two modules.

## 2. The one gate, and the five deferrals

* **Homed:** `Def_Compat_Mathlib430` **block D** only (99 pin lines) as `Algebra/AddAutCompat.lean`
  (17 of 19 declarations wired; the anonymous `instance : Group (AddAut A)` and one `@[scoped simp]` lemma
  are parser-invisible). Blocks A–C (the v4.30 `Representation`/`Rep` API) are **not** homed — recorded in
  CARRY-FORWARD with the trigger.
* **Deferred, all on missing definition gates** (inventory in CARRY-FORWARD):
  `LocalNewvector` pair (647 pin lines behind 864 lines of gate: `AdelicSpanCarrier` 179/**173 importers**,
  `ConductorDatum` 114, `GL2CongruenceSubgroup` 531, `IntegralSubgroupCompact` 40);
  `HeckeEis.coresHom_eq_transfer` (59 behind `Def_Gamma0HeckeOperatorHom`, 304);
  `RatAdele.denseRange_algebraMap_add_adeleSingleAt` (309 behind `Def_LanglandsTunnell_StandardLocalConstantsAt`,
  144, **799 importers**);
  `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` (312 behind `Def_RatIdele_Normalizer` — `RatIdele.ρ`,
  `ρ_spec`, `ρ_ne_zero`, `IsNormalizer`, absent from the port entirely; the group also found that the port's
  `AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` is a *stronger* form, so the pin's
  variant is a two-line corollary — and rightly reported rather than restated).

## 3. Mathlib-first: two real hits

* **`LaurentSeries.algebraMap_apply` *is* the pin's private `algebraMap_eq_C`** — the helper is dropped and
  mathlib's lemma used at both call sites.
* **`RingHom.lift_injective_of_ker_le_ideal`** replaces the pin's hand-rolled quotient-lift injectivity
  (`rw [injective_iff_map_eq_zero]` and an instance-inference blowup).
* Deprecated spellings: `SchwartzMap.smul_apply`/`ContinuousLinearMap.smul_apply` → `_root_.smul_apply`,
  `push_neg` → `push Not`. For all 26 of F's headlines the negative is recorded in the module header.

## 4. Heartbeats: four more pin bumps, none needed

Group F alone carried four large bumps and dropped all four: `Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot`
(`synthInstance.maxHeartbeats 1600000` + `maxHeartbeats 8000000`; green at 200k after two *shape* fixes —
`RingHom.lift_injective_of_ker_le_ideal`, and keeping the quotient ideal as a named local `I` with an explicit
`Nontrivial`, instead of a `set` type), `WittVector.exists_valuationSubring_lift_with_transcendental`
(12.8M + 1.6M; green at **60,000**), `VectorFourier`/`SchwartzMap` (3.2M; green at 200k), `IntermediateField`
(4M; green at 200k). With E's unneeded 8M and D's clean sweep this session has five pin bumps that were
precaution and two that were real (`ResidueSumQExpansion` 300k–400k, and the `ZLattice` draft at 429 s) — every
real one turned out to be **instance inference with a guessed argument**, i.e. a shape problem.

## 5. Drift and traps worth keeping

* **`Finset.prod_le_prod` changed shape**: v4.34 needs `[MulLeftMono N]`, which `ℝ` does not have, so every ℝ
  product-monotonicity proof moves to **`Finset.prod_le_prod₀`**, with a confusing error, not a rename hint.
* **`Group (AddAut A)` was deleted** (AddAut became additive). A typeclass instance is invisible to `rg`, so the
  pin's compat import looked "dead"; `Subgroup (AddAut …)` cannot elaborate without it. The general lesson: when
  a statement is stated over a `Sub*hom` structure, the instance is part of the statement.
* **The dot-namespace trap**: `theorem Foo.bar` elaborates its *statement and proof* inside namespace `Foo`, so
  unqualified names silently resolve to `Foo.…` (it shadowed `IsIntegral`/`Finite` with `RingHom`'s classes;
  fixed with `_root_.`). Also `linter.dupNamespace` catches the `WittLift.WittLift.x` form.
* **`List.TFAE` is 1-based** now: every pin `.out i j` in that area needs +1.
* **`nsmul_eq_mul` emits a `NatCast`**: `n • a = ↑n * a`, so a `smul_eq_mul` transcription needs `Nat.cast_id`
  erasure before `omega` closes.
* **`isPreconnected_univ` requires `[PreconnectedSpace]`**, so a `haveI : PreconnectedSpace` cannot be
  discharged through the `IsPreconnected` API — use `Subtype.preconnectedSpace` explicitly.
* **`Ideal.under` is an `abbrev`**: `rw` does not see through it; fold in `Ideal.under_def`.
* **`scoped instance` must sit inside a namespace** (a root-level one is a hard error, not merely
  checker-invisible), and it remains invisible to both checkers.
* Renames fixed at source: `norm_prod`→`Complex.norm_prod`, `Subgroup.normal_of_index_eq_two` →
  `GroupTheory/IndexNormal.lean`, `Equiv.setCongr`→`Set.equivOfEq`, `Set.mem_diff`→`Set.mem_sdiff`,
  `ncard_diff_singleton_of_mem`→`ncard_sdiff_singleton_of_mem`, `if_pos/if_neg/if_true`→`ite_*`,
  `IsGLPos.coe_smul`→`FunLike.coe_smul`, `HasDerivAt.comp_add_const` (no dot projection).
* **Oleans**: `Mathlib.Tactic.Omega` and `Mathlib.LinearAlgebra.Quotient` have no olean in this tree (and
  neither import was needed); earlier `ModularForms/Level/Degeneracy`, `ConstTermCubeIntegral` and the two
  `AddCommGroup` modules were missing theirs. A "missing declaration" may be a missing olean.

## 6. Scoping, recorded so it is not repeated

Phase 2 was dispatched on "a ready leaf in a one-to-three-node family" alone and thereby included 12 nodes over
300 pin lines (57 % of its lines) and several FLT-flavoured subjects. It was already in flight when that was
caught, so it completed; the criterion is now written down
([leaf-families note](../topics/deligneSerre/TOPIC-ds-leaf-families.md) §8: size ≤ ~250 lines, shape read
not inferred, the mathlib-first negative, and a gate-to-family ratio), and the re-scoped cut that actually meets
it — **37 nodes / 3,641 lines / 283 publics in 7 families** — is
[TOPIC-phase3-small-supplements.md](../topics/deligneSerre/TOPIC-phase3-small-supplements.md), recorded and
**not scheduled**. This front is closed.

## 7. What remains from this family

* `LocalNewvector` (2 nodes / 647) — gate 864 lines, `AdelicSpanCarrier` a 173-importer hub.
* `HeckeEis.coresHom_eq_transfer` (59) — gate 304 lines.
* `RatAdele.denseRange_algebraMap_add_adeleSingleAt` (309) — gate 144 lines, 799 importers.
* `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` (312) — gate `Def_RatIdele_Normalizer`, entirely absent.
* The free-group family (`Monoid.CoprodI` + `ModularGroup` + `SimpleGraph` + `Subgroup`, 3,275 lines) and its
  four `Matrix.SpecialLinearGroup` rows — priced at 3,291 net / 2 modules.
* The `ZLattice` pair (3 nodes / 1,321) — parked at `lean/tmp/zlattice/` with its profile log and handover.
* Phase 3 (37 nodes / 3,641 lines) — recorded, not scheduled.
