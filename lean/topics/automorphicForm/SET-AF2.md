# SET-AF2 — the adelic maximal compact subgroup

**Status: landed 2026-11-02** — the gate by the manager (§1.5), the seven rows by one worker
dispatch ([WORKORDER-AF2-proofs.md](WORKORDER-AF2-proofs.md), §1.6). §8 is measured, with the
post-landing correction its own landing made necessary. Read off the D–S
shelf after SET 10 and the SET-AF1 landing, with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), and with
`--include-leaves` — which this time *is* the cut: the set is taken from the **leaves** block, not
from the ready shelf.

The set is **one definition module and seven leaf rows**: `Def_AutomorphicForm_AdelicMaximalCompact`
(331 pin lines / 38 declarations) plus the eight leaves that module gates (1,690 silo, of which seven
are cut: 1,231) → **1,562 pin lines, ≈1,263 net new math lines**, three new modules, fifteen wire
lines, no promotion, no migration, no marker, no tree build, no edits to existing modules. It is the
column's remaining **definition** debt that a cluster hangs on: 848 pin files import the gate.

§0 the read and the census that chose the cluster; §1 the cut; §2 what the gate and the rows say;
§3 homes; §4 ground prep; §5 traps; §6 gates; §7 calls; §8 reproduce and the forecast; §9 what this
set does not do. **Appendix A** names all 24 `AutomorphicForm` ready rows and **Appendix B** all 91
leaves, grouped by the definition module each one is waiting on.

## 0. The read

### 0.1 The canonical read, with the leaves

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af2.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS** (1,334 `Thm_` sources, 1,498 declared names, frontier inside the graph).

| figure | value |
|---|---:|
| `needed [F terminal]` | 917 / 374,592 |
| `needed [literal]` | 930 / 378,067 |
| frontier F (union) | 1,498 / 752,774 |
| … of F, inside the cone | 1,173 / 604,106 |
| port cone / avoided R | 2,103 / 982,173 · 140 / 74,620 |
| ready rows, all namespaces | 55 / 10,732 |
| leaves, all namespaces | 262 / 64,874 |
| `AutomorphicForm` ready rows | **24 / 5,248** |
| `AutomorphicForm` leaves | **91 / 18,510** |
| `AutomorphicForm` demand | 413 / 172,371 |
| withheld by the FR-0044 guard | 4 / 831 (unchanged) |

**The read is unchanged since SET-AF1's landing**: §8 of that brief measured exactly these figures
(917 / 374,592, AF 24 / 5,248), so this scoping opens on its own predecessor's re-read rather than on
a stale absolute. The withheld block is still the four prunable-subject rows
(`ModularCurve.moduleFinite_and_free_padicInt_tateModule_j{One,H}` 283 + 327,
`AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` 126,
`AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` 95) — none of them this column's.

### 0.2 `--include-leaves` is the whole point here

Without the flag the 91 leaves vanish, and the AF shelf looks like 24 ready rows: a mixture of
same-subject singletons, two gated rows (`FnTwist` 433, `UnramifiedWhittaker_HeckeRecursion` 138 +
146), and the no-Hecke-eigenvalue pair (1,040). With the flag the picture inverts, exactly as the
recipe says it does: **14,880 of the 18,510 leaf silo needs no unported definition module at all**,
and the leaves carry the column's largest self-contained proofs (755, 695, 646, 587, 576, 520 …) whose
`S_` files cite **no** pin theorem — only definitions — which is why they cost nothing in glue.

This set takes the one part of that block which *is* gated, and the largest such part.

### 0.3 The gate census, and the SET-AF1 correction it forced

Grouping both AF blocks by the pin definition modules their `S_` files import and the port does not
have (a module is *ported* if `spec/old_check_stmts.py`'s `SOURCES`, any port module's `spec-pin:`
line, any `-- pin:` marker or `spec/UNWIRED-PUBLIC.md` names it):

| unported gate | ready rows | leaf rows | silo |
|---|---:|---:|---:|
| — none | 21 | 72 | 14,880 (leaves) + 4,531 (ready) |
| **`AdelicMaximalCompact`** | 0 | **8** | **1,690** |
| `RationalTorusUnipotentQuotient` | 0 | 2 | 780 |
| `HeckeEigenfunction` | 0 | 1 | 384 |
| `UnramifiedWhittaker_HeckeRecursion` | 2 | 2 (+2 shared) | 273 (+207 with two more gates) |
| `RationalCentreUnipotentQuotient` | 0 | 1 (+1 shared) | 119 (+46) |
| `BoundedGenuineCuspRealization` | 1 | 1 | 69 |
| `IwasawaShellIndex` | 0 | 1 (+1 shared) | 62 (+46) |
| `FnTwist` | 1 | 0 | 433 |
| `NumberField_IdeleProductMeasure` | 0 | 0 (+2 shared) | — (+207) |

**The correction.** Building that table forced a second look at SET-AF1's Appendix A, and its entry
for `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` (360) was **wrong**: it said
the row needs `Def_AutomorphicForm_AdelicMaximalCompact`. The wrapper *imports* that module, but
neither the wrapper nor the `S_` file uses a single declaration of it — `grep -c
'adelicMaximalCompact\|maximalCompactAt'` is **0** in both. The import is module-granular noise, the
error the carry-forward register already warns about ("a pin `import` is a module-granular fact").
So the 360 row is ready with no gate, and `Def_AutomorphicForm_AdelicMaximalCompact` is unported
because the **leaves** need it. SET-AF1 §9 and its Appendix A are corrected in place.

**The rule this gives the recipe**: a *declaration-level* grep decides whether a gate is real, and it
must be run in both directions — the survey that found the 8 rows checked usage (not just the import
block), and the same check demoted a gate SET-AF1 had claimed from an import alone. The three tests,
in order: (1) does the `S_` file import an unported `Def_` module; (2) does it *name* a declaration of
it; (3) does the port already hold that declaration under another name (the FR-0093 test).

### 0.4 Why this cluster, and not another

`AdelicMaximalCompact` is the only single-gate cluster above 400 silo on the whole AF shelf, and it is
the largest unported **vocabulary** module in the column: **848 pin files import it** (447 `S_` files
and 401 `Theorems/` wrappers), the highest fan-in of any module this column has not ported. Behind it
sit the six rows that use its declarations plus two that only import it (one of which, 43, is a
statement about the archimedean factor of the same subgroup and belongs anyway; the other, 459, is
import-only and is the arch-cut sibling of the already-ready 184 — §9 defers it there).

The alternative clusters are worse in every way: the 72 ungated leaves are a *sequence* of sets, not
one (their largest families are the arch-derivative chain 1,510 silo, `LocalIntertwining` 1,295 and
`CuspidalConstituent` 1,288 — §9 names all three), and every other gated group is ≤ 780 silo with a
module of its own to build.

### 0.5 The definition-layer test, machine-checked

`port_advise --with-defs` over the seven rows returns **nine** pin `Def_` modules in the closure:
`AdelicMaximalCompact` (38 declarations, **unported**), `ArchKFinite` (9), `CuspidalConstituent` (21),
`EtaFamily` (15), `InducedSection` (10), `RowIsometryInvariance` (12), `SmoothAutomorphicFnAt` (16),
`WeylIntertwining` (7), `NumberField_AdelicHaar` (25) — of which the other eight are ported and
**111 declarations / ≈878 lines** are `substitute`, 110 of them byte-identical. So the gate of this
set is exactly one module, and the rows' statement vocabulary is complete (the FR-0049 check):
`IsRowIsometry`, `rowIsometrySubgroup`/`rowIsometrySubgroup₀` (`WindowedSiegel/RowIsometry.lean`,
`ArchWeightCharTransport.lean`), `glFin`/`glArch`/`archComponent`/`continuous_*`
(`NumberTheory/AdelicLevel/Projections.lean`), `finiteIntegralGL2`/`mem_finiteIntegralGL2_iff`/
`isClosed_finiteLevelZero`/`valued_apply_le_one` (`AdelicLevel/Level.lean`), `integralFiniteAdeles`
(`AdelicLevel/IdealBall.lean`), `adelicWeyl` (`Adelic/WeylIntertwining.lean`), `etaFst`/`etaSnd`/
`IsInducedSection` (`Adelic/{EtaFamily,InducedSection}.lean`), `IsKfSmooth`
(`Adelic/SmoothAutomorphicFn.lean`), `IsArchKFinite` (`Adelic/ArchKFinite.lean`), and
`MeasureTheory.distribHaarChar` (mathlib).

### 0.6 The shelf, quoted whole

Appendix A lists all 24 ready rows with their unported gate; Appendix B all 91 leaves, grouped the
same way. The cut rows are marked **◀** in Appendix B; nothing is silently dropped.

## 1. The cut

### 1.1 The story

The maximal compact subgroup of `GL₂(𝔸_F)` and its compact-open factors. `adelicMaximalCompact` is
`GL₂(Ô_F) × ∏_w {row isometries}` — finite part integral, every archimedean component a row isometry.
It is closed (an intersection of preimages of closed sets), compact (a closed subgroup of a compact
product through `Units.embedProduct`, using `‖entry‖ ≤ 1` on both a matrix and its inverse), and
carries a Haar probability. Its two one-place factors are the interesting objects:
`maximalCompactAt S` (trivial at every finite place outside `S`) and `maximalCompactAway S` (trivial
at the archimedean places and at the finite places inside `S`); both are closed, compact, compact
spaces in their own right, with Haar probabilities, and the `maximalCompactAway S` form a
neighbourhood basis of `1` as `S` grows.

The seven rows are that subgroup's first harvest: the two-factor and one-place decompositions of an
element, the neighbourhood basis, the compactness of the archimedean determinant-one row isometries,
and two analytic consumers for which the compactness is the engine (a flat family over the maximal
compact, and the Weyl/unipotent non-vanishing of an induced section).

### 1.2 The steps

| step | node (`AutomorphicForm.` dropped) | pin lines | decls | net | gate |
|---|---|---:|---:|---:|---|
| **G** | `Def_AutomorphicForm_AdelicMaximalCompact` | 331 | **38** | ≈307 | — |
| **M1-1** | `exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq` | 158 | 10 | 142 | G |
| **M1-2** | `exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt` | 145 | 10 | 129 | G |
| **M1-3** | `exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty` | 114 | 11 | 89 | G |
| **M1-4** | `exists_maximalCompactAway_subset_of_mem_nhds_one` | 80 | 3 | 68 | G |
| **M1-5** | `isCompact_rowIsometrySubgroup_detOne` | 43 | 1 | 34 | G |
| **M2-1** | `flat_family_comp_mul_of_mem_adelicMaximalCompact` | 185 | 8 | 149 | G |
| **M2-2** | `exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` | 506 | 37 | 478 | G |
| | **8 steps** | **1,562** | | **≈1,263** | |

### 1.3 Pricing, and the prelude to port once

`port_advise` over the seven rows, then `port_plan`: **1,231 raw `S_` lines − 131 boilerplate = 1,100
declaration lines − 133 duplicate copies − 11 already in the port = 956 net new math lines**. The
gate is priced from its own file: 38 declarations, 307 declaration lines, no private prelude
(`drags`: `0 helpers`), nothing of it in the port.

**The 133 duplicate lines are one prelude, and it has a home.** `port_advise`'s *port once* block:
eight names proved in ≥2 of the seven files, ≈123 removable lines — `adelicGL2_ext` (3 copies, 30
lines), `finEntry_eq` (4 copies, 26), `atPlace` (2, 4), `glArch_atPlace` (2, 3),
`finComponent_atPlace_of_ne` (2, 5), `localEmbed_entries_integral` (2, 16), `atPlace_mem` (2, 22),
`mul_atPlace_comm` (2, 17): the "place decomposition" of an adelic matrix — `atPlace` is the element
that agrees with `g` at `v` and is `1` elsewhere. The strongest pair is M1-1 ↔ M1-2 (8 proofs /
93 lines). **Write it once, `private`, in the factors module (M1's home)**; M2 does not need it
(`finEntry_eq` appears there once, in M2-1, which is a different use — check the statement before
sharing).

### 1.4 The lanes

| order | who | steps | file (new) | pin lines | why this order |
|---|---|---|---:|---:|---|
| **1** | manager (definition layer) | G | `Adelic/AdelicMaximalCompact.lean` | 331 | nothing in the set can be *stated* before it |
| **2** | worker | M1-1 … M1-5 | `Adelic/MaximalCompactFactors.lean` | 540 | the factor arithmetic + the shared prelude; needs only G |
| **3** | worker | M2-1, M2-2 | `Adelic/InducedSectionMaximalCompact.lean` | 691 | the two analytic consumers; needs G + the *already ported* induced-section layer |

Orders 2 and 3 are disjoint (different new files, both read only G, which is frozen on landing) and
can run concurrently after order 1. The build lock is the only shared resource; no order edits a hub.

### 1.5 The landing — the gate, one manager session

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---|---:|
| G | `AutomorphicForm/Adelic/AdelicMaximalCompact.lean` (**+331**) | **37 ok** / 0 / 0 / 0 own | silent, **3.5 s**, zero warnings | clean on all 11 proof-carrying declarations |

**38 declarations, 37 public and `ok`** (the pin's one `private` helper
`isClosed_ker_finComponent_comp_glFin` is reached through the checker's pin-private fallback) — so the
figure in §1.2 and §8 is 37 checked, not 38. Two adaptations, both warning-driven, no statement
touched: the pin's `fun_prop` step in `isClosed_setOf_isRowIsometry` does not close the quadratic-form
continuity at `v4.34` (proved from the entry continuities instead), and the pin's
`Set.setOf_forall`/`Set.setOf_and`/`Set.mem_setOf_eq` are deprecated (`Set.ofPred_forall`/
`Set.ofPred_and`/`Set.mem_ofPred_eq`). `dedup.py --within` reports one 12-line intra-module cluster
(the six Haar/probability instances are the pin's own repeated shape — kept, the pin writes them that
way). The consumer probe `spec/AutomorphicFormSetAF2Consumer.lean` is new, two zones, 0 errors.

**What the gate unblocks, counted**: 848 pin files import it (447 `S_` files and 401 `Theorems/`
wrappers) — the highest fan-in of any module this column had not ported.

### 1.6 The landing — the seven rows, one worker dispatch

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---|---:|
| M1 | `Adelic/MaximalCompactFactors.lean` (**+439**, 5 public + 19 private) | **5 ok** / 0 / 0 | silent, **3.9 s** | clean ×5 |
| M2 | `Adelic/InducedSectionMaximalCompact.lean` (**+722**, 2 public + 43 private) | **2 ok** / 0 / 0 | silent, **7.4 s** | clean ×2 |

**What the set consumed**: 8 steps / 1,562 pin lines — **1,161 source lines** in three new modules
(331 gate + 439 + 722), against the 1,263 net-new declaration lines priced. The written-to-pin ratio
is **0.94**: the port-once prelude (the 9-name `atPlace` kit) and the 133 duplicate copies came out
exactly as `port_advise` predicted, so the dispatch wrote *less* than the pin's 1,231 row lines.
`dedup.py --within` — **0 clusters** in both modules (24 and 45 declarations); every module silent on
`lake env lean` and on its own `lake build`; the two consumer modules do not import each other; the
gate was not edited. The consumer probe grew from 2 to **9 zones**, 0 errors.

**Deviations held for review** (no statement changed; every `check_port` hash matched):

- **M1**: the pin's `attribute [-instance]` line dropped (nothing in its proofs reaches those
  instances); a `classical` is needed at the head of M1-1 (the `insert` branch of
  `Finset.induction_on` needs `DecidableEq (HeightOneSpectrum _)`, which the pin's environment
  supplied); `IsCompact.elim_directed_family_closed` takes the `Disjoint` form at `v4.34` where the
  pin used the `= ∅` form (M1-4 and M2 both); `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; M1-3's
  archimedean kit is one `private` section, so the pin's `main`/`solution` two-step collapses to one
  public declaration plus its private `kOne_main`.
- **The prelude is nine names, not eight**: `finComponent_atPlace_self` is a duplicate copy of M1-1 /
  M1-2 that `port_advise`'s *port once* block does not list. Written once, privately, at the head of
  M1 — the block's line count (123) still held.
- **M2** adds a **deprecation family the recipe's table did not have**: `dif_pos` / `dif_neg` /
  `if_pos` / `if_neg` are deprecated at `v4.34` in favour of `dite_eq_left` / `dite_eq_right` /
  `ite_eq_left` / `ite_eq_right` (13 occurrences). Recorded as FR-0094. Also:
  `continuous_finComponent_glFin` is proved from the port's own `continuous_finComponent` /
  `continuous_glFin`, because the pin's `Units.continuous_val.matrix_elem` route does not elaborate
  (the `TopologicalSpace (Matrix …)` instance is not synthesised *inside the term* even though
  `#synth` finds it) — and the pin's generated `WITNESS` label is not carried.

## 2. What the gate and the rows say

**G `AdelicMaximalCompact` (331 / 38).** `adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)`,
membership `glFin k ∈ finiteIntegralGL2 ∧ ∀ w, IsRowIsometry (archComponent K w (glArch k))` and its
primed form through `rowIsometrySubgroup`; the projections and the local valuation consequences
(`valued_finComponent_apply_le_one` both ways, `valued_det_finComponent_eq_one` — `|det| ≤ 1` twice
against `det g · det g⁻¹ = 1`). Closed: `isClosed_setOf_isRowIsometry` (a determinant-norm equation
plus the row-norm quadratic form, `isClosed_iInter` over `x y`), then
`isClosed_adelicMaximalCompact` as `glFin ⁻¹' finiteIntegralGL2 ∩ ⋂_w (archComponent w ∘ glArch) ⁻¹'
{IsRowIsometry}`. Compact: `IsRowIsometry.norm_apply_le_one` bounds every entry by `1` (from the two
row norms by `linarith`), the completion ball `{‖x‖ ≤ 1}` and the product
`{a | a.2 integral, ∀ w, ‖a.1 w‖ ≤ 1}` are compact, and
`isCompact_adelicMaximalCompact` is a closed-subgroup-of-a-compact-product argument through
`Units.embedProduct` (`C ×ˢ op '' C`). Then `CompactSpace`, `maximalCompactHaar` with its
`IsHaarMeasure`/`IsProbabilityMeasure` instances, and measurability of the coercion. The `Factors`
section is the local layer: `maximalCompactAt S` and `maximalCompactAway S`, their membership
normal forms, `≤ adelicMaximalCompact`, closedness (the level-`v` kernels are closed), compactness as
a closed subset of the compact group, `CompactSpace` instances, and their Haar probabilities.

**M1-1 (158).** `k ∈ adelicMaximalCompact` splits as `k = k₁ * k₂` with `k₁ ∈ maximalCompactAt S`,
`k₂ ∈ maximalCompactAway S`: at each finite place outside `S` the component is integral and the
away-factor takes it, at the places inside `S` the `At`-factor does, and the archimedean parts split
by `1 · k_w` vs `k_w · 1`. The proof is the `atPlace` prelude.

**M1-2 (145).** The one-place refinement, with commutation: for `v ∈ S`, `k ∈ maximalCompactAt S`
splits into `k' ∈ maximalCompactAt (S.erase v)` and `kv ∈ maximalCompactAt {v}` with *trivial
archimedean part*, and the two commute (`k' * kv = kv * k'`) — the statement the Weyl/shell arguments
consume when they move one place at a time.

**M1-3 (114).** For `k ∈ maximalCompactAt ∅` and a fixed infinite place `w`: `k = k₁ k₂` with `k₁,
k₂` commuting, `k₁` supported at `w` (trivial finite part, trivial archimedean part away from `w`),
`k₂ ∈ maximalCompactAt ∅` with trivial archimedean part at `w`. The archimedean mirror of M1-2.

**M1-4 (80).** Every neighbourhood `W` of `1` contains some `maximalCompactAway S₀`: the
`maximalCompactAway` form a neighbourhood basis of the identity — the fact that makes "away from a
finite set of places" arguments uniform.

**M1-5 (43).** `rowIsometrySubgroup₀ w.Completion` — the determinant-one row isometries at `w` — is
compact. The archimedean half of the gate's compactness, stated for the group the gate uses.

**M2-1 (185).** A family `φ : ℂ → GL₂(𝔸_F) → ℂ` of induced, arch-`K`-finite, `K_f`-smooth sections,
holomorphic in `s` and jointly continuous, which is *flat* over the finite-integral × row-isometry
subgroup (`φ s k = φ s' k` for `k ∈ adelicMaximalCompact`) — is constant in `s` on that subgroup. The
compactness of `adelicMaximalCompact` is what makes the flatness propagate.

**M2-2 (506).** For a nonzero continuous `K_f`-smooth induced section `φ` (for the modulus character
`α = distribHaarChar`, `s : ℂ`), some adelic `x` has `φ (w⁻¹ * u(x)) ≠ 0`: the Weyl/unipotent
non-vanishing that feeds the `archSupportedAt` row. Uses `isCompact_adelicMaximalCompact` for the
support argument — the reason the gate is on this row's path at all.

## 3. Homes — three new modules

The "above all premises" search: the gate's seven dependencies **are** dominated by existing modules
(`IsotypicCuspSpace`, `Cusp/Constituent`, `ArchType`, `TestFnNearIdentity` all sit above all seven),
so insertion is *possible* — but every one of them is a hub (11, 10, 6, 4 in-tree importers) and none
of them is the subject. A pin `Def_` transcription belongs in a module of its own role (playbook §3.1),
and a new module is cascade-free; insertion would re-elaborate the AF definition layer for nothing.

| # | module (all new) | imports | holds |
|---|---|---|---|
| 1 | `FLTForHuman/AutomorphicForm/Adelic/AdelicMaximalCompact.lean` | `WindowedSiegel/RowIsometry`, `Adelic/Basic`, `NumberTheory/AdelicLevel/{Level,Projections,IdealBall}`, `NumberTheory/AdelicHaar/{Adele,GeneralLinear}` | G (38) |
| 2 | `FLTForHuman/AutomorphicForm/Adelic/MaximalCompactFactors.lean` | 1, `NumberTheory/AdelicDock/LocalEmbedding`, `Adelic/ArchWeightChar`, `NumberTheory/AdelicLevel/Projections` | M1-1…M1-5 (5) + the private `atPlace` prelude |
| 3 | `FLTForHuman/AutomorphicForm/Adelic/InducedSectionMaximalCompact.lean` | 1, `Adelic/{InducedSection,EtaFamily,WeylIntertwining,ArchKFinite,ArchType,SmoothAutomorphicFn}`, `NumberTheory/AdelicHaar/PlaceMeasure` | M2-1, M2-2 (2) |

**Import-direction check.** Module 1 imports only modules that exist and that nothing in the set
imports back; 2 and 3 import 1 and nothing of each other. Do **not** let 3 import 2: the two consumer
modules must stay independent, or the second worker's build drags the first's proof bodies in.
`maximalCompactAt`/`maximalCompactAway` are *defined* in module 1 (they are part of the pin's
definition module), so both consumer modules state over them without a further gate.

**Namespace.** Keep the pin's `AutomorphicForm` (the gate's declarations are in the root
`AutomorphicForm` namespace, not a sub-namespace — that is the pin's shape and the checker diffs it).

**No legacy module, no migration, no promotion.** None of the three is in `PORT_FILES`; the gate's 38
declarations exist nowhere in the port (`adelicMaximalCompact`, `maximalCompactAt`,
`maximalCompactAway`, `maximalCompactHaar`, `maximalCompactAtHaar`, `maximalCompactAwayHaar`,
`isCompact_adelicMaximalCompact` — all grepped, all absent).

## 4. Ground prep (the manager's)

1. **Wires.** Fifteen `spec-pin:` lines: one for the gate
   (`Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean`), two per row for the seven rows
   (`Theorems/Thm_…` + `P2M/Sol/S_…   -- comparable copy`).
2. **`decl_markers.tsv`: none.** Every declaration is at the pin's name and namespace. The pin's
   `private theorem isClosed_ker_finComponent_comp_glFin` stays `private` (the checker's pin-private
   fallback reaches it).
3. **`PORT_FILES`/`SOURCES`: do not append** — the three modules are wired by their own lines.
4. **Consumer zone**: a new `spec/AutomorphicFormSetAF2Consumer.lean` (the AF1 probe is at 252 lines
   and has its own subject) — zone A: the gate's compactness composed with `maximalCompactAway`'s
   neighbourhood basis, read at a concrete open set containing `1`; zone B: the two-factor split
   landed in `cuspMemberSubmodule`-style use, or at least composed with the gate's
   `mem_adelicMaximalCompact_iff'`. Error count is the metric.
5. **After the landing**: `dedup.py`/`move_dead.py` on the three modules, `unwired_register.py --check`
   (expect no drift: all three are tier 1 through their own wires), and the shelf re-read of §8.

## 5. Per-step traps

**G (331 / 38).** (i) `omit [NumberField K] in` guards two declarations
(`isCompact_setOf_norm_le_one_completion`, and the `WindowedSiegel.IsRowIsometry` lemma is
`variable {K} in`): keep the pin's `omit`/`variable … in` form, do not restate binders (FR-0091).
(ii) `Units.isClosedEmbedding_embedProduct.isCompact_preimage` is the v4.34 spelling shape the port
already uses (`ArchHaar.lean:62`, `TestFnTop.lean:88`); if the projection name differs, the fallback
is `IsClosedEmbedding.isCompact_preimage`. (iii) `Measure.haarMeasure_self` +
`TopologicalSpace.PositiveCompacts.coe_top` are the two-step proof of the probability instances; both
exist at v4.34 (`TateGlobal/ReferenceMeasure.lean` uses the second). (iv) The `attribute [local
instance] NumberField.AdelicHaar.glBorel … borelSpace_glBorel` line is the pin's and is needed for
`measurable_subtype_val_adelicMaximalCompact`; keep it module-local. (v) `Valued.v` lemmas
(`Valuation.map_sub`, `mul_le_one'`, `le_antisymm`) are the `valued_det_finComponent_eq_one` proof —
it is the one place a valuation rewrite can close a goal by `le_antisymm` and needs both inequalities
in that order. (vi) `isCompact_univ_pi`, `IsCompact.prod`, `MulOpposite.continuous_op`,
`isCompact_iff_compactSpace` are all used in the port already.

**M1 rows (540).** (i) Write the `atPlace` prelude once, `private`, at the head of the module (8 names,
≈123 lines); the two big rows share 93 of them, M1-3 shares none. (ii) `adelicGL2_ext` is the pin's
`Prod.ext`/`RestrictedProduct.ext` shape — check whether the port has an equivalent under another name
before writing the third copy (`HeckeCharacter/Equality.lean` has adelic `ext` lemmas). (iii)
M1-1/M1-2 are `Finset` inductions over `S`; the pin's `S.erase v` case is where the commutation
hypothesis of M1-2 enters, and the *statement* order (`k = k' * kv ∧ k' * kv = kv * k'`) is the
wrapper's — keep it.

**M2-1 (185).** The statement is a chain of `_hφ…` hypotheses (`IsInducedSection`, `IsArchKFinite`,
`IsKfSmooth`, joint continuity, holomorphy, flatness); transcribe them in the wrapper's order. The
proof's flatness step is the only consumer of `mem_adelicMaximalCompact_iff` and hence of the gate.

**M2-2 (506).** The 478-line proof is the set's weight. (i) The statement is `let α := …` bound — the
`let` must stay in the statement (the checker hashes it). (ii) `push_neg` in the pin's `by_contra` is
`push Not` at v4.34 (FR-0036). (iii) The support argument uses the gate's compactness; if a
`maxHeartbeats` wall appears at `-DmaxHeartbeats=1000000` in the edit loop, report it rather than
adding `set_option` (the project cap is 4M, and the row is 506 pin lines — the one row of the set that
may need the cap).

## 6. The gates, per order

As in SET 6–10, SET-AF1 and the recipe §6:

1. `python3 spec/check_port.py --force <module>` → 0 mismatch, 0 missing; expect the gate **38 ok**,
   M1 **5 ok**, M2 **2 ok** (the pin's private helpers go through the pin-private fallback).
2. `#print axioms` on the gate's proof-carrying declarations and on the seven headlines →
   `[propext, Classical.choice, Quot.sound]`.
3. Each module's own `lake build` under `flock`/`timeout 110`; **silent** (zero warnings). No tree
   build, no dependents.
4. `dedup.py --within --module <module>`; `move_dead.py` (exempt for the gate: a `Def_` transcription
   is a flat public surface, and FR-0086 makes `move_dead`'s "0 dead" uninformative there anyway).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`.
6. The consumer zone of §4.4: its error count, and it must break if any of the three modules is deleted.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **the AMC cluster: 8 steps / 1,562 pin lines / ≈1,263 net**, three orders | the alternative is the 1,040-silo no-Hecke-eigenvalue pair (a theorem set with no gate, and the Langlands–Tunnell column's) or one of the three big ungated families (§9); this one is the column's only remaining gate-shaped cluster and its highest-fan-in vocabulary |
| 2. **the gate's home** | **a new `Adelic/AdelicMaximalCompact.lean`**, not an insertion into `IsotypicCuspSpace`/`Cusp/Constituent` (possible — they are above all seven of its dependencies) | an insertion edits a hub with 10–11 importers and re-elaborates the AF definition layer; a new module is cascade-free and matches the pin's role split |
| 3. **the M1/M2 split** | **two modules by closure, not by size** | M1 needs only the gate + `LocalEmbedding` + `ArchWeightChar`; M2 needs the induced-section layer. One module would make every future consumer of the factor arithmetic drag in `InducedSection`/`EtaFamily`/`WeylIntertwining` |
| 4. **the 459 row** | **defer it** (import-only; it is `184`'s arch-cut sibling, and `184` is ready with no gate) | cutting it would put a 459-line arch-cut proof in a compactness set; it belongs with its sibling in the `archCutSubmodule` family |
| 5. **the prelude** | **write the 8 `atPlace` names once, `private`, in module 2** | 123 lines saved; and it is the one place a later `maximalCompactAt` consumer will look |
| 6. **the dispatch** | **order 1 (manager): the gate; then orders 2 and 3 concurrently** | the gate must be frozen before either worker states a row; the two consumer modules are disjoint |

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af2.json   # §0.1
python3 frontier.py --selfcheck                                                                          # PASS
python3 port_advise.py --with-defs --nodes <the seven rows> --json build/af2-defs.json                   # §0.5/§1.3
python3 port_plan.py --json build/af2-defs.json                                                          # 956 net
python3 port_advise.py --target Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean --json build/af2-gate.json
python3 twin_scan.py --node <each of the seven rows>                                                     # new × 7
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/AdelicMaximalCompact.lean            # after landing
```

**What the set consumes**: 1,562 pin lines — one definition module (331 / 38 declarations) and seven
rows (1,231 → 956 net); **≈1,263 net new math lines**; three new modules; 15 wire lines; 0 edits to
existing modules, 0 imports added elsewhere, 0 promotions, 0 migrations, 0 markers, 0 tree builds.

**Measured after the landing — twice**, because the landing created a name shadow (FR-0095). The raw
re-read (the instrument) and the corrected read (one `--unport`) differ in both directions:

| figure | before | forecast | measured (raw) | **measured (corrected)** |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 917 / 374,592 | 910 / 373,361 | 909 / 373,333 | **910 / 373,361** ✓ |
| frontier F | 1,498 / 752,774 | 1,505 / 754,005 | 1,506 / 754,033 | **1,506 / 754,033** |
| `AutomorphicForm` ready rows | 24 / 5,248 | 24 / 5,248 | 29 / 7,430 | **27 / 6,669** |
| `AutomorphicForm` leaves | 91 / 18,510 | 84 / 17,279 | 83 / 17,251 | **84 / 17,279** ✓ |
| `AutomorphicForm` demand | 413 / 172,371 | 406 / 171,140 | 405 / 171,112 | **406 / 171,140** ✓ |
| `--selfcheck` | PASS | — | PASS (1,341 `Thm_` / 1,506 names) | PASS |

**The shadow, and why it matters here.** The new M2 module proves a `private theorem
continuous_unipotentGL2` — a helper whose *last name* is the pin node
`AutomorphicForm.continuous_unipotentGL2` (28 silo, a leaf). The frontier's ported set is a set of
last-name components **including `private` declarations**, so that node reads as ported: the raw read
loses 1 node / 28 lines of `needed`, and two rows whose sole missing premise was that node
(`continuous_rightConv_and_contDiff_of_isFactorizableTestFn`,
`isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset`)
appear on the ready shelf, where they cannot be written. **A large transcription manufactures these
shadows**, so `--unport` is not a SET-AF1-only correction: it must be re-run after every landing,
with the new modules' `private` declaration names diffed against the unported last names. The
corrected read is the one quoted in the table above and in the status line at the top of this brief.

**The rows this set makes ready** (corrected read — three, not the raw read's five):

| row | silo | prem | lev |
|---|---:|---:|---|
| `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule` | 998 | 1 | 5 / 6 |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2 / 4 |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1 / 3 |

That is the set's own §7 answer, and it is the biggest readiness return of the column's sets so far
(SET-AF1 made one row ready, 37 silo): 1,421 new silo on the shelf for 331 gate lines, because the
`maximalCompactAt`/`Away` vocabulary is what those rows were waiting for.

**What becomes *writable* rather than ready**: the eight leaf rows (the seven cut plus 459) stop being
gated, and the 848 pin files that import the gate become transcribable one premise-wave at a time —
which is the figure that makes this gate worth more than its 331 lines.

## 9. What this set does not do

- **The 72 ungated leaves / 14,880 silo.** Named row by row in Appendix B. They need no definition
  module, so they are the column's next *three* sets and not one: the arch-derivative chain
  (`archDerivAt*`/`archCasimirAt*`/`archDerivAtComplex*`, 1,510 silo over 8 rows), `LocalIntertwining`
  (7 / 1,295) and `CuspidalConstituent` (6 / 1,288). Each is a story; none has a gate.
- **The other gated leaves** (Appendix B): `RationalTorusUnipotentQuotient` (2 / 780),
  `HeckeEigenfunction` (1 / 384), `UnramifiedWhittaker_HeckeRecursion` (2 / 273 + 2 shared),
  `RationalCentreUnipotentQuotient` (1 / 119 + 1 shared), `IwasawaShellIndex` (1 / 62 + 1 shared),
  `BoundedGenuineCuspRealization` (1 / 69), and the two RankinSelberg rows that need three gates at
  once (207). Each is its own gate and its own small set.
- **The 459 row** (`finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule`): import-only, so
  the gate does not touch it; it is the arch-cut sibling of the ready
  `finiteDimensional_span_translates_of_mem_archCutSubmodule` (184), and the two belong in one set.
- **The 24 ready rows** (Appendix A). Three are definition-gated elsewhere (`FnTwist` 433,
  `UnramifiedWhittaker_HeckeRecursion` 138 + 146 with `BoundedGenuineCuspRealization`), and the rest
  are other subjects; the highest-leverage ready row in the whole shelf (`exists_mem_adelicBorel_mul_eq`,
  372, 14 / 63) is still uncut.
- **Anything behind the prunable complex-analytic subject**: the withheld 4 / 831 (the RR column's
  phase 3). No new `Def_` module, no promotion, no migration, no tree build.

## Appendix A — the 24 `AutomorphicForm` ready rows, 5,248 silo (as read in §0.1, before the landing)

With the unported definition module each one is waiting on (`—` = none: the row is writable today).

| row (`AutomorphicForm.` dropped) | silo | prem | lev | unported gate |
|---|---:|---:|---|---|
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1 / 2 | — |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1 / 1 | — |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4 / 10 | AutomorphicForm_FnTwist |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14 / 63 | — |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1 / 1 | — |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1 / 1 | — |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2 / 2 | — |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3 / 20 | — |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2 / 27 | — |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1 / 1 | — |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1 / 1 | — |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4 / 12 | — |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5 / 8 | — |
| `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 1 | 6 / 7 | — |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2 / 2 | — |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1 / 11 | — |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1 / 2 | AutomorphicForm_BoundedGenuineCuspRealization, UnramifiedWhittaker_HeckeRecursion |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2 / 5 | UnramifiedWhittaker_HeckeRecursion |
| `isKfSmooth_rightConv` | 70 | 1 | 7 / 21 | — |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1 / 1 | — |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1 / 1 | — |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3 / 8 | — |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2 / 3 | — |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1 / 6 | — |

total 24 rows / 5248 silo

## Appendix B — the 91 `AutomorphicForm` leaves, 18,510 silo (as read in §0.1, before the landing)

Grouped by the definition module each waits on; the set's rows are marked **◀**. `lev` is
`leverage / leverage_project` (cone / project fan-in), the column the recipe ranks leaves by.

**no unported definition module** — 72 row(s), 14,880 silo

- `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` 755  (lev 3/4)
- `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` 695  (lev 2/2)
- `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` 646  (lev 2/4)
- `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` 587  (lev 1/1)
- `exists_sum_prod_mul_of_rightTranslatesSpanFinite` 576  (lev 2/2)
- `exists_coversModCentre_centreCutSiegelSetAmple` 520  (lev 1/3)
- `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` 445  (lev 1/2)
- `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` 432  (lev 2/7)
- `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` 404  (lev 2/2)
- `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` 401  (lev 8/9)
- `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` 386  (lev 3/4)
- `exists_isArchBiFinite_rightConv_comp_inv` 376  (lev 1/1)
- `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` 362  (lev 1/1)
- `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` 347  (lev 1/1)
- `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` 346  (lev 1/2)
- `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` 328  (lev 3/4)
- `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` 317  (lev 1/1)
- `CuspidalSpectrum.exists_isArchBiFinite_flat` 304  (lev 1/1)
- `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` 298  (lev 2/3)
- `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` 282  (lev 5/10)
- `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` 250  (lev 2/2)
- `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` 245  (lev 1/1)
- `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` 222  (lev 1/1)
- `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` 219  (lev 1/1)
- `archDerivAt_commutator_of_isArchSmoothAt` 208  (lev 1/4)
- `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` 199  (lev 7/20)
- `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` 196  (lev 4/5)
- `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` 189  (lev 1/4)
- `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` 184  (lev 8/14)
- `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` 184  (lev 1/1)
- `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` 179  (lev 1/1)
- `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` 177  (lev 1/1)
- `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` 170  (lev 1/1)
- `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` 165  (lev 1/5)
- `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` 156  (lev 1/1)
- `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` 154  (lev 8/19)
- `typeSubmodule_inf_typeSubmodule_eq_bot` 152  (lev 1/2)
- `coversModCentre_of_le_of_lt_of_coversModCentre` 150  (lev 4/8)
- `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` 148  (lev 2/2)
- `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` 147  (lev 1/1)
- `constantTerm_adelicBox_unipotentGL2_mul` 144  (lev 1/14)
- `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` 136  (lev 1/3)
- `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` 133  (lev 2/3)
- `whittakerCoefficient_unipotentGL2_mul` 123  (lev 17/54)
- `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` 117  (lev 2/2)
- `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` 116  (lev 1/1)
- `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` 110  (lev 2/3)
- `continuous_whittakerCoefficient` 108  (lev 3/14)
- `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` 108  (lev 2/3)
- `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` 107  (lev 2/3)
- `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` 102  (lev 1/1)
- `isFactorizableTestFn_sum_mul_comp_mul_mul` 98  (lev 1/1)
- `whittakerCoefficient_sum_smul_of_continuous` 86  (lev 10/17)
- `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` 78  (lev 2/2)
- `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` 78  (lev 1/1)
- `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` 75  (lev 2/4)
- `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` 71  (lev 3/22)
- `exists_isRightEquivariant_comp_subtype_eq_of_injective` 70  (lev 3/8)
- `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` 65  (lev 2/3)
- `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` 62  (lev 2/14)
- `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` 62  (lev 1/2)
- `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` 55  (lev 1/1)
- `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` 51  (lev 5/18)
- `IsKfSmooth.finite_smul_image_of_isCompact` 40  (lev 3/4)
- `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` 33  (lev 1/2)
- `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` 30  (lev 2/10)
- `continuous_unipotentGL2` 28  (lev 8/122)
- `exists_iUnion_centreCutSiegelSet_mem_nhds` 25  (lev 1/1)
- `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` 23  (lev 1/1)
- `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` 21  (lev 17/48)
- `constantTerm_add` 13  (lev 1/2)
- `constantTerm_smul` 11  (lev 1/1)

**AutomorphicForm_AdelicMaximalCompact** — 8 row(s), 1,690 silo

- `exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` 506  (lev 1/1) **◀**
- `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` 459  (lev 2/3)
- `flat_family_comp_mul_of_mem_adelicMaximalCompact` 185  (lev 3/3) **◀**
- `exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq` 158  (lev 2/3) **◀**
- `exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt` 145  (lev 1/1) **◀**
- `exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty` 114  (lev 1/1) **◀**
- `exists_maximalCompactAway_subset_of_mem_nhds_one` 80  (lev 3/4) **◀**
- `isCompact_rowIsometrySubgroup_detOne` 43  (lev 12/18) **◀**

**AutomorphicForm_RationalTorusUnipotentQuotient** — 2 row(s), 780 silo

- `isFundamentalDomain_boxSheet_rationalTorusUnipotent` 440  (lev 2/15)
- `isFundamentalDomain_boxSheet_rationalCentreUnipotent` 340  (lev 2/3)

**AutomorphicForm_HeckeEigenfunction** — 1 row(s), 384 silo

- `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` 384  (lev 1/2)

**UnramifiedWhittaker_HeckeRecursion** — 2 row(s), 273 silo

- `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` 192  (lev 1/1)
- `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` 81  (lev 1/2)

**AutomorphicForm_AdelicMaximalCompact, NumberField_IdeleProductMeasure, UnramifiedWhittaker_HeckeRecursion** — 2 row(s), 207 silo

- `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` 141  (lev 1/1)
- `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` 66  (lev 1/1)

**AutomorphicForm_RationalCentreUnipotentQuotient** — 1 row(s), 119 silo

- `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` 119  (lev 1/1)

**AutomorphicForm_BoundedGenuineCuspRealization** — 1 row(s), 69 silo

- `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` 69  (lev 1/1)

**AutomorphicForm_IwasawaShellIndex** — 1 row(s), 62 silo

- `isLocallyConstant_iwasawaShellIndex_and_measurable` 62  (lev 2/2)

**AutomorphicForm_IwasawaShellIndex, AutomorphicForm_RationalCentreUnipotentQuotient** — 1 row(s), 46 silo

- `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` 46  (lev 2/2)
