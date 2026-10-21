# The D-S cone's leaf families — the pool, the pricing, and the criterion

Scoped 2026-10-20, after WORKORDER-MG1's landing (checker 2038) and with WORKORDER-MG2 in flight.
This note answers one question: *of the D-S demand, what is left that is mathlib-shaped, how is it
grouped into families, and what does closing it cost?*

> **On the name.** This front was filed as *mathlib-small-families* for its first day, and that was a
> misnomer on both counts: the wave took every ready leaf in a one-to-three-node family of the D-S cone,
> which included nodes of 1,111 and 797 pin lines, and subjects that are FLT-flavoured however clean their
> imports (`PeriodPair`'s ℘-torsion, `LocalNewvector`, `RatIdele`). It is now **the D-S cone's leaf
> families**, and the four tests a "small supplement" actually has to pass are §8 of
> this note; the re-scoped cut that
> passes them is [TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md).

## 1. The pool

The frontier's own family preamble (`frontier.py --ds --include-leaves`, the
`unported demand by top-level namespace` table) crossed with a per-node classification of each pin
`S_` file's imports. A node is **mathlib-like** when its `S_` file imports nothing from
`Definitions/`, `Theorems/` or `P2M/` — `P2M.Util` excepted, it is only the pin's `p2m_*` tactic
macros.

* **179 nodes / 36,993 raw `S_` lines / 1,952 named declarations** (1,462 public, 311 `private`,
  179 `solution` copies) — 13.2 % of the demand's nodes, 7.3 % of its raw lines. Measured on the tree
  before WORKORDER-MG2 landed; its four `Matrix` rows have since landed (+73), so the pool now reads
  **175 nodes / 35,952 lines** and the remaining wired surface is ≈1,568 (both are the pre-wave-1
  snapshot; §7.5 has the live figures — 103 ready candidates).
* **All 179 are graph leaves** (`needed 1`, `--include-leaves`): every premise is already ported, so
  the whole pool is *ready*; none of it is a gate for anything else in the cone.
* **No definition gate anywhere in the pool** — by construction (no `Definitions/` import survives
  the filter). The one FLT import inside a would-be family, the free-group family's
  `Definitions/Def_Compat_Mathlib430` (34 declarations of vendored mathlib-4.30 API), is **inert**:
  0 of its 34 declarations occur in the consumer's proof.
* Closing the pool faithfully (one module per subject, every public statement transcribed) wires
  **≈1,641 declarations**: the 1,462 publics plus one `Theorems/` headline per node; the 311
  `private` helpers stay private and unchecked, and the 179 `solution` copies are not ported.

## 2. The families

Prices are **M**easured (`port_advise` + `port_plan`) or **E**stimated at 0.92 × raw — the two
measured ratios were 0.917 (free-group) and 0.917 (ValuationSubring), so 0.92 is the honest default.
"modules" is a layout estimate at ~700 net lines per module.

| family (frontier preamble) | nodes | raw lines | decls | modules | price |
|---|---:|---:|---:|---:|---:|
| `ValuationSubring` | 15 | 3,875 | 215 | 2 | **3,553 M** |
| `LanglandsTunnell` | 10 | 3,856 | 116 | 2 | 3,548 E |
| `ModularCurve` | 8 | 2,216 | 165 | 2 | 2,039 E |
| `NumberField` | 10 | 2,060 | 139 | 2 | 1,895 E |
| `WeierstrassCurve` | 13 | 2,033 | 104 | 2 | 1,870 E |
| `MeasureTheory` | 14 | 1,962 | 55 | 2 | 1,805 E |
| `AutomorphicForm` (all `LocalIntertwining` + one) | 8 | 1,871 | 88 | 1 | 1,721 E |
| `ContinuousLinearMap` | 7 | 1,539 | 82 | 1 | 1,416 E |
| `CongruenceSubgroup` | 5 | 1,054 | 74 | 1 | 970 E |
| ~~`Matrix`~~ **landed (MG2, +73)** | ~~4~~ | ~~1,041~~ | ~~82~~ | — | **970 M** |
| `Module` (`Module.End`, `LinearMap`) | 4 | 1,028 | 53 | 1 | 946 E |
| `EisensteinGeneral` (`Arch`, `Piece`) | 2 | 899 | 26 | 1 | 827 E |
| `MulAction` | 2 | 848 | 32 | 1 | 780 E |
| `SchwartzMap` | 2 | 743 | 44 | 1 | 684 E |
| `jacobiTheta_two_eq_tprod` | 1 | 702 | 58 | 1 | 646 E |
| `IsDedekindDomain` | 4 | 701 | 25 | 1 | 645 E |
| `PowerSeries` | 4 | 696 | 18 | 1 | 640 E |
| `Representation` | 5 | 659 | 26 | 1 | 606 E |
| `AddCommGroup` | 2 | 640 | 39 | 1 | 589 E |
| `Function` | 3 | 626 | 31 | 1 | 576 E |
| `ModularForm` | 5 | 529 | 25 | 1 | 487 E |
| `ModularGroup` | 1 | 519 | 59 | 1 | 478 E |
| `BrauerNesbitt` | 1 | 414 | 19 | 1 | 381 E |
| `LinearEquiv`+`HexagonalLattice`+`Monoid`+`UpperHalfPlane`+`Algebra`+`Subgroup` | 13 | 2,242 | 183 | 1 | 2,063 E |
| `Nat`+`Complex`+`IntermediateField`+`VectorFourier`+`PeriodPair` | 6 | 1,304 | 41 | 1 | 1,200 E |
| `TateCurve`+`ZSpan`+`ZLattice`+`integralClosure`+`IsLocalRing` | 7 | 1,095 | 51 | 1 | 1,007 E |
| `LSeries`+`AlgebraicCurve`+`SimpleGraph`+`WittVector`+`ZMod`+`Int`+`IsLocallyConstant`+`AbsoluteValue` | 9 | 1,073 | 52 | 1 | 987 E |
| the 36-node tail: 31 families of at most 305 raw lines each (`Submodule`, `LaurentSeries`, `LinearMap`, `ContinuousMap`, `RingHom`, `Polynomial`, `ValuationRing`, `AddChar`, the `tsupport`/`Ioi` one-liners, `Subalgebra`, `ClassGroup`, `IsAddCyclic`, …) | 36 | 4,240 | 200 | 1 | 3,901 E |
| **pool** | **179** | **36,993** | **1,952** | **~25** | **~34,000** |

## 3. The free-group family — the blockers of the four `Matrix.SpecialLinearGroup` rows

This is the family the `Matrix` pricing left open, and it is the one to cut first: it is the only
batch whose *consumers* are already on the shelf.

| node | own lines | role |
|---|---:|---|
| `Subgroup.card_orbitRelQuotient_mul_card_eq_index` | 121 | leaf premise |
| `SimpleGraph.exists_walkConnected_transversal_of_preconnected` | 156 | leaf premise |
| `Monoid.CoprodI.isTree_cosetGraph` | 391 | leaf premise |
| `ModularGroup.exists_mulEquiv_freeProduct_quotient_center` | 519 | leaf premise |
| `Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero` | 543 | leaf premise |
| `Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank` | 1,545 | the engine's main theorem |
| `Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne` | 180 | headline |
| `…exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero` | 194 | headline |
| `…exists_generators_free_mod_neg_one_of_forall_trace_ne` | 157 | headline |
| `…finrank_addMonoidHom_eq_of_forall_trace_ne` | 155 | headline |

**10 nodes / 3,961 raw → 3,291 net new (measured)**, 381 declaration groups; 10 declarations are
already in the port (tier 1, importable: 34 lines not to re-prove), and **2 trusted substitutions**
(34 lines). The family is one development: **37 names are proved in ≥ 2 of its files, 506 removable
lines** — `mem_center_iff_eq` ×5 (72 lines), `finrank_addMonoidHom` ×2 (49), `exists_isConnectedTransversal`
×2 (40), … — so it lands as **one tier-3 engine + four public headlines = 2 modules**. The subject is
Bass–Serre/Kurosh: `SL₂(ℤ)` modulo its centre is free of rank 2, hence the `addMonoidHom` space has
`finrank` 2 and the trace-≠ condition gives generators modulo `-1`.

The two "suspicious" rows of its advise table are the parser's type-only `def` matches and are
**false**: `FreeActionRankFormula ↔ PeriodPair.DiscriminantNeZero` (149 copies — a `def` over the same
product type), `IrrationalPt ↔ CuspForm.heckeBaseAlgebra`, `Vertex ↔ CohCarrier.H1`. Read, not applied.

**Payoff: it closes the four `Matrix.SpecialLinearGroup` rows outright** (686 own lines, already
priced at 74 wired declarations in [TOPIC-matrix-family-in-cone.md](TOPIC-matrix-family-in-cone.md)),
i.e. the `Matrix.` namespace's demand goes to the GL/Serre pair alone (set MG4 in the pricing note), which is deferred.

## 4. What closing the whole pool takes

* **~33,000 net new lines** (34,000 before MG2 landed) — ten times the whole `TateSlots` + `tateCurve`
  engine work (3,343 net lines).
* **~25 modules** in **9–10 dispatches** (one per batch, 1–3 modules each).
* **≈1,568 wired declarations** after MG2's landing (1,641 measured before it), i.e. the checker goes
  2111 → ~3,680, a 1.7× growth of the verified surface; that is the single largest opportunity left in the column and it is all low-risk
  transcription (0 definitions to home, 0 promotions, 0 hub edits).
* It does **not** unblock the demand's interior by itself: these are leaves, so a consumer still needs
  its whole premise set. The unblocking wins are per family — the free-group batch closes four rows;
  `LanglandsTunnell`'s ODE leaves are the analytic side of §7's two gates; `WeierstrassCurve`'s are
  the ready shelf's own subject.

## 5. Recommended order

| order | batch | nodes | raw | price | why now |
|---:|---|---:|---:|---:|---|
| 1 | **free-group** (§3) | 10 | 3,961 | **3,291 M** | closes four rows and the `Matrix` namespace; one engine + 4 headlines; 506 lines of dedup already measured |
| 2 | **`ValuationSubring`** | 15 | 3,875 | **3,553 M** | largest single-subject family, all leaves, 0 substitutions, 190 groups |
| 3 | `WeierstrassCurve` | 13 | 2,033 | 1,870 E | the column's own ready-shelf subject; its topic already exists |
| 4 | `MeasureTheory` | 14 | 1,962 | 1,805 E | measure/fundamental-domain leaves, mostly small |
| 5 | `LanglandsTunnell` | 10 | 3,856 | 3,548 E | the ODE/moderate-growth side of the two gates |
| 6 | `ModularCurve`+`ModularForm`+`UpperHalfPlane`+`CongruenceSubgroup`+`ModularGroup` | 22 | 4,699 | 4,323 E | one q-expansion/congruence layer |
| 7 | `NumberField`+`IsDedekindDomain` | 14 | 2,761 | 2,540 E | the adelic/Dedekind-zeta leaves |
| 8 | `ContinuousLinearMap`+`Module` | 11 | 2,567 | 2,362 E | compact-operator/spectral leaves |
| 9 | `AutomorphicForm` (`LocalIntertwining` + the `rightTranslatesSpanFinite` leaf) | 8 | 1,871 | 1,721 E | the archimedean intertwining integrals |
| 10 | the tail (58 nodes / 8,367 lines) | 58 | 8,367 | 7,698 E | many unrelated one-liners; highest review cost per line — do it in 2–3 sweeps |

**Read §7 before acting on rows 2–10**: the preamble's one-to-three-node families (§7) are cheaper per
family than anything in this table, and §7.4 re-orders the waves accordingly (nine pairs first, then the
ready tail, then the free-group family, then this table's subjects).

## 6. Residuals

* The 0.92 estimate is applied to whole-file raw lines; it is honest for the two measured families but
  will move for a family whose files re-prove a shared prelude (`ModularCurve`'s q-expansion leaves
  are the likeliest to dedup well, `jacobiTheta_two_eq_tprod` the least).
* The module counts are layout guesses. The measured families show the pattern: a family with one
  engine and *n* headlines lands as 1–2 modules, a family of unrelated leaves as 1 module each.
* Nothing in this pool is a definition gate and nothing is a hub edit, so no batch pays a wave.

## 7. The one-to-three-node families — the preamble's small entries

The pool of §1 is "mathlib-import-only". The *preamble* also shows many one-to-three-node families
whose pin file imports a **definition or theorem module**; those are excluded from §1 but are the
cheapest cuts of all when the import is already ported. Measured on the same tree:

| | families | nodes | raw lines |
|---|---:|---:|---:|
| **ready** (every premise ported) | 43 | 57 | 23,750 |
| **blocked** | 11 | 21 | 7,370 |
| total (≤ 3 nodes) | 54 | 78 | 31,120 |

### 7.1 Ready one-to-three-node families

All of these are `needed 1..3`: one module each (or one module for a related pair), nothing to home,
nothing to promote. **42 families / 56 nodes / 11,624 raw lines / 554 public declarations** (596 wired with
their headlines), ~10,700 net new at the 0.92 ratio. The last column names the families those nodes are premises *of*, i.e. what
cutting them also closes.

| lines | nd | publics | net | family | closes / feeds |
|---:|---:|---:|---:|---|---|
| 1,111 | 3 | 88 | 1,022 | `PeriodPair` | `CuspForm`, `ModularCurve` |
| 848 | 2 | 32 | 780 | `MulAction` | `CuspForm`, `ModularCurve` |
| 743 | 2 | 44 | 683 | `SchwartzMap` | **blocker of `ZLattice`** |
| 702 | 1 | 31 | 645 | `jacobiTheta_two_eq_tprod` | `CuspForm`, `ModularCurve` |
| 647 | 2 | 4 | 595 | `LocalNewvector` | `AutomorphicForm`, `DihedralWeightOne` |
| 626 | 3 | 31 | 575 | `Function` | `AutomorphicForm`, `ModularCurve` |
| 519 | 1 | 58 | 477 | `ModularGroup` | **premise of the free-group family** (§3) |
| 414 | 2 | 12 | 380 | `LSeries` | `AutomorphicForm` |
| 414 | 1 | 1 | 380 | `BrauerNesbitt` | `GaloisRep`, `Representation` |
| 398 | 1 | 19 | 366 | `LinearEquiv` | `AlgebraicCurve`, `ModularCurve` |
| 394 | 1 | 32 | 362 | `HexagonalLattice` | `CuspForm`, `ModularCurve` |
| **370** | **1** | **40** | **340** | **`AddAut`** | `CuspForm`, `WeierstrassCurve` |
| 329 | 2 | 12 | 302 | `Subgroup` | **premise of the free-group family** (the 121-line node) |
| 312 | 1 | 1 | 287 | `RatIdele` | `AutomorphicForm`, `LanglandsTunnell` |
| 309 | 1 | 1 | 284 | `RatAdele` | `AutomorphicForm`, `LanglandsTunnell` |
| 305 | 1 | 10 | 280 | `Nat` | **blocker of `Int`** |
| 272 | 2 | 4 | 250 | `Complex` | `GaloisRep`, `ModularCurve` |
| 258 | 1 | 12 | 237 | `IntermediateField` | `CuspForm`, `ModularCurve` |
| 241 | 1 | 18 | 221 | `LocalGL2` | `AutomorphicForm`, `EisensteinGeneral` |
| 235 | 1 | 7 | 216 | `VectorFourier` | `AutomorphicForm`, `NumberField` |
| **223** | **1** | **9** | **205** | **`ZSpan`** | `AutomorphicForm` |
| 221 | 1 | 10 | 203 | `integralClosure` | `CuspForm` |
| 204 | 2 | 8 | 187 | `IsLocalRing` | `AlgebraicCurve`, `ModularCurve` |
| 157 | 2 | 8 | 144 | `IsLocallyConstant` | `AutomorphicForm` |
| 156 | 1 | 10 | 143 | `SimpleGraph` | **premise of the free-group family** (§3) |
| 152 | 1 | 8 | 139 | `WittVector` | `ModularCurve`, `WeierstrassCurve` |
| 145 | 1 | 5 | 133 | the `tsupport` bound | `AutomorphicForm` |
| **101** | **1** | **7** | **92** | **`ZMod`** | **blocker of `EisensteinSeries`** |
| 98 | 2 | 9 | 90 | `CuspFormClass` | `CohCarrier`, `ModularCurve` |
| 91 | 1 | 1 | 83 | `AbsoluteValue` | **blocker of `HeckeCharacter`** |
| 83 | 2 | 2 | 76 | `Submodule` | `AlgebraicCurve`, `AutomorphicForm` |
| 77 | 1 | 4 | 70 | `LaurentSeries` | `ModularCurve` |
| 77 | 1 | 1 | 70 | `LinearMap` | `AutomorphicForm` |
| 68 | 1 | 1 | 62 | `ContinuousMap` | `MeasureTheory` |
| 59 | 1 | 4 | 54 | `HeckeEis` | `CohCarrier`, `ModularCurve` |
| 58 | 1 | 2 | 53 | `RingHom` | `CuspForm` |
| 52 | 1 | 1 | 47 | `ValuationRing` | `AlgebraicCurve`, `CuspForm` |
| 45 | 1 | 1 | 41 | `AddChar` | `NumberField` |
| 42 | 1 | 3 | 38 | `integrableOn_Ioi…` | `AutomorphicForm` |
| 36 | 1 | 1 | 33 | `Subalgebra` | **blocker of `Polynomial`** |
| 18 | 1 | 1 | 16 | `ClassGroup` | `AutomorphicForm` |
| 14 | 1 | 1 | 12 | `IsAddCyclic` | `CuspForm`, `WeierstrassCurve` |

Nine of the 42 are also *premises* elsewhere, and three of those (`SchwartzMap`, `SimpleGraph`,
`ModularGroup`, plus `Subgroup`'s 121-line node) land inside another batch — so the effective extra
cost of the nine pairs and of the free-group family is smaller than their tables suggest.

Grouping for dispatch: the 11 entries under 80 lines (546 lines, 20 declarations) are single
declarations each. Cutting them one-per-module is honest (§3.1 directory = theory) but wasteful; the
better move is to let each ride with the neighbour it feeds (`ZMod` → `EisensteinSeries`,
`Subalgebra` → `Polynomial`, `AbsoluteValue` → `HeckeCharacter`, `Nat` → `Int`), which is exactly what
§7.2's pairs do.

### 7.2 The blocked ones, and the nine that are one leaf away

| blocked family | own lines | blocker(s) | blocker's own demand | verdict |
|---|---:|---|---:|---|
| `Polynomial` | 207 | `Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental` | 36 (ready) | **pair** |
| `GaussProlongation` | 181 | `AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers` | 121 (ready) | **pair** |
| `IsAlgClosed` | 93 | `ValuationSubring.exists_ringHom_extend_of_isAlgClosed` | 343 (ready) | **pair**, and the blocker is in B1 |
| `Int` | 117 | `Nat.exists_squarefree_sq_add` | 305 (ready) | **pair** (also closes `Nat`) |
| `EisensteinSeries` | 489 | `ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun` | 101 (ready) | **pair** (also closes `ZMod`) |
| `ZLattice` | 450 | `SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` | 563 (ready) | **pair** (also closes `SchwartzMap`) |
| `HeckeCharacter` | 459 | `AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv` + `NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi` | 91 (ready) + 140 (needs 2) | **pair**, one more premise |
| `AddCommGroup` | 1,008 | `CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff` | 300 (ready) | **pair**, but the `CohCarrier` subject is the column's own |
| `omegaRow_T2` | 447 | 6 `ModularForm`/`ModularCurve` q-expansion leaves | 476 (all ready) | **pair** (7 nodes) |
| `Monoid` | 2,479 | the free-group family (§3) | 3,275 | already priced: 3,291 net, 2 modules |
| `GaloisRep` | 1,440 | **16 nodes / 20,438 lines** (`M4aTorus` 12,126, the `Representation`/`NumberField` cyclotomic chain, `BrauerNesbitt` …) | — | **not closeable cheaply**: this is the cone's centre, not a family |

The nine pairs are **31 nodes / 5,927 raw lines → ~5,450 net new**, and they close **14 families**
(the nine + `Subalgebra`, `ZMod`, `Nat`, `AbsoluteValue`, `SchwartzMap`).

A **definition-gate audit of the 31 nodes** (the §1 classifier is per-file, so a *pair's* leaf can still
import a gate the blocked family's file did not — this is the §4(a) blindness and it bites here):
**six pairs are gate-free, three needed small `Definitions/` modules** (359 lines in all) — **four
of the five gates were homed in wave 1, and only `Def_ModularCurve_EigenformIdeal` (24 lines) is still
deferred** — and the other eight gate imports the pairs make are already homed:

| pair | unported gate | lines | homed? |
|---|---|---:|---|
| `GaussProlongation` | `Def_AlgebraicCurve_RegularProlongation` + its prerequisite `Def_AlgebraicCurve_ConstantReduction` | 84 + 127 | **yes** — both homed in wave 1 (`AlgebraicCurve/{ConstantReduction,RegularProlongation}.lean`) |
| `HeckeCharacter` | `Def_HeckeCharacter_FiniteOrder` | 30 | **yes** — homed in wave 1 (`HeckeCharacter/FiniteOrder.lean`) |
| `omegaRow_T2` | `Def_ModularCurve_OmegaOf` + `Def_ModularCurve_EigenformIdeal` | 94 + 24 | **partly** — `OmegaOf` homed (`ModularCurve/Defs/OmegaOf.lean`); `EigenformIdeal` still deferred ([CARRY-FORWARD.md](../../CARRY-FORWARD.md)) |
| the other six | — (`Def_EisensteinSeries_EisensteinG`, `Def_CohCarrier_Level` already homed) | 0 | yes |

So wave 1 was really **31 nodes / 5,927 lines + a 359-line definition gate** — of which 335 gate
lines were homed in wave 1 and 24 are still deferred — and the gate was the manager's (or delegated to
the group that needed it; a leaf module with no dependents is not a hub edit).

The order is
[WORKORDER-MG3-ds-leaf-families.md](WORKORDER-MG3-ds-leaf-families.md); it is dispatched as
three coding groups (A: `Polynomial`/`Int`/`IsAlgClosed`/`GaussProlongation`, 1,403 + 84; B:
`EisensteinSeries`/`ZLattice`/`AddCommGroup`, 2,911; C: `HeckeCharacter`/`omegaRow_T2`, 1,613 + 148) with
phase 2 (the 34 free-standing small families, 46 nodes / 9,344 lines) as the next wave.

### 7.3 The two outliers of the small-family view

* **`M4aTorus` — 1 node, 12,126 lines, ready.** A family of one module, and the largest single cut in
  the column: the ray-class L-series whose continuation both gates of §7 use
  (`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one`). It is a single 12k-line `S_`
  file; the port would split it by subject (the ray-class characters, the Eisenstein/theta input, the
  continuation), so "1 node" is not "1 small module" — price it as its own topic, not as a small family.
* **`GaloisRep` — 2 nodes / 1,440 lines → 16 nodes / 20,438 lines.** The two nodes are the
  semisimple-representation/descent statements; their premises are the ray-class subject above plus the
  `Representation`/`NumberField` cyclotomic chain. Not a small family: schedule it behind `M4aTorus`.

### 7.4 Revised close-out order (supersedes §5's rows 2–10 for the small families)

| wave | content | nodes | raw | price | why |
|---:|---|---:|---:|---:|---|
| 1 | **the nine pairs** (§7.2) — **complete 2026-10-20**: 18 modules, 323 wired, checker 2111 → 2434; the `ZLattice` pair landed later the same day (+2 modules, +33 wired, 5.5 s + 5.4 s builds) | 31 | 5,927 | **measured: 6,291 port lines, +323 wired, then +33** | closes 14 families for ~200 lines each, every blocker a ready leaf |
| 2 | **the ready tail** (§7.1) | 56 | 11,624 | ~10,700 E | 42 families, no blockers; group the `≤ 60`-line ones by area |
| 3 | the free-group family (§3) | 10 | 3,961 | **3,291 M** | closes the four `Matrix.SpecialLinearGroup` rows |
| 4 | `ValuationSubring` + `LanglandsTunnell` | 25 | 7,731 | **3,553 M** + 3,548 E | the two largest single-subject families |
| 5 | the medium families (§2) | 60 | 12,000 | ~11,000 E | `WeierstrassCurve`, `MeasureTheory`, the q-expansion group, … |
| 6 | `M4aTorus` (own topic) | 1 | 12,126 | ~11,200 E | the ray-class hub; behind it, `GaloisRep` |

### 7.5 Status against the live tree — re-read 2026-10-20, after waves 1–2 and the `ZLattice` landing

`frontier.py --ds --include-leaves` now reads **1,282 needed nodes / 488,187 lines**, with **103 ready
candidates** (`--ready`, all premises ported) — §1's scoping figure was 175. What remains of this note's
programme, by wave:

* **wave 1 is complete** (31/31 nodes): the nine pairs all landed, the `ZLattice` pair on 2026-10-20 as
  `Analysis/Fourier/{PoissonSummationPi,PoissonSummationZLattice}.lean` — 31 + 7 `own:` and 2 wired
  declarations, 5.5 s and 5.4 s builds; its statement hotspot is
  [logs/poisson-summation-statements.md](../../logs/poisson-summation-statements.md). The one gate still
  deferred is `Def_ModularCurve_EigenformIdeal` (24 lines; no consumer in `omegaRow_T2`);
* **wave 2's ready tail** was cut by phase 2 (44 of 49 dispatched nodes; five deferred on gates). What is left of it is the
  re-scoped [TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md): **37 nodes / 3,641
  lines / 283 publics in 7 families** — recorded and **not scheduled**; its §1 also notes a "phase 3b",
  seven `ValuationSubring.*` nodes that are not `needed 1` (the 1,155-line family, once the bigger
  nodes land);
* **wave 3 — the free-group family is untouched**: no `CoprodI`/`freeGroupBasis` declaration is in the
  tree. The live namespace rows are exactly the priced family — `Monoid` 3 / 2,479
  (`nonempty_freeGroupBasis_fin_kuroshRank` 1,545, `conj_pow_minimalPeriod` 543, `isTree_cosetGraph`
  391), `Matrix` 4 / 686 (the four `SpecialLinearGroup` headlines), `ModularGroup` 1 / 519, `Subgroup`
  1 / 121, `SimpleGraph` 1 / 156 — 10 nodes / 3,961 raw, as in §3. (`Matrix` also carries set MG3: 5
  nodes / 1,928 total.)
* **waves 4–6 are untouched** — the live `--ds` namespace rows: `ValuationSubring` 24 / 6,218,
  `LanglandsTunnell` 37 / 16,932, `WeierstrassCurve` 30 / 9,506, `NumberField` 110 / 35,595,
  `ModularCurve` 238 / 109,359, `AutomorphicForm` 427 / 178,247; the §7.3 outliers `M4aTorus` 1 /
  12,126 and `GaloisRep` 2 / 1,440 are still behind them;
* **the gate-blocked nodes** are still the five in [CARRY-FORWARD.md](../../CARRY-FORWARD.md):
  `LocalNewvector` (864-line gate), `HeckeEis.coresHom_eq_transfer` (304), `RatAdele` (144, 799
  importers), `RatIdele`'s `Def_RatIdele_Normalizer`, and `EigenformIdeal` (24).

So the note's open residue is: **phase 3's remaining 33 nodes (the `Representation` family landed
2026-10-20, see below; the rest scheduled nowhere), the free-group family (10 nodes, the cheapest
remaining cut), the five gate-blocked nodes, and the §5 families / outliers**; nothing in wave 1 or
the ready tail is owed any more.

**Status 2026-10-20 (later) — wave 3 landed, and two of the five gate-blocked nodes are done.** The
free-group family was ported whole (WORKORDER-FG1) and re-homed by subject — the graph lemma under
`Combinatorics/SimpleGraph/Transversal.lean`, the group theory under
`GroupTheory/{FreeDoubleCoset,BassSerre/{CosetGraph,MinimalPeriod},ModularGroup/FreeProduct,FreeGroup/KuroshRank}.lean`
(the four `Matrix.SpecialLinearGroup` headlines in a user-facing API module over the Kurosh engine) — plus the
one-module `UpperHalfPlane` q-expansion trio; the
checker is **3496 ok over 129 modules** (from 3010), with the measured dedup paid (52 copies, 39 in
the Kurosh engine). The two `Rat*` gates that phase 2 deferred
(`Def_LanglandsTunnell_StandardLocalConstantsAt` and `Def_RatIdele_Normalizer`) were homed whole and
both nodes ported (`NumberTheory/RatAdele/DenseRange.lean`, `NumberTheory/RatIdele/ClassCharNorm.lean`).
The live `--ds` rows that remain of this note's subjects: `Matrix` 1 / 1,242 (the GL row; set MG4, now landed);
`SimpleGraph`/`Subgroup`/`ModularGroup`/`Monoid`/`RatAdele`/`RatIdele` are gone, and so is
`UpperHalfPlane` — its last Fricke row (1 / 156) was taken on 2026-10-20 as
`ModularForms/HeckeFrickeTrace.lean` (10 wired), clearing the namespace. The gate-blocked nodes still deferred are
`LocalNewvector` (864-line gate), `HeckeEis.coresHom_eq_transfer` (304) and `EigenformIdeal` (24).
Records: [../../logs/qexp-and-freegroup.md](../../logs/qexp-and-freegroup.md),
[../../logs/rat-def-gates.md](../../logs/rat-def-gates.md), [../../logs/rat-nodes.md](../../logs/rat-nodes.md).

**The `Representation` family, audited and dispatched 2026-10-20.** The live family is six nodes /
2,351 raw lines — the four small ones of phase 3 (69/112/36/151) plus `exists_basis_toMatrix_…`
(291; over the 250-line test) and `exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
(**1,692**; 105 public declarations). All six are `needed 1` and gate-free (only `P2M.Util`, plus
one `Theorems/` import whose declaration — `BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq` —
is ported). `port_advise`/`port_plan` on the six: 2,268 declaration lines, 143 groups, **71 already
in the port**, **2,197 net**; 6 trusted substitutions (3 public imports in
`GaloisRep/Defs/MatrixRepresentation.lean`, 3 port-private helpers to promote) and 1 suspect
(`DescentConjugatorSupply ↔ PeriodPair.DiscriminantNeZero`, the parser's type-only `def` match). The
family is cut by size and subject, not as one wave:
[WORKORDER-R2-representation-leaves.md](WORKORDER-R2-representation-leaves.md) took the five
mathlib-shaped leaves — **landed 2026-10-20**: five modules in mathlib's layout
(`RepresentationTheory/{Burnside,InvariantPairing,CompactGroup,SubrepresentationExtension}.lean`,
`LinearAlgebra/Matrix/SubfieldBasis.lean`), 955 port lines, 21 wired, 0 mismatch / 0 missing, 0
warnings, `grep -c sorry` 0; the mathlib-first audit recorded a negative for every declaration and
supplied ingredients only (record: [logs/representation-leaves.md](../../logs/representation-leaves.md)); [WORKORDER-R1-descent-charpoly.md](WORKORDER-R1-descent-charpoly.md) took the 1,692-line descent
development as three `GaloisRep/Deformation/` modules — **landed 2026-10-20**: 1,938 port lines,
103 checked, 0 mismatch / 0 missing, the Galois subject the §7.3 note puts behind `M4aTorus`
(record: [logs/descent-charpoly.md](../../logs/descent-charpoly.md)). **The whole family is therefore
complete: six nodes / 2,351 raw lines → eight modules / 124 checked declarations.** §1's pool counts (175 / 35,952 / ≈1,568 wired) are the
pre-wave-1 scoping snapshot.

## 8. What the "small mathlib-like family" criterion must be (phase 2's scoping error)

Phase 2 was dispatched on **"a ready leaf in a one-to-three-node family"** alone, and that is not the
criterion this note's §7.1 table actually stated. Measured on the 46 nodes it dispatched:

| | nodes | pin lines |
|---|---:|---:|
| phase 2 as dispatched | 46 | 9,552 |
| of which **> 300 pin lines each** (not small) | **12** | **5,477** (57 %) |
| of which FLT-flavoured subject (not mathlib-shaped) | ≥ 8 (`PeriodPair` ℘-torsion/modular forms, `LocalNewvector` adelic newvectors, `RatAdele`/`RatIdele` idèle-class characters, `jacobiTheta_two_eq_tprod`, `CuspFormClass`, `HeckeEis`, `ZSpan`) | ≳ 2,600 |
| of which a definition gate exceeds the family (`LocalNewvector`: 864 gate lines for 647 family lines) | 1 family | 1,511 |

The wave was already in flight when this was noticed, so it completes; **nothing further is cut from
this pool** until it is re-scoped under four tests, all of which phase 2 failed at least once:

1. **Size.** A node is a "small supplement" at **≤ ~250 pin lines**; a family is small if its nodes are
   each that size (a 2–3 node family of 50–200-line leaves is fine; a single 797-line node is not).
2. **Shape, read not inferred.** Read the `Theorems/` statement: FLT-specific vocabulary or subject
   (Weierstrass ℘ and modular forms, adelic/newvector, idèle-class characters, Hecke operators, Tate
   slots) disqualifies it, however clean its imports. The §1 import classifier only says the file names
   mathlib objects, not that the mathematics is mathlib's.
3. **The mathlib-first negative** of [TOPIC-mathlib-supplements.md](../TOPIC-mathlib-supplements.md) §1,
   recorded in the module header.
4. **The gate-to-family ratio.** If the pin `Definitions/` gate is larger than the family (the
   `LocalNewvector` case: 179 + 114 + 531 + 40 = 864 lines of gate for 647 of statement), the gate is a
   set of its own with its own consumers, not a side-charge — defer, and record it in `CARRY-FORWARD.md`
   as that pair is now recorded.

What survives these tests from this pool is recorded as the cut itself, recomputed on the tree phase 2
left: **37 nodes / 3,641 pin lines / 283 public declarations in 7 families**, every node `needed 1`, gate-free
and subject-read — `MeasureTheory` 1,336, `ValuationSubring` 738, `Representation` 368, `Algebra` 349,
`ContinuousLinearMap` 328, `PowerSeries` 265, `Module.End` 257. That is
[TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md), with the exclusions and the reasons
on the record. It is **recorded, not scheduled**: the column stopped this front after phase 2.
