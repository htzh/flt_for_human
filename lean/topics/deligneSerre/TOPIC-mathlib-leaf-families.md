# Mathlib-like leaf families in the D-S cone — the close-out survey

Scoped 2026-10-20, after WORKORDER-MG1's landing (checker 2038) and with WORKORDER-MG2 in flight.
This note answers one question: *of the D-S demand, what is left that is mathlib-shaped, how is it
grouped into families, and what does closing it cost?*

## 1. The pool

The frontier's own family preamble (`frontier.py --ds --include-leaves`, the
`unported demand by top-level namespace` table) crossed with a per-node classification of each pin
`S_` file's imports. A node is **mathlib-like** when its `S_` file imports nothing from
`Definitions/`, `Theorems/` or `P2M/` — `P2M.Util` excepted, it is only the pin's `p2m_*` tactic
macros.

* **179 nodes / 36,993 raw `S_` lines / 1,952 named declarations** (1,462 public, 311 `private`,
  179 `solution` copies) — 13.2 % of the demand's nodes, 7.3 % of its raw lines. Measured on the tree
  before WORKORDER-MG2 landed; its four `Matrix` rows have since landed (+73), so the pool now reads
  **175 nodes / 35,952 lines** and the remaining wired surface is ≈1,568.
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
i.e. the `Matrix.` namespace's demand goes to zero except set MG3.

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
nothing to promote. Excluding the outlier of §7.3: **42 families / 56 nodes / 11,624 raw lines**.

| lines | nodes | family | | lines | nodes | family |
|---:|---:|---|---|---:|---:|---|
| 1,111 | 3 | `PeriodPair` | | 235 | 1 | `VectorFourier` |
| 848 | 2 | `MulAction` | | 223 | 1 | `ZSpan` |
| 743 | 2 | `SchwartzMap` | | 221 | 1 | `integralClosure` |
| 702 | 1 | `jacobiTheta_two_eq_tprod` | | 204 | 2 | `IsLocalRing` |
| 647 | 2 | `LocalNewvector` | | 157 | 2 | `IsLocallyConstant` |
| 626 | 3 | `Function` | | 156 | 1 | `SimpleGraph` |
| 519 | 1 | `ModularGroup` | | 152 | 1 | `WittVector` |
| 414 | 2 | `LSeries` | | 145 | 1 | the `tsupport` bound |
| 414 | 1 | `BrauerNesbitt` | | 101 | 1 | `ZMod` |
| 398 | 1 | `LinearEquiv` | | 98 | 2 | `CuspFormClass` |
| 394 | 1 | `HexagonalLattice` | | 91 | 1 | `AbsoluteValue` |
| **370** | **1** | **`AddAut`** | | 83 | 2 | `Submodule` |
| 329 | 2 | `Subgroup` | | 77 | 1 | `LaurentSeries` |
| 312 | 1 | `RatIdele` | | 77 | 1 | `LinearMap` |
| 309 | 1 | `RatAdele` | | 68 | 1 | `ContinuousMap` |
| 305 | 1 | `Nat` | | 59 | 1 | `HeckeEis` |
| 272 | 2 | `Complex` | | 58 | 1 | `RingHom` |
| 258 | 1 | `IntermediateField` | | 52 | 1 | `ValuationRing` |
| 241 | 1 | `LocalGL2` | | 45 | 1 | `AddChar` |
| | | | | 42 | 1 | `integrableOn_Ioi…` |
| | | | | 36 | 1 | `Subalgebra` |
| | | | | 18 | 1 | `ClassGroup` |
| | | | | 14 | 1 | `IsAddCyclic` |

Cost: **~10,700 net new** at the 0.92 ratio, ~42 modules if each family is its own module, ~20 if the
`≤ 60`-line one-liners are grouped by area (they are single declarations, and grouping unrelated ones
in one module is against §3.1 — accept the extra small modules, or cut the tiny ones only when a
neighbouring batch touches the same area).

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

The nine pairs are **26 nodes / 5,927 raw lines → ~5,450 net new**, and they close **14 families**
(the nine + `Subalgebra`, `ZMod`, `Nat`, `AbsoluteValue`, `SchwartzMap`).

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
| 1 | **the nine pairs** (§7.2) | 26 | 5,927 | ~5,450 E | closes 14 families for ~200 lines each, every blocker a ready leaf |
| 2 | **the ready tail** (§7.1) | 56 | 11,624 | ~10,700 E | 42 families, no blockers; group the `≤ 60`-line ones by area |
| 3 | the free-group family (§3) | 10 | 3,961 | **3,291 M** | closes the four `Matrix.SpecialLinearGroup` rows |
| 4 | `ValuationSubring` + `LanglandsTunnell` | 25 | 7,731 | **3,553 M** + 3,548 E | the two largest single-subject families |
| 5 | the medium families (§2) | 60 | 12,000 | ~11,000 E | `WeierstrassCurve`, `MeasureTheory`, the q-expansion group, … |
| 6 | `M4aTorus` (own topic) | 1 | 12,126 | ~11,200 E | the ray-class hub; behind it, `GaloisRep` |
