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
  179 `solution` copies) — 12.7 % of the demand's nodes, 7.3 % of its raw lines.
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
| `Matrix` (MG2, in flight) | 4 | 1,041 | 82 | 4 | **970 M** |
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
| `LinearEquiv`, `HexagonalLattice`, `Monoid` | 3 | 1,183 | 102 | 1 | 1,088 E |
| `UpperHalfPlane`, `Algebra`, `Subgroup` | 10 | 1,059 | 68 | 1 | 974 E |
| `Nat`, `Complex`, `IntermediateField`, `VectorFourier`, `PeriodPair` | 6 | 1,304 | 41 | 1 | 1,200 E |
| `TateCurve`, `ZSpan`, `ZLattice`, `integralClosure`, `IsLocalRing` | 7 | 1,095 | 51 | 1 | 1,007 E |
| `LSeries`, `AlgebraicCurve`, `SimpleGraph`, `WittVector`, `ZMod`, `Int`, `IsLocallyConstant`, `AbsoluteValue` | 11 | 1,187 | 56 | 1 | 1,092 E |
| the rest of the tail (≤ 150 raw lines each; 25 nodes) | 25 | 4,800 | 200 | 2 | 4,416 E |
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

* **~34,000 net new lines** — by measured ratio, 3.4× the whole `TateSlots`+`tateCurve` engine work.
* **~25 modules** in **9–10 dispatches** (one per batch, 1–3 modules each).
* **≈1,641 wired declarations**, i.e. the checker goes 2038 → ~3,680, a 1.8× growth of the verified
  surface; that is the single largest opportunity left in the column and it is all low-risk
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

## 6. Residuals

* The 0.92 estimate is applied to whole-file raw lines; it is honest for the two measured families but
  will move for a family whose files re-prove a shared prelude (`ModularCurve`'s q-expansion leaves
  are the likeliest to dedup well, `jacobiTheta_two_eq_tprod` the least).
* The module counts are layout guesses. The measured families show the pattern: a family with one
  engine and *n* headlines lands as 1–2 modules, a family of unrelated leaves as 1 module each.
* Nothing in this pool is a definition gate and nothing is a hub edit, so no batch pays a wave.
