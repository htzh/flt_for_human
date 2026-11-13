# SET-AF50 — the ord equality of a chart, and the residue map's surjectivity at equal genus

**Status: LANDED (2026-11-12)** — §0 the read, §1 the cut and the price, §2 the homes and the manager's
landed layer, §3 the orders and gates, §4 the forecast, §5 what the set does not do, **§6 the landing
record and the re-read of AF50+AF51 together**. Read off the D–S
shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read
SET-AF48/AF49 left (with MD-005's ten and MD-006's one unported).

**2 rows / 1,303 silo / ≈1,100 net** in **80 declaration groups** and 607 written scaffold lines: the two
rows AF48's landing readied, and the closure of the chart's residue-degree dictionary.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin` | 758 | 1/1 | `∑ P ∈ T, P.ord f = ∑ Q ∈ T', Q.ord (R.residue f)`: the orders of an element and of its residue agree in total |
| **B1** | `AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq` | 545 | 1/10 | at equal genus, every element of the residue field's integral closure is a residue: the residue map is surjective onto `integralClosure` |

## 0. The read

`frontier.py --ds --ready --include-leaves --rank-by silo --top 0` (corrected: MD-005's ten **and** MD-006's
one unported — the eleven-marker read of SET-AF48 §6.2):

| figure | value |
|---|---:|
| `needed [F terminal]` | **703 / 294,693** |
| `needed [literal]` | 724 / 301,615 |
| frontier F | 1,703 / 828,332 |
| ready rows | 50 / 10,473 |
| leaves | 185 / 46,068 |
| `AlgebraicCurve` demand | 38 / 13,813 |
| withheld (`premises_pruned`) | 4 rows (the pruned subject's residue; none cut here) |

The two rows are the head of the ready shelf after the three biggest rows of AF48/AF49 left it, and B1 is
the set's **17-premise** node — the recipe's "give it its own order and its own wall time".

**The premise audit is closed**: A1's five premises and B1's seventeen are *all* ported (AF47's
`existsUnique_place…`/`ord_residue_le_sum_ord…`, AF49's `exists_monic_coeff_natDegree_le…`, AF45's
`mul_min_ord_residue_le_of_monic`/`isPrincipalIdealRing…`, the `Place`/ord calculus, the Riemann–Roch and
genus vocabulary, and `constantsAreBase_of_deg_eq_one`). No proof-reached target lies outside the port.

**The definition gate is closed**: both wrappers import the three `Def_AlgebraicCurve_*` modules
(`RegularProlongation`, `IsCurveOver`, `Repartitions`), all ported (SET-AF48 §0's check).

## 1. The cut, and the price

The two rows are one story: A1 turns the chart's Deuring inequality (AF48 B1) into an *equality*, and B1
supplies the residue-surjectivity that makes the degree count come out. They are siblings (no premise of
one is the other), so their orders run concurrently.

| figure | AF50 |
|---|---:|
| raw `S_` lines | 1,303 |
| declaration lines | 1,229 |
| distinct declaration groups | 80 |
| duplicate copies inside the set | 0 |
| boilerplate dropped | 74 |
| **net new math lines** | **≈1,100** |

**The price is an estimate, and the reason is FR-0184**: `port_plan` prices against the tree, and the
scaffolds are in it, so a post-scaffold run reads "already in the port 1,210 / net 19". The tree-independent
figures are the raw/declaration/group counts above; the 1,100 is those minus the pin-side substitutes the
port already holds (the `ord_*` prelude and `constHom`, ≈120 lines).

## 2. The homes, and the manager's landed layer

| module | row | namespace | imports |
|---|---|---|---|
| `AlgebraicCurve/RegularProlongationSumOrdResidue.lean` | A1 | `AlgebraicCurve.RegularProlongation.SumOrdResidue` (pin label `SOSR`) | the `RegularProlongation*` family, `Defs/*`, `Place/Approximation`, `IsCurveOver/PerfectField`, `FieldTheory/ValuationSubring*` |
| `AlgebraicCurve/RegularProlongationResidueIntegralClosure.lean` | B1 | `…ResidueIntegralClosure` (pin label `CbPrime`) | the same set |

**The manager's layer is landed and measured** (the AF48 generation recipe: the pin's namespace/section
structure verbatim, `p2m_open` → `open`, the `attribute [-]` shims and the pin's `set_option` dropped,
theorem bodies `sorry`, data definitions verbatim):

| module | lines | decls | `sorry` | `check_port --force` |
|---|---:|---:|---:|---|
| `RegularProlongationSumOrdResidue.lean` | 355 | 53 | 46 | **54 ok / 0 / 0** |
| `RegularProlongationResidueIntegralClosure.lean` | 252 | 24 | 23 | **26 ok / 0 / 0** |

All **80 statements** are verified before a proof is written, the pin's machine labels rectified
(`SOSR` → `SumOrdResidue`, `CbPrime` → `ResidueIntegralClosure`), and the data definitions (`divOf`,
`zsum`, `Dom`, `Fnt`, `Red`, `cst`, `phi`, `kappa`; `placeOfValuationSubring`, `mulRight`, `constHom`,
`chart`) transcribed and building.

## 3. The orders, and the gates

Two dispatches, disjoint modules, concurrent:
`tmp/af50/WORKORDER-AF50A-sum-ord-residue.md` (A1) and
`tmp/af50/WORKORDER-AF50B-residue-integral-closure.md` (B1, alone because of its 17 premises). The gates are
the recipe's §6 per module: silent at 200,000 heartbeats and `sorry`-free, the module's own `lake build`
under `flock`/`timeout`, the checker at §2's counts, `#print axioms`, `dedup`/`move_dead`, and one consumer
zone each.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 703 / 294,693 | **701 / 293,390** |
| frontier F | 1,703 / 828,332 | **1,705 / 829,635** |
| ready rows | 50 / 10,473 | read at the landing |
| `AlgebraicCurve` demand | 38 / 13,813 | **36 / 12,510** |

The per-set subtraction. Two cautions, both measured before: the *scaffold* books the demand and the proofs
do not (FR-0114), and a new same-last-name declaration can shadow a pin node into the frontier (MD-006) —
so the frontier cell is the one to check for a 176-line-class artefact. **Rows readied are not forecast**:
A1's consumer is `sum_ord_eq_ord_residue_of_residue_integralClosure_surjective` (398), and B1's ten
consumers are large `ModularCurve` rows that will need more than this set.

## 5. What this set does not do

The ready block is SET-AF48 §5's table with AF48's two rows and AF49's two removed; the head is now
`EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` (890, six `Def_` modules — a priced
definition gate, not taken), the `AutomorphicForm` `tsum`-average row (635), the `NumberField`
Dedekind-zeta product row (580, **AF51's**), the `GaloisRep` semisimplicity row (495) and the `ModularCurve`
diamond row (485). `M4aTorus.completedRayL_fe` (12,126 silo) stays the queued big effort. The Kummer
root-lifting family (`exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_*`, 255 + 249) is **not** ready: it
needs `sum_genusFF_le_of_sum_finrank_eq_of_{isAlgClosed,krullDimLE_one}` (193 + 216) and
`genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero` (262), which in turn need
`exists_forall_finrank_residueSpan_inf_add_card_le` (638) and
`exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_*` (566/783) — a two-set story of its own.

## 6. The landing (2026-11-12)

Two orders, disjoint modules, **zero `sorry`**, no statement moved (the checker counts are the scaffold's):

| order | module | lines | decls | `sorry` → | `check_port` | build | axioms | consumer |
|---|---|---:|---:|---|---|---:|---|---:|
| **50A** | `RegularProlongationSumOrdResidue.lean` | 355 → **798** | 53 | 46 → 0 | **54 ok / 0 / 0** | 3,857 jobs, 11 s | clean | 111 lines, 0 err |
| **50B** | `RegularProlongationResidueIntegralClosure.lean` | 252 → **573** | 24 | 23 → 0 | **26 ok / 0 / 0** | 3,863 jobs, 7.2 s | clean | 168 lines, 0 err |
| | | **607 → 1,371** | **77** | **69 → 0** | **80 ok, 0 mismatch, 0 missing** | | **2/2** | **279 lines, 0 err** |

Both modules are silent at 200,000 heartbeats with zero warnings, carry no `set_option` beyond
`autoImplicit false` and no silencer, and build alone under `flock`/`timeout` (no tree build, no
dependents). `dedup` reports **0 clusters / 0 removable lines** on both; `move_dead` 0 declarations, with
50A calibrating the tool's own scanner (`decls: 54, live: 54, dead: 0`) so the zero is a measurement.

### 6.1 What the two orders found

1. **The seventeen-premise row closed positive.** 50B checked every premise the pin uses against the
   port's statement and found them all strong enough to discharge the pin's proof **verbatim** — the only
   gap was the scaffold's import cone (four project imports: `Genus/DegreeIdentity`,
   `ResidueTheorem/RRAssembly`, `Place/ConstantFieldExtension`, and
   `RegularProlongationGaussDegree`, the last one for `exists_monic_coeff_natDegree_le_of_forall_subring`
   at pin :329, which the manager's list had missed). So the recipe's "17 premises is where a set stalls"
   did not bite here: the premises were fine, the *imports* were not.
2. **A one-line pin proof that needs a seven-figure heartbeat budget is a defeq trap** (FR-0187): the pin's
   `ord_add_algebraMap_eq_zero` (`:101`) does not fit at 200,000 and measures ≥2,000,000, because
   `P.ord`'s argument is `↑(⟨m,_⟩ + ⟨alg,_⟩)` on one side and the raw `m + algebraMap K F c` on the other
   and `isDefEq` unfolds the coercion. The worker replaced it with a `congrArg Subtype.val` / `rw` /
   `ord_coe_unit` proof (statement untouched) and the file then fits at 100,000 — i.e. **half the gate**.
   The rest of the module's deviations are mechanical v4.34 renames, two qualified names
   (`Ideal.sub_mem`, `Polynomial.leadingCoeff_ne_zero` — FR-0174's shadowing again) and one
   `simp only` → `rw` that was emitting unused-arg warnings.
3. **The 50A blocker was the manager's import cone** (FR-0181, third instance): the worker proved the two
   missing lemmas unreachable by computing the closure of all 14 frozen project imports (32 modules) and
   asked, instead of editing a frozen list. Granted as two `FLTForHuman` lines; the build cost is two
   previously-unbuilt sibling dependencies.
4. **Warning-carrying neighbours in the cone**: `RegularProlongationResidueIntegralClosure`'s build replays
   41 warnings from modules its new imports pull in (`P1/TraceEngine` 14, `P1/PerfectResidue` 11,
   `Genus/Stichtenoth` 8, `P1/Separating` 3, `Defs/LocalResidue` 3, `Tate/CompletionTraceSum` 1). None is in
   this set and none is silenced; carried forward as a hygiene item.

### 6.2 The re-read, AF50+AF51 together (four rows / 1,988 silo)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 703 / 294,693 | **699 / 292,705** | 699 / 292,705 ✓ |
| `needed [literal]` | 724 / 301,615 | **720 / 299,627** | — |
| frontier F | 1,703 / 828,332 | **1,707 / 830,320** | +1,988 ✓ |
| ready rows | 50 / 10,473 | **47 / 8,883** | — |
| leaves | 185 / 46,068 | 185 / 46,068 | ✓ |
| `AlgebraicCurve` demand | 38 / 13,813 | **36 / 12,510** | 36 / 12,510 ✓ |
| `NumberField` demand | 99 / 34,198 | **97 / 33,513** | 97 / 33,513 ✓ |
| rows readied | — | **1 / 398** | not forecast, as stated |

**Every cell closes exactly** on the four rows' 1,988 lines and 4 nodes — no shadow artefact this time,
because the read carried MD-006's `--unport`. Ready rows: 50 − 4 cut + 1 entered = 47; silo
10,473 − 1,988 + 398 = 8,883. The one row readied is
`RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective` (398) — 50B's consumer,
exactly as forecast.

**Named next**: that 398 row and the two `ModularCurve` rows it gates; the `EisensteinGeneral.Piece`
factorization (890, six `Def_` modules — the largest ready row, with a priced def gate); the
`AutomorphicForm` `tsum`-average row (635, lev 1/1); the `GaloisRep` semisimplicity row (495); and the
Kummer root-lifting family, still two sets away (SET-AF50 §5). `M4aTorus.completedRayL_fe` (12,126 silo)
remains the queued big effort.
