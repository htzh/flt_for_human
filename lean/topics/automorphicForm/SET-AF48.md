# SET-AF48 — the reduced place on a chart, and Deuring's multiplicity inequality

**Status: LANDED (2026-11-12)** — §0 the read, §1 the cut and the price, §2 the homes and the manager's
landed layer, §3 the orders and gates, §4 the forecast, §5 what the set does not do, **§6 the landing
record**. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read
SET-AF47's landing left. Forty-eighth set of the column: the two rows AF47 §6.2 named first.

**2 rows / 2,173 silo / ≈2,105 net** in **81 declaration groups** and 741 written scaffold lines. The two
rows are the shelf's head by size and by the pin's own route: they are the place-theoretic half of the
residue/ord dictionary the regular prolongation's level-lowering argument consumes.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits` | 1,083 | 3/9 | every place of `F` at which the chart element `x` is congruent to a constant has a **unique** place of the residue field above it, characterized by the residue non-unit condition |
| **B1** | `AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin` | 1,090 | 2/2 | Deuring's multiplicity inequality: the order of `R.residue f` at that place is at most the sum of the orders of `f` over the chart's matching places |

## 0. The read

`frontier.py --ds --ready --include-leaves --rank-by silo --top 0` (corrected: the ten MD-005 markers
unported, the same command as SET-AF47 §0):

| figure | value |
|---|---:|
| `needed [F terminal]` | **707 / 297,649** |
| `needed [literal]` | 728 / 304,571 |
| frontier F | 1,699 / 825,376 |
| ready rows | 52 / 12,126 |
| leaves | 185 / 46,068 |
| `AlgebraicCurve` demand | 42 / 16,769 |
| withheld (`premises_pruned`) | 4 rows |

The read is AF47's landing read: `--selfcheck` still fails the same ten phi-refactor markers (MD-005,
open, the workstream's), so the corrected column is the one quoted. The withheld block is unchanged and
is the pruned complex-analytic subject's residue (AF47 §0 names the four rows); none is cut here.

**The premise audit is closed.** A1's six premises and B1's six are all ported: `ValuationSubring.exists_le_forall_mem_iff_apply_mem`
(AF47 A1), `ValuationSubring.isAlgClosed_residueField` (AF47 D2), `ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin`
(AF45 B2), `RegularProlongation.eq_integers_of_forall_mem_adjoin_iff`,
`Place.exists_forall_ord_eq`, `Place.mem_toValuationSubring_of_isIntegral_adjoin`,
`Place.mem_iff_ord_nonneg`, `Place.ord_algebraMap`, `exists_separating_transcendental_of_perfectField`.
No proof-reached target lies outside the port.

**The definition gate is closed**: the wrappers import `Def_AlgebraicCurve_RegularProlongation`,
`Def_AlgebraicCurve_IsCurveOver` and `Def_AlgebraicCurve_Repartitions`, and `port_advise --with-defs`
finds all their declarations in the port (the three Def_ modules are the AF45 migration's homes:
`AlgebraicCurve/RegularProlongation.lean`, `Defs/IsCurveOver.lean`, `Defs/Repartitions.lean`).

## 1. The cut, and the price

The two rows are the shelf's two largest, and they are one story: the reduced place and the multiplicity
bound at it. Their preludes are the pin's copies of the same place/ord lemmas, all of which the port
already has (promoted in the `Place`/`Defs` modules, as binder variants — the recipe's §2 warning: take the
promoted statement, do not re-prove). `port_advise`:

| figure | AF48 |
|---|---:|
| raw `S_` lines | 2,173 |
| declaration lines | 2,113 |
| distinct declaration groups | 81 |
| duplicate copies inside the set | 0 |
| boilerplate dropped | 60 |
| **net new math lines** | **≈2,105** |

**Read this price off the pre-scaffold tree.** The scaffold is in the port before the workers start, and a
post-scaffold `port_plan` therefore reads "already in the port 2,100 / net 13" — the tool is answering
"how much of this is not yet declared anywhere", and the scaffold's own statements are. Price first, then
scaffold (FR-0184).

**One in-file substitute**: A1's `constHom` is already the port's `RegularProlongation.constHom`
(`RegularProlongationFinrank.lean`, three pin copies) — the scaffold drops it and calls the imported one.

## 2. The homes, and the manager's landed layer

| module | row | namespace | imports |
|---|---|---|---|
| `AlgebraicCurve/RegularProlongationReducedPlace.lean` | A1 | `AlgebraicCurve.RegularProlongation.ReducedPlace` (pin label `ExUniqPlace`) | `RegularProlongation{,Finrank,GaussBasis}`, `Defs/{Place,PushPull,Repartitions,IsCurveOver,PlacesOverDVR}`, `Place/Approximation`, `IsCurveOver/PerfectField`, `FieldTheory/ValuationSubring{,Composite,ResidueField}` |
| `AlgebraicCurve/DeuringMultiplicity.lean` | B1 | `AlgebraicCurve.RegularProlongation.DeuringMultiplicity` (pin label `ORLS`) | the same set |

Both are new modules: the cascade is zero, and no existing hub is edited. The pin's own import direction
(A1 and B1 both cite `RegularProlongation`/`Place` modules and nothing of each other) is preserved — the two
modules are *siblings*, so the two orders can run concurrently.

**The manager's layer is landed and measured** (scaffolds generated from the pinned text: the pin's
namespace and section structure verbatim, the tooling lines translated — `p2m_open` → `open`,
`p2m_export`/`p2m_reactivate` and the 84-line `attribute [-instance]`/`[-simp]` shims dropped, the pin's
`set_option maxHeartbeats` dropped — every theorem body `sorry`, every `def`/`structure` body verbatim):

| module | lines | decls | `sorry` | `check_port --force` |
|---|---:|---:|---:|---|
| `RegularProlongationReducedPlace.lean` | 390 | 43 | 43 | **44 ok / 0 / 0** |
| `DeuringMultiplicity.lean` | 351 | 35 | 35 | **35 ok / 0 / 0** |

The headlines sit at the wrappers' fully-qualified names (`theorem AlgebraicCurve.RegularProlongation.<name>`,
the wrappers' own shape), the pin's label namespaces are rectified (`ExUniqPlace` → `ReducedPlace`,
`ORLS` → `DeuringMultiplicity`), and the three data definitions (`constHom` is imported; the small
`def`s/structures of each file) are transcribed and building. All 78 statements are verified before a
proof is written.

## 3. The orders, and the gates

Two dispatches, disjoint modules, concurrent: `tmp/af48/WORKORDER-AF48A-reduced-place.md` (A1) and
`tmp/af48/WORKORDER-AF48B-deuring-multiplicity.md` (B1). The gates are the recipe's §6, per module: silent
at `-DautoImplicit=false -DmaxHeartbeats=200000` and `sorry`-free, the module's own `lake build` under
`flock`/`timeout` with no dependents and no tree build, the checker at §2's counts, `#print axioms` on the
two headlines, `dedup`/`move_dead`, and one consumer zone per order with a real cross-module composition.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 707 / 297,649 | **705 / 295,476** |
| frontier F | 1,699 / 825,376 | **1,701 / 827,549** |
| ready rows | 52 / 12,126 | **50 / 9,953** |
| leaves | 185 / 46,068 | 185 / 46,068 |
| `AlgebraicCurve` demand | 42 / 16,769 | **40 / 14,596** |
| rows readied | — | read at the landing |

The model is the per-set subtraction. **Caution, measured in AF47:** the shelf reads a pin node as ported
from its *declared statement*, so the scaffold moves these figures and the proofs do not; and the rows these
two readied must be measured, not forecast — AF47's forecast missed three cells for exactly that reason
(a `Place`/ord row readied by a premise the brief had not named). Also, both rows are `AlgebraicCurve`, so
the `AlgebraicCurve` demand *is* expected to fall here (unlike AF47's, whose readied rows were themselves
unported AC nodes).

## 5. What this set does not do

The shelf is AF47 §5's table with B1's row removed and these two cut; the rows that entered on AF47's
landing are `existsUnique_place_forall_residue_sub_mem_nonunits` (1,083, cut here),
`ord_residue_le_sum_ord_of_isIntegral_adjoin` (1,090, cut here) and
`exists_prolongation_of_card_roots_eq` (613, **AF49's row**). The rest of the ready block is deferred as a
block, as AF47 §5 records it, with the same three named next-in-line stories: the `EisensteinGeneral.Piece`
factorization (890, six `Def_` wrappers), the `NumberField` Dedekind-zeta pair (580 + 105, 18 consumers) and
the `ModularCurve` diamond row (485). `M4aTorus.completedRayL_fe` (12,126 silo) stays the queued big effort.

## 6. The landing (2026-11-12)

Two orders, disjoint modules, **zero `sorry`**, no statement moved (the checker counts are the scaffold's):

| order | module | lines | decls | `sorry` → | `check_port` | build | axioms | consumer |
|---|---|---:|---:|---|---|---:|---|---:|
| **48A** | `RegularProlongationReducedPlace.lean` | 390 → **1,108** | 43 | 43 → 0 | **44 ok / 0 / 0** | 3,266 jobs, 9.7 s | 3/3 | 152 lines, 0 err |
| **48B** | `DeuringMultiplicity.lean` | 351 → **1,124** | 36 | 35 → 0 | **35 ok / 0 / 0** | 3,266 jobs, 8.4 s | 5/5 | 93 lines, 0 err |
| | | **741 → 2,232** | **79** | **78 → 0** | **79 ok, 0 mismatch, 0 missing** | | **8/8** | **245 lines, 0 err** |

Both modules are silent at `-DautoImplicit=false -DmaxHeartbeats=200000` (9.6 s and 8.22 s) with zero
warnings, carry no `set_option` beyond `autoImplicit false`, no `omit` used as a silencer and no linter
silencing; each builds alone under `flock`/`timeout` (no tree build, no dependents). `dedup` over the four
new modules of AF48+AF49 reports **0 clusters across modules** (and the one intra-Kummer cluster is the
pin's own two public copies, kept); `move_dead` reports 0 declarations on both, and 48B calibrated the tool
against another module to prove "0" means *nothing dead* rather than *nothing parsed*. The manager re-ran
the checker, the axioms probes and both consumer zones independently.

### 6.1 What the two orders found

1. **The 84-line `attribute [-instance]`/`[-simp]` shim and `p2m_*` lines are pure tooling** — dropping
   them was right, and every proof still found its instances (48A added **no** import; 48B none either).
2. **A port-local lemma can shadow a mathlib one and force a qualification** (48B, pin :113): the port
   already carries `RegularProlongation.residue_eq_zero_iff` (`RegularProlongationFinrank.lean:118`, about
   `R.residue`), which shadows mathlib's inside `namespace AlgebraicCurve.RegularProlongation` — the pin had
   no sibling, so its bare `residue_eq_zero_iff` meant mathlib's. Proof-side qualification only; FR-0174's
   class, in a new namespace.
3. **Heartbeat margin measured, not assumed**: 48A's whole file is silent at 60,000; 48B's is silent at
   35,000 and its *first* timeout at 30,000 is `isIntegral_of_monic_of_coeff_mem` (:317) — **not** the two
   declarations the order flagged as risks (`exists_vanishing`, the headline). So the order's risk list was
   wrong about which declaration binds, which is the playbook's "bisect before trusting any attribution"
   lesson at one-file scale.
4. **The manager's declaration inventory was wrong** for 48A: three `eval₂`-family names were truncated by
   an ASCII-only regex at the Unicode subscript `₂` (`coe_eval₂_constHom` → `coe_eval`, and two distinct
   `residue_eval₂_*` collapsed into one repeated name, which the order then explained as a namespace split).
   The worker followed the pin and reported it; FR-0185 records the rule (verify an inventory's count
   against the pin's file before pasting it into an order).

### 6.2 The re-read (taken together with SET-AF49's landing)

| figure | before AF48+AF49 | **after** |
|---|---:|---:|
| `needed [F terminal]` | 707 / 297,649 | **703 / 294,693** |
| `needed [literal]` (corrected read) | 728 / 304,571 | **724 / 301,615** |
| frontier F | 1,699 / 825,376 | **1,704 / 828,508** |
| ready rows | 52 / 12,126 | **50 / 10,473** |
| leaves | 185 / 46,068 | 185 / 46,068 |
| `AlgebraicCurve` demand | 42 / 16,769 | **38 / 13,813** |
| rows readied | — | **2 / 1,303** |

**The accounting closes exactly on every cell** — `needed`, `literal`, ready rows and the AC demand move by
the four rows (2,956 silo) and nothing else. Two rows readied:
`RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin` (758, lev 1/1, 5 premises) and
`RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq` (545, lev 1/10, **17 premises** — a
genuine risk node for the next order). Ready rows: 52 − 4 cut + 2 entered = 50; silo
12,126 − 2,956 + 1,303 = 10,473.

**One cell needed a correction, and it is a new instrument finding**: as read, the frontier rose by
**3,132** lines, not 2,956. The extra **176** is `ValuationSubring.isIntegral_of_forall_mem` — a pin node the
port does **not** have, which the name tier now reads as ported because `ReducedPlace`/`DeuringMultiplicity`
declare a same-last-name lemma (`twin_scan` → `relative=1`: same last name, different statement). Registered
as **MD-006**; adding it to the `--unport` list (with MD-005's ten) gives the corrected frontier
**1,703 / 828,332** = 825,376 + 2,956 exactly, so all four cells close. The shadow is benign here — the node
is off the target closure, so `needed` never moved — but it inflates the frontier and would hide the node
from a future shelf that wanted it. **This is the FR-0047 limitation in the opposite direction** from the
recorded cases: there a shadow hid a *missing* node, here it adds one the port does not have.
