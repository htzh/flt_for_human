# SET-AF49 — Kummer splitting of a regular prolongation, and the Gauss degree bound

**Status: LANDED (2026-11-12)** — §0 the read, §1 the cut and the price, §2 the homes and the manager's
landed layer, §3 the orders and gates, §4 the forecast, §5 what the set does not do, **§6 the landing
record**. Read off the same corrected shelf as SET-AF48.

**2 rows / 783 silo / ≈740 net** in **57 declaration groups** and 469 written scaffold lines. The two rows
are the shelf's next `RegularProlongation` nodes after AF48's: the Kummer extension step and the monic
polynomial certificate that the degree argument consumes.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq` | 613 | 1/2 | Kummer splitting: if the residue of `f` has `q` distinct `q`-th roots in `Fbar`, the prolongation extends to `F(f^{1/q})` as `q` prolongations with distinct integer rings |
| **B1** | `AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring` | 170 | 2/13 | monic equation with Gauss degree bounds: an element whose integrality is decided by the chart has a monic annihilating polynomial over `A[X]` with `natDegree (coeff j) ≤ (natDegree − j) * m` |

## 0. The read

Same command and correction as SET-AF48 §0 (`needed` **707 / 297,649**, ready 52 / 12,126, leaves
185 / 46,068, `AlgebraicCurve` demand 42 / 16,769), with the two AF48 rows now scaffolded in the tree.
`--selfcheck` still names the ten MD-005 markers. The premise audit: A1 cites only
`ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card` (AF45) and
`ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card` (AF47 C1), both ported; B1 cites four
premises (`RegularProlongation.coeff_mem_of_aeval_mem_integers`,
`RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers`,
`Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental`,
`RegularProlongation.transcendental_of_residue_transcendental`), all ported. No proof-reached target lies
outside the port. **The definition gate is closed**: both wrappers import only
`Def_AlgebraicCurve_RegularProlongation`, which is ported.

## 1. The cut, and the price

The two rows are one subject — the *degree theory* of a regular prolongation: A1 moves a `q`-th root through
the chart (the Kummer step), B1 produces the polynomial certificate the residue-degree count consumes. They
are not each other's premise (both cite the finrank/valuation modules, not each other), so they are
siblings, and both are cheap in lines and expensive in declarations.

| figure | AF49 |
|---|---:|
| raw `S_` lines | 783 |
| declaration lines | 744 |
| distinct declaration groups | 57 |
| duplicate copies inside the set | 3 (`constHom`, already in the port) |
| boilerplate dropped | 39 |
| **net new math lines** | **≈740** |

Same instrument caveat as SET-AF48 §1: the price is the pre-scaffold one; a post-scaffold `port_plan`
reads ≈0 because the scaffolds' statements are in the tree (FR-0184).

## 2. The homes, and the manager's landed layer

| module | row | namespace | imports |
|---|---|---|---|
| `AlgebraicCurve/RegularProlongationKummer.lean` | A1 | `AlgebraicCurve.RegularProlongation.KummerSplitting` (the pin's own label — descriptive, kept) | `RegularProlongation{,Finrank,GaussBasis}`, `Defs/{Place,PushPull,Repartitions,IsCurveOver,PlacesOverDVR}`, `Place/Approximation`, `IsCurveOver/PerfectField`, `FieldTheory/ValuationSubring{Composite,ResidueField}` |
| `AlgebraicCurve/RegularProlongationGaussDegree.lean` | B1 | root (the pin's file is flat: `open AlgebraicCurve IsLocalRing Polynomial`, declarations at `AlgebraicCurve.RegularProlongation.*`) | the same set |

**The manager's layer is landed and measured** (the same generation recipe as SET-AF48: the pin's
namespace/section structure verbatim, tooling translated, `p2m_open` → `open`, the `attribute [-]` shims and
the pin's `set_option maxHeartbeats` dropped, theorem bodies `sorry`, all defs/structures verbatim):

| module | lines | decls | `sorry` | `check_port --force` |
|---|---:|---:|---:|---|
| `RegularProlongationKummer.lean` | 397 | 48 | 47 | **55 ok / 0 / 0** |
| `RegularProlongationGaussDegree.lean` | 72 | 1 | 1 | **1 ok / 0 / 0** |

Kummer's module carries the pin's three namespace blocks merged into one (`KummerSplitting`), its six data
definitions (`evalAt`, `resEval`, the `CentredAt` structure, `incl`, `theta`, `thetaBar`, `resBar`,
`thetaEquiv`, `liftResidue`) transcribed and building. **The pin's `S_…exists_monic_coeff…` carries
`set_option maxHeartbeats 4000000`** — the port does not (the playbook's §6 rule), so B1's single proof is
the set's one measured risk and the order gives it the probe ladder.

## 3. The orders, and the gates

One dispatch, two modules, disjoint from AF48's: `tmp/af49/WORKORDER-AF49A-kummer-and-gauss-degree.md`.
The gates are the recipe's §6 per module: silent at `-DautoImplicit=false -DmaxHeartbeats=200000` and
`sorry`-free, each module's own `lake build` under `flock`/`timeout`, the checker at §2's counts,
`#print axioms` on both headlines, `dedup`/`move_dead`, and one consumer zone.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 705 / 295,476 (after AF48) | **703 / 294,693** |
| frontier F | 1,701 / 827,549 | **1,703 / 828,332** |
| ready rows | 50 / 9,953 | read at the landing |
| `AlgebraicCurve` demand | 40 / 14,596 | **38 / 13,813** |

The per-set subtraction, with AF47's lesson applied: the *scaffold* books the demand, and the landing's own
contribution is axioms and silence. The rows these two ready (the two
`exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_*` at 255 + 249 are gated on A1 **and** on three further
unported premises — `sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed` 193,
`…_of_krullDimLE_one` 216, `genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero`
262 — so they are **not** expected to become ready here; the pair enters AF50 as its own story with those
three ingredients).

## 5. What this set does not do

The ready block is AF48 §5's, with A1 and B1 cut. Not taken here, and named so the next scoping has the
list: the `EisensteinGeneral.Piece` factorization (890, six `Def_` wrappers), the `NumberField`
Dedekind-zeta pair (580 + 105), the `ModularCurve` diamond row (485) and the `GaloisRep` semisimplicity row
(495) — all in the ready block's table (SET-AF47 §5); the `RegularProlongation` residue rows
`exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq` (261, lev 1/6) and
`finiteDimensional_adjoin_residue_of_sum_finrank_eq` (27, lev 3/5) stay; and `M4aTorus.completedRayL_fe`
(12,126 silo) remains the queued big effort.

## 6. The landing (2026-11-12)

One order, two modules, **zero `sorry`**, no statement moved (the checker counts are the scaffold's):

| module | lines | decls | `sorry` → | `check_port` | build | axioms |
|---|---|---:|---|---|---:|---|
| `RegularProlongationKummer.lean` | 397 → **630** | 49 | 47 → 0 | **55 ok / 0 / 0** | 3,272 jobs, 8.4 s | clean |
| `RegularProlongationGaussDegree.lean` | 72 → **212** | 1 | 1 → 0 | **1 ok / 0 / 0** | 3,266 jobs, 5.8 s | clean |
| | **469 → 842** | **50** | **48 → 0** | **56 ok, 0 mismatch, 0 missing** | | **2/2** |

Both modules are silent at `-DautoImplicit=false -DmaxHeartbeats=200000` with zero warnings, carry no
`set_option maxHeartbeats` and no silencer, and build alone under `flock`/`timeout` (no tree build, no
dependents). `dedup` reports one intra-module *shape* cluster and 0 removable lines — the pin's own two
copies of `algebraMap F F' (bv0 : F) ∈ V` (`CentredAt.algebraMap_mem` :249 and `mem_of_mem_integers` :395),
kept **because the pin states both publicly**; `move_dead` reports 0. The consumer zone
(`spec/AlgebraicCurveSetAF49AConsumer.lean`, 114 lines) compiles at 0 errors with three executed
compositions: the Kummer headline at `q = 2` (read as the injectivity of the family's integer rings), the
`minpoly_eq` statement at `q = 2`, and the Gauss bound at `m = 0` (every coefficient constant).

### 6.1 What the order found

1. **The pin's `maxHeartbeats 4000000` was never needed.** The Gauss file's single proof measures
   **27,000–28,000 heartbeats** (probe ladder: OK at 28,000, FAIL at 27,000), i.e. ~14 % of the 200,000
   gate. The port carries no override, as the playbook requires. **A fact discovered on the way, worth
   recording because the playbook's "project cap" phrasing invites a wrong reading**: this package's
   `lakefile.lean` already sets a *package-wide* `maxHeartbeats = 4000000` (line 11, alongside
   `autoImplicit false`), so `lake build` runs at 4M while `lake env lean -DmaxHeartbeats=200000` (the
   edit loop and every work order's gate) is the strict bound. No module carries a *per-file* override —
   that is the rule the pin's `set_option` would have broken.
2. **Two imports added, both reported** (the frozen list was incomplete, the manager's error — FR-0181's
   second instance): `Mathlib.FieldTheory.KummerExtension` for `rootOfSplitsXPowSubC`, and
   `FLTForHuman.FieldTheory.ValuationSubringCompleteSplitting` for the AF47 C1 axiom
   (`exists_valuation_mul_eq_one_of_finrank_le_card`) that pin :606–:608 cites.
3. **Drift**: two new rows for the `_sum` → `Sum` rename family — `Polynomial.eval₂_finset_sum` →
   `Polynomial.eval₂_finsetSum` (one site) and two more instances of the already-recorded
   `finset_sum_coeff` — appended to [../TOPIC-mathlib-drift.md](../TOPIC-mathlib-drift.md); plus one
   unused-simp-argument dropped (`simp [Polynomial.natDegree_X_pow]` → `simp`) and `haveI` → `have` at four
   sites (FR-0173).
4. **The headline's `open …KummerSplitting in` has no counterpart** in the scaffold's frozen `open` block, so
   the body writes its five `KummerSplitting` references fully qualified instead of adding an `open`. That
   is a proof-side deviation only — the statement is untouched and the checker reads it `ok`.

### 6.2 The re-read

*(taken together with SET-AF48's: see [SET-AF48.md](SET-AF48.md) §6.)* The forecast's per-set subtraction is
expected to hold for this set's two rows (both `AlgebraicCurve`, both declared): `needed` falls by 2 nodes /
783 lines, the frontier rises by the same, and the two `exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_*`
rows are **not** expected on the ready shelf — they need the three ingredient nodes §4 names, which is the
next scoping's cut.
