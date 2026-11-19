# SET-AF86 — the converse, the archimedean adjointness, and the balanced-compact idèles

**Status: LANDED (2026-11-14).** The fourth set of the wave, cut from the shelf SET-AF85
landed on: **5 rows / 2,677 silo** in **three orders**, four modules (three new).

| # | order | rows | silo | module(s) | pin publics on the wire | manager-scaffolded | order-scaffolded |
|---|---|---|---:|---|---:|---:|---:|
| A | the converse: an arithmetic genuine cuspidal eigensystem is a weight-one lift | 1 | 950 | `LanglandsTunnell/Converse.lean` (new) | 1 | 1 | — |
| B | the archimedean derivative and the Casimir against the Petersson pairing | 4 | 1,523 | `AutomorphicForm/Adelic/PeterssonSkewAdjunction.lean` (new) | 59 | 4 | 55 |
| C | the balanced-compact idèles and the infinite-adele Haar measure | 2 | 204 | `NumberTheory/NumberField/TateGlobal/BalancedCompact.lean` (new), `…/AdelicHaar/ProductMeasure.lean` | 11 + 1 | 2 | 10 |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af86_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **539 / 248,145** |
| ready rows | **16 / 4,392** |
| leaves | **118 / 30,021** |
| withheld (FR-0044 guard) | 4 / 831 |

Exactly SET-AF85's measured landing, and the ready block's head is the row the last set readied: the
950-line `LanglandsTunnell.Converse…` (nine premises, every one ported), then the two
`setIntegral_archDerivAt…` rows (392 + 385) whose own premise is AF85's 119-line volume row.

## 1. The cut

| # | row | silo | lev | pub | priv |
|---|---|---|---:|---:|---:|
| A | `LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable` | 950 | 1/3 | 1 | **61** (58 new) |
| B1 | `AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain` | 385 | 1/2 | 22 | 10 |
| B2 | `AutomorphicForm.setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain` | 392 | 3/4 | 22 | 10 |
| B3 | `AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain` | 270 | 2/6 | 6 | 1 |
| B4 | `AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain` | 476 | 2/2 | 9 | 0 |
| C1 | `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 1/2 | 11 | 0 |
| C2 | `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 4/5 | 1 | 0 |

**B is a chain, not four independent rows.** The two Casimir rows cite the two derivative rows (B3's
premise is B1, B4's is B2, together with the commutator rows and AF85's slab-volume row), so they are
priced *in the same order and the same module*: one worker writes the skew-adjointness rows first and the
Casimir rows on top of them. That is what makes B 1,523 silo rather than two orders of 777 and 746 that
could not run concurrently anyway.

**The three stories.** A is the converse direction of the weight-one lift: outside a finite set of places,
the Hecke ratio `a²/b` of an arithmetic genuine cuspidal eigensystem is the square of a real and the
Ramanujan-type bound holds — it reads the Petersson integral off the cuspidal realization and needs
AF85's `ℚ` Siegel cover, which is why it became ready last wave. B is the archimedean calculus of the
Petersson pairing: the directional derivative is formally skew-adjoint, the Casimir is self-adjoint, and
the raised/lowered combinations are adjoint up to a sign, in both the real and the complex place. C is the
idèle group's shape: one compact norm-one set such that every idèle is a principal idèle times a *balanced*
archimedean dilation times an element of it, and the right-invariance of a Haar measure on the
infinite-adele `GL₂`.

**`centralChar` is deferred again, now with a measured gate.** The 113-silo
`AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` was deferred by SET-AF84
for its `Def_HeckeCharacter_FiniteOrder` prefix; that module has since landed, but the row's *proof*
closure still names `Def_AutomorphicForm_ViaCompactCuspNotion` (74 lines), which is unported. All four of
that module's own imports are ported, so it is a one-module definition gate — a set of its own, not a rider.

The rest of the ready block stays deferred for the recorded reasons: `WeierstrassCurve` 697 / 599 and
`GaloisRep` 495 (other columns), `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_…` 200,
`ValuationSubring` 138, `ModularForm.exists_gamma0_qExpansion_…` 66, `AlgebraicCurve.exists_placeMap_…`
59, the `ModularCurve` rows 36 / 34 / 24 (other columns). The leaves block is unchanged at 118 / 30,021 and
carries this column's own remaining leaves (`AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite`
576, `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` 501,
`AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` 445,
`LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` 446,
`AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` 282, …).

## 2. The homes and the scaffolds

| module | home | imports the vocabulary from |
|---|---|---|
| `LanglandsTunnell/Converse.lean` | new, beside the Rankin–Selberg and ODE modules of the subject | `AutomorphicForm/Adelic/PeterssonSlabPairing` (the pairing row), `DetNormSlabFundamentalDomain`, `Siegel/FiniteCover` (AF85's cover row), `Cusp/{GenuineRealization,LevelOneObstruction}`, `IdeleNormDet{,Glue}`, `RatIdele/ClassCharNorm`, `TateGlobalContinuousIdeleNorm` |
| `AutomorphicForm/Adelic/PeterssonSkewAdjunction.lean` | new: the archimedean differential operators' adjointness is a subject of its own, above `ArchDerivCasimir{,Complex}` and above AF85's `SlabVolume` | the two `ArchDerivCasimir` modules, `Siegel/SlabVolume`, `IdeleNormDet`, `TateGlobalIdeleNormDet`, `AdelicHaar/GeneralLinear` |
| `NumberTheory/NumberField/TateGlobal/BalancedCompact.lean` | new: the balanced refinement of the norm-one compactness, above the Fujisaki façade | `TateGlobalCompactness` (the compact set), `NumberTheory/AdelicModulus` (the Haar-character product formula) |
| `NumberTheory/AdelicHaar/ProductMeasure.lean` | append: the product structure of the adelic Haar measure is this module's subject | its own closure plus `NumberTheory/AdelicLevel/Countability` (added; that module imports mathlib and `LinearAlgebra/Countable` only, so the edge is acyclic) |

No legacy home is touched. A and C's two modules are new and disjoint; C's `ProductMeasure` edit is the
only insertion, and no other order builds against it. All three run concurrently and only the build lock
is shared.

| module | scaffold state | `check_port` at scaffold | `scaffold_audit` at scaffold |
|---|---|---:|---|
| `LanglandsTunnell/Converse.lean` | 1 headline, `sorry` | **1 ok / 0 / 0** | complete |
| `AutomorphicForm/Adelic/PeterssonSkewAdjunction.lean` | 4 headlines, `sorry` | **4 ok / 0 / 0** | 4 FOLDED + 55 MISSING (the order's step 1) |
| `NumberTheory/NumberField/TateGlobal/BalancedCompact.lean` | 1 headline, `sorry` | **1 ok / 0 / 0** | 1 FOLDED + 10 MISSING (step 1) |
| `NumberTheory/AdelicHaar/ProductMeasure.lean` | 23 landed + 1 headline, `sorry` | **24 ok / 0 / 0** | complete |

Two scaffolding notes. The Casimir rows' statements are `let`-chain statements
(`let lower := …; let raise := …; (∫ …) ∧ (∫ …) ∧ (∫ …)`), and a text-level cut at the first
line-ending `:=` stops *inside* the `let` block: the two statements are therefore taken from their
`Theorems/` wrappers (whose `:= by p2m_exact_reverting …` tail is the unambiguous cut), not from the `S_`
files — the same `MISSING`-vs-`mismatch` discipline as FR-0224, applied to the cut itself.

## 3. The orders and the gates

Orders in `lean/tmp/af86/WO.md`. The gates are SET-AF85's six, unchanged:

1. `check_port --force` → the module's full pin public count `ok`, `0 mismatch / 0 missing / 0 own` (for B
   and C's new module the count is the *port's* declaration count after step 1, and `scaffold_audit`
   `complete` is the acceptance test — FR-0226).
2. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` → **silent**; `lake build` per
   module under `flock`/`timeout` for the olean.
3. `#print axioms` on every row and on the largest engine → `[propext, Classical.choice, Quot.sound]`.
4. `dedup.py --within --module <stem>` → 0 clusters, or the pin's own engine/row pair with the reason.
5. `move_dead.py … --dry-run` → `0 declarations, 0 lines`.
6. A heartbeat *probe* in the header, never a `set_option` (FR-0225).

## 4. The forecast, measured with the scaffolds on disk

| figure | §0 | forecast (AF86) |
|---|---:|---:|
| `needed [F terminal]` | 539 / 248,145 | **534 / 246,214** |
| ready rows | 16 / 4,392 | **15 / 5,002** |
| leaves | 118 / 30,021 | **118 / 30,021** |
| withheld | 4 / 831 | 4 / 831 |

**Four rows become ready**, and they are this set's own two chains:

| row readied by the set | silo | by |
|---|---:|---|
| `AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact` | 935 | C2 |
| `AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional` | 860 | C2 |
| `AutomorphicForm.setIntegral_archCasimirAtComplex_mul_conj_eq_and_archDelAt_adjoint_of_isFundamentalDomain` | 476 | B2 |
| `AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain` | 270 | B1 |

The two Casimir rows are cut *inside* B (the chain), so the shelf's new block is dominated by the
**level-spherical pair (1,795 silo)**, whose ten premises include C2's Haar-invariance row — that pair is
the next set's order A once C2 lands.

## 5. The landing

All five rows in, no `sorry`, four modules (three new), three consumers.

| file | rows | lines | decls | checker | probe (silent / fails) |
|---|---|---:|---|---|---:|
| `LanglandsTunnell/Converse.lean` (new) | A | **1,001** | 62 (1 + 61) | **1 ok / 0 / 0** | 9,000 / 4,500 |
| `AutomorphicForm/Adelic/PeterssonSkewAdjunction.lean` (new) | B1–B4 | **1,507** | 63 (45 + 18) | **45 ok / 0 / 0** | 120,000 / 60,000 |
| `NumberTheory/NumberField/TateGlobal/BalancedCompact.lean` (new) | C1 | **184** | 11 (11 + 0) | **11 ok / 0 / 0** | 10,000 / 5,000 |
| `NumberTheory/AdelicHaar/ProductMeasure.lean` | C2 | **613** (was 489; +128 −4) | 55 (24 + 31) | **24 ok / 0 / 0** | 15,000 / 10,000 |
| | **5** | **+3,305** | **+137 (5 rows + 132 engines)** | **81 ok, 0 mismatch, 0 missing, 0 own** | |

Every module is silent at `-DmaxHeartbeats=200000` with **no** in-file `set_option`; axioms
`[propext, Classical.choice, Quot.sound]` on every row and on the largest engines (A probed all 62
declarations, B probed 14 sites, C all 11); `move_dead` reads `0 declarations, 0 lines` on all four;
`scaffold_audit` reads **complete** on all four (B's 59-public wire lands 45 declarations, the four
`solution`s folded); `dedup --within` is 0 on three and **3** on B — the pin's own `ℝ`/`ℂ` matrix
duplication (`dA`/`dAC`, `dB`/`dBC`, `sw`/`swC`), the instance-argument false-positive class, recorded.

Consumers, each silent: `spec/LanglandsTunnellSetAF86AConsumer.lean` (the row as a finiteness statement —
the failing places are finite — and as a one-place conjunction), `spec/AutomorphicFormSetAF86BConsumer.lean`
(the two real rows on the diagonal `x' = x`: the derivative pairing cancels, the Casimir is symmetric),
`spec/NumberFieldSetAF86CConsumer.lean` (the balanced decomposition at `ℚ`; the Haar row through
`MeasureTheory.map_mul_right_eq_self`).

### What the workers' diagnoses overrode in this brief

1. **Five `import` lines across three orders** (FR-0229): B needed `MulRightInvariant`, `ArchCasimir`,
   `ArchCasimirComplex` and a mathlib module (`HasDerivAt.star`), C needed `MulRightInvariant` and
   `ArchType`. All five were import edits on modules that already existed; nothing was missing from the
   port. A's nine premises, measured, were all in its 146-module closure — no import added. This is the
   measured case that produced `tools/deps/premise_imports.py` (FR-0229's instrument entry).
2. **B's "≈55 declarations" was unreachable**: four of the 55 names collide across the four pins
   (`main` ×4, `integral_lincomb` ×2), so six renames are forced and the landing is 45 public; all six
   verify at the checker's content-hash tier, so no marker row was needed — and none was invented.
3. **`port_advise`'s "`Γp` already in the port" is wrong**: `AutomorphicForm.adelicUnipotent` is the
   unipotent-radical subgroup, not the pin's `Γp = (globalPoints …).range`; the prelude was transcribed at
   the pin's text. Two of its other pointers (`mapMatrix_scalar`, `mul_conj_eq_normSq`) are private in
   `Cusp/SatakeBound.lean` and were restated privately, as the pin does.
4. **C1's scaffold header called the pin's ten helpers `private`**; they are public — which is exactly why
   step 1 existed with ten MISSING rows. C2's premise claim was false for two of three (item 1).
5. **A's scaffold was two `open`s short** (`open scoped MatrixGroups`, `open NumberField.TateGlobal
   NumberField.AdelicVolume` for bare `ideleNorm`/`archDetNorm`/`archCentralUnit`) — a `lake env lean`-visible
   defect, not a statement defect, so it was fixed in place and the statement stayed `1 ok`.

### Interface decision (recorded, not deferred)

`dedup --cross` pairs A's private prelude with `Cusp/SatakeBound.lean`'s `F`-general copy of it. **Keep the
duplication.** The pin proves the `ℚ` row and the `F`-general sibling in separate files, each with its own
private prelude; promoting the shared engine would put an `F`-general block on the public API with its own
wire obligations and no consumer (the two modules are deliberately independent — neither imports the other,
recorded in both headers).

### The set's numbers

| figure | before | **after** (measured) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 539 / 248,145 | **527 / 243,269** | 526 / 242,269 |
| ready rows | 16 / 4,392 | **10 / 2,212** | 8 / 2,057 |
| leaves | 118 / 30,021 | **118 / 30,021** | 118 / 30,021 |
| withheld | 4 / 831 | 4 / 831 | 4 / 831 |

Two corrections to the forecast's reading, both attributable and neither a surprise: the forecast read was
taken with four of the five scaffolds on disk (the two Casimir rows were folded into B afterwards), and the
landing read also carries SET-AF87's scaffolds — two of the ten ready rows (`CuspidalConstituent.exists_rightConv_injOn_…`,
78 + 77 silo) cite AF87A's level-spherical pair and are therefore AF87's readies, not AF86's. AF86's own
readies are the level-spherical pair (935 + 860), which SET-AF87 cut, and the Casimir pair (476 + 270),
which this set cut inside its own order B.
