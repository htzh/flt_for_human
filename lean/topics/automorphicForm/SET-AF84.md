# SET-AF84 — the Siegel cover, the irreducibility spine, the unramified Whittaker model, and the Eisenstein archimedean core

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** The second set of the wave, cut from the shelf SET-AF83
landed on: **15 rows / 4,596 silo** in **five new modules**, four orders (one of them two modules).

| # | order | rows | silo | module(s) | pin publics | manager-scaffolded | order-scaffolded |
|---|---|---|---:|---|---:|---:|---:|
| A | the finite Siegel cover of the centre | 2 | 1,811 | `AutomorphicForm/Adelic/Siegel/FiniteCover` | 3 | 2 | — |
| B | the irreducibility spine of the cuspidal constituent | 4 | 946 | `AutomorphicForm/Adelic/Cusp/IrreducibleSpine` | 16 | 2 | 14 |
| C | the unramified Whittaker model | 3 | 792 | `RepTheory/LocalLanglands/WhittakerRecursion` | 23 | — | 11 declared |
| D | the Eisenstein piece: archimedean core and Euler factor | 6 | 1,047 | `EisensteinGeneral/ArchIntegralBound`, `LanglandsTunnell/RankinSelberg/EulerPolyRecursion` | 10 | 6 | 4 |

Per-order pin load is 792–1,811 lines, and the engine count is the number that matters for the workers: **A
transcribes 100 private declarations** (the heaviest single row in the column so far), B 30, C 18, D 21.

**Counts, and the instrument.** Every figure in this brief's tables comes from `spec/statement_db.py`'s parser
(`parse_file`), not from a `private`-prefix regex — the manager's first cut used the regex, which reads
`@[scoped simp] private theorem` as public, and it inflated order C to "26 public declarations". The wire actually
carries **23** public declarations, and the module's structural maximum is **11**: 10 of the 23 are the pin's own
byte-identical engine block shared by the C2 and C3 files (declared once, the *port once* rule), 3 are the pins'
`solution` wrapper glue (folded onto the rows), and 1 is the C1 `solution`, which re-states the C1 row. See
FR-0226.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_after_af83.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **563 / 256,474** |
| ready rows | **18 / 5,347** |
| leaves | **128 / 31,935** |
| withheld (FR-0044 guard) | 4 / 831 |

Exactly SET-AF83 §5's measured post-landing figures. The ready block's head is now the 1,781-line Siegel-covering
row — three of the four rows SET-AF83 readied are *also* ready rows, not leaves — and the leaves block has ten
rows of this wave's own subject matter.

## 1. The cut

Five rows come from the ready block (1,781 + 30 + 320 + 317 + 234 = 2,682 silo) and ten from the leaves
(1,914). The selection criterion is the same as SET-AF83's: **silo per public statement**. A row that is one
public headline over a 15–108-declaration private engine is the ideal order content — the agent gets the engine,
the manager's scaffold is one statement.

| # | row | silo | lev | pub | priv |
|---|---|---:|---:|---:|---:|
| A1 | `AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet` | 1,781 | 4/41 | 1 | **100** |
| A2 | `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | 2 | 0 |
| B1 | `AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep` | 320 | 1/1 | 1 | 15 |
| B2 | `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep` | 317 | 1/1 | 1 | 15 |
| B3 | `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal` | 234 | 2/3 | 11 | 0 |
| B4 | `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | 3 | 0 |
| C1 | `UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor` | 380 | 3/7 | 1 | 18 |
| C2 | `UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow` | 205 | 1/2 | 11 | 0 |
| C3 | `UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval` | 207 | 1/2 | 11 | 0 |
| D1 | `EisensteinGeneral.Arch.exists_norm_archIntegral_le` | 233 | 2/2 | 1 | 9 |
| D2 | `EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero` | 189 | 2/2 | 1 | 6 |
| D3 | `EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable` | 165 | 1/1 | 1 | 5 |
| D4 | `EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq` | 125 | 4/6 | 1 | 1 |
| D5 | `LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one` | 231 | 1/1 | 5 | 0 |
| D6 | `LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow` | 104 | 1/1 | 1 | 6 |

**The four stories.** A is the quantitative Siegel cover: a *finite* set `T` fixed in advance such that the
translates of one centre-cut Siegel set cover `GL₂(𝔸_K)` modulo the centre for every window — and its two
premises are exactly the two integrality rows SET-AF82A and SET-AF83B landed, so the order closes a loop this
column opened two sets ago. B is the cuspidal constituent's irreducibility spine (the invariants of a cusp
subrepresentation lie in finitely many irreducible archimedean types, plus the orthogonality that makes the
decomposition available). C is the local unramified Whittaker model: the Hecke recursion sequence, its
summability, and its identification with the Rankin–Selberg Euler polynomial. D is the Eisenstein piece's
analytic core — the archimedean bound behind the `FactorizationDatum` factors, the induced section's continuity,
the Bruhat-series Whittaker coefficient, the additive-character integral identity, and the two Rankin–Selberg
lemmas (the Euler polynomial's reciprocal Taylor expansion and the ODE vanishing lemma its continuation runs on).

**What was deferred, and why.** `LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_…` (589 silo, 1 public,
15 private) was this wave's intended fifth order and is **withdrawn at scoping**: its statement and proof need six
`Def_` modules the port does not have — `Def_LocalNewvector_AdelicSpanCarrier` (179 lines),
`Def_LocalNewvector_ConductorDatum` (114), `Def_LocalNewvector_PrincipalSeriesCarrier` (255),
`Def_RepTheory_GL2CongruenceSubgroup` (531), `Def_AutomorphicForm_DihedralWeightOneLift` (30),
`Def_LocalLanglands_IntegralSubgroupCompact` (40) — **1,149 lines of definition layer**, which is a set of its own
and not a rider on this one. Recorded here so the next scoping pass does not rediscover it: that row plus the two
`LocalNewvector` siblings is 647 silo *after* ~1,149 lines of `Def_` work, and the `Def_RepTheory_GL2CongruenceSubgroup`
half is `RepTheory` vocabulary that the generic `typeSubmodule` home debt
([../../CARRY-FORWARD.md](../../CARRY-FORWARD.md)) also wants.

The rest of the ready block stays deferred for the recorded reasons: `WeierstrassCurve` 697/599,
`GaloisRep` 495, `MeasureTheory` 200, `ValuationSubring` 138, `NumberField.TateGlobal` 120,
`AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` 113 (its `Def_` prefix pulls
`Def_HeckeCharacter_FiniteOrder`, a different subject; *(correction, SET-AF89: that module landed, and the
row's live gate — `Def_AutomorphicForm_ViaCompactCuspNotion` — was paid there; the row is ported at
`AutomorphicForm/Adelic/Cusp/CentralCharacter.lean`)*), `ModularForm`/`ModularCurve`/`AlgebraicCurve` rows (other
columns), and `NumberField.AdelicHaar.isMulRightInvariant_…` 84.

## 2. The homes and the scaffolds

| module | home | imports the vocabulary from |
|---|---|---|
| `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` | new, under the existing `Siegel/` subject | `Siegel/CentreCutCover`, `ContentBound` (A's premise), `FiniteIntegralConjugation` (A's other premise), `NumberTheory/AdelicHeight` |
| `AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` | new, under `Cusp/` | `Cusp/Constituent`, `Cusp/SpectrumCarrier`, `Cusp/SpectrumSubrep`, `CarrierPins`, `WindowedSiegel/CentreCutSet`, `IsotypicCuspSpace`, `NumberTheory/AdelicBox` |
| `RepTheory/LocalLanglands/WhittakerRecursion.lean` | new, beside the definition module it extends | `RepTheory/LocalLanglands/UnramifiedWhittaker`, `LanglandsTunnell/RankinSelberg/Euler` |
| `EisensteinGeneral/ArchIntegralBound.lean` | new | `AutomorphicForm/Adelic/{WhittakerCoefficient,InducedSection,EtaFamily,WeylIntertwining,ArchKFinite,SmoothAutomorphicFn,ProductionPins,ConstantTerm}`, `NumberTheory/{AdelicBox,AdelicFourier,AdelicHaar/Adele}`, `LanglandsTunnell/{TateLocalZeta,TateLocalConstantsAt}` |
| `LanglandsTunnell/RankinSelberg/EulerPolyRecursion.lean` | new | `LanglandsTunnell/RankinSelberg/Euler` |

No legacy home is touched, no hub is edited, the four orders touch disjoint files, and every row is a leaf or a
ready row whose premises are already in the tree — so all four run concurrently and only the build lock is shared.

**Scaffolding split, and the deviation in order C.** The manager scaffolded the headlines: A's two rows, B's two
single-headline constituent rows, all four of D1's single-headline rows, and D2's two rows — ten statements, each
`check_port`-green at scaffold. **Order C's module is a header, an import list and a three-line `spec-pin:` wire
with no declarations**, and its public surface is the order's step 1 — 11 declarations over the wire's 23 public
declarations (the pin's duplicated block declared once, the three `solution`s folded, the C1 row covering its own
`solution`). The reason is structural, not
budgetary: the three `UnramifiedWhittaker` pins are *flattened* files whose public declarations sit in in-file
namespaces with their own section variables (`variable {K} [Field K] …`, `open Polynomial UnramifiedWhittaker`,
`namespace …`), so transcribing them is a re-derivation of the file's shape, not a copy of statements — the same
argument that moved SET-AF81/AF82 to the delegated-scaffold discipline. B's remaining 14 and D2's remaining 4
statements are in the same position and are also the orders' step 1.

| module | scaffold state | `check_port` at scaffold | `scaffold_audit` at scaffold |
|---|---|---:|---|
| `Siegel/FiniteCover.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | complete |
| `Cusp/IrreducibleSpine.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | 14 MISSING (the order's step 1) |
| `RepTheory/…/WhittakerRecursion.lean` | header + wire only | **0 ok / 0 / 0** | 23 on the wire: 3 FOLDED + 20 MISSING (the order's step 1) |
| `EisensteinGeneral/ArchIntegralBound.lean` | 4 headlines, `sorry` | **4 ok / 0 / 0** | complete |
| `LanglandsTunnell/…/EulerPolyRecursion.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | 4 MISSING (the order's step 1) |

## 3. The orders and the gates

Orders in `lean/tmp/af84/WO.md`. The gates are SET-AF83's six, with two corrections that wave produced:

1. `check_port --force` → the module's **full** pin public count `ok`, `0 mismatch / 0 missing / 0 own`.
2. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` → **silent** (`lake build` per module
   under `flock`/`timeout` for the olean).
3. `#print axioms` on every row and on the largest engine declaration → `[propext, Classical.choice, Quot.sound]`.
4. `dedup.py --within --module <stem>` → 0 clusters, or the pin's own engine/row pair with the reason recorded.
5. `move_dead.py --source <module> --target /dev/null --dry-run` → `0 declarations, 0 lines`.
6. **A heartbeat *probe*, recorded in the module header — never a `set_option`.** Playbook §3.5: no module
   carries a `set_option maxHeartbeats`; an in-file cap is a defect marker. Probe with
   `-DmaxHeartbeats=N` until it fails, write "silent at N, fails at N/2" in the header comment, install nothing.
   (FR-0225: the previous wave's gate asked for the opposite and four workers obeyed it literally.)

Plus `scaffold_audit` reading **complete** at the end — which for B, C and D2 is the proof that step 1 actually
happened rather than being folded into the proofs — and a `spec/` consumer per order written by the manager on
landing.

## 4. The forecast, measured with `--port`

All fifteen rows `--port`ed on this read:

| figure | §0 | forecast (AF84) |
|---|---:|---:|
| `needed [F terminal]` | 563 / 256,474 | **548 / 251,878** |
| ready rows | 18 / 5,347 | **22 / 6,398** |
| leaves | 128 / 31,935 | **118 / 30,021** |

**Nine rows become ready** (the block's silo total therefore *rises* while its membership turns over):

| row readied by the set | silo | order |
|---|---:|---|
| `EisensteinGeneral.Arch.exists_complexKType` | 1,004 | D1 |
| `EisensteinGeneral.Arch.exists_realKType` | 790 | D1 |
| `UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero` | 646 | C |
| `UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 618 | C |
| `AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul` | 273 | B |
| `AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral` | 138 | D2 |
| `EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum` | 122 | D3 |
| `AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain` | 119 | A |
| `AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat` | 23 | A |

The next scoping pass opens on a ready block headed by the **two `EisensteinGeneral.Arch` K-types (1,794 silo
together, readied by D1)** and the **two `UnramifiedWhittaker` rows (1,264, readied by C)** — 3,058 silo of two
subjects, which is two orders and the natural successor to this set.

## 5. The landing

All fifteen rows in, no `sorry`, five new modules, four consumers. The measured shelf re-read is the forecast to
the line.

| file | rows | lines | decls | checker | probe (silent / fails) |
|---|---|---:|---|---|---:|
| `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` | A1–A2 | **1,846** | 110 (2 + 108) | **2 ok / 0 / 0** | 30,000 / 28,000 |
| `AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` | B1–B4 | **719** | 31 (16 + 15) | **16 ok / 0 / 0** | 18,500 / 9,250 |
| `RepTheory/LocalLanglands/WhittakerRecursion.lean` | C1–C3 | **508** | 24 (11 + 13) | **11 ok / 0 / 0** | 10,000 / 5,000 |
| `EisensteinGeneral/ArchIntegralBound.lean` | D1–D4 | **690** | 27 (4 + 23) | **4 ok / 0 / 0** | 12,000 / 6,000 |
| `LanglandsTunnell/RankinSelberg/EulerPolyRecursion.lean` | D5–D6 | **363** | 12 (6 + 6) | **6 ok / 0 / 0** | 25,000 / 12,000 |
| | **15** | **4,126** | **204 (39 + 165)** | **39 ok / 0 / 0** | |

Every module silent at `-DmaxHeartbeats=200000` with **no** in-file `set_option` (the probes above are header
comments, per FR-0225); axioms `[propext, Classical.choice, Quot.sound]` on all fifteen rows; `move_dead` reads
`0 declarations, 0 lines` on all five; `scaffold_audit` reads **complete** on all five; `dedup --within` reads 0
clusters on four and exactly **1** on `EulerPolyRecursion` — the pin's own `OsOde17.main`/row pair, which FR-0221
requires. Builds (under `flock`): A 12 s, B 15 s, C 7.1 s, D1 12 s, D2 4.5 s.

Consumers, each 0 errors / 0 warnings: `spec/AutomorphicFormSetAF84AConsumer.lean` (3 zones, the cover read as
*uniform in the window*), `…BConsumer.lean` (3 zones, the orthogonality row's idempotence and its composition with
the closure row), `spec/UnramifiedWhittakerSetAF84CConsumer.lean` (3 zones, composing the summability and
Euler-factor rows at `y = 0` to get `(rsEulerPoly lam (N*om) lam' (N*om') 0).eval 0 = 1`),
`spec/EisensteinGeneralSetAF84DConsumer.lean` (3 zones, the character removed at `ξ = 0` and the arch bound past
the unit annulus).

### The gate numbers, corrected by the workers

Three of the four orders pushed back on a number in their work order, and all three were right:

1. **A's `3 ok` is unreachable** and my order contradicted itself ("target 3 ok" and "do not declare the pin's
   `_impl` twice"). `check_port` emits **one `ok` per port declaration**, so the line is `2 ok`, with the pin's
   third public (`centreCutSiegelSet_coversModCentre_rat_impl`, statement-identical to the row) credited to the
   row's name and reported by the audit as `RENAMED?`. FR-0226 is extended with this: a target `N` must be the
   number of *port* declarations the wire folds onto, not the wire's public count.
2. **C's `26 ok` was a miscount** (FR-0226): the wire has 23 publics, the structural maximum is 11.
3. **D's `4 ok` for D2's step 1 was right but its shape was wrong** — the four Rankin–Selberg engines are public
   *and* the row's `solution` folds, so `6 ok` is the target; the worker read the audit, not the number.

The general form, now house rule: **`check_port`'s count is a size statement and `scaffold_audit: complete` is the
acceptance test.** A missing declaration is invisible to the checker (it iterates the module's declarations), so a
step-1 order is accepted on the audit and reported on the checker.

### What the workers' diagnoses overrode in this brief

- **A** added two imports the scaffold's closure lacked — `NumberTheory/AdelicLevel/StrongApproxRat` (the `K = ℚ`
  row's premise) and `Mathlib.RingTheory.Complex` — and recorded that the brief's "its two premises are imported"
  covered only the headline's premises.
- **B** found the scaffold header wrong in four small ways (the two `CuspidalSpectrum` pins carry 10 + 2 public
  *engines*, not 2 + 10; their section variable is `{F}`, not `(F)`; only two of the `Ws48Perp` lemmas are the
  general Hilbert-space section, the rest are on the cusp subcarrier; and the pin's 30 private constituent
  declarations fold to **15** because the two files' 14-declaration engine is identical text). It also reused the
  port's public `AutomorphicForm.eq_of_glArch_eq_of_glFin_eq` for the pins' private `…_eq_of_glArch_eq_of_glFin_eq'`
  rather than restating it — the right call (a more general public copy already at the pin's name).
- **D** found that the Glue pin's "7 private declarations" are 5 theorems plus **2 `private scoped instance`s**,
  reactivated in the pin by three `p2m_reactivate` calls the port lacks. It ported them as private theorems
  introduced at their use sites with class-typed `have` (FR-0223) after probing both ways — and recorded a
  gate-interaction worth keeping: a first cut using `local instance` made **`move_dead` report 2 dead
  declarations**, because the tool does not count a local-instance body as a reference; the `have` form is what
  keeps gate 5 at 0/0. It also noted that the Piece pin's 6 private engines include a `def` (`pc_diag`), so the
  count is 5 theorems + 1 def.
- **C** recorded the four declarations it dropped as dead *in the pin* (with pin lines) and kept the pin's scoped
  `simp` lemmas private, which is why its surface is 11 rather than 14.

### The set's numbers

| figure | before | **after** (measured) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 563 / 256,474 | **548 / 251,878** | 548 / 251,878 ✓ exact |
| ready rows | 18 / 5,347 | **22 / 6,398** | 22 / 6,398 ✓ exact |
| leaves | 128 / 31,935 | **118 / 30,021** | 118 / 30,021 ✓ exact |

The nine readied rows are the forecast's nine, and the block's silo total **rose** by 1,051 while its membership
turned over — five rows left (2,682 silo, this set's ready-block cut) and nine entered (3,733 silo). The next cut
is the one this set readied: the two `EisensteinGeneral.Arch` K-types (1,004 + 790, order D's return) and the two
`UnramifiedWhittaker` rows (646 + 618, order C's) — 3,058 silo in two subjects, two orders, and every one of the
four is a leaf with a ported `Def_` layer.
