# SET-AF100 — the torus trichotomy, the unipotent surgery, and the Haar dictionary

**Status: LANDED (2026-11-22).** The next ready set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. Six orders, fifteen rows, **4,607 silo**, three new modules and seven insertions.
This set **empties the AF-subject half of the ready shelf**: after it the only ready rows left are the
other columns' (`ModularCurve` 854 + 550 + 532 + 407 + 318 + 246 + 233 + 36 + 34 + 24,
`ModularForm` 951, `WeierstrassCurve` 697 + 599, `GaloisRep` 495, `AlgebraicCurve` 59,
`NumberField.Idele` 108 — cut here) and the `leaves` block, which it does not touch.

| # | order | rows | silo | modules |
|---|---|---|---:|---|
| A | the per-place Casimir-trichotomy decay of the `diagOne` coefficient (11 premises) | 2 | 1,909 | `AutomorphicForm/Adelic/WhittakerTorusDecay.lean` (new) |
| B | the unipotent surgery of the coefficient | 2 | 740 | `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` (insertion) |
| C | the archimedean atom: Möbius shift against the atom integral | 2 | 381 | `AutomorphicForm/Adelic/WeylIntegrable/ShiftConvergenceArch.lean` (new) |
| D | the constituent spine and the carrier's continuity | 2 | 538 | `Cusp/IrreducibleSpine.lean`, `Cusp/SpectrumTranslation.lean` (insertions) |
| E | the analyticity of the `S`-part integral, and the analytic floor leaf | 3 | 431 | `AutomorphicForm/Adelic/RankinSelbergAnalytic.lean` (new), `MeasureTheory/ParametricIntegral.lean` (insertion) |
| F | four Haar/integral dictionary rows | 4 | 608 | `AutomorphicForm/Adelic/BorelHaarDisintegration.lean`, `…/AdelicTraceTail.lean`, `MeasureTheory/HaarQuotient.lean`, `Cusp/SpectrumIntegration.lean` (insertions) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af100_read.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | 385 / 194,218 |
| ready rows | 30 / 10,642 |
| leaves | 44 / 18,163 |
| withheld (FR-0044 guard) | 4 / 831 |

These are SET-AF99's landing read reproduced exactly, so nothing has been ported since. The
`--selfcheck` correction set is the same as AF98's read (five over-broad wires outside the D–S
demand); no `--unport` is applied, so the corrected and uncorrected reads agree on this shelf.

## 1. The stories

* **A is the quantitative decay half of the `diagOne` dictionary.** Two 934/975-line pins that are
  the *same development twice*: `port_plan` reports **577 duplicate lines** (the 395-line
  `dpure_fn` engine, `central_iterate`, the `archIdele`/`archComp` dictionary, the two product
  lemmas), which the port writes **once**. The two headlines differ in the complex-place hypothesis:
  the plain copy assumes `h1` (any two complex places coincide), the `_of_finite_span` copy assumes
  `hcu` (the coefficient is a finite combination of fixed profiles). Both are the pin's public API
  and both are transcribed. **28 declarations / 19 public each** at the pin's names, `dpure_fn`
  written once.
* **B is the unipotent surgery**, and its pins are **1 public + 19/21 private** (so `check_port`
  diffs the headline and the engine gate is the `statement_db` diff, FR-0277). The two headlines
  differ only in the last conjunct's indicator (a level-`m` box versus a prescribed vector `a`).
  `port_plan` reports 182 duplicate lines. Its home **is** the module holding its premise
  `exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow` — the shell indicator of SET-AF98 C.
* **C is the archimedean atom** (`AutomorphicForm.LocalIntertwining`'s real- and complex-place
  rows): the atom integral is bounded on `1/2 < σ ≤ 1` and the Möbius-shifted integral converges to
  it. The two pins are *not* duplicates (287 differing lines) — the complex case is a
  two-dimensional `ℂ` integral with the `z^a₀ (star z)^b₀` weight, the real one a `ℝ` integral.
  Both are **all-public** flattened files (15 + 13), and their home is the `WeylIntegrable` theory
  that already holds the adic sibling `…_weylShift_sub_integral_smoothAtom_adicCompletion`.
* **D is the constituent spine**: the sup of a finite family of cusp subreps commutes with the
  level-invariant and archimedean cuts (D1, all-public, 22 declarations), and the carrier map
  `toCarrier` is continuous under right translation (D2, 5 public). D2's home is the module whose
  headline `exists_isLift_rightTranslate` is its premise; D1's is the irreducibility spine, which is
  the same statement family one cut down.
* **E is the `S`-part integral's analyticity** — the row SET-AF99's §9 named as the consumer of its
  own orders A and G: the Petersson integral of `x·G(s,·)·ȳ·‖det‖^{-w}` is holomorphic in `s` under
  a growth-and-decay hypothesis, and vanishes to the order of `G`. Its two pins differ by 31 lines
  (the centre-cut Siegel set versus the integral windowed set). The third row is the general
  analytic-floor leaf `analyticOnNhd_integral_and_im_eq_zero_and_re_pos_…`, homed in
  `MeasureTheory/ParametricIntegral.lean`, whose two rows it consumes.
* **F is four small dictionary rows of one subject each**, all insertions: the Iwasawa
  disintegration of `adelicGLHaar` (252, project fan-in **16**) beside the Borel disintegration it
  generalises; the *constant* idèle-norm band measure (108, fan-in 13) beside the finite-measure
  slice it sharpens; the Haar-quotient `tsum`-over-`ℤ` identity (170) in `HaarQuotient`; and the
  compact-open double-coset average (78) in the averaging module.

## 2. The scaffolds

As SET-AF98/99: each new module exists before any order starts, with its header prose, its
`spec-pin:` wires, a **narrow** import list and the **headline(s)** only, at the pin's own `solution`
statement (so `check_port` matches it on the content tier) and at the published name, body `sorry`.
The insertion orders add their headline(s) to the existing module and one wire line each.

No `import Mathlib` — four of these pins list it wholesale and one is `Mathlib`-only (C). The
narrow list is part of the order's work (SET-AF99 order G's recipe).

The scaffolds, measured before any order starts (`check_port --force`, then `lake build` of all
eleven modules: 4,411 jobs, `sorry`-only warnings, and the set-level import probe silent):

| module | scaffold `check_port` | declaration inventory |
|---|---:|---|
| `WhittakerTorusDecay.lean` (new) | 2 ok | 17 shared engine + 2 `main` + the 2 headlines |
| `RankinSelbergShellIndicator.lean` (+2 headlines) | 41 ok | 17 private engine rows (13 shared) |
| `ShiftConvergenceArch.lean` (new) | 2 ok | 13 (real) + 15 (complex), all public |
| `Cusp/IrreducibleSpine.lean` (+1) | 22 ok | 21 public engine |
| `Cusp/SpectrumTranslation.lean` (+1) | 4 ok | 4 public engine |
| `RankinSelbergAnalytic.lean` (new) | 2 ok | 2 shared + 2 + the 2 headlines |
| `MeasureTheory/ParametricIntegral.lean` (+1) | 5 ok | — (the leaf is one declaration) |
| `BorelHaarDisintegration.lean` (+1) | 2 ok | 14 public engine + 3 anon instances |
| `AdelicTraceTail.lean` (+1) | 3 ok | 1 private engine |
| `HaarQuotient.lean` (+1) | 7 ok | 15 public engine |
| `Cusp/SpectrumIntegration.lean` (+1) | 6 ok | — (the headline is the whole pin) |

Two wire findings at scaffold time: four rows' `S_` files state their headline with **fully
qualified** names (`NumberField_AdelicHaar_…`), so the content tier cannot match the port's
short-spelled statement — the fix is the `Theorems/Thm_…` wrapper line in the header (F1 needed
it), which is the playbook's "list the copy whose statement text the port transcribes". And two
insertions had to re-open a namespace after the file's `end` (the local `attribute [local instance]`
block is scoped to the namespace, so the new block carries its own).

## 3. The pricing

`port_advise` + `port_plan` per order:

| order | raw `S_` lines | dup copies | boilerplate | in the port | **net new** |
|---|---:|---:|---:|---:|---:|
| A (2 nodes) | 1,909 | 577 | 74 | 115 | **1,143** |
| B (2 nodes) | 740 | 182 | 54 | 5 | **499** |
| C (2 nodes) | 381 | 0 | 28 | 85 | **268** |
| D (2 nodes) | 538 | 13 | 59 | 19 | **447** |
| E (3 nodes) | 431 | 10 | 58 | 0 | **363** |
| F (4 nodes) | 608 | 0 | 99 | 20 | **489** |
| **total** | **4,607** | **782** | **372** | **244** | **3,209** |

The `in the port` column is the reuse the set gets for free (the AF93–AF99 archimedean engine). C
and D were priced separately for this table; their joint run reads 919 raw / 13 dup / 87 boilerplate
/ 104 in-port / 715 net, so the split above is the exact one (268 + 447 = 715).

## 4. The gates

As SET-AF99 §4: `check_port --force` 0 mismatch / 0 missing / 0 own, every declaration `ok`
(and for a mostly-`private` pin, the `statement_db` pin-vs-module diff: B); module silent at
`lake env lean -DautoImplicit=false`; one globally serialized `lake build`; `#print axioms` clean;
`dedup --within` 0 or the pin's own pairs; `move_dead --dry-run` 0 / 0; a heartbeat probe pair in
the header, never installed; the set-level import probe for FR-0274.

## 5. The landing

Every number below was re-measured by the manager on the landed files, not copied from the orders'
reports.

| order | module | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `WhittakerTorusDecay.lean` (new) | **1,351** | **21 ok / 0 / 0** | 19 pin publics per copy, 19/19 hash-shared each side, 17 byte-identical across the copies, 2 `main`s separate, 0 unmatched | clean (21) | 0 | 0 / 0 | 90,000 / 80,000 |
| B | `RankinSelbergShellIndicator.lean` (+587) | **1,995** | **41 ok / 0 / 0** | 40 pin engine rows → 0 unmatched; 23 module rows → 0 invented (17 shared + `units_expansion_finset` + 3 shell rows + 2 `main`s) | clean (41) | 2 (pin's own `main`↔`solution`) | 1 / 3 (pin's own dead `dil_snd_of_ne`) | 8,500 / 8,400 (engine), file pair 70,000 / 65,000 |
| C | `ShiftConvergenceArch.lean` (new) | **432** | **28 ok / 0 / 0** | 28 pin publics / 28 port publics, 26 hash-shared engines + 2 headlines, 0 shared names | clean (28) | 0 | 0 / 0 | 6,000 / 5,000 |
| D | `Cusp/IrreducibleSpine.lean` (+394) | **1,403** | **43 ok / 0 / 0** | 22 pin publics / 43 module publics / 22 matched / 0 hash-differs | clean (43) | 2 (pin's own pairs) | 0 / 0 | 35,000 / 32,000 (floor is a landed row) |
| D | `Cusp/SpectrumTranslation.lean` (+180) | **608** | **8 ok / 0 / 0** | 5 / 8 / 5 matched / 0 | clean (8) | 0 | 0 / 0 | 65,000 / 62,000 (floor is a landed row) |
| E | `RankinSelbergAnalytic.lean` (new) | **431** | **6 ok / 0 / 0** | 8 pin rows ← 6 port publics, 2 hash-shared, 0 unmatched | clean (6) | 0 | 0 / 0 | 25,000 / 12,000 |
| E | `MeasureTheory/ParametricIntegral.lean` (+70) | **341** | **5 ok / 0 / 0** | 1 / 1 | clean (5) | 1 (pin's own pair) | 0 / 0 | 8,000 / 5,000 |
| F | `BorelHaarDisintegration.lean` (+346) | **878** | **16 ok / 0 / 0** | 14 / 14 `IwasawaCoord` engine rows hash-identical; the pin's `S_` `solution` is the wrapper statement in fully qualified names, matched via the `Theorems/` wire | clean (16) | 4 (pin's own pairs) | 14 / 225 (pre-existing `scoped instance` blind spot, 15 / 229 before) | 12,000 / 10,000 |
| F | `AdelicTraceTail.lean` (+102) | **465** | **3 ok / 0 / 0** | 2 / 2 (the `private` helper reused from the module's existing `IdeleNormSlice` copy, same statement hash) | clean (3) | 2 (pin's own, unchanged) | 0 / 0 | 12,500 / 6,250 |
| F | `MeasureTheory/HaarQuotient.lean` (+218) | **1,264** | **22 ok / 0 / 0** | 16 / 16 by hash | clean (22) | 1 (pin's own) | 0 / 0 | 12,000 / 11,000 |
| F | `Cusp/SpectrumIntegration.lean` (+105) | **1,136** | **6 ok / 0 / 0** | 1 / 1 | clean (8) | 0 | 0 / 0 | 120,000 / 100,000 |

**The set-level gates**: the eleven modules' import probe is silent; a locked wave build of the eleven
plus their eleven priced dependents is `Build completed successfully (4987 jobs)`, 0 errors, and **no
warning from any module of this set**; `#print axioms` on all fifteen headlines and on the consumer
zone's theorem is `[propext, Classical.choice, Quot.sound]` with **no `sorryAx`**; `dedup --cross`
over the set reports no new duplication (the clusters that touch these modules are the pin's own
`main`↔`solution` pairs and the `Reserve/` shelves' by-design copies).

The consumer zone is `spec/AutomorphicFormSetAF100Consumer.lean` (151 lines, one zone): order B's
surgery identity at `g' = 1`, multiplied by order A's `∃ δ C` decay bound, giving the surgery's finite
linear combination the torus decay bound. Deleting either module breaks it and its axioms are clean.

## 6. Plan vs actual (the honesty section)

| order | silo (priced) | net new (predicted) | lines landed | ratio |
|---|---:|---:|---:|---:|
| A | 1,909 | 1,143 | 1,351 | 1.18 |
| B | 740 | 499 | 587 | 1.18 |
| C | 381 | 268 | 432 | 1.61 |
| D | 538 | 447 | 574 | 1.28 |
| E | 431 | 363 | 501 | 1.38 |
| F | 608 | 489 | 771 | 1.58 |
| **total** | **4,607** | **3,209** | **4,216** | **1.31** |

1.31 is inside the band this column records (1.0–1.45). The two high ratios are C and F, and both for
the same reason the column has seen before: **all-public flattened pins**. C's two pins are 13 + 15
declarations with no `private` prelude, so every one of the 28 rows carries a full statement and the
port pays the statements it priced only as "declaration lines"; F's four pins are the same shape.
`port_plan`'s budget is a *lower* bound wherever a pin's public surface is all engines.

**Four brief claims were false, and every worker caught its own:**

1. **Order A: "19 ok".** `check_port` counts the module's public declarations, so the two scaffold
   headlines are rows: 21. (Same error in order E, where the answer was 6, not 8, because two rows
   are hash-shared across the pins.) The rule is now stated in §6 of this file.
2. **Order B: "13 shared + 4 shell-specific".** Measured 17 shared + `units_expansion_finset` + 3
   shell rows + 2 `main`s = 23 module rows for 40 pin rows. The brief's split would have left six rows
   untranscribed, including both `main`s.
3. **Order E's scaffold import list** did not reach `TateGlobalContinuousIdeleNorm` (the port's home
   of `continuous_ideleNorm_det`); both headlines fail on `unknown constant` without it.
4. **Order F: "F4 needs nothing but `HaarAveraging`, which is in the module's closure".** Nothing in
   the tree imported `MeasureTheory/HaarAveraging.lean`; three modules needed it added (F1, F3, F4),
   plus `NumberTheory/Adelhaar/MulRightInvariant` for F1's compact-group `IsInvInvariant`.

**Two `set_option`s / renaming decisions came out of the set.** Order A silenced
`linter.unusedVariables` for the pin's own dead hypothesis; the manager refused it and the binder is
`_hb` (the SET-AF99 `_hδ` precedent), so no module of this set carries a `set_option` but
`autoImplicit false`. Order B named the shell copy `main_shell`; the house convention for a pin that
states one last name twice is a namespace split, so it is `UnipotentSurgery.Shell.main`.

**Two checker behaviours were confirmed, not changed**: a pin that states its headline byte-identically
twice (`solution := main`) is credited to the first matching row, leaving the `solution` wire row
unused while the count stays complete; and a `scoped instance` a statement needs stays at the pin's
spelling and name (invisible to `statement_db` on both sides).

**One deliberate non-cut.** Order A declares `unipotentGL2_algebraMap` (8 lines, pin-public) which is
byte-identical to `AutomorphicForm.UFnAux.unipotentGL2_algebraMap` in
`LanglandsTunnell/WhittakerODELinearDependence.lean`. The copies sit in two subject namespaces, one of
them a pipeline label this column must not propagate, the pin states the lemma inside both blocks, and
the saving is 8 lines against an import dependency on a premise module's labelled namespace — recorded
in [CARRY-FORWARD.md](../../CARRY-FORWARD.md) as a refactor-round item rather than taken here.

**What the set leaves behind that is reusable, in order of value:** the two all-public transcription
patterns and their measured ratios (C, F); `tmp/af100/collision-probe.lean` (eleven modules, the only
FR-0274 detector); the engine-diff scripts `diffB.py` / `engine-diff-A.py`; the five frictions this
set produced (FR-0290 … FR-0297); and the wave build's price (4,987 jobs for eleven modules plus
sixteen dependents).

## 8. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af100_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 385 / 194,218 | **370 / 189,611** |
| ready rows | 30 / 10,642 | **24 / 10,139** |
| leaves | 44 / 18,163 | 44 / 18,163 |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is exactly the cut — **−15 nodes / −4,607 lines**, no more and no less, which is the check
that the eleven wires are honest (an over-broad wire shows up as a larger delta). **Nine rows became
ready because of the set** (4,104 silo), and every one of them is a consumer of a landed order:

* `AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery` (1,194) — the
  consumer of orders B and E together, and the next step of the Rankin–Selberg column;
* `AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa`
  (453) — order F1's quotient form;
* `AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_sub_lt` (446),
  `…exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq` (428),
  `…exists_monoidHom_isCuspLift_rightTranslate_and_norm_eq_and_continuous` (294) and
  `…_of_isCompact` (174) — order D2's four consumers;
* `AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le`
  (439) and `…_inf_invariants_inf_archCutSubmodule_le` (415) — order D1's dual rows;
* `HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer` (261)
  — order F3's integrable sibling.

## 7. Not cut — named and deferred (FR-0040)

* **Ready rows of the other columns**, untouched by design: `ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`
  (951), `ModularCurve.isIntegral_adjoin_coeffEmb_jq_inv_…` (854), `WeierstrassCurve.natCard_torsionOrbit_…`
  (697), `WeierstrassCurve.exists_isGalois_goodModel_…` (599), `ModularCurve.isIntegral_adjoin_jqModC_…`
  (550 + 532), `GaloisRep.exists_isSemisimpleRepresentation_…` (495), `ModularCurve.StarBank.hassePolyDescent`
  (407), `ModularCurve.card_quotient_gamma0_le_dedekindPsi` (318), `ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_…`
  (233), `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36),
  `ModularCurve.exists_coeffMap_diffQExp_…` (34), `ModularCurve.rep_tateModule_jOne_comm` (24),
  `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59).
* **The `leaves` block** (44 / 18,163) is not touched: `M4aTorus.completedRayL_fe` (12,126),
  `TateCurve.*` (1,038), `ValuationSubring.*` (825), `WeierstrassCurve.*` (sixteen rows),
  `NumberField.mixedEmbedding.*` (the AF99 §7 definition-layer block, still unported),
  `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (684), and the three small
  `NumberField` leaves (69 + 94 + 98).
* **Withheld by the FR-0044 guard** (the pruned complex-analytic subject's work):
  `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327), `…_jOne` (283),
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126),
  `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95).
