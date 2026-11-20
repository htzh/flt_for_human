# SET-AF97 — the lift's cuspidal realization, and the additive-character shelf beneath it

**Status: IN FLIGHT (2026-11-20).** Seven orders, eleven modules, **19 rows / 3,761 silo**, priced at
**1,792 net new math lines**. This is the first set cut on the *headline-scaffold* convention: a
module is scaffolded with its headline statement(s) only, and the pin's development is the order's
transcription.

| # | order | rows | silo | modules |
|---|---|---|---:|---|
| A | the lift is a nonzero cuspidal function of the primitive form's level | 2 | 2,099 | `LanglandsTunnell/WeightOneLiftCuspidalRealization.lean` (new) |
| B | the shell measure and the Rankin–Selberg quotient integrand | 1 + def layer | 362 | `AutomorphicForm/Adelic/RankinSelbergQuotientIntegral.lean` (new, 46 pin lines), `…/ShellMeasureIntegral.lean` (new) |
| C | the standard additive character | 4 | 202 | `NumberTheory/StandardAddChar/GlobalAndInfinite.lean` (new) |
| D | the additive character's level and Fourier support | 3 | 231 | `LanglandsTunnell/TateLocal/AddCharLevel.lean` (new) |
| E | three AF leaves | 3 | 168 | `AutomorphicForm/Adelic/LocalIntegralSet.lean`, `…/BruhatRepresentative.lean`, `…/CuspidalSpace.lean` (new) |
| F | level-one forms and cusp-form multiplication | 5 | 529 | `ModularForms/LevelOneSlash.lean`, `…/CuspFormMul.lean` (new) |
| G | the Haar quotient's density | 1 | 170 | `MeasureTheory/HaarQuotientDensity.lean` (new) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af97_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | 437 / 210,582 |
| ready rows | 13 / 4,538 |
| leaves | 68 / 20,311 |
| withheld (FR-0044 guard) | 4 / 831 |

The AF subject's ready block is the three rows the SET-AF96 landing created: the two lift rows
(**1,096** and **1,003**, nine premises each) and the shell-measure row (**362**). This set cuts all
three plus the AF-subject leaves that flank them. The rest of the ready shelf is the other columns
(`WeierstrassCurve` 1,296, `GaloisRep` 495, `ModularCurve`, `AlgebraicCurve`, `NumberField`).

## 1. The headline-scaffold convention (new this set)

SET-AF96 scaffolded every declaration of every pin (statements verbatim, `sorry` bodies) and then
had agents fill the bodies. That worked — 158 declarations read `ok` before a line of proof was
written — but it spends the manager's attention on transcription that the agent will do anyway, and
its value is concentrated in two things only: **the headline statements** (the interface, and the
statement-fidelity gate) and the **public API of a `Definitions/` module**.

So a SET-AF97 scaffold is: header prose + `spec-pin:` wires + a narrow import list + the headline
theorem(s) at the pin's own `solution` statement, renamed to the published name. Nothing else. The
check is still exact: `check_port` reads **24 ok / 0 mismatch / 0 missing / 0 own** across the eleven
modules before any order starts, so every headline is the pin's byte-for-byte, and `scaffold_audit` is
what turns `complete` when the order has transcribed the rest. The cost per module is ~25 lines
instead of ~200–700.

Two consequences the orders carry: a `MISSING` row now means an invented helper (keep it `private` or
report it), and `scaffold_audit` `incomplete` is the *order's* to-do list, not a scaffold defect.

## 2. The stories

* **A is one development with two headlines.** `port_advise` prices the two 76-declaration pins as
  **71 shared declarations** (915 once-lines), of which **646 lines are already in the port** — 89
  declarations importable, mostly from `LanglandsTunnell/WeightOneLiftAdelic.lean` (the AF93 prelude).
  Writing it twice would be the set's biggest waste; the order imports and writes the shared block
  once. Both rows have nine premises: this is the risk order and it has its own wall time.
* **B is the definition gate the shell-measure row needs** (`Def_AutomorphicForm_RankinSelbergQuotientIntegral`,
  46 lines / 4 declarations), and it is the one module of the set that is fully scaffolded, because its
  whole public surface *is* its API.
* **C and D are the additive-character shelf** the Tate column reads: the global character and its two
  infinite places in C, and in D the level `addCharLevel` both ways (fan-in 116 and 100) plus the
  Fourier transform of an indicator. These are the high-leverage leaves §1 of the scoping note
  describes: 45 and 37 silo carrying project fan-in that no 500-line node here has.
* **F is a story, not five names**: level-one forms as a source (restriction, the finite-slash-cover
  sum, the integral `E₄`/`Δ` q-expansion, the `E₄³/Δ` basis) with the cusp-form multiplication row that
  reads the same analytic-order dictionary. None of the five pins imports a `Definitions/` module.
* **E and G are the leaves**: three AF rows of 78/65/14+11 silo and the Haar quotient's density (170,
  fan-in 39). G's report also asks whether its pin duplicates the already-ported
  `MeasureTheory/HaarQuotient.lean` — a hand-over question for the manager, not a re-derivation.

## 3. The pricing

`port_advise` over the nineteen rows: **115 declarations / ≈1,341 lines already in the port** (115
byte-identical, 89 of them public and importable). `port_plan`:

| figure | lines |
|---|---:|
| raw `S_` lines (47-node slice) | 3,761 |
| declaration lines | 3,399 |
| duplicate copies (removable by porting once) | 943 |
| boilerplate | 362 |
| once-cost after dedup | 2,456 |
| already in the port | 664 |
| **net new math lines** | **1,792** |

## 4. The gates

As SET-AF96 §4, with the three build lessons of that set now written into every order:

1. `check_port --force` → 0 mismatch / 0 missing / 0 own, **every** declaration `ok` (the headlines
   already are; each added declaration must be too).
2. `scaffold_audit` → `complete` (the order's completeness gate).
3. The module's own `lake env lean -DautoImplicit=false` → no output at all; one locked `lake build`.
4. `#print axioms` → `[propext, Classical.choice, Quot.sound]`.
5. `dedup --within` → 0 clusters, or the pin's own pairs with the reason.
6. `move_dead --dry-run` → 0 / 0, or the documented escape clause.
7. A heartbeat probe pair in the header, never installed.

**No bare `import Mathlib`** (FR-0254: 6.1 GB closure vs 7 GB RAM, ≈100 s per run, transitive).
**Narrow before the first build**: a `timeout`-killed `lake build` deletes the target's olean and
blocks every importer (FR-0256), and `flock /tmp/…` is inert in this harness. **Body deprecations**
surface once the monolith is gone (FR-0255: `zero_le'` → `zero_le`, `if_pos`/`if_neg`,
`haveI`/`letI`).

## 5. The landing

| order | module | lines | decls | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `LanglandsTunnell/WeightOneLiftCuspidalRealization.lean` | **728** | 30 (5 public / 25 private) | **5 ok / 0 / 0** | clean (30 swept) | 0 | 0 / 0 | 10,000 / 5,000 |
| B | `AutomorphicForm/Adelic/RankinSelbergQuotientIntegral.lean` | **119** | 4 | **4 ok / 0 / 0** | clean | 0 | 0 / 0 | 1,000 / 500 |
| B | `AutomorphicForm/Adelic/ShellMeasureIntegral.lean` | **499** | 21 (16 / 5) | **16 ok / 0 / 0** | clean (16) | 0 | 0 / 0 | 12,500 / 6,250 |
| C | `NumberTheory/StandardAddChar/GlobalAndInfinite.lean` | **272** | 11 (7 / 4) | **7 ok / 0 / 0** | clean (7) | 0 | 0 / 0 | 3,000 / 1,500 |
| D | `LanglandsTunnell/TateLocal/AddCharLevel.lean` | **312** | 5 (3 / 2) | **3 ok / 0 / 0** | clean (5) | 0 | 0 / 0 | 8,000 / 6,000 |
| E | `AutomorphicForm/Adelic/LocalIntegralSet.lean` | **132** | 8 | **8 ok / 0 / 0** | clean (8) | 0 | 0 / 0 | 2,000 / 1,000 |
| E | `AutomorphicForm/Adelic/BruhatRepresentative.lean` | **106** | 3 | **3 ok / 0 / 0** | clean (3) | 0 | 0 / 0 | 4,000 / 2,000 |
| E | `AutomorphicForm/Adelic/CuspidalSpace.lean` | **78** | 2 | **2 ok / 0 / 0** | clean (2) | 0 | 0 / 0 | 500 / 250 |
| F | `ModularForms/LevelOneSlash.lean` | **379** | 19 | **19 ok / 0 / 0** | clean (19) | 0 | 0 / 0 | 8,000 / 4,000 |
| F | `ModularForms/CuspFormMul.lean` | **256** | 7 | **7 ok / 0 / 0** | clean (7) | 0 | 0 / 0 | 8,000 / 4,000 |
| G | `MeasureTheory/HaarQuotientDensity.lean` | **251** | 12 | **12 ok / 0 / 0** | clean (12) | 0 | 0 / 0 | 5,000 / 4,000 |

**3,132 lines, 0 `sorry`, 20 rows on the wire, 86 declarations checked `ok`.** The manager re-read
`check_port` over all eleven modules (**86 ok / 0 mismatch / 0 missing / 0 own**), `scaffold_audit`
(`complete` on all eleven), the silence gate on all eleven, and `#print axioms` on all twenty rows
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) independently of the orders' reports.

**A found that the two 1,000-line pins are one development** — 75 of 76 declarations byte-identical, so
the engine is written once: 30 declarations, 46 of the pins' 71 private declarations imported from the
AF93 prelude (`LanglandsTunnell.{RatArch,DetIntegral,ArchLift}`, `WeightOneLiftLevel`) and 25
transcribed.

**The set's payoff is a `spec/` consumer zone**, `spec/WeightOneLiftConductorConsumer.lean`: the lift's
newvector conductor at `q` **is** `N.factorization q`, unconditionally. It composes SET-AF97's A
(nonvanishing plus level invariance) with SET-AF96's C and D (the span rows and the factorization
bound), which had to *assume* those two facts; the hypotheses are now discharged and the composition
is axiom-clean.

**Six instrument findings, in [frictions.md](../../logs/frictions.md).** Two are structural and cost
the set real time: FR-0259 (two modules must not declare the same public *full* name — the port hit it
twice, on `IsCuspidalFn.add/smul` and on `slash_eq`, and no gate can see it; a consumer zone has to be
the detector), and FR-0261 (`WeightOneLiftLevel.lean` declares nine `DihedralWeightOne.ratArch*` names
that shadow the opened AF93 prelude, so a body silently proves the wrong law). Three are build/matcher
classes: FR-0260 (a `rw` list ending in a big term can burn the whole heartbeat budget; `rw` + `exact`
elaborates the module in 5.7 s), FR-0262 (`linter.style.haveILetI`'s `have` cure is *wrong* for an
inlined instance, so that one declaration-scoped `set_option` stays, with the reason), FR-0263
(`port_advise` mis-reports home namespaces past an `open … in`), and FR-0257 (the `AdeleRing`/
`InfiniteAdeleRing` `def`-transparency drift, met four ways in this set).

**Two dedup hand-overs, recorded in [CARRY-FORWARD.md](../../CARRY-FORWARD.md):** `IsCuspidalFn.add`/
`.smul` were landed twice (resolved in this session — `CuspidalSpace.lean` owns them,
`ProductionPinsTail.lean` lost the block and its two wires); and the Haar quotient density exists
three or four times over (G measured 33 clusters / 405 removable lines across the four Haar modules).
Also routed: `SPart.continuous_diagOne` is public here and byte-identically `private` in
`BorelHaarDisintegration.lean`, whose promotion is a shared-home decision.

## 6. Not cut — named and deferred (FR-0040)

* Ready rows of the other columns: `WeierstrassCurve.natCard_torsionOrbit_…` (697),
  `WeierstrassCurve.exists_isGalois_goodModel_…` (599),
  `GaloisRep.exists_isSemisimpleRepresentation_…` (495),
  `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` (108),
  `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` (59), and the three
  `ModularCurve` rows (36 + 34 + 24).
* Withheld by the FR-0044 guard: `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327),
  `…moduleFinite_padicInt_tateModule_jOne` (283),
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126),
  `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95). The pruned subject's work.
* `AutomorphicForm.IsCuspidalFn.add` / `.smul` were **cut** by order E and are on the wire; they no
  longer appear in §6 because the shelf now credits them (FR-0264).
* AF-subject leaves left for the next set: `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt`
  (69, fan-in 41), `ValuationSubring.*` (37 + 83 + 174 + 262 + 269, the ramification column),
  `MeasureTheory.*` (the analytic leaves: 99, 98, 98, 90, 84, 63, 26), `NumberField.mixedEmbedding.*`
  (237, 71, 67, 17), `TateCurve.*` (471, 247, 157, 69, 22, 19, 19, 17, 17), `WeierstrassCurve.*` (16
  rows) and `M4aTorus.completedRayL_fe` (12,126 — the one node that is bigger than this whole set).

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af97_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 437 / 210,582 | **417 / 206,821** |
| ready rows | 13 / 4,538 | **27 / 12,612** |
| leaves | 68 / 20,311 | **53 / 19,036** |
| withheld | 4 / 831 | 4 / 831 |

The eighteen rows the shelf carried left it, and **fifteen rows became ready** (11,801 silo of ready
work against 4,538 before): the AF97 set opened the whole Rankin–Selberg and Whittaker block of the
`AutomorphicForm` column — `exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String`
(1,827), `RankinSelberg.exists_finset_norm_whittakerCoefficient_sq_mul_norm_section_le_shell_indicator_of_shell_surgery_of_section_law`
(1,418), `RankinSelberg.lintegral_sPart_quotientIntegrand_eq_mul_lintegral_torus_and_sPartIntegral_eq`
(818), the three `whittakerCoefficient_*` rows (681, 573, 306), the fundamental-domain row (621) — plus
`ModularForm.exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic` (464),
`…isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic` (452),
`ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem` (175),
`ModularCurve.StarBank.hassePolyDescent` (407) and `ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_…`
(233), `EisensteinGeneral.LocalUnr.integral_twisted_eq` (601), `LanglandsTunnell.TateLocal.psiLocal_ne_one`
(74) — which is the next set's story twice over.

**The two false-ready rows are gone (FR-0264).** `AutomorphicForm.IsCuspidalFn.add` and `.smul`
(14 + 11) read as needed on every read from SET-AF95 through this set's first landing read, although
the port has held both since AF95 with the pin wired and the checker reading them `ok`. The
front-end, not the port, was wrong: the name scan drops a last name shorter than six characters with
no underscore or capital (`add`, `smul` — the guard that keeps `HahnSeries.HasRamBound.add` from
reading as ported), and the sources reading mapped only `Thm_` sources, so a wire that names an `S_`
file — which is the port's own protocol — contributed nothing. `frontier.py` now credits the nodes of the pin sources a tracked module's header wires —
**file level, never statements** (FR-0265): the shelf counts node files, `check_port` owns statement
fidelity, and a refactor that moves, renames or drops a declaration cannot put a node back on the
shelf. The figures above are the post-fix read; the pre-fix landing read was 419 / 206,846 with 28
ready rows. The credit admits five over-broad wires as well (`…ncard_fibSet`,
`ModularCurve.isInftySide_cuspInftyBar`, `…JOne.degeneracyPullbackInputs`,
`…FullLevel.laurentBaseChange_gamma0_le_fieldBar`,
`AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends`) — all of them outside the D–S
demand, so `needed` is the same either way, and `--selfcheck` prints them.
