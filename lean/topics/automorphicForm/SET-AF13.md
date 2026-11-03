# SET-AF13 — the Bruhat Eisenstein series in the half-plane: flat sections, heights, and the constant term

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, all four rows, all gates
green; **§5.1 records the landing and the re-read**. The order is
[WORKORDER-AF13-eisenstein-half-plane.md](WORKORDER-AF13-eisenstein-half-plane.md). Read off the D–S
shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF12 left. It is the **thirteenth** `AutomorphicForm`-serving set, and it is the first
**composition** set in six: of its 1,509 declaration lines **562 are already in the port**, so the
work is **947 lines in 56 declarations** — the `WeylIntegrable` engine SET-AF6/AF7 built, finally
consumed.

The set is **4 rows / 1,637 silo / 959 net** (`port_plan`), one order, one new module.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| the flat Eisenstein series in the half-plane | 4 | 1,637 | 947 | new `AutomorphicForm/Adelic/BruhatEisenstein.lean` |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af12-landed.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF12 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **865 / 351,925** | 865 / 351,925 |
| `needed [literal]` | 878 / 355,400 | 878 / 355,400 |
| frontier F | **1,550 / 775,441** | 1,550 / 775,441 |
| ready rows, all namespaces | 66 / 17,896 | 66 / 17,896 |
| ready rows, `AutomorphicForm` | **37 / 12,552** | 37 / 12,552 |
| leaves, all namespaces | 232 / 58,795 | 232 / 58,795 |
| leaves, `AutomorphicForm` | **63 / 12,756** | 63 / 12,756 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,369 `Thm_` sources, 1,550 declared names) | PASS |
| correction | **none needed** | none needed |

This is SET-AF12's landing read (same tree). Both blocks are quoted whole and every row accounted
for in Appendix A: 37 ready / 12,552 and 63 leaves / 12,756, of which 4 are this set's and 96
deferred (§7 groups them; the rest are one-line `deferred`). The withheld block is unchanged (two
`ModularCurve` Tate-module rows, two `AlgebraicCurve` Pic₀ rows, 831 lines).

### 0.2 Why the flat Eisenstein series, and not the three larger cuts

The three alternatives, priced on this shelf:

- **the Weyl-integrand pair**, `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349) and `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291) — **2,640 silo**, the largest ready subject on the shelf, and a transcription set (its only
  in-port lines are the shared integrability lemma; price it with `port_plan` before cutting). It is
  the next set after this one, not this one: at 2,640 it is two dispatches, and it wants its own read
  (`Def_LanglandsTunnell_TateLocalZeta` enters its closure).
- **the flat-section indicator row**, `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow`
  (1,043, 3 premises, 1/3) — the single largest ready row, one subject (the height of the bottom-row
  indicator section). It shares this set's subject but not its engine: taking it now would double the
  set's size and dilute the story. It is §7's first candidate, with the two rows that follow it.
- **the `diagOne` family** (`whittakerCoefficient_diagOne_satisfies_whittaker_ode_…` 306 and its
  four consumers, 394/464/934) — the natural sequel to SET-AF12, but **every row of it needs an
  unported premise outside this column**: `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`,
  `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar`, and the
  `LanglandsTunnell` `moderateGrowth`/`rpow_bound` rows. It cannot be cut until those land.

The flat-Eisenstein block is the cut for three reasons.

- **It is one story, four faces, all ready.** The flat section `φ` (an induced section with `etaFst`/
  `etaSnd` at `s`), the *flat Eisenstein series* `E (s) g = φ s g + ∑' ξ, φ s (w n(ξ) g)` it generates,
  and three facts about `E` in the half-plane `re s > 1/2`: it is holomorphic there
  (`bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family`, 624), it is bounded by a power of
  the archimedean height on the centre-cut Siegel set
  (`exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet`, 431), and its constant
  term is the section plus the Weyl-intertwining integral
  (`constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral`, 257) — the Rankin–Selberg
  ingredient this column has been building towards. The fourth row,
  `exists_flat_isInducedSection_family_eq_of_isInducedSection` (325), is the dictionary the other three
  quantify over: a family of sections is (the `s`-dependence of) a family of induced sections.
- **It is a composition set, and the engine is AF6/AF7's.** 519 of the 1,510 declaration lines are
  already in the port (100 tier-1, i.e. statement-checked; 419 tier-3, i.e. the `WeylIntegrable/*`
  engine's registered surface), and 32 more are duplicate copies the plan removes. The work is 947
  lines, so this is the first set in six to *use* the Weyl-integrand engine rather than extend it.
- **It carries the largest outbound demand left on the ready shelf.** The pin files that cite the four
  rows number **5, 5, 15 and 20** — 45 in all, and the two heavy ones are the dictionary (15) and the
  constant term (20). That is where the set's return is, and it is a return of *premises*, not of rows
  (§0.4 and the forecast).

### 0.3 Why this is a composition set, and what it costs

`port_plan`: raw **1,637** → declaration lines **1,510** → −32 duplicate copies → 1,478 once-cost →
**−519 already in the port** → **NET NEW 959**; boilerplate 127. The worklist (Appendix B) counts
**1,509 declaration lines, 562 imported, 947 to write in 56 declarations**. The distribution is
uneven and worth stating:

- the **differentiability** row is 592 declaration lines of which **432 import** — it is mostly a
  reuse of the port's `etaFst`/`etaSnd`/`adelicWeyl` API, with 160 lines of new work in 5 declarations;
- the **height bound** is the set's real cost: 404 declaration lines, only 24 imported, **380 to write
  in 25 declarations** (a local/ultrametric height calculus over `K = F_v`);
- the **dictionary** is 298 / 102 imported / **196 in 18**;
- the **constant term** is 215 / 4 imported / **211 in 8**.

### 0.4 The four rows' outbound demand, and the shape of the return

| row | pin files citing it |
|---|---:|
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 5 |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 5 |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | **15** |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | **20** |

The 15- and 20-file rows are the reason to take this block rather than the two big single subjects:
they are premises of the Rankin–Selberg and Bruhat-transversal developments, so landing them moves a
*cluster* closer rather than one row. Whether any of the 45 files' rows actually becomes ready is the
re-read's question (§C); several of them also cite the indicator row (1,043) that this set defers.

## 1. The four rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | **160** | 5 | 3 | 2/5 | for a family `φ` of induced sections depending holomorphically on `s`, the flat Eisenstein series `s ↦ φ s g + ∑' ξ, φ s (w n(ξ) g)` is holomorphic on `{re s > 1/2}`, at every `g` |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | **380** | 25 | 3 | 1/5 | a bound `‖E (s) g‖ ≤ C · archHeight g ^ k` on the centre-cut Siegel set, uniform in `s` in a strip, from the summand estimate |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | **196** | 18 | 2 | 4/15 | a family of sections is (the restriction of) a family of induced sections: the dictionary between `IsInducedSection` and the flat family, with the `finLocalHeight`/`InK` invariance |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | **211** | 8 | 1 | 3/20 | `constantTerm (φ + ∑' ξ φ (w n(ξ) ·)) g = φ g + (vol (adelicBox))⁻¹ · weylIntertwiningIntegral φ g` — the constant term of the flat Eisenstein series is the section plus the Weyl integral |

The four are independent rows (none cites another), so the worker may take them in any order; the
constant-term row is the one to do last, because it is the one whose statement must be read by eye
(§6.1).

**Helper visibility follows the pin's, not the set's convenience.** These four `S_` files are *not*
uniformly flat public: their preludes contain `private theorem`s — in the first one alone
`exists_bound_on_unitBox_family_j1`, `hpow`, `finLocalHeight_one'` — so a helper the pin states
`private` stays `private` here, and only the pin-public ones sit in the four subject namespaces.
Making a pin-private helper public is not free: its statement is spelled with the pin file's `section`
variables (`variable {A : Type*} [CommRing A]`, …), and inlining them into the declaration is a
`MISMATCH` on the checker's text diff (FR-0123) that no re-spelling fixes. `private` is the faithful
answer, and it is also the cheap one.

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family \
  --nodes AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet \
  --nodes AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection \
  --nodes AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral \
  --json build/af13-advise.json
python3 port_plan.py --json build/af13-advise.json    # 1,637 raw / 1,510 decl / 519 in port / 959 net
python3 build/af-worklist.py bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family \
  exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet \
  exists_flat_isInducedSection_family_eq_of_isInducedSection \
  constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
```

**The substitution block is this set's whole economy: 69 substitutions, 519 lines saved.** Sixty-six
are byte-identical and public; two more are public but binder-spelled; the remaining two are the ones
to read:

| pin declaration | pin line | claimed port copy | reading |
|---|---|---|---|
| `norm_finComponent_le_one_of_mem` (13) | `S_…flat_isInducedSection…:102` | `BigCellExpansion.Height.norm_finComponent_le_one_of_mem` | the advise row found the **`private` twin**; there is a **public** copy of the same statement at `NumberField/AdelicHeight.lean:442` (`NumberField.AdelicHeight.norm_finComponent_le_one_of_mem`), so this one is **imported**, not re-stated. (Read the advise row's `port` module, not only its `port_name` — FR-0128.) |
| `finLocalHeight_one'` (8) | `S_…flat_isInducedSection…:125` | `FlatInducedSection.finLocalHeight_one` | public, same statement, binder-spelled with a prime: **imported as-is**. |
| `hpow` (2) | `S_…flat_isInducedSection…:166` | `FlatInducedSection.flatOne` | **a shift, not a rename**: the pin's `hpow t g = (archHeight g) ^ t`, the port's `flatOne s g = (archHeight g) ^ (s + 1/2)`, so `hpow t = flatOne (t - 1/2)`. The two companions `hpow_mul_inK`/`hpow_of_inK` have `flatOne` twins in `InducedSectionFlat`; use them with the shift, or write the two-line `hpow`. Record which. |
| (the other 65) | — | — | byte-identical, public; imported. |

**No port-once block and no siblings block**: the four target files share no declaration and neither
generalises the other — they share the *engine*, which is what the substitution block already is.

**The per-declaration worklist** is Appendix B: 1,509 declaration lines, 562 imported, **947 to write
in 56 declarations**.

## 3. The definition gate

`spec/gate_scan.py` over the eight `Def_` modules of the four wrappers' closure, all four rows
(`--rows` takes a list), reports **0 missing in every module**:

| pin `Def_` module | port home | used (max) | missing |
|---|---|---|---:|
| `Def_AutomorphicForm_InducedSection` | `…/Adelic/InducedSection.lean` | 1/10 | **0** |
| `Def_AutomorphicForm_EtaFamily` | `…/Adelic/EtaFamily.lean` | 3/15 | **0** |
| `Def_AutomorphicForm_WeylIntertwining` | `…/Adelic/WeylIntertwining.lean` | 3/7 | **0** |
| `Def_NumberField_AdelicHaar` | `…/NumberTheory/AdelicHaar/Adele.lean` | 3/25 | **0** |
| `Def_NumberField_AdelicHeight` | `…/NumberTheory/AdelicHeight.lean` | 4/27 | **0** |
| `Def_NumberField_AdelicBox` | `…/NumberTheory/AdelicBox.lean` | 3/36 | **0** |
| `Def_AutomorphicForm_CentreCutSiegelSet` | `…/Adelic/WindowedSiegel/CentreCutSet.lean` | 1/22 | **0** |
| `Def_AutomorphicForm_ArchKFinite` | `…/Adelic/ArchKFinite.lean` | 4/9 | **0** |

**No `Def_` node**, and unlike SET-AF11/12 this one is genuinely free: the closure was checked per
module over the union, which is the only reading that sees every one (FR-0117). Two of the eight port
homes are **legacy** (`NumberField/AdelicHaar/Adele.lean`, `…/Adelic/ArchKFinite.lean`, both in
`PORT_FILES`); both are *imported*, never edited, so no migration is owed (the recipe's own rule: a
legacy module migrates when a set edits it). No promotion is owed either: the one `private` copy
(`norm_finComponent_le_one_of_mem`) is `private` in the pin too.

## 4. The home

**One new module, `AutomorphicForm/Adelic/BruhatEisenstein.lean`.** The subject is the flat Eisenstein
series and its half-plane analysis; the port has the *section* (`InducedSection.lean`, `InducedSectionFlat.lean`),
the *Weyl integral* (`WeylIntertwining.lean`), the *transversal summand estimate* (`WeylIntegrable/*`)
and the *height* (`AdelicHeight.lean`), but no module about the Eisenstein series it generates.
The module imports, in the port's own names:

- `FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining` — `adelicWeyl`, `weylIntertwiningIntegral`,
  `adelicWeyl_mul_unipotentGL2`-shaped API;
- `FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat` — `IsInducedSection`, the `flatOne`/
  `finLocalHeight` calculus, `FlatInducedSection.flatOne`;
- `FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable` (the umbrella) — the Bruhat-transversal summand
  estimate `bruhatTransversal_summand_norm_summable_of_re_gt_half` and
  `weylIntertwiningIntegrand_integrable_of_re_gt_half`;
- `FLTForHuman.AutomorphicForm.Adelic.ConstantTerm`, `…Adelic.EtaFamily`, `…Adelic.LsXi`
  (`IsUnitaryChar`), `…Adelic.ArchKFinite`, `…Adelic.SmoothAutomorphicFn`;
- `FLTForHuman.NumberTheory.AdelicHeight` — `adelicHeight`, `continuous_adelicHeight`,
  `adelicHeight_mul_of_inK`;
- `Mathlib.MeasureTheory.Integral.Pi`, `Mathlib.Analysis.SpecialFunctions.Log.Summable`,
  `Mathlib.Topology.Algebra.InfiniteSum.Order` — the analytic imports the pin's `S_` files name (the
  pin's first `S_` file says `import Mathlib`; the port never does).

**Import direction, measured.** The union of those closures is a DAG below `WeylIntegrable` and
`AdelicHeight`; no member imports anything in `AutomorphicForm` above them, so a new module is
acyclic and cascade-free. **No legacy edit** (all seven are wired or tier-3 and are only imported),
**no promotion**, **no `Def_` node**.

**Names.** The four headlines are pin-public and keep their pin names at `AutomorphicForm` level. The
helpers go in four subject namespaces — the pin's file labels (`SolE_j1`, `Ws37EisMaj`,
`BruhatCTSol`) are proof-search artefacts and are dropped: `BruhatEisensteinDiff` (the derivative
calculus), `FlatEisensteinHeight` (the local/ultrametric height calculus), `FlatSectionFamily` (the
dictionary), `BruhatConstantTerm` (the unfolding).

## 5. The cut

**One order, one worker, 947 lines in 56 declarations, one new module.** The four rows are
independent of one another, so the order can be taken in any sequence; the constant-term row is last
(§6.1). The worker takes the whole block — no row is cut, because each of the four is a premise of
different consumers (§0.4).

**The manager's layer** is: the module skeleton with its **eight `spec-pin:` lines** (the four
`Theorems/` wrappers and the four `S_` files), its imports and opens; **a statements probe** of all
four headlines against the skeleton; and the two `private`/shift decisions of §2 written into the
order. No `Def_` node, no promotion, no migration. The probe matters more than usual here: one of the
four statements carries a `letI` inside it (§6.1), and only a probe tells you the module can state it.

**Gates.** No tree build; the module's own `lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000` silent and its own `flock`/`timeout 280 lake build`; `check_port --force` →
`0 mismatch / 0 missing` with the ok count = 4 + the engine declarations that resolve by hash
(measure it; a `MISSING` is a port-side helper — keep it private); `#print axioms` on all four
headlines → `[propext, Classical.choice, Quot.sound]`; zero warnings; `dedup`/`move_dead` per module;
and one `spec/AutomorphicFormSetAF13Consumer.lean` zone that **composes the constant term with the
differentiability**: at a section family `φ`, the two rows give the constant term of the flat
Eisenstein series in terms of `weylIntertwiningIntegral`, and (via a section family that is
holomorphic in `s`) the holomorphy of `E`; the zone should state the constant-term identity at an
`φ` obtained by the dictionary row's `exists_flat_isInducedSection_family_eq_of_isInducedSection` from a
flat family — a real three-row composition, no `#check`, no `sorry`.

### 5.1 The landing (2026-11-02)

**Files.** `AutomorphicForm/Adelic/BruhatEisenstein.lean` 84 (skeleton) → **1,158** (+1,074);
`spec/AutomorphicFormSetAF13Consumer.lean` (81, new). **65 declarations: 42 public, 23 `private`** —
the four headlines, the row-3 height engine with its six `def`s and the row-4 unfolding public, and
the pins' own `private` preludes (`SolE_j1`'s four, `FlatSectionFamily`'s nineteen) private.

**65, not 56, and why.** The worklist's 56 declarations plus nine it does not list: the six `def`s of
the height calculus (`frobSq`, `distort`, `maxEntry`, `fdistort`, `archDistort`, `finDistort`), the
`Nontrivial` instance and `principalEquiv` of the constant-term unfolding, and `adelicHeight_one'` in
the dictionary. All nine are the pin's (the worklist lists theorems).

**Gates, re-run by the manager.** Edit loop at `-DmaxHeartbeats=200000` **silent, 14.3 s**; own
`flock`/`timeout 280 lake build` green (3,644 jobs, no warnings); `check_port --force` **41 ok / 0
mismatch / 0 missing** at the pin's visibility; the recipe's surface gate (all 23 `private` dropped)
**64 ok / 0 mismatch / 0 missing** — so every helper is byte-faithful to the pin and *none* had to stay
private for the checker's sake: it is private because the pin's is. `#print axioms` on the four
headlines `[propext, Classical.choice, Quot.sound]`; the four-statement probe still exactly four
`sorry` warnings; the consumer zone 0 errors, 0 warnings; `dedup --within` 0 clusters and `move_dead`
0/0/0; the statements probe re-run clean.

**The constant-term row needed the eye, not the checker.** Its statement carries
`letI := adeleBorel (𝓞 F) F` (and `let E := …`), so `check_port`'s `top_level_cut` truncates its diff
(FR-0056) and its `ok` is degenerate. The check that counts is a token comparison against the
wrapper: 191 tokens, identical, `letI` included.

**Manager's edits after the report.** Two, both recorded: the fourth mathlib import
(`Mathlib.Analysis.Complex.LocallyUniformLimit`, added at the row-1 blocker), and a naming
rectification — the four row-1 helpers carried the pin's proof-search suffix (`…_j1`) and are renamed
`exists_bound_on_unitBox_family`, `rpow_neg_le_add`, `exists_family_bound`, `summable_alpha_rpow`
(private, so the checker does not move: 41 ok before and after, and the surface gate still 64).

**Deviations from the pin, all recorded.** Visibility follows the pin's (§1); six worklist entries
were satisfied by import instead of re-statement, including the two-copy case of §2
(`norm_finComponent_le_one_of_mem`, imported from `NumberField/AdelicHeight.lean:442`, not the `private`
twin the advise file named — FR-0128); `hpow` is written at the pin's statement because
`InducedSectionFlat` has no `flatOne` twins of `hpow_mul_inK`/`hpow_of_inK`; **one `Def_`-level
prerequisite was absorbed**: `isSmoothVector_rightTranslationFn_mul` lives in the unported
`Definitions/Def_AutomorphicForm_FnTwist.lean:67`, and its ~10-line product-smoothness argument is
inlined into `isKfSmooth_mul_hpow` rather than added as public surface (FR-0129 — the definition gate
reads the *statements*' closure and this one is proof-only); the rest are v4.34 proof shifts
(`Finset.prod_le_prod` → `prod_le_prod₀` at three sites, an explicit `rw` for
`Set.Finite.coe_toFinset`, the `section UltraBase` split that clears `linter.unusedSectionVars`
without touching a statement, `fun _ _` for an unused binder, `haveI` → `have`) — FR-0130.

**Plan against actual.** Lines: **1,074 written** against the worklist's 947 and `port_plan`'s 959 net
— **+12 %**, the largest overrun the column has had (+0.6 % at AF12, −0.1 % at AF11), and the causes are
identifiable: the six height `def`s the worklist omits, and the explicit `rw`/`have` where the pin used
`simp` arguments that no longer fire. Declarations: 65 against 56 (+9, same cause). Checker: 41 at the
pin's visibility (the 42nd public declaration is the `Nontrivial` instance, which the checker's
declaration regex does not see), 64 at the dropped surface.

**The re-read. Exact on the demand side; it readies nothing again.** The four rows leave the ready
shelf and the leaves are untouched — no leaf was in the set — and, despite the four rows being cited by
45 pin files (§0.4), **no row becomes ready**: each of the 45 files needs more than these four (§7
names the three clusters that would finish them).

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 865 / 351,925 | **861 / 350,288** | −4 / −1,637 ✓ (the four rows' silo, exact) |
| `needed [literal]` | 878 / 355,400 | **874 / 353,763** | −4 / −1,637 ✓ |
| frontier F | 1,550 / 775,441 | **1,554 / 777,078** | +4 / +1,637 ✓ |
| ready rows, all namespaces | 66 / 17,896 | **62 / 16,259** | −4 / −1,637 (the four rows leave) |
| `AutomorphicForm` ready rows | 37 / 12,552 | **33 / 10,915** | −4 / −1,637 |
| leaves, all namespaces | 232 / 58,795 | 232 / 58,795 | — (the set took no leaf) |
| `AutomorphicForm` leaves | 63 / 12,756 | 63 / 12,756 | — |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,369 / 1,550) | **PASS** (1,373 `Thm_` sources, 1,554 declared names) | — |

**Three sets in a row with at most one readied row.** That is a property of where the AF shelf now
is, not of these three cuts: the remaining ready rows' consumers are gated on rows in *other*
columns (`TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`,
`AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar`, the `LanglandsTunnell`
`moderateGrowth`/`rpow_bound` rows) or on the two big AF blocks this column has deferred. The next
scoping should decide between three moves and say so explicitly: **(a)** the flat-section indicator
row (1,043) plus the Weyl pair (2,640) — the AF column's own largest subjects, two dispatches,
no external blocker; **(b)** a *boundary* set that ports the three gating rows above, which is a
column-plan decision, not a scoping one; **(c)** the high-fan-in API tail (§7's last item), which
readies nothing but cheaply hardens the surface the Rankin–Selberg development will read.

## 6. Risk register

1. **The constant-term row's statement carries a `letI`.** Its conclusion is
   `letI := adeleBorel (𝓞 F) F; let E := …; constantTerm … = φ g + (vol box)⁻¹ * weylIntertwiningIntegral …`.
   The checker's `top_level_cut` stops at the first top-level `:=`, which is the instance binding's
   value, so its diff is **degenerate** (FR-0056): `check_port` will report it `ok` on a truncated
   signature. Read that statement by eye against the wrapper, and keep the `letI` spelled as the
   wrapper's (the checker compares text; `letI` in a *statement* is not the linter's target).
2. **The 380-line height bound is the set's cost** (25 declarations, the largest block after the
   52-declaration complex prelude of SET-AF12). It is a local-then-ultrametric height calculus over a
   nonarchimedean `K = F_v`: read the pin's `Local`/`Ultra` sections in order, and do not try to unify
   them before the last declaration.
3. **`hpow` is a shift, not a rename** (§2): use `FlatInducedSection.flatOne` with `s = t - 1/2` and
   the `flatOne` twins of `hpow_mul_inK`/`hpow_of_inK`, or write the two-line `hpow`. Either is
   acceptable; a silent third spelling is not.
4. **`norm_finComponent_le_one_of_mem` is `private` in the port** (and in the pin): re-state its 13
   lines here, do not promote it for this set.
5. **The pin's `S_` file imports `Mathlib`**; the port module must name the three mathlib modules
   above and nothing more. Importing `Mathlib` is an edit-loop cost of its own.
6. **No `set_option`** — the pin's `letI`/`haveI` walls in proofs become `have`/`let` (Lean 4 registers
   local instances for those; FR-0126). No `sorry`, no `native_decide`, zero warnings.
7. **Binder shadowing for the checker** (FR-0123): the four headlines must spell the wrappers' binders
   inline, including the `let α := …` preamble of two of them; the probe is the check.

## 7. What this set does not do

- **It does not take the flat-section indicator row** —
  `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043, 3 premises, 1/3), the largest
  ready row on the shelf: the height of the *bottom-row indicator* section. It is the same subject's
  other half and the natural companion of this set's height row; it is AF14's first candidate, with
  `exists_flat_isInducedSection_family_eq_of_isInducedSection` already in hand from here.
- **It does not take the Weyl-integrand pair** — 1,349 + 1,291 = **2,640 silo**, a transcription set
  whose only in-port lines are the shared integrability lemma. Two dispatches; a set of its own.
- **It does not take the `diagOne` family** — `whittakerCoefficient_diagOne_satisfies_whittaker_ode_…`
  (306) and its consumers (394, 464, 934), the sequel to SET-AF12: blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`,
  `AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` and the `LanglandsTunnell`
  `moderateGrowth`/`rpow_bound` rows.
- **It does not take the `su(2)` string** — the 681-line `whittakerCoefficient_su2String_…_hypotheses`
  row (ready once the 61-line complex-place `stdAddChar` lemma lands) and the 755-line
  `su2Derivs_stable_…` leaf, which has **no consumer in the pin** (nothing imports its `S_` file): the
  pin's unreachable mathematics, ported whole or not at all, and not by this set.
- **The 4 withheld rows / 831 silo** remain the prunable complex-analytic subject.
- **No `Def_` node, no promotion, no migration**; one new module, cascade-free.

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af12-landed.json` by `build/af13-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **37 rows / 12552 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | 3 | 2/5 | **SET-AF13** |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | 3 | 1/5 | **SET-AF13** |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | 2 | 4/15 | **SET-AF13** |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | **SET-AF13** |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |

### The leaves block — **63 leaves / 12756 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | deferred (§7) |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 1/1 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | deferred (§7) |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred (§7) |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | deferred (§7) |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | deferred (§7) |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred (§7) |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred (§7) |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred (§7) |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | deferred (§7) |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred (§7) |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred (§7) |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | deferred (§7) |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred (§7) |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | deferred (§7) |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred (§7) |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred (§7) |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred (§7) |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred (§7) |
| `constantTerm_add` | 13 | 1/2 | deferred (§7) |
| `constantTerm_smul` | 11 | 1/1 | deferred (§7) |

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py` from the port's statement index: per row, every declaration whose
statement is not in the port, with its pin line and span.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 592 | 432 | 160 | 5 |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 404 | 24 | 380 | 25 |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 298 | 102 | 196 | 18 |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 215 | 4 | 211 | 8 |
| **4 rows** | **1509** | **562** | **947** | **56** |

### `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family`

592 declaration lines, 432 imported, **160 to write** in 5 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 66 | 560 | theorem |
| `summable_alpha_rpow_j1` | 47 | 513 | theorem |
| `exists_family_bound_j1` | 17 | 496 | theorem |
| `exists_bound_on_unitBox_family_j1` | 16 | 216 | theorem |
| `rpow_neg_le_add_j1` | 14 | 482 | theorem |

### `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet`

404 declaration lines, 24 imported, **380 to write** in 25 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 94 | 339 | theorem |
| `fdistort_eq_one` | 35 | 193 | theorem |
| `distort_le_mul_localHeight` | 33 | 97 | theorem |
| `finLocalHeight_mul_le` | 25 | 168 | theorem |
| `finHeight_mul_le` | 25 | 270 | theorem |
| `fdistort_finComponent_eventually_eq_one` | 24 | 239 | theorem |
| `localHeight_mul_le` | 22 | 75 | theorem |
| `det_mul_rowMaxNorm_le` | 21 | 147 | theorem |
| `archDistort_le_of_mem` | 18 | 321 | theorem |
| `det_sq_mul_rowNormSq_le` | 12 | 63 | theorem |
| `norm_sub_mul_sq_le` | 9 | 54 | theorem |
| `adelicHeight_mul_le` | 9 | 303 | theorem |
| `finDistort_eq_one_of_mem` | 9 | 312 | theorem |
| `archHeight_mul_le` | 8 | 295 | theorem |
| `cramer10` | 4 | 46 | theorem |
| `cramer11` | 4 | 50 | theorem |
| `le_maxEntry` | 4 | 135 | theorem |
| `hasFiniteMulSupport_fdistort` | 4 | 263 | theorem |
| `frobSq_nonneg` | 3 | 31 | theorem |
| `det_norm_pos` | 3 | 36 | theorem |
| `distort_nonneg` | 3 | 39 | theorem |
| `maxEntry_nonneg` | 3 | 132 | theorem |
| `archDistort_nonneg` | 3 | 236 | theorem |
| `finDistort_nonneg` | 3 | 267 | theorem |
| `fdistort_nonneg` | 2 | 141 | theorem |

### `exists_flat_isInducedSection_family_eq_of_isInducedSection`

298 declaration lines, 102 imported, **196 to write** in 18 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 43 | 284 | theorem |
| `isArchKFinite_mul_hpow` | 27 | 198 | theorem |
| `isInducedSection_mul_hpow` | 24 | 260 | theorem |
| `inK_of_mem_archRowIsometrySubgroup` | 16 | 144 | theorem |
| `isKfSmooth_hpow` | 13 | 181 | theorem |
| `continuous_mul_hpow` | 9 | 225 | theorem |
| `split_snd` | 9 | 251 | theorem |
| `split_fst` | 8 | 243 | theorem |
| `adelicHeight_mul_of_inK` | 6 | 119 | theorem |
| `inK_of_mem_finiteAdelic` | 6 | 160 | theorem |
| `differentiable_mul_hpow` | 6 | 234 | theorem |
| `adelicHeight_eq_one_of_inK` | 5 | 139 | theorem |
| `hpow_mul_inK` | 5 | 168 | theorem |
| `InK` | 4 | 115 | def |
| `hpow_of_inK` | 4 | 173 | theorem |
| `hpow_zero` | 4 | 177 | theorem |
| `isKfSmooth_mul_hpow` | 4 | 194 | theorem |
| `alphaF` | 3 | 240 | def |

### `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral`

215 declaration lines, 4 imported, **211 to write** in 8 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl` | 67 | 166 | theorem |
| `integrableOn_and_setIntegral_tsum_translate` | 49 | 64 | theorem |
| `constantTerm_cond_adelicBox_eq` | 28 | 117 | theorem |
| `solution` | 26 | 233 | theorem |
| `constantTerm_bruhatEisenstein_core` | 21 | 145 | theorem |
| `tsum_lintegral_adelicBox_comp_add` | 8 | 48 | theorem |
| `tsum_integral_adelicBox_comp_add` | 8 | 56 | theorem |
| `principalEquiv` | 4 | 39 | def |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af12-landed.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family \
  --nodes AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet \
  --nodes AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection \
  --nodes AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral \
  --json build/af13-advise.json
python3 port_plan.py --json build/af13-advise.json     # 1,637 raw / 1,510 decl / 519 in port / 959 net
python3 build/af-worklist.py bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family \
  exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet \
  exists_flat_isInducedSection_family_eq_of_isInducedSection \
  constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
cd ../lean
ROWS="Theorems/Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean \
  Theorems/Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean \
  Theorems/Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.lean \
  Theorems/Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean"
for pin in Def_AutomorphicForm_InducedSection Def_AutomorphicForm_EtaFamily \
  Def_AutomorphicForm_WeylIntertwining Def_NumberField_AdelicHaar Def_NumberField_AdelicHeight \
  Def_NumberField_AdelicBox Def_AutomorphicForm_CentreCutSiegelSet Def_AutomorphicForm_ArchKFinite; do
  python3 spec/gate_scan.py --pin Definitions/$pin.lean --rows $ROWS
done
```

`--rows` takes a **list** in one flag (`--rows A B C D`); repeating `--rows` silently keeps only the
last one (found at this pass — a three-block read became a one-block read).

**Forecast on landing** (read at §0.1): `needed` **865 / 351,925 → 861 / 350,288** (−4 / −1,637, the four
rows' silo), frontier **1,550 / 775,441 → 1,554 / 777,078**. The ready shelf should keep the indicator
row on it and may gain the rows the four consumers feed — §0.4 lists 45 citing files, of which the 15-
and 20-file rows are the ones to watch; the re-read decides.

**Measured at landing (§5.1):** exact on every figure — `needed` **861 / 350,288**, literal
**874 / 353,763**, frontier **1,554 / 777,078**, ready 66 / 17,896 → **62 / 16,259**, leaves untouched,
`--selfcheck` PASS (1,373 / 1,554) — and **no row readied**: the 45 citing files each need more than
these four, which is the third consecutive set with a ready-shelf delta of at most one. The next
scoping's choice between the two big AF blocks, a column-boundary set, and the API tail is stated at
the end of §5.1.
