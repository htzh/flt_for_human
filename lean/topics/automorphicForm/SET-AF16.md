# SET-AF16 — an induced section is determined by its maximal compact: regularity, height, span, and the two reductions

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, all eight rows, all gates green;
**§5.1 records the landing and the re-read** (exact on every figure, and a ready-shelf delta of exactly
its own consumption). The order is
[WORKORDER-AF16-section-K-dictionary.md](WORKORDER-AF16-section-K-dictionary.md): all three module
skeletons exist, build and wire clean (`check_port --force` 0 / 0 / 0 on each), and
`lean/tmp/probe-af16-statements.lean` states all eight headlines with exactly eight `sorry` warnings.
Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF15 left. It is the **sixteenth** `AutomorphicForm`-serving set, and it is **the block SET-AF15's
own landing readied**: eight rows, 1,278 silo, one subject — *a section is determined by, and inherits
the regularity of, its restriction to the maximal compact* — which is the pointwise consequence of the
Borel decomposition SET-AF15 ported. Eight of the nine rows AF15 readied are these; the ninth (890) is
another column's.

The set is **8 rows / 1,278 silo / 877 net lines** (`port_plan`) — **883 lines to write in 35
declarations** by the worklist — in **three orders over three new modules**. It is a **composition**
set in the AF13 sense: **209 of its 1,086 once-cost lines are already in the port** (19 %), almost all of
it genuine public reuse, and its 8 rows drag in only 35 declarations.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the section's `K`-dictionary: value, continuity, height | 5 | 542 | 357 | new `AutomorphicForm/Adelic/InducedSectionKRegular.lean` |
| B — the span of a differentiable family of flat sections | 1 | 264 | 154 | new `AutomorphicForm/Adelic/InducedSectionSpan.lean` |
| C — the two maximal-compact reductions | 2 | 472 | 372 | new `AutomorphicForm/Adelic/MaximalCompactReductions.lean` |
| | **8** | **1,278** | **883** | three files, one dispatch |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af15-landed.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF15 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **850 / 347,609** | 850 / 347,609 |
| `needed [literal]` | 863 / 351,084 | 863 / 351,084 |
| frontier F | **1,565 / 779,757** | 1,565 / 779,757 |
| ready rows, all namespaces | 69 / 17,772 | 69 / 17,772 |
| ready rows, `AutomorphicForm` | **39 / 11,538** | 39 / 11,538 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 |
| leaves, `AutomorphicForm` | **56 / 11,461** | 56 / 11,461 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (1,384 `Thm_` sources, 1,565 declared names) | PASS (1,384 / 1,565) |
| correction | **none needed** | none needed |

Same tree, same read as SET-AF15's landing: zero delta on every row, no correction owed. Both blocks are
quoted whole in Appendix A — 39 ready / 11,538 and 56 leaves / 11,461 — of which **8 rows / 1,278 are
this set's** and 87 are deferred (§7). The withheld block is the same four rows (831 lines).

### 0.2 Why this block

- **It is the whole of what the last landing created.** SET-AF15 §5.1 forecast nine readied rows /
  2,168 silo and measured exactly that; eight of the nine (1,278) are here. Taking them is the recipe's
  §7 discipline — *a shelf re-read, not a shelf memory, opens the next scoping* — followed one step
  further: the set that opens work should be followed by the set that takes it.
- **It is one subject, and the subject is new to the port.** The eight rows all say something of the
  form "on the maximal compact, the section's value/regularity/height is what you see; elsewhere it is
  the Borel factor times that". The port has the *ingredients* (the induced-section layer, the height,
  the row-isometry subgroup, `maximalCompactAt`) and the decomposition itself, landed last set; it has
  no module where the dictionary between a section on `GL₂(𝔸)` and its restriction to `K` lives.
- **It is a composition set, and this time the reuse is real.** `port_plan` finds 209 lines in the port
  and `port_advise` 13 trusted substitutions with **no** type-only `def` match; the biggest block is
  `RepTheory/TranslateSpan.lean`'s `EvalMatrix`/`UniformRank` engine (83 lines, another column's, and
  already public), then `MaximalCompactFactors`' `atPlace` kit (54) and `InducedSectionFlat`/
  `AdelicHeight`'s height comparisons (78). Only one of the 218 "imported" worklist lines is not
  importable (`KT`, 2 lines — FR-0134 again, an `abbrev` matched by shape).
- **It is the last AF block on the shelf that one dispatch can close.** After it the AF ready shelf is
  31 rows / 10,260, and its largest entries are the Weyl pair (2,640), the indicator row (1,043) and the
  two `SmoothCuspRealizationAt` rows (527 / 513) — each of them measured (or measured twice) to ready
  nothing, and the `diagOne` family still blocked on other columns (§7).

### 0.3 What a landing would change — the forecast

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 850 / 347,609 | **842 / 346,331** | −8 / −1,278 ✓ (the eight rows' silo, exact) |
| `needed [literal]` | 863 / 351,084 | **855 / 349,806** | −8 / −1,278 ✓ |
| frontier F | 1,565 / 779,757 | **1,573 / 781,035** | +8 / +1,278 ✓ |
| ready rows, all namespaces | 69 / 17,772 | **61 / 16,494** | −8 / −1,278 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — |

**Nothing is readied.** This is a pure consumption set — the first of the column's sets whose purpose is
to *empty* a subject rather than to open one — and the brief says so plainly so that the re-read's
"readied: 0" is the measured expectation, not a disappointment. Its return is that the AF shelf's
biggest cheap block disappears and the remaining ones are the honest big ones.

## 1. The eight rows

| row (`AutomorphicForm.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `exists_flat_isInducedSection_sum_eq_of_differentiable_family` | 264 | **154** | 7 | 3 | 5/11 | a differentiable family `φ` of flat sections, continuous in `(s, g)` and holomorphic in `s`, is `φ s = ∑_i c_i(s) · ψ_i(s)` with the `c_i` differentiable, the `ψ_i(s)` flat sections with the same `IsArchKFinite`/`IsKfSmooth`/continuity/holomorphy properties, and **`ψ_i s k = ψ_i s' k` for `k` integral with row-isometry archimedean components** |
| `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 245 | **171** | 2 | 1 | 2/2 | if a Whittaker function `W` (a `ψ`-eigenfunction, `ω`-equivariant under the centre) does not vanish at `g₀`, then for some `t` (trivial outside `S`) and `k ∈ maximalCompactAt F S`, `W (diagOne t * k) ≠ 0` — the `diagOne` reduction of a non-zero value |
| `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` | 227 | **201** | 14 | 3 | 1/2 | the set of points written `b * k` with `k` integral and of bounded archimedean height is compact — the Siegel-set compactness that the centre-cut estimates quantify over |
| `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` | 161 | **56** | 3 | 2 | 1/4 | `‖φ g‖ ≤ C · adelicHeight g ^ σ` for an induced section of the character pair at `s = σ` — the `K`-argument only enters through the height |
| `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` | 155 | **136** | 4 | 1 | 1/6 | continuity of a section on the maximal compact transfers to continuity everywhere |
| `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` | 116 | **97** | 3 | 1 | 1/4 | the same, from the pointwise Borel form `φ (b * g) = χ(b) · φ g` |
| `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` | 81 | **57** | 1 | 2 | 1/1 | a flat family is invariant in its `k`-argument on `maximalCompactAway S` |
| `IsInducedSection_eq_of_eqOn_maximalCompact` | 29 | **11** | 1 | 1 | 1/5 | a section that is an induced section and agrees with another on the maximal compact **is** that section |

**Visibility is mixed and both readings matter.** Rows 3 and 5 are flat public surfaces (13 and 4 public
declarations); rows 1, 2, 4 and 6 are private preludes with one public headline each (13, 6, 5 and 2
private); rows 7 and 8 are a single public declaration each. So the checked surface at the pin's
visibility is **23 declarations** and the dropped-`private` surface is **49** — the two readings together
are the statement check, and the set has more public surface than SET-AF15's three.

**Namespaces** (one per pin file, the pin's proof-search labels replaced by subject names):
`FlatFamilyDecomposition` (row 1, the pin's own name), `DiagOneReduction` (row 2, pin `NondegKit`),
`BorelHeightCompact` (row 3, pin `B3Translate`), `SectionHeightBound` (row 4, pin `SphericalCollapse`),
`ContinuousOnMaximalCompact` (row 5, pin `ICTProof`), `ContinuousOnBorel` (row 6, pin `ICGProof`),
`FlatFamilyKInvariance` (row 7, no pin namespace) and `IsInducedSectionEqOnK` (row 8, none). **Each
headline is at its pin's name — `AutomorphicForm.<name>`, and `AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact`
for row 8 — not inside the helper namespace** (§5.1 item 3: the landing first put seven of them in their
helper namespaces, which no instrument flagged).

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family \
  --nodes AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero \
  --nodes AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 \
  --nodes AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection \
  --nodes AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact \
  --nodes AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn \
  --nodes AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family \
  --nodes AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact \
  --json build/af16-advise.json
python3 port_plan.py --json build/af16-advise.json     # 1,278 raw / 1,093 decl / 209 in port / 877 net
python3 build/af-worklist.py exists_flat_isInducedSection_sum_eq_of_differentiable_family \
  exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero \
  exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 \
  exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection \
  continuousOn_of_isInducedSection_of_continuousOn_maximalCompact \
  continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn \
  exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family \
  IsInducedSection_eq_of_eqOn_maximalCompact
```

`port_plan`: raw **1,278** → declaration lines **1,093** → −7 duplicate copies → 1,086 once-cost →
**−209 already in the port** → **NET NEW 877**; boilerplate 185; 50 distinct declaration groups.
The worklist (Appendix B): **1,101 declaration lines, 218 imported, 883 to write in 35 declarations**.

### 2.1 The reuse is real — 216 of 218 lines

| pin declaration | row | lines | port copy | reading |
|---|---|---:|---|---|
| `evalMatrix` (+ `_apply`, 3) | 1 | 7 | `EvalMatrix.evalMatrix` (`RepTheory/TranslateSpan.lean:88`) | **identical definition** (checked body to body): import |
| `exists_det_evalMatrix_ne_zero` | 1 | 44 | `EvalMatrix.exists_det_evalMatrix_ne_zero` | public, statement-identical: import |
| `linearIndependent_of_det_evalMatrix_ne_zero` (+ the `iff`, 4) | 1 | 14 | `EvalMatrix.…` | public: import |
| `eq_sum_inv_evalMatrix_mulVec_smul` | 1 | 19 | `UniformRank.eq_sum_inv_evalMatrix_mulVec_smul` | public: import |
| `atPlace` (+ `glArch_atPlace`, `finComponent_atPlace_{self,of_ne}`, 3+4+5) | 2 | 16 | `AutomorphicForm.atPlace` etc. (`MaximalCompactFactors.lean:112–166`) | **`private` in the port** — **promoted at the landing (§5.1)**, then imported |
| `localEmbed_entries_integral` (16) + `atPlace_mem` (22) | 2 | 38 | `AutomorphicForm.…` (`MaximalCompactFactors.lean`) | **`private`** likewise — **promoted**, then imported |
| `rowMaxNorm_mul_le_of_entries` (27) + `finLocalHeight_mul_of_entries` (38) | 4 | 65 | `FlatInducedSection.rowMaxNorm_mul_le` / `finLocalHeight_mul_integral` (also in `NumberField.AdelicHeight`) | public: import (either copy) |
| `finHeight_mul_of_mem` | 4 | 13 | `NumberField.AdelicHeight.finHeight_mul_of_mem` | **shape** tier, same statement: import |
| `KT` | 1 | 2 | `ZbarHomsConj.Qbar` (`Algebra/IntegralExtensionCharacters.lean`) | **false positive** (FR-0134): the pin's `KT = {k // InK F k}` is a subtype of adelic matrices, the port's `Qbar` a subtype of `ℂ` — **write the 2-line abbrev** |

So the honest net is **877 + 2 = 879** (once-cost 1,086 − 207 importable): **write `KT` (2 lines) and
import the rest**, once the six `atPlace`-kit declarations are promoted out of `private` — which the
manager did at the landing (§5.1, on the rule that a helper that is *mathematics* is promoted and only a
tactical helper may be duplicated). This corrects the first
reading of this table (the landing, §5.1): `atPlace` and its kit are `private` in
`MaximalCompactFactors.lean:112–166`, so they are not importable — the same FR-0133 trap as SET-AF15,
and this pass walked into it by reading the statement match without the declaration's visibility. What
*is* true is that the other 153 lines are genuine reuse, and the reason is worth stating: the modules a
composition set cites were landed *by previous sets of this column* (`InducedSectionFlat` by AF13) or
already existed (`TranslateSpan`, another column's).

**No port-once block and no cross-file duplicates**; the one *in-file* engine is row 1's
`EvalMatrix`/`UniformRank` block (5 declarations, 83 lines, inside one file — the *pin's* own structure,
and the port has it at exactly those names).

## 3. The definition gate

`spec/gate_scan.py` over the fifteen `Def_` modules in the eight rows' closure — the twelve the wrappers
name, plus the three its `S_` files name and its wrappers do not (`Def_AdelicDock_LocalEmbedding`,
`Def_AutomorphicForm_ProductionPinsGeneral`, `Def_AutomorphicForm_PeterssonIntegral`,
`Def_NumberField_TateGlobalZeta` are the FR-0129 class; `LocalEmbedding` is scanned against the `S_`
file, which uses **24 of its 62** declarations):

| pin `Def_` module | port home | used (max over rows) | missing |
|---|---|---:|---:|
| `Def_AutomorphicForm_InducedSection` | `…/Adelic/InducedSection.lean` | 1/10 | **0** |
| `Def_AutomorphicForm_EtaFamily` | `…/Adelic/EtaFamily.lean` | 3/15 | **0** |
| `Def_AutomorphicForm_SmoothAutomorphicFnAt` | `…/Adelic/SmoothAutomorphicFn.lean` | 2/16 | **0** |
| `Def_AutomorphicForm_ArchKFinite` | `…/Adelic/ArchKFinite.lean` | 4/9 | **0** |
| `Def_AutomorphicForm_AdelicMaximalCompact` | `…/Adelic/AdelicMaximalCompact.lean` | 2/37 | **0** |
| `Def_AutomorphicForm_WhittakerCoefficient` | `…/Adelic/WhittakerCoefficient.lean` | 1 | **0** |
| `Def_AutomorphicForm_WindowedSiegelSet` | `…/Adelic/WindowedSiegel/Set.lean` | 3/29 | **0** |
| `Def_NumberField_AdelicHeight` | `…/NumberTheory/AdelicHeight.lean` | 4/27 | **0** |
| `Def_NumberField_AdelicHaar` | `…/NumberTheory/AdelicHaar/Adele.lean` | 1 | **0** |
| `Def_NumberField_AdelicLevel` | `…/NumberTheory/AdelicLevel/{Level,Projections}.lean` | 9/114 | **0** |
| `Def_AutomorphicForm_RowIsometryInvariance` | `…/Adelic/WindowedSiegel/RowIsometry.lean` | 1/12 | **0** |
| `Def_AutomorphicForm_WeylIntertwining` | `…/Adelic/WeylIntertwining.lean` | 1 | **0** |
| `Def_AdelicDock_LocalEmbedding` (via the `S_` file) | `…/NumberTheory/AdelicDock/LocalEmbedding.lean` | **24/62** | **0** |
| `Def_NumberField_TateGlobalZeta` | `…/NumberTheory/NumberField/TateGlobal/Defs.lean` | 1 (row 3's `hgt` is `TateGlobal.ideleNorm fst / ideleNorm snd`) | **0** |
| `Def_AutomorphicForm_ProductionPinsGeneral`, `…_PeterssonIntegral` | imported by row 8's wrapper, unused by any statement | 0 | **0** |

**No `Def_` node, no promotion, no migration.** Every used declaration is ported and public. **One
correction, made at the landing (§5.1):** the first reading of this gate called
`Def_NumberField_TateGlobalZeta` "unused by any statement" — it is not. Row 3's `hgt` is
`TateGlobal.ideleNorm (borelDiagFst b) / ideleNorm (borelDiagSnd b)`, so `TateGlobal.ideleNorm` is in six
of the row's *statements*, and the module is `NumberTheory/NumberField/TateGlobal/Defs.lean` (plus
`TateGlobalContinuousIdeleNorm` for the continuity). Two port
homes are legacy (`NumberTheory/AdelicHaar/Adele.lean`, `…/Adelic/ArchKFinite.lean` — AF13's list) and
are only imported; the rest are wired, non-legacy modules. The one heavy gate is
`AdelicDock.LocalEmbedding`'s 24 declarations in row 2, all ported.

## 4. The homes

**Three new modules, one per order.**

- **Order A — `FLTForHuman/AutomorphicForm/Adelic/InducedSectionKRegular.lean`** (rows 4, 5, 6, 7, 8).
  Subject: the section's value, continuity and height as functions of its `K`-argument. Imports
  `…/Adelic/InducedSection`, `…/Adelic/InducedSectionFlat` (`FlatInducedSection`, `flatOne`,
  `finLocalHeight`), `…/Adelic/InducedSectionMaximalCompact` (the `adelicMaximalCompact`/`maximalCompactAway`
  calculus, `flat_family_comp_mul_of_mem_adelicMaximalCompact`), `…/Adelic/EtaFamily`,
  `…/Adelic/ArchKFiniteFamily{,Theorems}`, `…/Adelic/SmoothAutomorphicFn`, `…/Adelic/AdelicMaximalCompact`,
  `…/Adelic/WindowedSiegel/{RowIsometry,Set,Topology}`, `…/Adelic/AdelicIwasawa` (the decomposition,
  SET-AF15), **`…/Adelic/MaximalCompactFactors`** (row 7's `exists_maximalCompactAway_subset_of_mem_nhds_one`,
  added at the landing), `…/NumberTheory/AdelicHeight`, `…/NumberTheory/AdelicLevel/{Level,Projections}`,
  and `Mathlib.MeasureTheory.Measure.Haar.DistribChar`, `Mathlib.Analysis.Meromorphic.Order`,
  `Mathlib.MeasureTheory.Group.FundamentalDomain`.
- **Order B — `FLTForHuman/AutomorphicForm/Adelic/InducedSectionSpan.lean`** (row 1). Subject: a
  differentiable family of flat sections spans finitely many `K`-flat ones — the `EvalMatrix`/det
  argument. Imports order A's module is *not* needed: `…/Adelic/InducedSection`, `…/Adelic/InducedSectionFlat`,
  `…/Adelic/ArchKFiniteFamily{,Theorems}`, `…/Adelic/EtaFamily`, `…/Adelic/SmoothAutomorphicFn`,
  `…/Adelic/BorelSubgroup`, `…/Adelic/AdelicIwasawa`, **`…/Adelic/BruhatEisenstein`**
  (`exists_flat_isInducedSection_family_eq_of_isInducedSection`, added at the landing),
  `FLTForHuman.RepTheory.TranslateSpan` (`EvalMatrix`, `UniformRank`), and
  `Mathlib.LinearAlgebra.{Pi,Finsupp.LinearCombination}`, `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
- **Order C — `FLTForHuman/AutomorphicForm/Adelic/MaximalCompactReductions.lean`** (rows 2, 3). Subject:
  the two reductions to the maximal compact — the `diagOne` support of a Whittaker function, and the
  compactness of a bounded-height Siegel set. Imports `…/Adelic/MaximalCompactFactors` (`atPlace`, the
  one-place splitting), `…/Adelic/WhittakerCoefficient`, `…/Adelic/AdelicMaximalCompact`,
  `…/Adelic/WindowedSiegel/{Set,Topology,RowIsometry}`, `…/Adelic/AdelicIwasawa`,
  `…/NumberTheory/AdelicHeight`, `…/NumberTheory/AdelicDock/LocalEmbedding`,
  `…/NumberTheory/NumberField/TateGlobal/Defs` and `…/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm`
  (row 3's `hgt` is `TateGlobal.ideleNorm fst / ideleNorm snd` — added at the landing, see §3),
  `…/NumberTheory/AdelicLevel/{Level,Projections}`, `Mathlib.MeasureTheory.Measure.Haar.DistribChar`.

**Import direction, measured.** All three orders import only modules that are *below* them: the
`InducedSection*` layer, the `WindowedSiegel` set, `MaximalCompactFactors`, `WhittakerCoefficient`,
`AdelicHeight`, and SET-AF15's `AdelicIwasawa`. `RepTheory/TranslateSpan` imports **mathlib only** (checked),
so the `AutomorphicForm/Adelic → RepTheory` edge is safe and mirrors the pin, which takes the engine from
`Theorems/`. Nothing imports the three new modules: all cascade-free, and mutually independent (order A's
rows do not cite order B's or C's; the three orders' pin files are disjoint).

## 5. The cut

**Three orders, one dispatch, three workers.**

| order | rows | silo | lines | decls | module |
|---|---:|---:|---:|---:|---|
| A — the `K`-dictionary | 5 | 542 | 357 | 12 | `InducedSectionKRegular.lean` |
| B — the span of a flat family | 1 | 264 | 154 | 7 | `InducedSectionSpan.lean` |
| C — the two maximal-compact reductions | 2 | 472 | 372 | 16 | `MaximalCompactReductions.lean` |
| | **8** | **1,278** | **883** | **35** | three files |

**Disjoint files, disjoint pin files, no cross-citation**: the three orders are safe concurrently. Order C
carries the set's cost (372 lines, and row 3 alone is 14 declarations), order A the largest row count,
order B the heaviest single engine (the `EvalMatrix`/det argument, 7 declarations but 154 lines).

**The manager's layer** is the three skeletons with their `spec-pin:` wires (A: five wrappers + five `S_`
files; B: one + one; C: two + two — sixteen lines in all), their imports and opens; a **statements probe
of all eight headlines**; and the §2.1 decision written into the order: **write `KT`, import everything
else** on the substitution table, and keep every helper's visibility as the pin's (26 private, and 17
public helpers in rows 3 and 5 — the flat public surfaces are checked surface, not free).

**Gates, per order** (recipe §6):

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; the ok count **measured at
   both readings** — at the pin's visibility the set has **23** public declarations in all (16 of them in
   order A's five rows, 6 in order C's two, 1 in order B's one), and the dropped-`private` reading ~49. A
   `MISMATCH` at either reading is a mis-transcription; a `MISSING` at the dropped reading is a port-side
   helper (keep it private).
2. `#print axioms` on the eight headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` silent and its own
   `flock`/`timeout 280 lake build`. No tree build, no dependents.
4. `dedup.py --within` / `move_dead.py --dry-run` per module; the pin's own intra-file structures (row 1's
   `EvalMatrix`/`UniformRank` block, a headline against its `main`) stay, with the reason recorded.
5. `spec/AutomorphicFormSetAF16Consumer.lean` — **one zone per order**, each a real composition, no
   `#check`, no `sorry`:
   - **A**: from `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` and
     `IsInducedSection_eq_of_eqOn_maximalCompact`, prove that two continuous induced sections agreeing on
     the maximal compact are equal — the set's own headline pair, composed;
   - **B**: take the decomposition `φ s = ∑ c_i(s) ψ_i(s)` of `exists_flat_isInducedSection_sum_eq_of_differentiable_family`
     at a family with `n = 1`, and read `φ` as `c_fun * ψ_fun`, with `ψ_fun` constant in its `K`-argument
     on the integral row-isometry subgroup;
   - **C**: use `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` to produce
     `(t, k)` and then `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_…` to place `diagOne t * k`
     in the compact set, at a bounded height.
   Each zone imports the two new modules it composes (and, where needed, one port module); error count is
   the deliverable metric.
6. Zero warnings, no `sorry`/`admit`/`axiom`/`native_decide`, no `set_option` beyond `autoImplicit false`,
   no new import without a report.

### 5.0 The manager's layer (landed 2026-11-02)

Three skeletons — `InducedSectionKRegular.lean` 94 lines (ten `spec-pin:` lines, seventeen imports),
`InducedSectionSpan.lean` 66 (two wires, eleven imports) and `MaximalCompactReductions.lean` 69 (four
wires, twelve imports) — each silent, each built green (`flock`/`lake build <module>`, 3,901 jobs for the
closure), `check_port --force` **0 ok / 0 mismatch / 0 missing** on all three. The statements probe
(`lean/tmp/probe-af16-statements.lean`) states all eight headlines verbatim from their wrappers and
elaborates with **exactly eight `declaration uses 'sorry'` warnings**; it settled that the probe needs
`open scoped NNReal` at file level (four statements spell `ℝ≥0`). The §2.1 decision is written into the
order: **import the 216 lines** (the `EvalMatrix` engine from `RepTheory/TranslateSpan`, the `atPlace` kit
from `MaximalCompactFactors`, the three height comparisons) and **write `KT`** (2 lines), because the
advise's match to `ZbarHomsConj.Qbar` is a shape-tier match on a subtype of a `Type` — FR-0134's class
once more, and the only false substitution in the block.

### 5.1 The landing (2026-11-02)

**Files.** `InducedSectionKRegular.lean` 94 (skeleton) → **461** (12 declarations: 8 public, 4 `private`);
`InducedSectionSpan.lean` 66 → **221** (8: 1 public, 7 `private`); `MaximalCompactReductions.lean` 69 →
**496** (22: 15 public, 7 `private`); `spec/AutomorphicFormSetAF16Consumer.lean` (160, new). **42
declarations: 24 public at the pin's visibility, 42 at the dropped-`private` surface.**

**Gates, re-run by the manager after the fixes below.** Edit loops silent (5.4 / 4.4 / 10.4 s); own
builds green and silent (3,877 / 3,905 / 3,823 jobs); `check_port --force` **8 / 1 / 15 ok, `0 mismatch /
0 missing`** at the pin's visibility (24) and **12 / 8 / 22 (42)** at the dropped-`private` surface — both
with `0 mismatch / 0 missing`, and the surface reading is what confirms the six re-transcribed `atPlace`
helpers; `#print axioms` on all eight headlines `[propext, Classical.choice, Quot.sound]`; the probe
exactly eight `sorry` warnings; the consumer **0 errors**; `dedup --within` A **3 clusters** (row 5's and
row 6's `main` against their headlines, and the two namespaces' copies of `isClosed_adelicBorel` — all the
pin's own structure, kept), B and C **0**; `move_dead --dry-run` **0 dead** in all three. Zero warnings
anywhere.

**Plan against actual, after the promotion.** The three modules end at 461 + 221 + 439 = **1,121 lines**,
i.e. **892 appended** over the 229-line skeletons, against `port_plan`'s 877 net — **+1.7 %**; declarations
**36** against the worklist's 35 (+1: `KT`), the six kit helpers having been promoted rather than copied.
Checker: **24** at the pin's visibility and **36** at the dropped-`private` surface (it was 42 before the
promotion; the six copies are gone and their promoted originals are counted in `MaximalCompactFactors`).

**Three deviations adjudicated, and two manager edits.**

1. **The import list was three modules short, and they are accepted.** Order A needed
   `AutomorphicForm/Adelic/MaximalCompactFactors` (row 7's `exists_maximalCompactAway_subset_of_mem_nhds_one`
   lives nowhere else, `MaximalCompactFactors.lean:365`); order B needed
   `AutomorphicForm/Adelic/BruhatEisenstein` (`exists_flat_isInducedSection_family_eq_of_isInducedSection`,
   `BruhatEisenstein.lean:490`); order C needed `NumberTheory/NumberField/TateGlobal/Defs` and
   `…/TateGlobalContinuousIdeleNorm` (row 3's `hgt` cannot even be *stated* without `TateGlobal.ideleNorm`).
   Each is the port home of a lemma the pin's own `S_` file imports; the §4 lists below are corrected.
2. **Six of the "imported" declarations are `private` in the port** (`atPlace`, `glArch_atPlace`,
   `finComponent_atPlace_{self,of_ne}`, `localEmbed_entries_integral`, `atPlace_mem`;
   `MaximalCompactFactors.lean:112–166`). They were re-transcribed verbatim as `private` copies and match
   their pin declarations at the surface reading. §2.1's table is corrected: this is **FR-0133's trap for
   the third set running**, and this pass fell into it by reading the statement match without the
   declaration's visibility — the rule it had just written down.
3. **Seven of the eight headlines were declared inside their helper namespaces**
   (`AutomorphicForm.LocalIntertwining.ContinuousOnBorel.continuousOn_…`) instead of at the pin's names
   (`AutomorphicForm.continuousOn_…`). **No instrument caught it**: `check_port` matches by statement hash,
   and the frontier by last name, so both read green. **Manager's edit**: the seven are now
   `theorem _root_.AutomorphicForm.<pin name>` (one prefix each; the proofs keep their namespace helpers),
   the consumer's four references follow, and the rebuild, the checker (unchanged counts), the axioms, the
   probe and the consumer were all re-run green. Row 8's `AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact`
   was already right. FR-0135 records the gap.
4. **The consumer's order-C zone concludes `k * diagOne t = b * u`, not `diagOne t * k`** — accepted,
   because the Siegel headline decomposes `g * t` with `g` the *integral* factor and `diagOne t` is not
   integral, so the `diagOne` point can only be the right translate; the height bound then collapses to
   `k₁ ≤ hgt b ≤ k₂` since `archHeight (glArch k) = 1` for `k ∈ maximalCompactAt F S`. The order's sketch
   of that zone was loose; the composition is documented in the consumer's header.

5. **The six `atPlace`-kit declarations were promoted, not kept as copies** (manager's edit, after the
   dispatch). They are mathematics — *the adelic matrix agreeing with `g` at `v` and `1` elsewhere*, that
   it is in the maximal compact, and the two component computations — so the rule "promote a private
   helper that is math, duplicate only a tactical one" applies. `MaximalCompactFactors.lean` lost six
   `private` markers and now reads **12 ok / 0 mismatch / 0 missing / 0 own** (`0 own`: the checker's
   statement index already covers them, so no marker row is owed); `MaximalCompactReductions.lean` lost
   its six copies (496 → **439** lines, its surface reading 22 → **16**). `dedup --cross`'s six name
   clusters (`atPlace`, `glArch_atPlace`, `finComponent_atPlace_{self,of_ne}`,
   `localEmbed_entries_integral`, `atPlace_mem`) are **gone**; `move_dead` still reads **0 dead** on all
   four modules; the axioms, the probe and the consumer were re-run green. The edited module is **not
   legacy** — no `PORT_FILES` row, it carries its own six `spec-pin:` wires — so no migration is owed.

**The re-read is exact, and it readies nothing — as forecast.**

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 850 / 347,609 | **842 / 346,331** | −8 / −1,278 ✓ (the eight rows' silo, exact) |
| `needed [literal]` | 863 / 351,084 | **855 / 349,806** | −8 / −1,278 ✓ |
| frontier F | 1,565 / 779,757 | **1,573 / 781,035** | +8 / +1,278 ✓ |
| ready rows, all namespaces | 69 / 17,772 | **61 / 16,494** | −8 / −1,278 |
| ready rows, `AutomorphicForm` | 39 / 11,538 | **31 / 10,260** | −8 / −1,278 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,384 / 1,565) | **PASS** (1,392 `Thm_` sources, 1,573 declared names) | — |

**Nothing readied: the eight rows left and nothing entered**, which is the first time in the column's
history that a landing has a ready-shelf delta of exactly its own consumption. The AF ready shelf is now
**31 rows / 10,260**, and the subject this brief named is closed.

## 6. Risk register

1. **Row 3 is the set's cost and the least "K-flat" of the rows**: 14 declarations, 201 lines, and its
   pin imports the height, the Haar character and the Tate-local zeta definition. Read it as the Siegel-set
   compactness it is: bounded archimedean height + integrality ⇒ a compact set of `b * k`, using SET-AF15's
   decomposition to write the point and the height's own algebra to bound it.
2. **Row 2 is one theorem of 171 lines** with a 24-declaration `AdelicDock.LocalEmbedding` gate: the
   `diagOne` reduction goes through the local embedding of the idele group into the adelic matrices, place
   by place, with `maximalCompactAt F S` collecting the local compact factors. Its `S`-side hypotheses
   (`hg₀` trivial outside `S`) are the ones that make the reduction finite.
3. **Row 1's argument is linear algebra, not analysis**: the `EvalMatrix`/`UniformRank` engine decides that
   a family of translates has finite rank, and the *port's* engine is in another column
   (`RepTheory/TranslateSpan.lean`) at the pin's names. Do not re-prove it; import it. The three
   finiteness properties (`IsArchKFinite`, `IsKfSmooth`, continuity) must be transported through the
   combination, which is the pin's real work.
4. **The `K`-invariance statements are about `maximalCompactAway` and `finiteIntegralGL2` + `IsRowIsometry`,
   not about a single subgroup**: rows 1 and 7 use `maximalCompactAway S` (trivial archimedean part),
   rows 1, 5, 6 use "`k` integral with every `glArch` component a row isometry". Keep the pin's predicates;
   a `K`-invariance stated for the wrong subgroup is a `MISMATCH`.
5. **Binder spelling is the statement** (FR-0123): eight headlines, all with the pin's section variables
   spelled inline, and rows 7 and 8 are single declarations whose names are `AutomorphicForm.…`-level
   (`IsInducedSection.eq_of_eqOn_maximalCompact` sits *inside* the `IsInducedSection` namespace).
6. **No `set_option`**, no top-level `letI` in any of the eight statements, no `import Mathlib`.

## 7. What this set does not do

- **It does not take the Weyl pair** (1,349 + 1,291 = 2,640, measured return zero, deferred for the fourth
  set running) nor **the flat-section indicator row** (1,043, return zero). After this set they are the two
  largest ready blocks in the column, and neither opens work: the honest reading is that the column's
  ready shelf is now *dominated by transcription sets*.
- **It does not take the two `SmoothCuspRealizationAt.not_exists_…` rows** (527 / 513) nor
  `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` (468) nor the three
  `rightTranslate`/`hasDerivAt` rows (433 / 390 / 367): 2,698 silo of the AF ready shelf that this brief
  has not priced, and that the next scoping should price before cutting anything.
- **It does not take the ninth row AF15 readied**, `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum`
  (890): another column's.
- **It does not take the `diagOne` family** (2,098 in four rows), still blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` and the two `LanglandsTunnell`
  rows, nor the `su(2)` string (681 + 755).
- **The 4 withheld rows / 831 remain** the prunable complex-analytic subject.
- **No `Def_` node, no promotion, no migration**; three new modules, all cascade-free.

## Appendix A — the shelf, every row accounted for

### The ready block — **39 rows / 11,538 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `exists_flat_isInducedSection_sum_eq_of_differentiable_family` | 264 | 3 | 5/11 | **SET-AF16** |
| `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 245 | 1 | 2/2 | **SET-AF16** |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` | 227 | 3 | 1/2 | **SET-AF16** |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` | 161 | 2 | 1/4 | **SET-AF16** |
| `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` | 155 | 1 | 1/6 | **SET-AF16** |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` | 116 | 1 | 1/4 | **SET-AF16** |
| `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` | 81 | 2 | 1/1 | **SET-AF16** |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |
| `IsInducedSection.eq_of_eqOn_maximalCompact` | 29 | 1 | 1/5 | **SET-AF16** |

of which **8 rows / 1,278 silo** are this set's.

### The leaves block — **56 rows / 11,461 silo**

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
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
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

of which **0 rows / 0 silo** are this set's.

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py`. **216 of the 218 "imported" lines are genuine; write `KT` (2)** — §2.1.

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `exists_flat_isInducedSection_sum_eq_of_differentiable_family` | 240 | 86 | 154 | 7 |
| `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 225 | 54 | 171 | 2 |
| `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` | 201 | 0 | 201 | 14 |
| `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` | 134 | 78 | 56 | 3 |
| `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` | 136 | 0 | 136 | 4 |
| `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` | 97 | 0 | 97 | 3 |
| `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` | 57 | 0 | 57 | 1 |
| `IsInducedSection_eq_of_eqOn_maximalCompact` | 11 | 0 | 11 | 1 |
| **8 rows** | **1101** | **218** | **883** | **35** |

### `exists_flat_isInducedSection_sum_eq_of_differentiable_family` (order B)

240 declaration lines, 86 imported, **154 to write** in 7 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 91 | 175 | theorem |
| `exists_linearIndependent_subfamily` | 22 | 120 | theorem |
| `isInducedSection_sum` | 15 | 160 | theorem |
| `eq_of_eqOn_of_isOpen` | 11 | 142 | theorem |
| `eq_of_isInducedSection_of_forall_inK` | 7 | 153 | theorem |
| `InK` | 4 | 110 | abbrev |
| `restr` | 4 | 116 | def |

### `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` (order C)

225 declaration lines, 54 imported, **171 to write** in 2 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 143 | 104 | theorem |
| `exists_truncation` | 28 | 76 | theorem |

### `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` (order C)

201 declaration lines, 0 imported, **201 to write** in 14 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 56 | 173 | theorem |
| `hgt_eq_archHeight` | 40 | 133 | theorem |
| `localHeight_archComponent_borel` | 24 | 109 | theorem |
| `norm_snd_eq_one_of_integral` | 18 | 79 | theorem |
| `continuous_hgt` | 14 | 65 | theorem |
| `continuous_borelDiagFst` | 9 | 47 | theorem |
| `continuous_borelDiagSnd` | 9 | 56 | theorem |
| `ideleNorm_eq_prod_of_integral` | 7 | 97 | theorem |
| `isClosed_adelicBorel` | 6 | 31 | theorem |
| `archComponent_glArch_apply` | 5 | 104 | theorem |
| `hgt_mul` | 4 | 40 | theorem |
| `continuous_entry` | 3 | 28 | theorem |
| `hgt` | 3 | 37 | def |
| `hgt_pos` | 3 | 44 | theorem |

### `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` (order A)

134 declaration lines, 78 imported, **56 to write** in 3 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 40 | 123 | theorem |
| `adelicHeight_one'` | 9 | 114 | theorem |
| `adelicHeight_mul_of_mem` | 7 | 107 | theorem |

### `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` (order A)

136 declaration lines, 0 imported, **136 to write** in 4 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 107 | 36 | theorem |
| `solution` | 14 | 143 | theorem |
| `tendsto_units` | 8 | 28 | theorem |
| `isClosed_adelicBorel` | 7 | 21 | theorem |

### `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` (order A)

97 declaration lines, 0 imported, **97 to write** in 3 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 75 | 28 | theorem |
| `solution` | 15 | 103 | theorem |
| `isClosed_adelicBorel` | 7 | 21 | theorem |

### `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` (order A)

57 declaration lines, 0 imported, **57 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 57 | 26 | theorem |

### `IsInducedSection_eq_of_eqOn_maximalCompact` (order A)

11 declaration lines, 0 imported, **11 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 11 | 20 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af15-landed.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family \
  --nodes AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero \
  --nodes AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 \
  --nodes AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection \
  --nodes AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact \
  --nodes AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn \
  --nodes AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family \
  --nodes AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact \
  --json build/af16-advise.json
python3 port_plan.py --json build/af16-advise.json     # 1,278 raw / 1,093 decl / 209 in port / 877 net
python3 build/af-worklist.py exists_flat_isInducedSection_sum_eq_of_differentiable_family \
  exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero \
  exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 \
  exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection \
  continuousOn_of_isInducedSection_of_continuousOn_maximalCompact \
  continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn \
  exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family \
  IsInducedSection_eq_of_eqOn_maximalCompact
python3 build/af14-forecast.py \
  AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family \
  AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero \
  AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 \
  AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection \
  AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact \
  AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn \
  AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family \
  AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact    # the §0.3 forecast
python3 build/af15-imported.py <the eight stems>                # §2.1: which "imported" declarations are public
cd ../../lean
ROWS="<the eight Theorems/ wrappers>"
for pin in Def_AutomorphicForm_InducedSection Def_AutomorphicForm_EtaFamily \
  Def_AutomorphicForm_SmoothAutomorphicFnAt Def_AutomorphicForm_ArchKFinite \
  Def_AutomorphicForm_AdelicMaximalCompact Def_AutomorphicForm_WhittakerCoefficient \
  Def_AutomorphicForm_WindowedSiegelSet Def_NumberField_AdelicHeight Def_NumberField_AdelicHaar \
  Def_NumberField_AdelicLevel Def_AutomorphicForm_RowIsometryInvariance Def_AutomorphicForm_WeylIntertwining; do
  python3 spec/gate_scan.py --pin Definitions/$pin.lean --rows $ROWS
done
python3 spec/gate_scan.py --pin ~/proj/fermats-last-theorem/Definitions/Def_AdelicDock_LocalEmbedding.lean \
  --rows ~/proj/fermats-last-theorem/P2M/Sol/S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean
```

`--rows` takes a **list** in one flag; repeating it silently keeps only the last (AF13's finding, re-hit
at every pass since).

**Forecast on landing** (§0.3): `needed` **850 / 347,609 → 842 / 346,331**, literal
**863 / 351,084 → 855 / 349,806**, frontier **1,565 / 779,757 → 1,573 / 781,035**, ready
**69 / 17,772 → 61 / 16,494**, leaves untouched, **nothing readied**. The re-read must confirm every
figure; the "0 readied" is the expectation, and a non-zero one would mean a row was hidden by a
premise the shelf does not see (the AF14 §2.1 / AF15 §2.1 class).
