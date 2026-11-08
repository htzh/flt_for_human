# SET-AF21 — the rational unipotent quotient measures: box sheets, Haar-quotient integrals, and the comparison identity

**Status: LANDED 2026-11-07** — four modules, eight headlines, every gate green; §9 records the
landing and the re-read (exact against §7's forecast, with one arithmetic slip of mine corrected
there: the four AF rows are 1,254 silo, not 1,354). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF20 just landed (§4.3 of that brief). It is the **twenty-first** `AutomorphicForm`-serving set
and it is the continuation SET-AF20 §9 named: the same two subgroups, now with their **quotient**
measures compared.

The set is **8 rows / 2,352 silo / 1,342 net new math lines (`port_plan`), ≈1,166 lines in 101
declarations to write (`af-worklist`)**, in four orders over two new modules and one insertion.

| order | rows | silo | to write | decls | home |
|---|---:|---:|---:|---:|---|
| **A** — coset representatives cut a fundamental domain | 2 | 176 | 31 | 5 | new `MeasureTheory/IsFundamentalDomainCosets.lean` |
| **B** — the box sheets and the Bruhat decomposition of the Borel | 3 | 888 | 263 | 26 | new `AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean` |
| **C** — the Haar-quotient integral calculus | 2 | 922 | 714 | 53 | **insertion** into `MeasureTheory/HaarQuotient.lean` |
| **D** — the two quotient integrals agree | 1 | 366 | 158 | 17 | new `AutomorphicForm/Adelic/RationalUnipotentQuotientIntegral.lean` |
| | **8** | **2,352** | **1,166** | **101** | |

D consumes B and C (and A, through D's own premises); A, B and C are independent of each other and
touch disjoint files.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af21.json
python3 frontier.py --selfcheck        # PASS (1,422 Thm_ sources, 1,603 names)
```

The read is SET-AF20 §4.3's post-landing read: `needed` **813 / 340,699**, frontier 1,603 / 786,677,
ready 62 / 20,332, leaves 224 / 57,377, `AutomorphicForm` 34 / 14,193 ready and 56 / 11,461 leaves.
No `--unport` correction.

**How these eight rows sit on it.** Two of them are shelf leaves
(`isFundamentalDomain_boxSheet_rationalTorusUnipotent` 440, `…_rationalCentreUnipotent` 340); the
other six are **not on the shelf at all** — they are the rows one to three edges behind those two,
found by the gateway query (`tools/deps/build/af20-gates.py`) rather than by the shelf listing. The
set is the recipe's SET-10 shape again, one level deeper than AF20's: `366` needs `{440, 340, 302,
108, 99, 77}`, `302` needs `620`, and the whole block is one subject.

## 1. The rows

| order | row (namespace dropped) | silo | to write | decls | what it states |
|---|---|---:|---:|---:|---|
| A | `MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives` | 77 | 10 | 2 | `Γ₂ ≤ Γ₁` and coset reps `R` cut a `Γ₁`-domain into a `Γ₂`-domain `⋃ i, (R i)⁻¹ • 𝓕` |
| A | `…setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives` | 99 | 21 | 3 | integration over that union is the `∑'` over the reps (both `∫⁻` and `∫`, with integrability) |
| B | `AutomorphicForm.existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 34 | 4 | a Borel element has a **unique** diagonal part modulo scalars · unipotent |
| B | `…isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 135 | 13 | the box read inside `rationalTorusUnipotent` is a fundamental domain for `B = borelSubgroup.map globalPoints` |
| B | `…isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 94 | 9 | the same for the centre-unipotent `P` |
| C | `HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out` | 620 | 582 | 45 | `∫_S f = ∫_quotient (∫_T f (· * q.out))` for `Γ ≤ H`, `ℝ≥0∞` |
| C | `HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out` | 302 | 132 | 8 | the `ℂ` form with its two integrability conclusions |
| D | `…integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient` | 366 | 158 | 17 | the two rational quotient integrals agree after summing over `Kˣ` |

**Premise audit.** Every unported premise of the eight is inside the set (that is how the block was
found). Everything else is ported: the `Def_` layer (`RationalTorusUnipotentQuotient`,
`BorelSubgroup`, `HaarQuotient`, `NumberField/AdelicLevel`), AF20's three modules, and
`PeterssonSlabPairing.Γp` (the pin's `ratP` abbrev, ported). No definition gate: `gate_scan` over
the eight wrappers' `Def_` closure is 0 missing.

**`twin_scan` on the eight: `new` eight times** before the scaffolding (no port statement twin), and
`TWIN-public` against the skeletons afterwards.

## 2. The price, and the composition payoff

`port_plan` over the eight: 2,352 raw / 2,187 declaration lines / **61 duplicate copies** / 146
boilerplate / **183 already in the port** → **1,342 net new math lines**; `af-worklist` (which drops
what is *reusable* declaration by declaration) says **739 of the 1,160 AF declaration lines are
already there** — this is the column's most composition-heavy set since AF8/AF9, and it is
composed of **the modules SET-AF20 just wrote**: `ratCentralHom`, `ratCentralHom_apply_entry`,
`ratCentralHom_comm`, `ratCentralHom_eq_centralScalar`, `continuous_toAdelicUnipotent`,
`CentreUnipotent.{sheet, continuous_sheet, measurable_sheet, sheet_entries, exists_eq,
rationalCentreUnipotentHaar_eq}`.

- **substitute** (import, do not re-prove): 37 declarations, 183 lines — the chart dictionary above,
  plus `AutomorphicForm.unipotentGL2_mul_diagHom`, `torus_mul`, `torus_one`, `torus_inv`,
  `mem_torus`/`mem_unipotent` where the statements coincide, and `PeterssonSlabPairing.Γp` for the
  pin's `ratP`.
- **port once**: the pin's own duplication, 61 lines — the two box-sheet files repeat the chart
  prelude (`ratCentralHom` 6, `sheet` 4, `sheet_coe` 2, `continuous_sheet` 2, `measurable_sheet` 1,
  `sheet_entries` 10, `exists_eq` 19, `rationalCentreUnipotentHaar_eq` 2, `continuous_toAdelicUnipotent`
  2, `ratCentralHom_apply_entry` 6, `ratCentralHom_comm` 13, `ratCentralHom_eq_centralScalar` 6 …).
  All of it is imported, none of it restated.
- **generalise**: `equalDiagBorel` (21 lines, both box-sheet files) → `WindowedSiegel.rowIsometrySubgroup`,
  `diagHom` → `ratCentralHom`, `ratP` → `Γp`. No same-name pair inside the set.
- **drags**: `A` has no prelude (5 declarations, two of which are the ones the pin re-proves in the
  box-sheet files); `C`'s 582-line row is **one declaration with a private prelude of 44** — the
  largest single-engine row of the column since the arch-Casimir algebra.

## 3. Homes, and one consolidation the column declines for now

```
MeasureTheory/IsFundamentalDomainCosets.lean          (order A: generic, over any group action)
        ▲                                   ▲
        │                                   │
MeasureTheory/HaarQuotient.lean  (order C: the supplement module AF20 created, +2 theorems)
        ▲
AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean  (order B: imports AF20's chart module)
        ▲
AutomorphicForm/Adelic/RationalUnipotentQuotientIntegral.lean  (order D)
```

- **A is a mathlib supplement** (statement names only mathlib objects, generic over `G`, `X`, `ι`):
  home `MeasureTheory/`, with the mathlib-first negative recorded in the header — mathlib's
  `FundamentalDomain.lean` has no coset-representative statement.
- **C is an insertion**, not a new module: `MeasureTheory/HaarQuotient.lean` is the module AF20
  created for the pin's `Def_HaarQuotient`, it is 0-importer, and these two theorems are the
  integral calculus *of that definition*. The insertion edits a 100-line module and re-checks it.
- **B imports `RationalUnipotentHaar.lean`** for the chart dictionary rather than restating it. The
  chart is arguably a subject of its own (`RationalUnipotentChart.lean` between the definitions and
  both users), but moving it would move the checker's rows with it: a declaration lives in the
  module whose `spec-pin:` wire covers its pin source, so a chart module would have to carry the two
  `isHaarMeasure` `S_` files' wires while the Haar module lost them. That is a refactor with a real
  cost and no mathematical gain, and AF21 is a *consumer* of the chart, not its author — recorded
  here so the next set that needs the chart knows the price. **Do not restate the chart in B.**
- The pin's `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` is homed in
  B, not in `Adelic/BorelSubgroup.lean`: its subject is the Borel, but its only consumer is this
  block, and `BorelSubgroup.lean` is a hub (7 in-tree importers).

## 4. Ground prep (landed by the manager)

Headers, imports, wires and the eight statements are in place, each stated verbatim from its
wrapper with a `sorry` body, and every module is checker-green at its statement surface:

| module | checker at scaffolding |
|---|---:|
| `MeasureTheory/IsFundamentalDomainCosets.lean` | **2 ok** |
| `MeasureTheory/HaarQuotient.lean` (3 defs + 2 new) | **5 ok** |
| `AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean` | **3 ok** |
| `AutomorphicForm/Adelic/RationalUnipotentQuotientIntegral.lean` | **1 ok** |

**Two statement-fidelity traps were met and are now fixed in the skeletons**, worth carrying:
(i) `HaarQuotient.measure` must be **qualified** in the two `C` statements — the pin's wrapper
states them outside the namespace and writes `HaarQuotient.measure`, and the checker's hash is
text-sensitive to that qualification (this is what `MISMATCH` reported on the first pass);
(ii) a docstring containing `centre-/torus-` **closes the block comment** (`-/` inside `/- … -/`), so
the header must not write a hyphen immediately before a slash.

## 5. The cut, and what each order writes

| order | file | writes | the route |
|---|---|---:|---|
| A | `MeasureTheory/IsFundamentalDomainCosets.lean` | 31 | the pin's two generic lemmas: the `Γ₂`-domain by `NullMeasurableSet.iUnion` + `ae_covers` from the coset decomposition; the integral identity by unfolding the `Γ₁`-integral over the disjoint union and Tonelli over the countable index |
| B | `AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean` | 263 | the Bruhat decomposition of the Borel (unique diagonal part), then the box as `T = toAdelicUnipotent '' adelicBox` and the four conjuncts of each box-sheet statement |
| C | `MeasureTheory/HaarQuotient.lean` | 714 | the pin's 44-declaration private engine: the `density`-weighted measure pushed along `Quotient.mk''`, the `∫_S = ∫_q ∫_T` computation, then the `ℂ` form with integrability |
| D | `AutomorphicForm/Adelic/RationalUnipotentQuotientIntegral.lean` | 158 | three applications of the box sheets and of the Haar-quotient integrals, glued by `tsum` over `Kˣ` |

## 6. Gates, per order

As in SET-AF14–AF20 and the recipe §6, unchanged: `check_port --force` **0 mismatch / 0 missing**
with every pin-public declaration `ok` (the surface gate: keep the pin's helpers public — the pin
states them public); `#print axioms` on each headline `[propext, Classical.choice, Quot.sound]`; the
module's own `lake build` under `flock`/`timeout`, silent, zero warnings; `dedup.py --within` and
`move_dead.py --dry-run`; no `sorry`/`set_option`/`import Mathlib`; a `spec/` consumer zone per order
with a real composition.

## 7. Forecast

The eight rows' silo is 2,352, and every one of them is in the D–S target's demand, so on landing:

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 813 / 340,699 | **805 / 338,347** |
| `needed [literal]` | 825 / 344,164 | **817 / 341,812** |
| frontier F | 1,603 / 786,677 | **1,611 / 789,029** |
| `AutomorphicForm` demand | 318 / 139,306 | **314 / 138,052** (the four AF rows, 1,254 silo; 176 of the set's silo is `MeasureTheory`, 922 `HaarQuotient`) |
| leaves | 224 / 57,377 | **218 / 55,693** (the six shelf leaves it takes) |
| ready rows | 62 / 20,332 | **62 / 20,332** (nothing readied, as forecast) |

**Rows it readies**: none of the eight has a consumer whose only unported premise is one of them
(the next block up is `exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa`
453, which needs `616` + `252` + `170` + `134` too). The set's payoff is the **story completed** —
with it, the rational-unipotent quotient measures are fully available (definition, Haar-ness,
closedness, fundamental domains, quotient integrals) — and `HaarQuotient`'s own block
(`lintegral_eq_lintegral_lintegral_mul_out` 616), which is AF22's natural first row.

## 8. What this set does not do

- **`HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out`** (616) and
  `NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa` (252): the
  `lintegral` sibling and the Iwasawa comparison — different subjects, one of them AF22's.
- **The arch-approximation gate leaves** (70 → 1,445, 71 → 1,361, 98 → 1,131): still the column's
  largest readiness event, and still unbuilt.
- Nothing is legacy, nothing is migrated, no tree build.

## Appendix — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af21.json
python3 build/af-return.py build/shelf-af21.json AutomorphicForm. 1
python3 build/af20-gates.py AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
python3 port_advise.py --nodes <each of the eight rows> --json build/af21-advise.json
python3 port_plan.py --json build/af21-advise.json
python3 build/af-worklist.py --prefix S_HaarQuotient_ setLIntegral_eq_lintegral_setLIntegral_mul_out integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
```

## 9. The landing (2026-11-07)

Four orders, one dispatch, every gate green on the landed tree.

| order | module | lines | decls | checker | build |
|---|---|---:|---:|---|---|
| A | `MeasureTheory/IsFundamentalDomainCosets.lean` (new) | 216 | 6 | **6 ok** / 0 / 0 / 0 own | silent, 5.1 s |
| B | `AutomorphicForm/Adelic/RationalUnipotentBoxSheet.lean` (new) | 720 | 28 | **28 ok** / 0 / 0 / 0 own | silent, 8.1 s |
| C | `MeasureTheory/HaarQuotient.lean` (insertion) | 100 → 955 | 3 + 47 | **5 ok** / 0 / 0 / 0 own | silent, 7.1 s |
| D | `…/AutomorphicForm/Adelic/RationalUnipotentQuotientIntegral.lean` (new) | 317 | 13 | **13 ok** / 0 / 0 / 0 own | silent, 6.9 s |
| | | **2,208** | **52 ok** | 0 mismatch / 0 missing | |

**All eight headlines** are on `[propext, Classical.choice, Quot.sound]`
(`lean/tmp/ax_af21.lean`, one block over the four modules), no `sorryAx`. `dedup --within` is 0
clusters on A, B and D and **1 on C** — the pin's own `d2` (63 lines, `private`) restating the
`ℝ≥0∞` headline (15 lines): its `solution` is a one-line application of `d2`, so the pair is the
pin's duplication and stays, with this reason. `move_dead --dry-run` is **0 dead on all four** (C
dropped two pin helpers that are dead in the pin too: `core`, an alias of
`lintegral_eq_lintegral_measure`, and `measurable_lintegral_mul_out`, whose public form is a *third*
`Thm_` wrapper this set does not wire). Four consumer zones —
`spec/IsFundamentalDomainCosetsConsumer.lean`, `…AF21BConsumer.lean`, `…AF21DConsumer.lean`,
`…HaarQuotientIntegralConsumer.lean` — at **0 errors**.

**The re-read, exact against §7.**

| figure | before | after | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 813 / 340,699 | **805 / 338,347** | 805 / 338,347 ✓ |
| `needed [literal]` | 825 / 344,164 | **817 / 341,812** | 817 / 341,812 ✓ |
| frontier F | 1,603 / 786,677 | **1,611 / 789,029** | 1,611 / 789,029 ✓ |
| ready rows | 62 / 20,332 | **62 / 20,332** | unchanged ✓ |
| leaves | 224 / 57,377 | **218 / 55,693** | −6 rows ✓ |
| `AutomorphicForm` demand | 318 / 139,306 | **314 / 138,052** | −4 / −1,254 ✓ |
| `MeasureTheory` demand | 17 / 2,296 | **15 / 2,120** | −2 / −176 ✓ |
| `HaarQuotient` demand | 7 / 2,245 | **5 / 1,323** | −2 / −922 ✓ |
| `--selfcheck` | PASS | **PASS** (1,430 sources / 1,611 names) | — |

**A transient worth recording.** The first `--selfcheck` after the modules were green read
**INCONSISTENT**: two `HaarQuotient` source nodes were "not covered by the name scan", because the
scan ran while order C's file was still being written (`declared names` 1,609 at that moment,
1,611 a minute later). Re-running both instruments on the settled tree gives PASS. The recipe's
"re-run §0 after the landing" is about exactly this: a read taken mid-write is a read of a tree that
never existed.

**Deviations, by class** (each order's report carries the detail):

* **A** (2): one new import (`Integral.DominatedConvergence`, for `integral_tsum`); the pin's
  deprecated `AEMeasurable.ennreal_tsum` inlined rather than costing a second heavy import, and the
  pin's two-step summability leaf replaced by v4.34's `tsum_enorm_ne_top_iff_summable_norm`.
* **B** (5): the chart dictionary is *imported* (not restated) and one `open TorusUnipotent` is what
  makes the three statements that spell `diagHom` unqualified hash-match; `haveI` → `have`; and the
  two box-sheet proofs are one argument at two subgroups. **One of my own brief's claims was false
  and the order's report caught it**: I had accepted `port_advise`'s shape-tier suggestion that the
  pin's `equalDiagBorel` *is* `WindowedSiegel.rowIsometrySubgroup`; it is not — the port's subgroup
  needs `[NormedField K]` and admits rotations with `1 0 ≠ 0`, while the pin's is the entry condition
  `1 0 = 0 ∧ 0 0 = 1 1` over a bare `[Field K]`, so the headline has no norm instance and cannot even
  mention it. `equalDiagBorel` is ported at its own name. That is the `shape`-tier false positive of
  FR-0111 measured again, on a *scoping* claim rather than on a port copy: a substitution suggestion
  is a hypothesis about the mathematics, not a fact.
* **C** (2): one new import (`Measure.Haar.Unique`, for `haarScalarFactor`); the pin's unused
  `hΓ : Γ ≤ H` dropped from the *private* helpers that never use it (private, so no statement
  drifts).
* **D** (2): one new import (`RationalUnipotentClosed`, which no module on the import path carried);
  the pin's `set_option linter.deprecated false` dropped because the deprecated
  `Measurable.ennreal_tsum` is *re-derived inline* (three lines) — its suggested replacement does
  not exist in this mathlib checkout (FR-0146) — which collapses the pin's 37-line `Finset`-exhaustion
  proof to one line. A and C met the same deprecation and worked around it the same way.

**Two findings that are not about Lean.** (i) A statement that mentions a declaration from its own
namespace must be written **qualified exactly as the wrapper does** (`HaarQuotient.measure`), or the
checker reports `MISMATCH` on texts that print identically — FR-0145. (ii) An unused hypothesis must
be *referenced* in the proof, not renamed to `_hle`: the checker normalises a binder's *kind*, not
its *name* (measured on order A's module, reverted) — FR-0145's symptom 3.
