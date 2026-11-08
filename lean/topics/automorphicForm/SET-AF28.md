# SET-AF28 — the left Casimir acting on factorizable test functions

**Status: LANDED 2026-11-07** — one order, one new module, three headlines; §5 is the forecast and
§6 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF27 left. It is the **twenty-eighth** `AutomorphicForm`-serving set.

**3 rows / 1,535 silo / 1,338 net new math lines (`port_plan`) / 95 declaration groups**, of which 52
lines are already in the port — and 43 of the pin's lines are one prelude copied into the real and the
complex file.

| row (`AutomorphicForm.` dropped) | silo | prem | block | what it says |
|---|---|---:|---|---|
| `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite` | 472 | 0 | ready | the real-place Casimir `β = −¼ L.H(L.H α) − ½ L.H α + L.E(L.Fm α)` of a factorizable, arch-bi-finite, level-`N`-invariant `α` is again factorizable and arch-bi-finite; `rightConv · β` is the Casimir applied to the convolution; the level and arch-cut memberships are preserved |
| `isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite` | 651 | 0 | ready | the complex mirror: the four-term `H`/`iH`/`E`/`F⁻` Casimir, its conjugate `βb`, and `l.foldr L α` factorizable for every list of directions |
| `exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul` | 412 | 0 | ready | an arch-cut eigenvector of `rightConv · f` is an eigenvector of `rightConv · f'` for some arch-bi-finite factorizable `f'` |

## 0. The read (SET-AF27's post-landing read)

| figure | value |
|---|---|
| `needed [F terminal]` | **781 nodes / 329,875 lines** |
| `needed [literal]` | 793 / 333,340 |
| frontier F | 1,635 / 797,501 |
| ready block | **69 / 22,193** — 41 `AutomorphicForm` / 16,054 |
| leaves block | 208 / 54,145 |
| `AutomorphicForm` demand | 291 / 129,719 |
| `MeasureTheory` demand | 14 / 1,981 |
| withheld | 4 (prunable) |
| `--selfcheck` | PASS (1,454 sources / 1,635 names) |

## 1. Why this cut

All three rows have **zero unported premises** — they are on the ready block and their closures are
complete — and they are one subject: the archimedean Casimir's action on the test-function side of
right convolution, in the real and the complex place, plus the eigenvalue transfer that the
archimedean type theory consumes. The shelf's return column is empty at this point (best row 576 →
552), so the cut is on subject and completeness; the chain the three rows belong to
(`isFactorizableTestFn_leftCasimir…` → the cut-weight block) is what the next sets will consume.

The two big files are mirrors: `port_plan` prices **43 duplicated lines** and a shared 5-declaration
block (`equivariant_mem_iSup_typeSubmodule`, `rightConv_mem_levelInvariantSubmodule_of_left_inv`,
`rowIsometryInclAt₀_injective`, `Tens`, `rT_mul`), written once.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 1,535 |
| declaration lines | 1,433 |
| — duplicate copies | 43 |
| — boilerplate | 102 |
| distinct declaration groups | 95 |
| already in the port (vetted) | 52 |
| **net new math lines** | **1,338** |

7 trusted substitutions, 2 suspect (the parser's type-only `def` matches — `c10b`, `Ld`; read the
bodies). No definition gate (`gate_scan` over `ProductionPinsGeneral`, `CuspidalConstituent`,
`ArchDerivCasimir{,Complex}`, `FactorizableTestFn`, `RightConvolution`: 0 missing). `twin_scan`:
`new` three times.

## 3. Home

**One new module, `Adelic/LeftCasimirTestFn.lean`**, above `ArchDerivCasimir{,Complex}`,
`ArchCasimir{,Complex}`, `FactorizableTestFn`, `RightConvolution`, `ProductionPinsGeneral` and
`Cusp/Constituent`. Not an insertion: the two Casimir modules are 1,638 / 2,124 lines with dependents,
and this is a distinct role — "the Casimir on the test-function side" against "the Casimir on
automorphic functions". Cascade-free.

## 4. The cut and the gates

One order, against the checker-green scaffold
(**3 ok / 0 mismatch / 0 missing**). Three headlines, in the order real → complex → eigenvalue.

## 5. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 781 / 329,875 | **778 / 328,340** |
| `needed [literal]` | 793 / 333,340 | **790 / 331,805** |
| frontier F | 1,635 / 797,501 | **1,638 / 799,036** |
| ready block | 69 / 22,193 | **66 / 20,658** (3 rows out; 0 in) |
| leaves block | 208 / 54,145 | **208 / 54,145** |
| `AutomorphicForm` demand | 291 / 129,719 | **288 / 128,184** |
| rows readied | — | **0** |

## 6. The landing (2026-11-07)

`Adelic/LeftCasimirTestFn.lean` — **1,174 lines / 81 declarations** (14 shared + 21 real + 43 complex
+ 3 headlines), one order, one dispatch.

| gate | result |
|---|---|
| `check_port --force` | **81 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | success, 4,103 jobs, 8.7 s |
| axioms (3 headlines) | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | 81 declarations, **0 clusters / 0 removable** |
| `move_dead` | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF28Consumer.lean` | **0 errors / 0 warnings** (146 lines) |

**The cross-file block was written once** (`LeftCasimirShared`, 14 declarations / 94 lines incl.
proofs) and both places reuse it — `port_plan`'s 43 line estimate came out as the same nine
declarations without proofs. The complex row is a near-verbatim mirror of the real one plus
`leftCas`/`leftCasBar`/`W10`/`c10`/`c10b`, the ten-term linearity, eight `archDel*/archCasimir*`
leaves and the `OpPkg` generalisation of the real membership pair.

**The one substantive route change, and it is a win.** The eigenvalue headline (pin 412) does **not**
replay the pin's 290-line `sandwich`; the port's generic
`ArchApproxIdentity.integral_mul_dconvWith` (`RepTheory/ConvolutionLimit.lean`) *is* that sandwich's
conclusion, so the headline is `ArchCutReproducer`'s reproducing kernel +
`ArchApproximation`'s kernel-bi-finiteness row + that identity. Consequence: **the pin needed
`set_option maxHeartbeats 3200000` for its `sandwich`, and the port fits the default 200,000-heartbeat
budget** — so the module carries no `set_option` at all beyond the project's `autoImplicit false`.

**`ArchApproximation`'s projector headline is not usable here**, contrary to the order's hint:
`exists_rightConv_eq_of_archCutProjector` assumes its input `f` is already arch-bi-finite — exactly
what this headline must produce — so feeding it would be circular. Nor would `ArchCutProjector` alone
suffice: the headline needs the reproducing kernel (`ArchCutReproducer`), the translate-span
finite-dimensionality (`ArchCutSpan`) and `ConvolutionLimit`'s sandwich.

Deviations (bodies only, statements byte-identical): the pin's in-proof `attribute [local instance]`
and `letI`/`haveI := AdelicHaar.glBorel …` blocks became four file-level `attribute [local instance]`
lines plus `open scoped Classical ArchInfra` (the `haveILetI` linter rejects the in-proof form);
`μK := Measure.haarMeasure …` became `ArchInfra.muK` with its scoped instances; nine new imports,
reported.

## 7. What this set does not do

- **The cut-weight block** (`CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt`
  1,416 and `iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar` 929) is one premise behind
  `exists_eq_rightConv_of_mem_cut`, whose own closure is 94 nodes / 21,595 silo — a chain head, not a
  gate.
- **The Weyl intertwining pair** stays blocked on the two statement-spelling decisions of FR-0151.
- The `isCuspConstituent` cluster and the Siegel/Petersson blocks remain as SET-AF25 §8 lists them.
