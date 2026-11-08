# SET-AF29 — the Whittaker coefficient at `diagOne`

**Status: LANDED 2026-11-07** — one order, one new module, three headlines; §4 is the forecast and
§5 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF27 left. It is the **twenty-ninth** `AutomorphicForm`-serving set.

**3 rows / 2,343 silo / 1,539 net new math lines (`port_plan`) / 95 declaration groups**, of which 164
lines are already in the port and **563 lines are one prelude copied into the two `CuspidalConstituent` files** — the two
files are byte-identical over lines 1–574 except the `namespace` line, and the prelude is
**41 declarations / 484 lines** (the brief first said 36; the agent measured 41).

| row | silo | prem | block | what it says |
|---|---|---:|---|---|
| `AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt` | 913 | 0 | ready | the `diagOne` value of the coefficient of a circle-weight vector is its value at the split torus times the character factor |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent` | **714** | 0 | ready | on a cusp constituent every coefficient of a member is a finite sum of `diagOne` coefficients against a separating family |
| `…_norm_infinitePlace_eq_one_of_isCuspConstituent` | **716** | 0 | ready | the same expansion with the coefficient normalized at the infinite places |

## 0. The read

SET-AF27's post-landing read (see [SET-AF27.md](SET-AF27.md) §6): `needed` **781 / 329,875**, ready
**69 / 22,193**, leaves 208 / 54,145, `AutomorphicForm` demand 291 / 129,719, `--selfcheck` PASS.

## 1. The definition gate — paid by the manager, and it was real

The 913 row's statement names `NumberField.AdeleRing.infiniteUnitsComponent`, a declaration of the
pin's `Definitions/Def_NumberField_IdeleBox.lean` that the port had **not** carried (the pin's
`finitePartUnits` was ported alone, with the header saying so). `gate_scan` over that `Def_` module
reads 1 missing / 4 pin lines for exactly this declaration, and 0 elsewhere.

So this set's manager layer is a `Def_` port, as the instructions require: `infiniteUnitsComponent`
and its `rfl` lemma `val_infiniteUnitsComponent`, at the pin's names and namespace, added to
`NumberTheory/NumberField/FiniteIdeles.lean` (the module that already holds `finitePartUnits` and is
wired to that `Def_` module). The module goes **3 ok → 5 ok / 0 mismatch / 0 missing**, builds in
3.2 s, and its header now records which of the pin's declarations the port carries and why. With it in
place the 913 statement elaborates verbatim: the scaffold is `3 ok / 0 / 0`.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 2,343 |
| declaration lines | 2,266 |
| — duplicate copies | **563** (the two-file prelude) |
| — boilerplate | 77 |
| distinct declaration groups | 95 |
| already in the port (vetted) | 164 |
| **net new math lines** | **1,539** |

19 trusted substitutions, 0 suspect. `twin_scan`: `new` three times.

## 3. Home

**One new module, `Adelic/WhittakerDiagOne.lean`**, above `WhittakerCoefficient` (the coefficient and
its API, SET-AF11), `ArchDerivCasimirComplex` (the split torus and `HasCircleWeightAt`, SET-AF24's
predicate), `ArchWeightCharTransport`, `Cusp/Constituent`, `IsotypicCuspSpace` and `ArchType`. Not an
insertion: `WhittakerCoefficient.lean` is a small API module and these are three developments, one of
them 913 lines.

## 4. Forecast

*(relative to SET-AF27's read; the landing order of AF28/AF30 shifts the absolute figures, not the
deltas)*

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 781 / 329,875 | **778 / 327,532** |
| `needed [literal]` | 793 / 333,340 | **790 / 330,997** |
| frontier F | 1,635 / 797,501 | **1,638 / 799,844** |
| ready block | 69 / 22,193 | **66 / 19,850** (3 rows out; 0 in) |
| leaves block | 208 / 54,145 | **208 / 54,145** |
| `AutomorphicForm` demand | 291 / 129,719 | **288 / 127,376** |
| rows readied | — | **0** |

## 5. The landing (2026-11-07)

`Adelic/WhittakerDiagOne.lean` — **1,865 lines / 97 declarations** (53 for the 913 row, 41 the shared
prelude written once, 3 headlines), one order, one dispatch.

| gate | result |
|---|---|
| `check_port --force` | **97 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | success, 4,103 jobs, 15 s |
| axioms (3 headlines) | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | **2 clusters / 11 lines** — `centralScalar_comm`/`mul_centralScalar_comm` and `archComplexGLAt_mul_g0`/`g0_comm`, both the pin's own per-file duplicates: kept |
| `move_dead` | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF29Consumer.lean` | **0 errors / 0 warnings** (228 lines, three zones) |

**The 714/716 question is answered: the second row is a strict strengthening of the first.** The two
pin proofs differ in exactly one place — the final `refine`, where
`…_norm_infinitePlace_eq_one…` inserts the conjunct `∀ w, ‖ε.1 w‖ = 1` — so in the port the prelude
exists once and the second body is the first with that line changed (144 vs 146 lines). That is the
composition the 563-line dedup bought.

**Two brief errors, corrected here**: the two cusp files' sizes in §0's table were swapped (the
`…_of_isCuspConstituent` row is the 714-line file, the `…_norm_infinitePlace_eq_one` row the 716-line
one), and the prelude has 41 declarations, not 36. Both were caught by the worker against the pin, not
by any instrument.

Deviations (bodies only; statements frozen, 0 mismatch): `InfinitePlace.Completion` is a structure at
v4.34, so sixteen `show … Function.update (1 : InfiniteAdeleRing K) …` sites are respelled with the pi
type (pin 913 lines 73–694), keeping the pin's `attribute [-ext] …Completion.ext`;
`dif_pos`/`if_pos` and friends → `dite_eq_left`/`ite_eq_left`; `Finset.noncommProd`'s new
`Set.Pairwise (Commute on f)` datum handled by `Set.Pairwise.of_forall₂` in `archProd` and by
`noncommProd_induction`/`mul_noncommProd_erase` instead of `Finset.map_noncommProd`; one new import;
`omit [NumberField K] in` where the new `unusedSectionVars` linter fires; the pin's
`set_option linter.unusedVariables false` replaced by explicit references; two private `exists_factor`s
made public; pipeline ids stripped (`E40DCFN` → `DCFN`, `E40IFC` → `IFC`).

## 6. What this set does not do

- **The Whittaker surgery rows** (`exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell`
  398 and `…_sum_mul` 342) share the gateway
  `exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow` — a natural next pair once that gateway is
  measured.
- **The cusp-constituent cluster** (the 458 row's 94-node / 21,595-silo closure) and the
  **Weyl intertwining pair** (blocked on FR-0151) remain open, as SET-AF25 §8 and SET-AF27 §7 record.
