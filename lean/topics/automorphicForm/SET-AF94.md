# SET-AF94 — the Nebentypus of the weight-one lift, and its q-expansion

**Status: LANDED (2026-11-20).** The cut opened as the four `DihedralWeightOne` rows that
SET-AF93's landing readied — the lift's Nebentypus and the Hecke-eigenvalue relation for its
q-expansion — 4 rows / 3,475 silo into three new modules, and settled at **3 rows / 2,622 silo**
when the second Nebentypus row turned out to need an unported definition (below).

| # | order | rows | silo | module | decls (pub/priv) |
|---|---|---|---:|---|---|
| A | the level structure of the lift (prelude) | — | 87 shared | `LanglandsTunnell/WeightOneLiftLevel.lean` (new) | 84 (84/0) |
| B | the Nebentypus of the lift | 1 | 435 | `LanglandsTunnell/WeightOneLiftNebentypus.lean` (new) | 1 public + private |
| C | the lift and the Hecke eigenvalues | 2 | 1,260 + 927 | `LanglandsTunnell/WeightOneLiftQCoeff.lean` (new) | 2 public + private |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af94_read.json
```

| figure | before (AF93 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 452 / 218,086 | **449 / 215,464** (landing read: same) |
| ready rows | 16 / 6,902 | **14 / 4,877** |
| leaves | 74 / 21,398 | 74 / 21,398 |
| withheld (FR-0044 guard) | 4 | 4 |

The delta is the three cut rows (−3 nodes / −2,622 lines); the fourth row's 853 returns to the
shelf with its deferral. (The read after the scaffolds, before the cut, was `448 / 214,611` and
`13 / 4,024` — that is the figure if the fourth row had landed.) **One row becomes ready, 597
silo**: `DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq`
— the converse of the q-expansion row, which the pair (B's Nebentypus + C's q-expansion relation)
unlocks together.

## 1. The cut, and what is not cut

The four rows are one story with two halves: the lift carries a Nebentypus `ε` and, on the
`ℓ + 1`-translate sum that makes it a Hecke eigenfunction, its q-expansion coefficients satisfy the
classical Hecke relation `a_{ℓn} + ε(ℓ) ℓ^{-1} a_{n/ℓ} = ε(ℓ) ℓ^{-1} λ a_n`.

Uncut, and why:

| row | silo | why not |
|---|---:|---|
| `DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul` | 853 | **definition gate**: its pin uses `AdelicSpan φ` (with `AdelicFnCarrier`, `AdelicSpanSubmodule`, the `HasReading` reading of the lift on a span) from `Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean`, and the port does not declare it. Scaffolded, then cut mid-order; the 853 returns to the ready shelf. |
| `LanglandsTunnell.weightOneLift_centralScalar_mul` | 1,134 | **definition gate**: its statement needs `DirichletCharacter.dirichletIdeleChar`, unported (FR-0244). This is the third set it has been deferred from; the definition layer (`Def_DirichletCharacter_DirichletIdeleChar`, 188 lines) is the manager's next groundwork. |
| `WeierstrassCurve.*`, `GaloisRep.*`, `AlgebraicCurve.*`, `ModularCurve.*` | 1,905 | other columns. |
| `AutomorphicForm.integral_mul_conj_unipotent_…`, `NumberField.Idele.exists_setLIntegral_indicator_…` | 324 | the adelic tails, still the manager's hub-edit work. |

## 2. The homes and the manager's layer

| module | direction | manager's work |
|---|---|---|
| `LanglandsTunnell/WeightOneLiftLevel.lean` | above `WeightOneLiftAdelic` (it imports `isReal_rat_infinitePlace`, `ratArchHom`, `glFin_globalPoints_apply` from it), `DihedralWeightOneLift`, `AdelicLevel/{Projections,Level,IdealBall}`, `AdelicDock/LocalEmbedding`, `ModularForms/HeckeNebentypusExistence` | the 84 statements + wire; `namespace DihedralWeightOne` |
| `LanglandsTunnell/WeightOneLiftNebentypus.lean` | + the prelude | the two row statements; the two statement-side gaps (`Int𝔸`, `AdelicSpan`) left to the worker |
| `LanglandsTunnell/WeightOneLiftQCoeff.lean` | + the prelude | the two row statements |

**The prelude is a port-once, and this time the pin's own names split two ways.** Of the 87
declarations the four pins share, **3 are statement-identical to declarations already in
`WeightOneLiftAdelic`** and are imported; the other **84 are written here**. Conversely
`archPart`/`glFin_archPart`/`ratArch_archPart` are *not* the AF93 engine's declarations of the same
names — there the pin's `archPart` is `𝔾 → 𝔾` on the adeles, here it is `GL₂(ℚ) → …` — so the port
follows the pin's own rule for a same-name pair: **two statements, two namespaces**
(`LanglandsTunnell.DetIntegral.archPart` and `DihedralWeightOne.archPart`), and the new module does
not open `DetIntegral`, which is what keeps `archPart` resolving to the pin's local declaration.

**Scaffold facts.** `check_port` read `83 ok, 1 mismatch` on the prelude's first pass, not 84: the
pin writes `repZ_eq_map`'s statement as `HeckeCosets.repZ p i = …`, qualifying its own declaration
through the search-stage namespace it lives in, and flattening that namespace away changed the
statement's text (see FR-0246). The fix is the pin's own line plus a `private` alias for the
qualifier — the statement then hashes to the pin's and the checker reads 84 ok with no metadata.
`check_port` reads `2 ok` on the q-expansion module (the two rows) and `complete` on the audit; the prelude's 84 declarations all match *private* pin declarations, so the checker's
`N ok` there is the FR-0242 case and the faithfulness test is the `statement_db` hash diff (84/84
identical). The Nebentypus scaffold carried four *statement-side* gaps (`Int𝔸`, `AdelicSpan`) that the
worker closes first — the statements themselves are the pin's.

## 3. The orders

`lean/tmp/af94/WO.md` (untracked): A the prelude, B the Nebentypus pair, C the q-expansion pair.
Disjoint files; A's `.olean` was built before B and C were dispatched.

## 4. The gates

As SET-AF89–AF93 §5, with the added instruction that a non-zero `move_dead` means the declarations
are dead in the pin too: delete them, register the deferred surface in the header, and report the
names for `CARRY-FORWARD.md` (the AF93 precedent).

## 5. The landing

| order | module | lines | decls (pub/priv) | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| C | `WeightOneLiftQCoeff.lean` | **320** | 7 (2/5) | **2 ok / 0 / 0** | clean | **0** | 0 / 0 | 10,000 / 5,000 |
| A | `WeightOneLiftLevel.lean` | **1,150** | 87 (84 pub + 3 priv) | **84 ok / 0 / 0** | clean (12 probed) | **0** | 0 / 0 | 100,000 / 50,000 |
| B | `WeightOneLiftNebentypus.lean` | **506** | 19 (19/0) | **19 ok / 0 / 0** | clean (4 probed) | **0** | 0 / 0 | 16,000 / 8,000 |

**The set: three new modules, 1,976 lines, 113 declarations, 0 `sorry`, no linter option of their
own, 105 `ok` with 0 mismatch / 0 missing / 0 own, `dedup` 0 clusters everywhere, `move_dead` 0/0
everywhere, and the three rows plus the prelude's twelve largest declarations on
`[propext, Classical.choice, Quot.sound]`.** It consumed **3 rows / 2,622 silo** and readied one row
(**597 silo**, the converse of the q-expansion relation), leaving `needed` at **449 / 215,464**.

**Gate 2 reads red on the prelude, by construction.** `scaffold_audit`'s wire is every *public*
declaration of the four whole `S_` files (33 rows), while the prelude transcribes only their *shared
private* part; 11 of the rows it calls `MISSING` are declared by the Nebentypus module (which imports
the prelude), the rest sit in that module's import closure or belong to the deferred pin. A
per-module audit has no view across sibling modules, so `complete` is unattainable for a prelude
module wired to whole multi-public pins — the reading is recorded in the module header and here, and
the two rows' modules both read `complete`.

**C's deferral is not all dead code.** Sixteen pin declarations were dropped for `0 / 0`; thirteen
are dead in their own pin too and one is a duplicate, but **three are alive in pin 2** (`det_val_mapGL`,
`isLift1_weightOneLift`, and the `Ψ`-general `sum_apply_eq_slash`) and are orphaned only because the
prelude took pin 1's *specialised* `sum_apply_eq_slash` instead of pin 2's general form. The port
therefore holds the special case and not the general one — the direction the playbook forbids when
the general does not cite the special — and it is registered in `CARRY-FORWARD.md` with its price
(~40–60 lines, no surviving statement changes). C also reports that the two rows are independent
(row 1 takes `heig` as a hypothesis), which is why pin 2's `solution` body needed a `ring`
rebracketing against the prelude's pin-1 form.
