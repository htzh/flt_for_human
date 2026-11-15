# SET-AF82 — the automorphic content bound, and three rows of the unipotent-Haar family

**Status: SCAFFOLDED-BY-WORKER, DISPATCHED (2026-11-14).** Read off the same shelf as SET-AF81. These four
rows are the ready block's `AutomorphicForm` residue: one heavy leaf-shaped row (a 17-declaration private
engine behind a single headline) and a trio of small public lemmas of one subject.

**4 rows / 672 silo** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | new `AutomorphicForm/Adelic/ContentBound` |
| **B1** | `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1/1 | new `AutomorphicForm/Adelic/RationalCentreHaar` |
| **B2** | `AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup` | 104 | 1/15 | same module |
| **B3** | `AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf` | 56 | 3/5 | same module |

## 0. The read

Identical to [SET-AF81 §0](SET-AF81.md): `needed` **582 / 262,734**, ready **21 / 4,877**, leaves
**140 / 36,013**; `--selfcheck` fails only on MD-005, which none of these rows cites.

## 1. The rows

- **A** — the content bound: a finite set of adelic points realises every value of the finite content map up
  to the bound `max ⋅ contentHomFin² ≤ …`. The pin's file is 333 lines with a **single public declaration**
  and a 17-declaration private engine, so this order is an engine transcription plus one headline.
- **B1** — the `L¹` integral of the rational-centre unipotent Haar against `heckeGen ⋅ centralScalar`
  conjugated; **B2** — the constant term of the adelic box is multiplicative on the global points of the
  Borel subgroup; **B3** — the isotypic cuspidal submodule is `⊥` when the production pins vanish. Three
  small public lemmas of one subject (the rational centre / constant-term bookkeeping of the automorphic
  representation), 19 public declarations in all, and `B2` has leverage 15 across the project, `B3` 5.

## 1.1 The shelf

Quoted whole in [SET-AF81 §1.1](SET-AF81.md) — the same 21-row block, of which this set cuts four and
leaves fifteen deferred. Its top deferred rows are the ones behind missing definition layers
(`EisensteinGeneral.Piece` 890 on `AutomorphicForm/Adelic/WeilIntertwining`; the two `WeierstrassCurve`
rows 697 / 599 on `IsCharTwoJNeZeroNF` / `IsCharThreeJNeZeroNF`) and the four that need their own topic
(`GaloisRep.exists_isSemisimpleRepresentation…` 495; `MeasureTheory.exists_integral_conj…` 200;
`ValuationSubring.exists_aeval_div…` 138; `NumberField.TateGlobal.exists_isCompact_forall_eq_principal…
120`).

## 2. The price and the homes

The joint price with SET-AF81 is in [SET-AF81 §2](SET-AF81.md): 1,292 raw `S_` lines, **564 net new**,
**586 declaration lines already in the port** (369 byte-identical substitutions), no `Def_` work. This
set's own share is the larger part of it — row A's engine is 18 declarations of pin, and B's trio is 19
public statements over three `S_` files sharing the `AdelicLevel`/`AdelicHaar` vocabulary.

| order | module | rows | content | public decls |
|---|---|---|---:|---:|
| `WORKORDER-AF82A` | `AutomorphicForm/Adelic/ContentBound.lean` (new) | A | ≈280 + 17 private | 1 |
| `WORKORDER-AF82B` | `AutomorphicForm/Adelic/RationalCentreHaar.lean` (new) | B1–B3 | ≈240 | 19 |

**One home question the order leaves open, deliberately.** The three rows of order B share a subject but
each may pull a different `Def_` prefix; the order says to stop and report *before* splitting the module if
that happens. A single module with three `spec-pin:` lines is the intended shape (the pin keeps them in
three files of one family), and splitting is the fallback, not the default.

## 3. The orders and the gates

Orders in `lean/tmp/af82/WO.md`, with the same delegated-scaffold discipline as SET-AF81 §3 (three steps:
header → verbatim public statements with `sorry`s → `check_port` green → fill bodies) and the same six
gates. Two instructions specific to this set, both from this session's frictions: **FR-0221** — where a pin
`S_` file ends in a `solution` that specializes an in-file general theorem, declare *both*, the engine and
the row at the row's name; and **no tokens in names** (drop `P2m*`, `C2prime`, `EgenGlue`, every label
namespace) — the manager's token sweep of this session (`P2mS26B6b` → `AdicCompletionDensity`) is the
standard.

## 4. The shelf effect

Forecast **measured with `--port`** on all six rows of AF81+AF82 (both sets open on this read):

| figure | §0 | forecast (AF81 + AF82) |
|---|---:|---:|
| `needed [F terminal]` | 582 / 262,734 | **576 / 261,442** |
| ready rows | 21 / 4,877 | **15 / 3,585** |
| leaves | 140 / 36,013 | 140 / 36,013 |

**No row readied.** The six rows of the pair are the last of
the cheap ready shelf; after them the block holds only rows behind missing definition layers or rows that
need their own topic, so the next scoping pass opens on the leaves block.

## 5. The landing

All four rows in, no `sorry`, two new modules, **one module for the three-row trio** as the order intended
(no split: the three rows share one vocabulary).

| file | rows | lines | decls | checker | axioms |
|---|---|---:|---:|---|---|
| `AutomorphicForm/Adelic/ContentBound.lean` | A | **392** | 18 (17 private engine + 1) | **1 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/RationalCentreHaar.lean` | B1–B3 | **330** | 17 | **17 ok / 0 / 0** | clean (3 rows + 5 engines) |

Consumers `spec/AutomorphicFormSetAF82AConsumer.lean` (5 zones) and `…B…` (7 zones, 215 lines): 0 errors,
0 warnings. `dedup --within`: 0 clusters in both. `move_dead`: 0 declarations, 0 live private helpers.
Heartbeat floors: A 8 000 (~25×), B 20 000 (~10×) — the headline is the binding declaration in B.

**The audit**: both modules read *complete*. In B that completeness is a 19-to-17 accounting with the same
two benign entries as AF81B — the pin's `continuous_unipotentGL2` is satisfied by the import closure (the
port's `ConstantTerm.lean` copy is more general, for an arbitrary commutative topological ring) and the
pin's `solution` is FOLDED into the in-file headline, which already carries the row's name. Declaring a
`_solution` copy to reach a count was offered and **refused**: it would be an in-module duplicate that
`dedup` flags, for the sake of a number.

### The warning episode, and the fact it established

Order B landed with five `linter.style.haveILetI` warnings and a claim that `have` could not replace them
because the values had to be instances. The ruling was: the linter prints a `Try this:` block precisely
when it has computed a compiling replacement, so apply it — and do not take "the sibling module has the
same warnings" as evidence (checked: AF81A's loop was warning-free). The worker applied all five
(`haveI := isAddHaarMeasure_adelicAddHaar …` → `have hAddHaar := …`, and four more), found no error, and
**nothing is silenced**: module silent at the 200 k cap, checker `17 ok` unchanged, dedup/move_dead
unchanged. The mechanism is worth carrying house-wide — Lean 4's instance resolution consults class-typed
*local hypotheses* regardless of binder info, so every `haveI`/`letI` warning of this class is a
substitution the compiler has already checked. Recorded as **FR-0223**, with the two wrong diagnoses it
cost (a deletion test read as a substitution test; a sibling's silence assumed without checking).

### A candidate promotion, and why it is not one yet

Row B1's hypothesis `hb` — that `Z(𝔸_K)·Kˣ·U(𝔸_K)` is normalised by `heckeGen v * centralScalar u` — is
*only a hypothesis* in the pin, and no ported module supplies it. The consumer proves it
(`conj_mem_iff`: the rational centre is scalar hence central via `ratCentral_eq_centralScalar` +
`centralScalar_mul_comm'`; unipotent carried to the shifted one by `conj_ratCentral_mul_unipotentGL2`), so
the row's statement holds unconditionally there — but the closure lemma is `private` in a `spec/` file,
where it is invisible to the port. It is the wave's **first named promotion candidate**: when a second
consumer needs it, it goes public into this module's neighbourhood with its own wire, not into a consumer.

### The set's numbers

| figure | before | **after** (measured, with AF81) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 582 / 262,734 | **576 / 261,442** | 576 / 261,442 ✓ exact |
| ready rows | 21 / 4,877 | **15 / 3,585** | 15 / 3,585 ✓ exact |
| leaves | 140 / 36,013 | 140 / 36,013 | unchanged ✓ |

No row readied — the pair's own finding, and the reason the next scoping pass opens on the leaves block
rather than on the ready shelf.
