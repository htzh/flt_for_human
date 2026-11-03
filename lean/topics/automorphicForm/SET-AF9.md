# SET-AF9 — the archimedean derivative algebra and the Casimir bridge: a **composition** set

**Status: LANDED 2026-11-02 — manager's layer plus one dispatch (orders A and B), all gates green; §5.1 records the landing and the re-read.** Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree as
SET-AF8 left it. It is the **ninth** `AutomorphicForm`-serving set and the set SET-AF6 §9 deferred by
name: the *algebra* of the archimedean derivative (Casimir, the `[E, F⁻]` commutators, the character
identities, the row-isometry invariance) and the two Casimir rows that are its bridge into right
convolution. One of those two rows is the headline SET-AF6 §9 pointed at: "the 779-line one *is* the
archDeriv↔Casimir bridge, i.e. the natural headline of that set".

The set is **10 rows / 2,503 silo**, and it is the second composition set in a row: of its 2,281
declaration lines, **911 already have their statement in the port** (875 of them byte-identical — the
pin's per-file preludes, imported in earlier waves), 184 are the pin's own duplicate copies, and
**1,380 lines / 105 declarations have to be written** (measured two ways, §2). The definition layer is
**complete** (6 `Def_` modules, 0 missing, §3).

| | rows | silo | work | who |
|---|---:|---:|---:|---|
| **A — the algebra** (`ArchCasimir{,Complex}.lean`) | 8 leaves | 1,510 | **975** | worker |
| **B — the Casimir bridge** (`ArchDerivRightConv.lean`) | 2 ready rows | 993 | **405** | worker |
| **manager's layer** (two legacy migrations, §4) | — | — | 1 declaration | manager |
| | **10** | **2,503** | **≈1,380** | |

Two orders, dispatched **in sequence** (both touch/import `ArchCasimir.lean`, so they share a hub; §5).

## 0. The read

### 0.1 The figures, and which read produced them

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af9.json
python3 frontier.py --selfcheck
```

**Take the read with `--unport` while a set is in flight.** The first read of this scoping pass ran
while SET-AF8 was still being written, and the new module's `spec-pin:` header (the manager wires the
skeleton so the worker can run `check_port` from its first file) had already marked the whole pin file
ported: it returned `needed 894 / 358,716`, i.e. SET-AF8's *post-landing* arithmetic, with 8 of the
row's 25 declarations on disk. `--unport AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep`
restored `895 / 362,549`. That finding is now FR-0114; the table below is the **landed** read (SET-AF8
has since landed, and the instrument's number became the true one).

| figure | value | SET-AF8 §5 (pre-landing) |
|---|---:|---:|
| `needed [F terminal]` | **894 / 358,716** | 895 / 362,549 |
| `needed [literal]` | 907 / 362,191 | 908 / 366,024 |
| frontier F | **1,521 / 768,650** | 1,520 / 764,817 |
| ready rows, all namespaces | 69 / 18,922 | 70 / 22,755 |
| ready rows, `AutomorphicForm` | **40 / 13,578** | 41 / 17,411 |
| leaves, all namespaces | 249 / 62,588 | 249 / 62,588 |
| leaves, `AutomorphicForm` | **80 / 16,549** | 80 / 16,549 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,357 `Thm_` sources, 1,521 declared names) | PASS |
| correction | **none needed** (`--unport` not required on the landed tree) | — |

**Both blocks are quoted and every row accounted for.** 40 ready rows / 13,578 and 80 leaves / 16,549;
Appendix A lists all 120 with a disposition each: 10 are this set's (8 leaves, 2 ready rows) and 110
are deferred — the three largest and the two next candidates with a reason in §7, the rest as one-line
`deferred (§7)` rows. It is the same shelf SET-AF5's Appendix A/B listed in full, re-read after
SET-AF6/AF7/AF8 landed. The withheld 4 / 831 is the prunable complex-analytic subject
throughout (two `ModularCurve` Tate-module rows, two `AlgebraicCurve` rows); none is
`AutomorphicForm`.

### 0.2 Why this family, and not the three larger rows

The shelf's three largest rows are 1,349, 1,291 and 1,043 silo (the Weyl-integrand integrability pair
and `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow`), and each is a *consumer* of a large
unported development (Weyl-intertwining integrand; flat/induced-section families), not a compact set.
The arch-derivative family is the one block on the shelf that is (i) a single subject, (ii) already 45%
importable, (iii) **named as the next set by the column's own record** (SET-AF6 §9, twice), and (iv)
carries the shelf's best fan-in: `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` has leverage
8 / 9 and `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` 8 / 14, and the family is what
every `archDerivAt_*` consumer above it rests on.

## 1. The family, quoted whole

Ten rows; the first eight are graph **leaves** (their `S_` files import only `Definitions/`), the last
two are **ready** rows with `Theorems/` premises. `work` is the per-declaration measurement of §2
(declarations whose statement is not in the port), not the silo.

| row | kind | silo | work | prem | lev | what it states |
|---|---|---:|---:|---:|---:|---|
| `archDerivAt_commutator_of_isArchSmoothAt` | leaf | 208 | **25** | 0 | 1/4 | the three `[H,E]`/`[H,F⁻]`/`[E,F⁻]` commutator identities of the archimedean flows on a smooth `φ` |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | leaf | 401 | **302** | 0 | 8/9 | the same over `GL₂(ℂ)` for the six complex directions (this is the pin file the rest of the complex engine is a prelude of) |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | leaf | 184 | **117** | 0 | 8/14 | `D_E − D_{F⁻} = 2·(weight)` on a function with an archimedean character — the Casimir acts by the character |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | leaf | 250 | **223** | 0 | 2/2 | the same character data over `ℂ` at weight `1`, in the `iH / E−F⁻ / i(E+F⁻)` basis (`swayGL` row-isometry argument) |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | leaf | 110 | **16** | 0 | 2/3 | the Casimir commutes with right translation by a row-isometry at a *different* place |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | leaf | 133 | **101** | 0 | 2/2 | the complex twin |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | leaf | 107 | **91** | 0 | 2/3 | a function whose `E` and `F⁻` derivatives vanish is right-invariant under `GL₂(ℝ)` at the place |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | leaf | 117 | **100** | 0 | 2/3 | the complex twin |
| `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` | **ready** | 779 | **217** | 5 | 1/1 | **the bridge**: if `x` is arch-smooth with continuous first and second derivatives, then `rightConv x f` is too, and `archCasimirAt (rightConv x f) = rightConv (archCasimirAt x) f` |
| `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar` | **ready** | 214 | **188** | 5 | 1/1 | the Casimir of a character-typed test function is again factorisable and bi-finite, and its right convolution preserves `levelInvariantSubmodule ⊓ archCutSubmodule` |
| | | **2,503** | **≈1,380** | | |

**Why this is one story, not ten.** The pin's own duplication says it: `port_plan`'s *port once* blocks
report **113 lines / 11 declarations proved identically in 2 of these files** and **44 lines / 7
declarations in 3 of them** (`archDerivAt_archDerivAt_eq` 27, `archDerivAt_apply_mul_archRealLiftAt`
18, `rel_Fm_E` 16, `archDerivAt_comm` 15, `hasDerivAt_flow_mul_const` 10, …), i.e. the real and complex
files are three copies of one development — 184 duplicate declaration lines across the ten files. And
the subject is one: the algebra generated by `archDerivAt`/`archCasimirAt` at one real (or complex)
place, and what it does to a right convolution. SET-AF6 §9 put the same boundary on it in words.

## 2. The price, measured two ways

```bash
python3 port_advise.py --nodes <the ten> --json build/af9-advise.json
python3 port_plan.py --json build/af9-advise.json
python3 build/af9-worklist.py      # the per-declaration reconciliation below
```

**`port_plan`'s budget.** raw `S_` lines 2,503 → declaration lines 2,281 → −184 duplicate copies →
**2,097 once-cost** → −690 already in the port (687 tier-1, 3 tier-3) → **NET NEW 1,407**; 111 trusted
substitutions + 2 suspect (`rotGL` → `splitTorusGL2`, `rotMat` → `RealIwasawa.rot`, i.e. type-only
`def` matches — the same instrument artefact SET-AF8 hit).

**The per-declaration reconciliation** (the instrument SET-AF8 needed to correct Appendix B, run over
all ten files; Appendix B is its output). Of the 2,291 declaration lines the ten files contain:

| class | lines | declarations | meaning |
|---|---:|---:|---|
| statement in the port (T1 byte 875 / T2 shape 36) | **911** | 134 | import it |
| genuinely new | **607** | 68 | write it |
| same last name, different statement | **773** | 37 | read it: the pin's `main` and `solution` are the row's own proof (a junk last-name match against unrelated port names, e.g. `main` → `TransvectionFrame`), `rightConv_{add,smul}_right` are the port's `ArchDualCut` linearity lemmas under other binders, and the rest are new statements the name tier cannot settle |
| **work (new + same-name)** | **1,380** | **105** | 975 order A + 405 order B |

The two figures agree to 2% (1,380 vs 1,407), and SET-AF6's forecast for the eight leaves — **1,001
net** — agrees with order A's 975 to 2.6%. The recipe's §7 rule ("read the delta, not the absolute")
is satisfied twice over: three instruments, one number.

**Where the work actually is.** 726 of the 975 lines of order A are the *complex* half
(`archDerivAtComplex_commutator…` 302, mostly a 14-row bracket table of three-line lemmas plus a
51-line `main`; `iH_eq_zero…` 223; the `apply_mul_archComplexGLAt` 100; the row-isometry twin 101);
the real half is 249 lines, of which the commutator leaf is **25** — 167 of its 192 declaration lines
are the port's `ArchCasimir.lean` engine already.

## 3. The definition gate: complete, no `Def_` node

`spec/gate_scan.py` against all ten rows for every `Def_` module of the closure — the two wrappers
import `Definitions.Def_AutomorphicForm_ArchDerivCasimir{,Complex}` and (through the character and
production rows) `…ArchDerivCasimirComplexAPI`, `…ProductionPinsGeneral`, `…ArchWeightChar`,
`…ArchWeightCharTransport`:

| pin `Def_` module | public decls | port home | missing |
|---|---:|---|---:|
| `Def_AutomorphicForm_ArchDerivCasimir` | 56 | `AutomorphicForm/Adelic/ArchDerivCasimir.lean` (445 pin lines) | **0** |
| `Def_AutomorphicForm_ArchDerivCasimirComplex` | 32 | `…/ArchDerivCasimirComplex.lean` (196) | **0** |
| `Def_AutomorphicForm_ArchDerivCasimirComplexAPI` | 43 | `…/ArchDerivCasimirComplexAPI.lean` | **0** |
| `Def_AutomorphicForm_ProductionPinsGeneral` | 50 | `…/ProductionPinsGeneral.lean` | **0** |
| `Def_AutomorphicForm_ArchWeightChar` | — | `…/ArchWeightChar.lean` | **0** |
| `Def_AutomorphicForm_ArchWeightCharTransport` | — | `…/ArchWeightCharTransport.lean` | **0** |

`uses` per row is small (33/56 for the character row, 4/43 for the `ComplexAPI` row, 0/50 for
`ProductionPinsGeneral`) — the rows rest on the *engine* (`archDerivAt`, `archCasimirAt`,
`archFlowAt`, `archDirMatrix`, `HasArchCharacterAt`), which landed with the earlier waves' definition
layer. So this set has **no definition-layer obligation**, like SET-AF8 and unlike SET-AF5/AF6.

## 4. Homes: chosen by subject, then priced by migration

**The eight leaves go into the module that already holds the engine they extend.**
`AutomorphicForm/Adelic/ArchCasimir.lean` is "the `𝔰𝔩₂` (Casimir) calculus at a real place, and its
three headlines"; it already holds 89 of these S_ files' declarations (752 lines: `archDerivAt_comm`,
`archDerivAt_archDerivAt_eq`, `bracket_H_E`, `rel_E_H`, `D1_*`, the `Casimir` API). The four real
leaves are the *continuation of that API* — `archDerivAt_commutator_of_isArchSmoothAt` is the headline
of an engine whose every lemma is already in the file (25 lines of work: `main` and `solution`).
`ArchCasimirComplex.lean` is the same for the four complex leaves (50 lines already there).
Both modules have **0 importers in the port today** (measured: no `import …Adelic.ArchCasimir` line
anywhere in `FLTForHuman/` or `spec/`), so inserting into them is cascade-free in practice as well as
correct by subject.

**Both are legacy, and the migration is measured, not assumed.** They are in
`spec/old_check_stmts.py`'s `PORT_FILES` and carry `-- pin:` markers plus tier-3 registration in
`spec/UNWIRED-PUBLIC.md`. The recipe's rule is to pay the migration in the same touch; this scoping
pass measured the price by copying each module with its `spec-pin:` wires added and running the
checker on the copy:

| module | its wire | `check_port --force` on the wired copy | what is left |
|---|---|---|---|
| `ArchCasimir.lean` | 3 `S_` files (`archCasimirAt_rightTranslate_archRealGLAt`, `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt`, `iterate_raise_iterate_lower_eq_smul_…`) | **130 ok / 1 mismatch / 0 missing** | one declaration: `smooth_sub` carries an extra unused `(hθ : IsArchSmoothAt hw θ)` — drop it, or record an `own:` row |
| `ArchCasimirComplex.lean` | 1 `S_` file (`archCasimirAtComplex_rightTranslate_archComplexGLAt`) | **97 ok / 0 mismatch / 0 missing** | nothing |

So the legacy tax here is **one hypothesis**, and the migration is otherwise mechanical (wire in,
`PORT_FILES` row out, silent build, `dedup`/`move_dead`, `spec/UNWIRED-PUBLIC.md` regenerated). That is
the manager's layer of this set.

**The two Casimir rows go into `ArchDerivRightConv.lean`** — "differentiating a right convolution along
an archimedean flow", the module SET-AF6 landed for exactly this statement shape
(`archDerivAt_rightConv_eq_rightConv_deriv`); the bridge is the same theorem with `archCasimirAt` in
place of `archDerivAt`. It is non-legacy (its own `spec-pin:`), has one importer
(`spec/AutomorphicFormSetAF6Consumer.lean`), and needs **one new import**: `ArchCasimir` (it currently
imports `ArchDerivCasimir` and `ArchDerivCasimirComplexAPI`, the *definition* modules, but not the
Casimir engine where `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` lives). Checked: `ArchCasimir`
imports neither `ArchDerivRightConv` nor anything that imports it, so the edge is acyclic.

**The import direction, checked row by row** (the rule that cost SET 3/4 two worker rounds):

| row group | consumes (port module) | so the home must be at or above |
|---|---|---|
| 4 real leaves | `ArchDerivCasimir`, `ArchWeightCharTransport`, `Cusp/Constituent`, `ProductionPinsGeneral` | `ArchCasimir` (imports `ArchDerivCasimir` → `ArchWeightCharTransport`, and `Cusp/Constituent`) ✓ |
| 4 complex leaves | `ArchDerivCasimirComplexAPI` → `ArchDerivCasimirComplex`, `Cusp/Constituent`, `ArchWeightChar` | `ArchCasimirComplex` (imports `Cusp/Constituent` + `ArchDerivCasimirComplexAPI`) ✓ |
| 2 Casimir rows | `ArchCasimir` (`leftCasimir_eq_…`), `FactorizableTestFnArchSmooth{,Left}`, `ArchDerivRightConv`, `RightConvRegularity`, `RightConvolution`, `TestFnTop` | `ArchDerivRightConv` — **at or above all of them once `ArchCasimir` is imported** ✓ |

### 4.1 The manager's layer, landed (2026-11-02)

Both migrations are done, not planned, and the numbers are the checker's:

| module | wire | `check_port --force` | build | `dedup` / `move_dead` |
|---|---|---|---|---|
| `ArchCasimir.lean` | 3 `S_` files | **131 ok / 0 mismatch / 0 missing** (was 130 ok / 1 mismatch at the probe) | 9.6 s, silent | 0 clusters / 0 dead |
| `ArchCasimirComplex.lean` | 1 `S_` file | **97 ok / 0 / 0** | 7.9 s, silent | 0 clusters / 0 dead |

The one drift was exactly what §4 predicted: `smooth_sub`'s unused hypothesis was spelled `_hθ` while
the pin writes `hθ` — the checker compares binder spelling, so the two-character rename is the whole
fix, and it earned one local `set_option linter.unusedVariables false in` (the hypothesis is the pin's
and stays). Both modules are out of `PORT_FILES`, their headers now describe the wire instead of the
tier-3 exemption, and `spec/UNWIRED-PUBLIC.md` is regenerated: **112 modules / 3,394 public
declarations** in the register, the two modules' 228 having left it.

**Markers are gone (policy, 2026-11-02).** The two migrations also revealed what the grandfathered
`-- pin:` lines were doing: besides naming the declaration, each named the *pin file* its original
lives in, and 3 of `ArchCasimir.lean`'s 6 and 2 of `ArchCasimirComplex.lean`'s 3 were files outside
the `spec-pin:` wire. So the strip and the wire are one edit — measured on `ArchCasimir.lean`: markers
stripped with the original three wires → `132 ok / 0 mismatch / 3 missing`; with all six files wired →
`135 ok / 0 / 0` over the same declaration set. Tracking is the header alone; the rule is recorded in
[porting-playbook.md](../porting-playbook.md) §5.

`ArchDerivRightConv.lean` — order B's home — gained the imports the two statements need
(`ArchCasimir`, `Cusp.Constituent`, `NumberField.AdelicLevel.Level`, `…HeckeGen`; measured, not guessed:
`levelInvariantSubmodule`, `levelOne`, `heckeGen`, `adelicBox` were all unreachable without them), still
builds (7.4 s) and is still **1 ok / 0 / 0**. And the three surfaces are verified by probes left in
`lean/tmp/`: `probe-af9-a.lean` (the eight leaves' vocabulary against the two Casimir modules),
`probe-af9-b.lean` (order B's vocabulary), and `probe-af9-statements.lean`, which states **both
order-B headlines as `example … := by sorry`** and elaborates them — the home can host the statements,
which no `#check` can show (FR-0112). Expected checker counts after the dispatch: **135 / 101 / 3 ok**.

## 5. The cut

**Order A — the algebra (975 lines).** Files: `AutomorphicForm/Adelic/ArchCasimir.lean` (4 real leaves)
and `…/ArchCasimirComplex.lean` (4 complex leaves). One worker, transcribed with the port's names; all
eight headlines public at their `Theorems/` wrapper statements, everything else `private` exactly as
the pin has it. The two files are disjoint from order B's.

**Order B — the Casimir bridge (405 lines).** File: `…/ArchDerivRightConv.lean` (both rows), plus the
one import of `ArchCasimir`. **Dispatch after A**, not concurrently: B imports the module A edits, and
two orders must never build against a hub the other is editing (the recipe's parallelism rule). The
same sequencing also lets B's headline use any of A's real leaves if the pin's proof wants them.

**Manager's layer, before A.** (i) migrate `ArchCasimir.lean` and `ArchCasimirComplex.lean` to
`check_port` — wires in, `PORT_FILES` rows out, the one `smooth_sub` hypothesis resolved, silent build,
`dedup`/`move_dead`, `UNWIRED-PUBLIC.md` regenerated; (ii) the two wrappers' `Def_` gate is already
0 missing (§3), so nothing else. This is a *small* migration, and it is the reason the worker's checker
gate is meaningful at all: a legacy module in `PORT_FILES` cannot be checked by `check_port` while
`PORT_FILES` still owns it.

**Gates (each order).** No tree build; the module's own `lake build` under `flock`/`timeout 280`;
`lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` in the edit loop and **no
`set_option maxHeartbeats`** (measured: none of the ten pin files carries one); `check_port --force`
→ `0 mismatch / 0 missing`, with every new declaration `ok` (the migrated modules' counts are quoted in
§4 and become the baseline); `#print axioms` on every headline; zero warnings; `dedup`/`move_dead` on
each module; and a `spec/AutomorphicFormSetAF9Consumer.lean` zone that composes the bridge with the
algebra (the Casimir identity composed with the commutator relations is a real composition).

### 5.1 The landing (2026-11-02)

**Files.** `ArchCasimir.lean` 1,437 → **1,640** (+354), `ArchCasimirComplex.lean` 973 → **1,588**
(+712), `ArchDerivRightConv.lean` 704 → **1,167** (+463), plus the new
`spec/AutomorphicFormSetAF9Consumer.lean` (60 lines). ≈1,529 written lines / **103 declarations**:
10 public headlines (verbatim from their `Theorems/` wrappers) and 93 private helpers.

**Gates, re-run by the manager on the landed tree.** `check_port --force` **135 ok / 0 mismatch / 0
missing** (`ArchCasimir`), **101 / 0 / 0** (`ArchCasimirComplex`), **3 / 0 / 0**
(`ArchDerivRightConv`); all four files `lake env lean`-silent at the project caps (zero warnings); each
module's own `flock`/`timeout 280` build silent (12.5 s / 15.3 s / 7.9 s); `#print axioms` on **all
ten** headlines `[propext, Classical.choice, Quot.sound]`; the consumer zone 0 errors; `dedup
--within` 0 clusters on all three, `--cross` 4 clusters / 21 lines **kept** — they are the ℝ/ℂ twins
`U`, `D1`, `D2`, `conjCLM` at lines predating this set, and the two copies are type-distinct, so
neither is removable without breaking a typed public statement; `move_dead` 0 / 0 / 0 after one
deletion (`rotAt_coe`, a `rfl` restatement, dead in the pin too).

**Markers.** The strip is complete: 151 + 131 `-- pin:` lines removed, 0 left, and the wires carry the
provenance instead — `ArchCasimir` **3 → 7** `spec-pin:` lines, `ArchCasimirComplex` **1 → 5**,
`ArchDerivRightConv` 2 → 4 — with the checker counts unchanged after the strip. That is the policy
`porting-playbook.md` §5 now records; it is also why the strip and the wire had to be one edit (§4.1).

**Two Appendix-B rows became deletions, and one is a duplicate the pin itself carries.** `dirM`
(pin `S_…commutator….Complex.lean:18`) is `archDirMatrixComplex` (`ArchDerivCasimirComplexAPI.lean:33`,
the same six bodies): the whole 17-row bracket table and `main` are stated on the port's name instead,
which is why Appendix B's "302 to write" over-counted ~24 declarations (they already sat in
`ArchCxGL`). And `CasLeft2.Ld` ≡ `CommConv17.Lf` is the pin's own cross-file duplicate — the one
`dedup --within` cluster, resolved by deleting `Ld`.

**Eight in-port declarations had to be re-stated privately, and the reason is a finding.** Row 2's
rotation prelude (`rotMat`, `det_rotMat`, `rotGL`, `rotGL_coe`, `rotGL_mem`, `rotSO`,
`archWeightOneℝ_rotSO`) *is* in the port — under `TSRot.*` in `Cusp/CutWeightDecomposition.lean`,
which is **downstream** of `ArchCasimir.lean`, so the home cannot import it; row 6's
`norm_ringEquivComplexOfIsComplex_symm` sits in `WeylIntegrable/LatticeEstimates.lean`, outside the
closure. Both were re-stated `private` rather than pulling an import upward into a hub. Appendix B's
"imported" column is therefore an *existence* claim, not an *importability* claim — FR-0115.

**The re-read.** The set consumed exactly its forecast on the demand side and **readied seven rows**,
which the brief's §7 predicted as 0–1:

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 894 / 358,716 | **884 / 356,213** | −10 / −2,503 ✓ (exact) |
| `needed [literal]` | 907 / 362,191 | **897 / 359,688** | −10 / −2,503 ✓ |
| frontier F | 1,521 / 768,650 | **1,531 / 771,153** | +10 / +2,503 ✓ (exact) |
| ready rows, all namespaces | 69 / 18,922 | 74 / 19,496 | +5 / +574 |
| `AutomorphicForm` ready rows | 40 / 13,578 | **45 / 14,152** | **+5 / +574** |
| `AutomorphicForm` leaves | 80 / 16,549 | **72 / 15,039** | −8 / −1,510 ✓ |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |

The seven readied rows are the Casimir-algebra consumers the leaves unblocked:
`archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex`,
`archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt`,
`archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul`,
`archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul`,
`archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero`,
`isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite_ofChar`,
`leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex`. **A per-row return cannot see
this** — five of the seven needed *two or more* of the leaves at once, exactly the FR-0106 mechanism
SET-AF6 recorded — and the seven are the next set's obvious start.

## 6. Risk register

1. **The 5-premise rows.** Both ready rows carry 5 premises and 1,000+ silo of `S_` file each; the
   recipe's warning is that a many-premise node is where a set stalls. Order B is therefore small
   (405 lines) and scheduled last, so a stall there costs the set one order, not both.
2. **The junk last-name matches.** `port_advise` matches `main` against `TransvectionFrame.main` and
   `solution` against `DeuringNormResidue.solution`; the two rows' 15- and 143-line proofs are *work*,
   not imports. Appendix B lists them explicitly so no worker reads "same name" as "have it".
3. **The complex bracket table.** `br_*` is 14 lemmas of 3 lines each plus 4 more (`br_H_iH` …
   `br_Fm_iFm`), all mechanical `Matrix` identities. They are new (the real `bracket_*` table is a
   different set of matrices), and they are the kind of block that invites a `native_decide` or a
   `maxHeartbeats` fix — both forbidden. A `ring`/`fin_cases` transcription is enough; if the pin's
   proof does not fit the cap, the fix is the instance, not the cap.
4. **`IsArchSmoothAt` walls and scoped instances.** These files are dense in `letI := glBorel` and in
   `ArchInfra` scoped instances; SET-AF8's FR-0112 applies — a `#check`-only surface probe will not
   reveal a missing `open scoped`. The order must ask for an `example` per instance the proofs need
   (`CompactSpace (ArchInfra.Kprod K)`, `IsFiniteMeasure (ArchInfra.muK K)`), not only `#check`s.
5. **Two legacy modules edit at once.** A and B both build against `ArchCasimir`; sequence them (§5).
6. **The `smooth_sub` drift is a decision, not a transcription.** Dropping the unused hypothesis is the
   faithful move (the pin has no such binder); if the worker's transcription of the pin's use sites
   needs it, record an `own:` row rather than weakening the pin.
7. **Silo ≠ work, and the pin's per-file preludes are the reason.** Order A's 1,510 silo is 975 work;
   a brief that priced it at silo would have trebled the order. Quote the work column, not the silo.

## 7. What this set does not do

- **The three largest ready rows** — `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349), `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291), `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043) — are three separate
  subjects (the Weyl-integrand integrability engine, the induced-section indicator identity), each a
  consumer of a large unported development; each is a set of its own, not a row of this one.
- **`bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family`** (624, 3 premises, leverage 2/5)
  and the **`SmoothCuspRealizationAt` pair** (527 + 513) are the next two candidates by size and
  fan-in; both wait on the Eisenstein/cusp-realization developments.
- **The 4 withheld rows / 831 silo** are the prunable complex-analytic subject (`Pic0` torsion
  finiteness, the prescribed-divisor engine) — not this column's work (§0.1).
- **No `Def_` node, no new module, no promotion**: the two homes exist and are the right ones, and the
  only metadata surface is the two legacy migrations (§4).
- **The re-read is done (§5.1)** and it corrected this brief's forecast: the set readied **seven**
  rows, not the 0–1 predicted here — a per-row return cannot see a row that needs several leaves at
  once (FR-0106), which is the shape of the whole Casimir-algebra tail.

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af9.json` by `build/af9-shelf-appendix.py` (silo, premises, leverage, and
the disposition of each row).

### The ready block — **40 rows / 13578 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` | 779 | 5 | 1/1 | **SET-AF9, order B** |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | 3 | 2/5 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | 3 | 1/5 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | deferred (§7) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | 2 | 4/15 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar` | 214 | 5 | 1/1 | **SET-AF9, order B** |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4/12 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1/2 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |
### The leaves block — **80 leaves / 16549 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 2/2 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 2/2 | deferred (§7) |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | 8/9 | **SET-AF9, order A** |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | deferred (§7) |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 1/1 | deferred (§7) |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 2/3 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | 2/2 | **SET-AF9, order A** |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | deferred (§7) |
| `archDerivAt_commutator_of_isArchSmoothAt` | 208 | 1/4 | **SET-AF9, order A** |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | 8/14 | **SET-AF9, order A** |
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
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 1/1 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | 2/3 | **SET-AF9, order A** |
| `whittakerCoefficient_unipotentGL2_mul` | 123 | 17/54 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | 2/2 | **SET-AF9, order A** |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | deferred (§7) |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | 2/3 | **SET-AF9, order A** |
| `continuous_whittakerCoefficient` | 108 | 3/14 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | 2/3 | **SET-AF9, order A** |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | 10/17 | deferred (§7) |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 1/2 | deferred (§7) |
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

Generated by `build/af9-worklist.py` from the port's own statement index: for each of the ten rows,
every declaration whose statement is **not** in the port, with its pin line and span. This is the
order's transcription list, corrected where §2's reading showed `port_advise` over-counted.

| row | decl lines | imported | to write |
|---|---:|---:|---:|
| `archDerivAt_commutator_of_isArchSmoothAt` | 192 | 167 | 25 |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 162 | 45 | 117 |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 82 | 66 | 16 |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 91 | 0 | 91 |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 385 | 83 | 302 |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 233 | 10 | 223 |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 105 | 4 | 101 |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 100 | 0 | 100 |
| `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` | 753 | 536 | 217 |
| `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar` | 188 | 0 | 188 |
| **10 rows** | **2291** | **911** | **1380** |

`imported` = the statement is in the port (byte-identical, or the same shape); `to write` = new,
**or** a same-last-name declaration to read first (§2's third class — `main`/`solution` of the row
itself are the two largest such rows, and they are work, not imports).

### `archDerivAt_commutator_of_isArchSmoothAt`

192 declaration lines, 167 imported, **25 to write** in 2 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 17 | 185 | theorem |
| `solution` | 8 | 202 | theorem |

### `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt`

162 declaration lines, 45 imported, **117 to write** in 11 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 37 | 141 | theorem |
| `hasDerivAt_rotMat_entries` | 18 | 86 | theorem |
| `archDerivAt_eq_fderiv` | 18 | 123 | theorem |
| `archWeightCharAt_rotAt` | 14 | 72 | theorem |
| `solution` | 8 | 178 | theorem |
| `norm_symm` | 5 | 56 | theorem |
| `rotAt_coe` | 4 | 64 | theorem |
| `adelicArchGLInclAt_rotAt` | 4 | 68 | theorem |
| `rotAt` | 3 | 61 | def |
| `rotMat_zero` | 3 | 104 | theorem |
| `one_mem_U'` | 3 | 120 | theorem |

### `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne`

82 declaration lines, 66 imported, **16 to write** in 1 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 16 | 96 | theorem |

### `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero`

91 declaration lines, 0 imported, **91 to write** in 6 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `exists_eq_lower_upper_lower_upper` | 31 | 56 | theorem |
| `apply_mul_archFlowAt_eq` | 28 | 18 | theorem |
| `main` | 14 | 87 | theorem |
| `solution` | 8 | 101 | theorem |
| `apply_mul_upper` | 5 | 46 | theorem |
| `apply_mul_lower` | 5 | 51 | theorem |

### `archDerivAtComplex_commutator_of_isArchSmoothAtComplex`

385 declaration lines, 83 imported, **302 to write** in 31 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 51 | 317 | theorem |
| `solution` | 35 | 368 | theorem |
| `archDerivAtComplex_archDerivAtComplex_eq` | 28 | 194 | theorem |
| `archDerivAtComplex_apply_mul_lift` | 19 | 147 | theorem |
| `hasDerivAt_archFlowMatrixComplex_apply` | 18 | 53 | theorem |
| `archComplexLiftAt_mul_archComplexGLAt` | 16 | 71 | theorem |
| `hasDerivAt_of_symm_mul_archFlowMatrixComplex` | 13 | 87 | theorem |
| `archComplexLiftAt_of_symm_one` | 10 | 104 | theorem |
| `hasDerivAt_flow_mul_const` | 10 | 184 | theorem |
| `comm_of_bracket_zero` | 10 | 260 | theorem |
| `dirM` | 9 | 18 | def |
| `hasDerivAt_flow_entries` | 8 | 176 | theorem |
| `archDerivAtComplex_comm` | 8 | 244 | theorem |
| `comm_of_bracket` | 8 | 252 | theorem |
| `archDerivAtComplex_eq_D1` | 6 | 166 | theorem |
| `D1_zero` | 6 | 238 | theorem |
| `br_Fm_iFm` | 5 | 312 | theorem |
| `br_H_E` | 3 | 270 | theorem |
| `br_H_Fm` | 3 | 273 | theorem |
| `br_E_Fm` | 3 | 276 | theorem |
| `br_H_iE` | 3 | 279 | theorem |
| `br_H_iFm` | 3 | 282 | theorem |
| `br_E_iFm` | 3 | 285 | theorem |
| `br_iE_Fm` | 3 | 288 | theorem |
| `br_iH_E` | 3 | 291 | theorem |
| `br_iH_Fm` | 3 | 294 | theorem |
| `br_iH_iE` | 3 | 297 | theorem |
| `br_iH_iFm` | 3 | 300 | theorem |
| `br_iE_iFm` | 3 | 303 | theorem |
| `br_H_iH` | 3 | 306 | theorem |
| `br_E_iE` | 3 | 309 | theorem |

### `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one`

233 declaration lines, 10 imported, **223 to write** in 15 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 32 | 220 | theorem |
| `archDerivAtComplex_eq` | 22 | 141 | theorem |
| `hasDerivAt_chart` | 18 | 123 | theorem |
| `fderiv_apply_eq_zero_of_mem` | 17 | 163 | theorem |
| `flow_iH_mem` | 16 | 99 | theorem |
| `hasDerivAt_rotGL` | 16 | 180 | theorem |
| `rotGL` | 14 | 45 | def |
| `swayGL` | 14 | 59 | def |
| `hasDerivAt_swayGL` | 14 | 196 | theorem |
| `rotGL_mem` | 13 | 73 | theorem |
| `swayGL_mem` | 13 | 86 | theorem |
| `apply_mul_archComplexGLAt_of_mem` | 10 | 26 | theorem |
| `mem_rowIsometrySubgroup₀_complex` | 9 | 36 | theorem |
| `archComplexGLAt_eq_lift` | 8 | 115 | theorem |
| `swayGL_zero` | 7 | 213 | theorem |

### `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne`

105 declaration lines, 4 imported, **101 to write** in 11 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 18 | 117 | theorem |
| `package` | 17 | 89 | theorem |
| `isArchSmoothAtComplex_rightTranslate` | 11 | 40 | theorem |
| `archComplexGLAt_mul_rowIsometryInclAt₀_comm` | 11 | 106 | theorem |
| `archDerivAtComplex_rightTranslate` | 9 | 51 | theorem |
| `archCasimirBarAtComplex_rightTranslate` | 7 | 78 | theorem |
| `archComplexLiftAt_mul_comm` | 6 | 30 | theorem |
| `archDelAt_rightTranslate` | 6 | 60 | theorem |
| `archDelBarAt_rightTranslate` | 6 | 66 | theorem |
| `archCasimirAtComplex_rightTranslate` | 6 | 72 | theorem |
| `archFlowAtComplex_mul_comm` | 4 | 36 | theorem |

### `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero`

100 declaration lines, 0 imported, **100 to write** in 6 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `exists_eq_lower_upper_lower_upper` | 32 | 64 | theorem |
| `apply_mul_archFlowAtComplex_eq` | 25 | 19 | theorem |
| `main` | 15 | 96 | theorem |
| `apply_mul_upper` | 10 | 44 | theorem |
| `apply_mul_lower` | 10 | 54 | theorem |
| `solution` | 8 | 111 | theorem |

### `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt`

753 declaration lines, 536 imported, **217 to write** in 15 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 117 | 649 | theorem |
| `solution` | 15 | 766 | theorem |
| `isFactorizableTestFn_Lf` | 11 | 567 | theorem |
| `rightConv_smul_right` | 10 | 615 | theorem |
| `integrable_integrand` | 9 | 591 | theorem |
| `continuous_conv` | 8 | 583 | theorem |
| `rightConv_sub_right` | 8 | 607 | theorem |
| `rightConv_add_right` | 7 | 600 | theorem |
| `hcs_smul` | 7 | 642 | theorem |
| `conv_smooth_and_deriv` | 5 | 578 | theorem |
| `rightConv_sub_left` | 5 | 637 | theorem |
| `rightConv_neg_right` | 4 | 625 | theorem |
| `rightConv_smul_left'` | 4 | 629 | theorem |
| `rightConv_neg_left` | 4 | 633 | theorem |
| `Lf` | 3 | 564 | def |

### `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar`

188 declaration lines, 0 imported, **188 to write** in 7 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 143 | 73 | theorem |
| `tens_Ld` | 13 | 34 | theorem |
| `Ld_left_inv` | 13 | 60 | theorem |
| `Ld_right_law` | 8 | 52 | theorem |
| `isFactorizableTestFn_of_tens` | 5 | 47 | theorem |
| `Ld` | 3 | 28 | def |
| `Tens` | 3 | 31 | def |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af9.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt \
  --nodes AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex \
  --nodes AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt \
  --nodes AutomorphicForm.archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one \
  --nodes AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne \
  --nodes AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne \
  --nodes AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero \
  --nodes AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero \
  --nodes AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt \
  --nodes AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar \
  --json build/af9-advise.json
python3 port_plan.py --json build/af9-advise.json     # 2,503 raw / 2,281 decl / 184 dup / 1,407 net
python3 build/af9-worklist.py                         # the per-declaration reconciliation (§2)
```

The migration probe of §4 (copy the module, add its `spec-pin:` lines, run the checker):

```bash
cd ../lean
python3 - <<'PY'
import pathlib
src = pathlib.Path('FLTForHuman/AutomorphicForm/Adelic/ArchCasimir.lean').read_text()
i = src.index('-/')
wires = ("  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean\n"
         "  spec-pin: P2M/Sol/S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean\n"
         "  spec-pin: P2M/Sol/S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean\n")
pathlib.Path('tmp/probe-ArchCasimir.lean').write_text(src[:i] + wires + src[i:])
PY
python3 spec/check_port.py --force tmp/probe-ArchCasimir.lean     # 130 ok / 1 mismatch / 0 missing
```

**Forecast on landing** (the two orders together, read *after* SET-AF8): `needed` **894 / 358,716 → 884 /
356,213**, frontier **1,521 / 768,650 → 1,531 / 771,153** (+10 rows / +2,503), the `AutomorphicForm`
ready shelf **40 / 13,578 → 39 / 12,585** (the 779 row leaves; the 214 row is in the same block, so
−1 row / −993), the leaves **80 / 16,549 → 72 / 15,039** (−8 / −1,510), and the rows readied by order A
counted on the re-read, not here.
