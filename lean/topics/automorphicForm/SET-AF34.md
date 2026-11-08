# SET-AF34 — the genuine cusp realization: modulus and continuity, the level-one Hecke obstruction, and the idèle-norm twist

**Status: LANDED 2026-11-08** — four orders on four new modules plus the definition layer; §7 is the
forecast and §8 the landing record. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read
that follows SET-AF33's landing. It is the **thirty-fourth** `AutomorphicForm`-serving set.

**4 rows / 1,606 silo / 1,155 net priced (`port_plan`)** plus **one premise row / 333 silo** that the
corrected read ($0.2$) shows is *not* ported and is what makes the general row of the pair ready:
**5 nodes / 1,939 silo / 1,555 net priced, of which ≈1,065 lines are written** (the second row of the
obstruction pair is *derived*, §2.1).

| # | row (`AutomorphicForm.` dropped unless noted) | silo | lev | what it says |
|---|---|---:|---:|---|
| **A** | *(premise)* `NumberField.denseRange_algebraMap_add_adeleSingleAt` | 333 | 1/1 | `K × K_v` maps densely into `𝔸_K` by `q + adeleSingleAt v y` |
| **B** | `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | **7/20** | the central character of a genuine realization is an idèle-class character admitting the level, and is continuous |
| **C** | `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 1/1 | no `heckeGen v`-eigenvalue outside the level, over any number field |
| **C′** | `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 1/1 | the same statement over `ℚ` — **derived from C** (§2.1) |
| **D** | `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 1/6 | the `‖det‖ ^ t` twist of a genuine realization, with the same exceptional set |

§0 the read and the correction; §1 the cut and why; §2 the pricing and the derivable pair; §3 homes;
§4 the definition layer; §5 the orders and their gates; §6 traps; §7 forecast; §8 landing; §9 what this
set does not do.

No Lean was run for the scoping figures; the read is `frontier.py`'s cached graph, the pricing
`port_advise`/`port_plan`, and the statement/wiring checks are the scaffolds of §5.

## 0. The read

### 0.1 The canonical read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af34.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS.** The figures, from that one read:

| figure | value |
|---|---:|
| `needed [F terminal]` | **763 / 319,019** |
| `needed [literal]` | 775 / 322,484 |
| frontier F | 1,653 / 808,357 |
| ready rows, all namespaces | 60 / 13,988 |
| leaves, all namespaces | 204 / 52,711 |
| `AutomorphicForm` ready rows | **32 / 7,849** |
| `AutomorphicForm` leaves | 40 / 7,730 |
| `AutomorphicForm` demand | 273 / 118,863 |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

This is the read SET-AF33's landing left (`needed` 763 / 319,019 matches its §6 re-read exactly).

### 0.2 The correction — a last-name shadow, and the row it was hiding

The general row C of a sibling pair read `needed = 1` with `premises_unported = 0`, but its pin proof
cites `NumberField.denseRange_algebraMap_add_adeleSingleAt` **at pin line 525**, and the port does not
hold that theorem: it holds `RatAdele.denseRange_algebraMap_add_adeleSingleAt` — the `K = ℚ` case, at
the **same last name**. The name tier therefore counts the general node as ported and the readiness
guard leaves the row on the shelf. This is the FR-0047 shadow class ("the last-name shadow the check
cannot see"), and **`--unport` is the instrument for it**:

```bash
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
  --unport NumberField.denseRange_algebraMap_add_adeleSingleAt --json > build/shelf-af34-corr.json
```

The corrected read:

| figure | instrument | corrected |
|---|---:|---:|
| `needed [F terminal]` | 763 / 319,019 | **764 / 319,352** (+1 / +333) |
| ready rows | 60 / 13,988 | **59 / 13,461** |
| leaves | 204 / 52,711 | **205 / 53,044** |

and the diff is exactly one row each way: C leaves `ready_rank` and
`NumberField.denseRange_algebraMap_add_adeleSingleAt` enters `leaves_rank` (333 silo, 0 premises, 15
declaration groups). Nothing else moves, so the shelf's *remaining* content is unchanged.

**The finding.** A "needed = 1" claim on this shelf is a premise claim, not a statement claim, and the
name tier is not a statement tier: `RatAdele.…` at the ℚ statement satisfied the general node's name.
The row is genuinely unavailable until its 333-line premise is ported — which is why this set carries
that premise as its own order rather than deferring C.

### 0.3 A scaffold at the wrapper's name counts as ported

The read above was taken **before** the scaffolds of §5 existed, and that ordering is what makes it
the baseline. `frontier.py`'s ported test is the *name* tier: it does not read statements and it does
not look for `sorry`. A scaffold that declares the wrapper's headline (with a `sorry` body) at the
wrapper's name therefore *is* the node, so a read taken while the scaffolds are in the tree prices the
set as landed. Measured on this set, mid-wave, right after the scaffolding of all four modules and the
landing of A only: `needed` read **759 / 317,413** — i.e. all five nodes gone — and the ready block
swapped the four rows for the two rows that only *depend* on them
(`…centralChar_eq_of_agreesAwayFromFinite` 113, `LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet`
1,187). None of that was true yet. The lesson for the landing record: the set's figures are the
**pre-scaffold** read plus the §7 arithmetic, and the post-landing re-read must be taken with every
scaffold sorry-free — the axiom gate (`#print axioms` without `sorryAx`), not `check_port`, is what
certifies that a scaffold is a proof.

## 1. The cut

**One story — the genuine smooth cusp realization `R` of a Hecke eigensystem: what its central
character is (B), what it cannot be (C/C′), and what it can be twisted into (D) — plus the adelic
density input C needs (A).** All five sit in the `SmoothCuspRealizationAt`/`IsGenuineCuspRealizationAt`
vocabulary of `AutomorphicForm/Adelic/ProductionPinsGeneral.lean`; four of the five are pin rows in the
`SmoothCuspRealizationAt` namespace, the fifth is the general-field form of the density lemma that its
`ℚ` twin (`RatAdele/DenseRange.lean`) already has.

B is taken on the recipe's cheap-leaf signal: **199 silo with 7 cone / 20 project consumers** — the
highest fan-in on the AF leaves shelf — and it is the only premise of
`SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` (113) that is not already ported, so B
readies that row on landing (§7).

### 1.1 The pair, and why it is not a duplication (§2 of the recipe)

C (general `F`) and C′ (`F = ℚ`) are **parallel, not nested**: neither pin file cites the other
(their `import Theorems.` lines are disjoint — C cites `NumberField_denseRange_algebraMap_add_adeleSingleAt`,
C′ cites `RatAdele_denseRange_algebraMap_add_adeleSingleAt`). The recipe's "port the general, derive
the special" therefore applies, and it was **measured, not assumed**:

* `productionPinsGeneral F` unfolds to `productionPinsGeneralOf F 1/2 1 1/2 2 …` unfolds to
  `productionPinsOf F (classRepSiegelSet F 1/2 1 1/2 2) (fun N => levelOne … ⊓ finiteAdelicGL2Subgroup F)
  (fun v => heckeGen …) (adelicBox F)`, i.e. **definitionally** the pins C demands
  (`lean/tmp/af34-probe-defeq.lean`: the equality closes by `rfl`);
* the whole ℚ statement follows from C by one application, with `D := classRepSiegelSet ℚ (1/2) 1 (1/2) 2`
  — written out and elaborated as `lean/tmp/af34-probe-derive.lean` (a three-line term, no `convert`).

So C′'s 513-line pin proof (the `ℚ`-only strong-approximation argument) is **not transcribed**; the
port keeps the statement (checker-green, §5) and writes the corollary. The saving is ~500 lines and it
removes the risk that the two copies drift.

## 2. The price

`port_advise --nodes` on the five, then `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines | 1,939 |
| declaration lines | 1,828 |
| — duplicate copies | 20 |
| — boilerplate (`import`/`attrs`/`p2m`) | 111 |
| distinct declaration groups | **174** |
| already in the port (vetted, all tier 1) | **253** |
| **net new math lines (priced)** | **1,555** |
| of which written (C′ derived) | **≈1,065** |

16 trusted substitutions; 2 suspect (`WP → CuspidalSpectrum.fdPins`, `windowBound → clamp01` — both
`def`-typed matches, read the bodies; the twist proof defines its own `windowBound`, and `WP` is the
pin's local abbreviation). Per row, the declaration/helper split is:

| row | public decls | private helpers | helper lines |
|---|---:|---:|---:|
| A `denseRange` | 1 | 22 | 191 (of which 20 new) |
| B central character | 1 | 13 | 137 (11 new) |
| C obstruction (general) | 2 | 47 | 436 |
| C′ obstruction (`ℚ`) | 1 | 47 | 434 (not written) |
| D twist | 36 | 0 | 0 — a flat public surface |

No definition gate beyond §4: `port_advise --with-defs` puts `Def_AutomorphicForm_ProductionPinsGeneral`,
`Def_HeckeCharacter_FiniteOrder`, `Def_NumberField_TateGlobalZeta`, `Def_LanglandsTunnell_RankinSelbergEuler`
and `Def_NarrowRayClassGroup` in the closure; the first three are ported whole (50 + 3 + 13 substitutions),
the last two are imported by the pin files but **their declarations are never used** (0 occurrences of
`primeFibre`/`rsDatum`/`inducedEulerPoly`/`narrowRay*`/`raySymbol`/`coprimeToModulus` in the five `S_`
files), so they are not a gate.

## 3. Homes

The home rule of the recipe §4 (the module must be at or above every port module holding a declaration
the proof consumes), applied per order:

| order | home | the port modules the proof consumes | why this module |
|---|---|---|---|
| **A** | `NumberTheory/NumberField/DenseRange.lean` (**new**) | `LanglandsTunnell/StandardLocalConstantsAt` (`adeleSingleAt`, `finAdeleSingleAt`), `NumberTheory/AdelicBox`, `Topology/Algebra/RestrictedProduct/TopologicalSpace` | the general-field twin of `NumberTheory/RatAdele/DenseRange.lean`; a number-theory module, not an automorphic one |
| **B** | `AutomorphicForm/Adelic/Cusp/GenuineRealization.lean` (**new**) | `AutomorphicForm/Adelic/ProductionPinsGeneral` (which is above `Cusp/ArithRealization` → `Cusp/SmoothRealization`), `HeckeCharacter/FiniteOrder` | the realization's central character — the first theorem about `IsGenuineCuspRealizationAt` itself, below nothing else |
| **C+C′** | `AutomorphicForm/Adelic/Cusp/LevelOneObstruction.lean` (**new**) | `ProductionPinsGeneral`, `NumberTheory/AdelicDock/LocalEmbedding`, `LinearAlgebra/Matrix/SL2Generation`, `NumberTheory/NumberField/DenseRange` (order A) | the "no level-one eigenfunction" theorem; `Cusp/CuspUnrealizable.lean` is the *centre-cut* unrealizability (a different engine: `CentreCutEngine.no_function_of_ne_zero`), so it is not the home |
| **D** | `AutomorphicForm/Adelic/Cusp/RealizationTwist.lean` (**new**) | `ProductionPinsGeneral`, `HeckeEigensystem`, `IdeleNormDet`, `Siegel/Covering`, and the new `AutomorphicForm/Adelic/FnTwist` | the idèle-norm twist of a realization; the twist vocabulary is its own definition layer (§4) |

All four are new modules with **no in-tree importers at creation**, so every cascade is a header. The
three `Cusp/` modules sit beside `SmoothRealization.lean`/`ArithRealization.lean` and above
`ProductionPinsGeneral`, which is the family hub; none of them imports another.

**No promotion and no migration.** Every premise of B, C′ and D is already public in the port at the
statement the `Theorems/` wrapper states (checked by reading the port declarations, not by last name):
`Place`-style shadows do not arise here because each premise name is unique in the tree
(`ProductionPinsGeneral`'s `IsGenuineCuspRealizationAt`, `IdeleNormDet.ideleNorm_det_globalPoints`,
`TateGlobal.ideleNorm_uniformizerIdele`, `TateGlobalContinuousIdeleNorm.continuous_ideleNorm_det`).

## 4. The definition layer — `Def_AutomorphicForm_FnTwist`

D's proof uses `fnTwist` (32 occurrences) and `twistedCentralChar`, which live in the pin's
`Definitions/Def_AutomorphicForm_FnTwist.lean` (104 lines / 14 declarations) — **not ported**, and a
definition gate the read cannot see (it is a `Definitions/` module of the twist proof, not a graph
node). It is the manager's (§3 of the instructions): ported whole, at the pin's names, into

**`AutomorphicForm/Adelic/FnTwist.lean`** — `14 ok / 0 mismatch / 0 missing`, built (4.6 s), wired by
`spec-pin: Definitions/Def_AutomorphicForm_FnTwist.lean`. Its one adaptation is the port's
`FLT.SmoothVectors.IsSmoothVector`/`RightTranslationFn` spelling (the pin's are the same names in the
same namespace); the module's header records it.

## 5. The orders, and the scaffolding

The manager wrote the four modules' headers, imports, wires and statements with `sorry` bodies, and
each scaffold is **checker-green before dispatch**:

| module | scaffold |
|---|---|
| `NumberTheory/NumberField/DenseRange.lean` | 1 ok / 0 / 0 |
| `AutomorphicForm/Adelic/Cusp/GenuineRealization.lean` | 1 ok / 0 / 0 |
| `AutomorphicForm/Adelic/Cusp/LevelOneObstruction.lean` | 2 ok / 0 / 0 |
| `AutomorphicForm/Adelic/Cusp/RealizationTwist.lean` | 1 ok / 0 / 0 |

Orders (`lean/tmp/`): **AF34A** `WORKORDER-AF34A-denserange.md`, **AF34B**
`WORKORDER-AF34B-central-character.md`, **AF34C** `WORKORDER-AF34C-levelone-obstruction.md`, **AF34D**
`WORKORDER-AF34D-idele-norm-twist.md`. A, B, D are disjoint files and run concurrently; C imports A, so
it is dispatched when A is green (the dependency is the *proof*, not the statement: C's scaffold is
already green).

Each order carries the standard gates: `check_port --force` at 0 mismatch / 0 missing with the surface
gate run, axioms clean on the headline, the module's own build under `flock`/`timeout` and silence,
`dedup`/`move_dead`, and a `spec/` consumer zone with a real composition.

## 6. Per-row traps

**A (denseRange, 333).** The ℚ twin in the port (`NumberTheory/RatAdele/DenseRange.lean`, 309 lines,
21 declarations) is the same Minkowski argument and documents every substitution it needed; read it
first. The general version's two extra ingredients are the Minkowski bound
(`exists_minkowskiBound_lt`) and `idealUnit` with `absNorm_idealUnit`. The statement lives at
**`K : Type`** (not `Type*`): the port's `StandardAddChar.adeleSingleAt` binds `K : Type`, so a
universe-polymorphic `K` fails at elaboration — this is the pin wrapper's own spelling.

**B (central character, 199).** The `private` helpers are `isLevelOneMatrix_of_isLevelUnit`,
`centralScalar_mem_level`, `continuous_fullChar`, `isLevelUnit_inv`, `admitsModulus`; three of them
(`fullChar_apply`, `globalPoints_scalar`, `centralScalar_mul_comm`) have statements already in the
port (`globalPoints_scalar` byte-identical) — reuse the ported ones, do not re-prove. `AdmitsModulus`
is `HeckeCharacter.AdmitsModulus F` (the `K` is an explicit first argument in the port).

**C (obstruction, 527).** The proof is over a general number field and closes with
`NumberField.denseRange_algebraMap_add_adeleSingleAt F v` (order A). The `ℚ` row C′ is **derived**:
`not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt ℚ (classRepSiegelSet ℚ (1/2) 1 (1/2) 2) Ψ R hR v hv`,
which is `lean/tmp/af34-probe-derive.lean`. Do not transcribe C′'s 513-line proof; if the derivation
fails the order stops and reports. C imports `AdelicDock/LocalEmbedding` (`localEmbed`/`finEmbed`, 14
uses) and `LinearAlgebra/Matrix/SL2Generation` (the `SL₂ = ⟨diag, unipotent, weyl⟩` closure, 13 uses).

**D (twist, 367).** A **flat public surface of 36 declarations** — the surface gate matters here: the
pin states every one of them publicly (`nchar`, `coe_nchar_apply`, `chiDet_nchar_apply`,
`norm_chiDet_nchar`, `twistRealization`, `continuous_twistRealization`, …), so nothing may stay
`private` except a genuine local re-spelling. `nchar s` is the norm character `x ↦ ‖x‖ ^ s`; the
`MemLp` bound is the pin's `memLp_fnTwist_nchar`; the `windowBound`/`ideleNorm_det_pinch_of_mem_centreCut`
pair is the measure-side input. The twist vocabulary is `AutomorphicForm.fnTwist`/`twistedCentralChar`
(`AutomorphicForm/Adelic/FnTwist.lean`, landed with this set).

## 7. Forecast

Every line column computed from the **silo** (the AF33 lesson: `needed` and the frontier count silo,
not `port_plan`'s net).

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 763 / 319,019 | **759 / 317,413** |
| `needed [literal]` | 775 / 322,484 | **771 / 320,878** |
| frontier F | 1,653 / 808,357 | **1,658 / 810,296** |
| ready block | 60 / 13,988 | **57 / 12,495** (4 rows out; 1 in) |
| leaves block | 204 / 52,711 | **204 / 52,711** (A is not in the instrument's block: it is shadowed; the corrected block goes 205 → 204) |
| `AutomorphicForm` demand | 273 / 118,863 | **269 / 117,257** |
| `AutomorphicForm` ready | 32 / 7,849 | **29 / 6,243** |
| `NumberField` demand | 99 / 34,198 | **98 / 33,865** |
| rows readied | — | `centralChar_eq_of_agreesAwayFromFinite` (113) needs B + a ported lemma only |

(C′'s 513 silo leaves `needed` although it is written in 10 lines: the frontier counts the node, not
the proof.) The corrected read after the set should be re-taken with no `--unport` — the shadow is
resolved by porting A at the general statement.

## 8. The landing (2026-11-08)

Four orders, five modules, all green. §4's definition layer was the manager's; the proofs were the
orders'.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| *(def)* | `AutomorphicForm/Adelic/FnTwist.lean` | 125 | 14 (all public) | 14 ok | 4.6 s | — |
| **A** | `NumberTheory/NumberField/DenseRange.lean` | 399 | 23 (1 public, 22 `private`) | 1 ok | 4.6 s | clean |
| **B** | `AutomorphicForm/Adelic/Cusp/GenuineRealization.lean` | 220 | 13 (all public after the surface gate) | 13 ok | 3.4 s | clean |
| **C** | `AutomorphicForm/Adelic/Cusp/LevelOneObstruction.lean` | 557 | 51 (`WP` + 2 headlines public, 48 `private`) | 3 ok | 5.8 s | clean, both |
| **D** | `AutomorphicForm/Adelic/Cusp/RealizationTwist.lean` | 412 | 36 (all public) | 36 ok | 4.3 s | clean |

`dedup --within` on each: 0 clusters. `move_dead --dry-run`: nothing dead in any of them. The
set-level probe `tmp/af34-axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for **all
five** headlines (the derived `ℚ` row included). Consumers:
`spec/NumberFieldSetAF34AConsumer.lean` (93), `spec/AutomorphicFormSetAF34BConsumer.lean` (123),
`spec/AutomorphicFormSetAF34CConsumer.lean` (117), `spec/AutomorphicFormSetAF34DConsumer.lean` (102),
each **0 errors**, each a real composition.

**What the set consumed**: 5 nodes / 1,939 silo; **1,299 declaration lines for the four rows plus 95
for the definition layer** against `port_plan`'s 1,555 priced — the difference is the `ℚ` row's ~500
lines not written (§1.1) partly repaid by the general row and A coming out longer than their helper
estimates (502 and 340 declaration lines). 4 new modules + 1 definition module, 8 `spec-pin:` lines;
4 new imports, each reported by its order (`LsXiCharacter` in B for `globalPoints_scalar` and
`continuous_centralScalar`; `IdeleNormDetGlue`, `TateGlobal/IdeleNormValues`,
`TateGlobalContinuousIdeleNorm` in D for the pin's `Theorems/` dependencies). 0 promotions, 0
migrations, 0 legacy touches, no tree build.

### 8.1 Deviations held for review

1. **The `ℚ` row is derived** (§1.1) — the set's headline decision; the pin's 513-line argument is not
   transcribed, and the defeq claim was *measured* twice: `tmp/af34-probe-defeq.lean` (the pins close by
   `rfl`) and `tmp/af34-probe-derive.lean` (the three-line term elaborates unchanged against the
   finished module). C's consumer reads the same statement back as the `(1/2) 1 (1/2) 2` instance.
2. **B promotes all 12 helpers; A keeps its 22 `private`.** Both are deliberate: B's helpers are the
   level-unit / central-character machinery the `SmoothCuspRealizationAt` tail will consume (playbook:
   "never make real mathematics `private`"; the surface gate read 13 ok with `private` dropped, and no
   `MISSING`), while A's are `Rat`-free Minkowski plumbing whose ported `ℚ` twin keeps its own copies
   private and documents that as its precedent. Recorded, not silently mixed.
3. **`TwistRpow.det_diagOne` is a one-line alias** of the already-ported
   `NumberField.TateGlobal.det_diagOne` (same statement, two pin proofs — the port-once rule); the
   module still checks 36 ok. This is the only edit the manager made inside a worker's module.
4. **C drops two pin helpers as dead in the pin**: `WP_gen_eq` (pin `:44`) and `level_invariant'`
   (pin `:365`) — `grep -c` finds only their own definitions. It **keeps** the pin's four
   `attribute [local instance]` lines (pin `:17-18`): without them `MeasurableSpace` synthesis fails in
   `apply_unipotent_mul`/`toFun_eq_zero`.
5. **C's `haveI` → `have`** at pin `:483`/`:485` — the pin's alternative is
   `set_option linter.style.haveILetI false`, which the port forbids.
6. **A's `open scoped Classical in`** (pin `:156`) is load-bearing at v4.34, not cosmetic:
   `MeasureSpace (mixedSpace K)` is `Measure.pi`, which needs `Encodable` of the two place subtypes.
7. **Version drift**: `Finset.prod_le_prod → prod_le_prod₀` (D, pin `:222`/`:224`);
   `zero_le' → zero_le` (B, pin `:137`); `ideleNorm_det_eq_prod_archDetNorm_pow_mult` called without
   the explicit `K` (D); one unused `simp` argument dropped (D, pin `:157`).

### 8.2 Two findings

* **The axiom gate must follow the module's own build.** C's first `#print axioms` reported `sorryAx`
  *through the import* — the scaffold's stale `.olean` (written with the `sorry` bodies) was still what
  the probe loaded. The certification is meaningful only after `lake build` refreshes
  `.lake/build/lib/lean/.../LevelOneObstruction.olean`. Neither `check_port`'s `ok` nor the edit loop's
  silence can see this; FR-0033 is the ancestor and the friction is logged as FR-0158.
* **The coset-sum/pointwise gap.** `SmoothCuspRealizationAt.hecke_eigen` states the eigenvalue relation
  in the **coset-sum** form `∑ i, φ (g * reps i) = Ψ.a v * φ g`, not pointwise in `g * gen v`; the bridge
  between the two is not in the port and is not implied by it (the pointwise reading is exactly what C
  refutes). The natural next composition — "every place outside `R.exceptionalSet` divides `Ψ.level`" —
  therefore carries that bridge as an explicit hypothesis in C's consumer. It is a real row for a later
  set (a Hecke-index/coset computation), not a consumer-zone trick.

### 8.3 The re-read, measured

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af34-final.json
python3 frontier.py --selfcheck   # PASS
```

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 763 / 319,019 | 759 / 317,413 | **759 / 317,413** ✓ |
| `needed [literal]` | 775 / 322,484 | 771 / 320,878 | **771 / 320,878** ✓ |
| frontier F | 1,653 / 808,357 | 1,658 / 810,296 | **1,657 / 809,963** |
| ready block | 60 / 13,988 | 57 / 12,495 | **59 / 13,881** |
| leaves block | 204 / 52,711 | 204 / 52,711 | **203 / 52,512** |
| `AutomorphicForm` demand | 273 / 118,863 | 269 / 117,257 | **269 / 117,257** ✓ |
| `AutomorphicForm` ready | 32 / 7,849 | 29 / 6,243 | **30 / 6,555** |
| `NumberField` demand | 99 / 34,198 | 98 / 33,865 | **99 / 34,198** |

**The two misses, and why.** (i) The frontier and the `NumberField` demand never counted A: its node id
was already in the instrument's declared-names tier through the shadow (§0.2), so porting the real
declaration adds nothing to either count — the 333 lines were invisible before and after (the tier that
did record it is the `SOURCES Thm_` count, 1,472 → 1,477; the union is keyed by node id and the id was
already there). That is the same effect the §0.2 correction priced, and it is why the corrected read is
the one to quote for A. The correction is now **spent**: re-running the read with
`--unport NumberField.denseRange_algebraMap_add_adeleSingleAt` leaves `ready_rank` and `leaves_rank`
identical (59 / 13,881 and 203 / 52,512) and `needed` at 759 / 317,413 — nothing is left for the override
to move, only the frontier's manual −1.
(ii) The ready/leaves cells were mis-assigned: **B is a leaf, not a ready row** (0 premises), so the
ready block loses only three rows while the leaves block loses one; and **two** rows were readied, not
one — `satake_norm_lt_…` (1,187) entered alongside `centralChar_eq_of_agreesAwayFromFinite` (113).
Every silo column was computed from the silo, so the line figures still landed where §7 said.

**Rows the set readied** (both verified: every other premise is a port declaration at its own
statement, checked by name *and* by statement, not by last name):

| row | silo | lev | why it is ready |
|---|---:|---:|---|
| `LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet` | **1,187** | 1/2 | cites B and C; its other premises are `DetNormSlabFundamentalDomain`, `PeterssonSlabPairing` and `TateGlobal/NormExponent.exists_norm_apply_eq_ideleNorm_rpow`, all ported |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | **1/16** | cites B and the ported `HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq` |

The AF ready shelf is now **30 rows / 6,555 silo**, headed by
`isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043) and the set's own readied
`satake_norm_lt_…` (1,187) — the Satake bound is the natural next cut, and the largest single-row
opportunity in the column.

### 8.4 The one cross-module duplicate

`dedup --cross` over the five modules reports exactly one cluster: `exists_pow_lt_of_lt_one`, 21 lines
in `NumberField/DenseRange.lean` against 17 in `RatAdele/DenseRange.lean`, both `private`. Kept, with the
reason: it is the pin's own per-file private prelude (the two pin files carry it independently, as the
`ℚ` twin's header documents), it is a `WithZero (Multiplicative ℤ)` utility rather than a mathematical
engine, and promoting it would put a 17-line helper on the public API for no consumer. The rule it
follows is the recipe's: a *pin-derived* private prelude stays with its module; the dedup phase targets
re-proved engines.

## 9. What this set does not do

- **`a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet` (125)** and the rest of the
  `SmoothCuspRealizationAt` tail (`centralChar_eq_of_agreesAwayFromFinite` excepted): they wait on
  `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`,
  `exists_sesqForm_eq_peterssonIntegral_…` and the Satake bound, none of which this set touches.
- **`AutomorphicForm` ready rows outside the family** (`a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero`
  468, `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` 429,
  `exists_integral_rightConv_eq_rightConv` 514, the `Weyl` value pair 360 + 217, the
  `isInducedSection` height row 1,043): untouched, and 1,043 is still the largest single row on the
  shelf.
- **The Euler-product consumer** `exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul`
  (995): still one premise short of AF33's pair plus the meromorphic continuation.
- **No promotion, no migration, no legacy module touch, no tree build.**
