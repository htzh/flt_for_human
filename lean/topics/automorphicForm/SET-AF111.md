# SET-AF111 — the polynomial-decay shelf: one giant row and its consumers

**Status: PLANNED and scaffolded (2026-11-27).** The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF110 left a shelf of fifteen ready rows, **6,727 silo**; this set cuts **twelve of
them, 6,525 silo**, in five orders: six new modules, four insertion sites (six rows).

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | polynomial decay of the Weyl-unipotent `addChar` integral | 1 | 3,747 | `AutomorphicForm/Adelic/PolyDecay.lean` (new) |
| B | the full-level slot/root dictionary | 3 | 1,404 | `ModularCurve/FullLevelSlotAlgHom.lean` (new), `ModularCurve/FullLevelFunctionField.lean` (insert ×2) |
| C | the geometric cycle, and `q`-th roots of residues | 2 | 535 | `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (insert), `AlgebraicCurve/Genus/ResiduePowerKrullDim.lean` (new) |
| D | the trace dual's measure, and the character normalization | 4 | 562 | `NumberTheory/AdelicFourier/TraceDual.lean` (insert ×2), `…/PoissonNormalized.lean` (new), `AutomorphicForm/Adelic/StdAddCharNormalization.lean` (new) |
| E | the local character's level, and the defect equation | 2 | 277 | `LanglandsTunnell/TateLocal/AddCharLevelDifferent.lean` (new), `TateCurve/SeriesIdentities.lean` (insert) |
| **total** | | **12** | **6,525** | 6 new + 4 insertions |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af111_read.json
```

The correction list is still SET-AF109's `unport_final.txt`, **20 names**, and `--selfcheck` still reports
the same twenty lines.

| figure | value |
|---|---:|
| `needed [F terminal]` | **226 / 142,553** |
| ready rows | 15 / 6,727 |
| leaves | 5 / 13,761 |
| withheld (FR-0044 guard) | 6 / 1,970 |

The shelf is SET-AF110's payoff, and its shape is new: **one row is 56 % of it** (the 3,747-line
polynomial-decay theorem), and the rest are consumers spread over five subjects. Three rows are not cut
(§5): the false ready (`exists_sum_smul_eq_of_isIntegralQExp_gamma1`, 36), the padic-Tate-module row
(`rep_tateModule_jOne_comm`, 24) and — new this shelf — `TateCurve.lineCoeff_eq_zero` (142), which the
def-layer read shows is **not statable**: it needs `Definitions/Def_TateCurve_QShift.lean` (48 declarations,
43 absent) **and** `Definitions/Def_TateCurve_DefectLines.lean` (128 declarations, all absent). That is a
definition-layer wave of 176 declarations, not a row.

Every other row's def-layer absences are structure fields; the only `GATE` lines on the shelf are that
row's two.

**The premise check was run after the fact, and it matters** (FR-0338): `tmp/af111/premcheck.py` reads
**54 premises ported, 3 SHADOW** — three premises the readiness test credited whose port copy is not the
pin's statement (§6.1). It belongs in this §0 read, next to the def-layer classification, and the next set
runs it before cutting.

## 1. The stories

### A — polynomial decay of the Weyl-unipotent `addChar` integral (3,747)

`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`: for a unitary Hecke
pair, a global character, `Re s > 1/2` and an induced archimedean-finite continuous `φ`, the `addChar`-twisted
unipotent integral decays like `(1 + ‖mixedEmbedding ξ‖)^{-N}` for every `N`. It is the estimate the
Eisenstein bound consumes, and the largest single row of the column (1.5× SET-AF109A's 2,468).

The pin's 240 declarations are one archimedean computation in layers, which the order's block plan follows:
lattices and idele classes; the place Haar measures; the row-isometry ↔ unitary/orthogonal dictionary; the
smooth-bounded CLM calculus; the Iwasawa real component; the `rpow`-negNat estimates; the trace/Fourier
pairings and `phaseAt`; the Weyl-unipotent-Borel factorization; the idele characters; the `radC`/`realRad`
integrations; then `archChar_factorization` (~250 lines) and `solution` (~925 lines).

### B — the full-level slot/root dictionary (1,404)

* `exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg` (906, 64 declarations): at a place where
  `jqModC` has negative order, a `K`-algebra homomorphism into `LaurentSeries K` with the twisted
  `q`-expansions and a measured order scaling — the *slot* half;
* `exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental` (309, 46): every root of the
  modular polynomial is the `q`-expansion of such a homomorphism — the *root* half (insertion);
* `ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero` (189, 34): the modular polynomial's
  image in `K(j)` is irreducible (insertion).

### C — the geometric cycle, and `q`-th roots of residues (535)

* `Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero` (286): the `Pic0`-side conclusion of
  SET-AF110D's descent row (insertion into that module);
* `RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one` (249): if the
  residue field's genus equals `F`'s and `w^q = residue f` with `f`'s orders divisible by `q`, then `f` is a
  `q`-th power in `F` — the consumer of SET-AF110D's genus bound.

### D — the trace dual's measure, and the character normalization (562)

* `measure_setOf_forall_addChar_finitePart_mul_eq_one` (263) and
  `isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one` (117): the *measure* and the
  *topology* of the trace-dual vanishing set (insertions into `AdelicFourier/TraceDual.lean`);
* `tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one` (64): Poisson summation
  for any global character at a normalized Haar measure — the hypothesis-free form of SET-AF110B's row;
* `AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` (118): every global
  character is `stdAddChar` composed with multiplication by some `a ≠ 0` — the normalization that turns the
  `hψ_inf` hypothesis into a consequence.

### E — the local character's level, and the defect equation (277)

* `LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal` (252): the level of
  `psiLocal K v` is the count of the different ideal — the Tate-local form of the conductor;
* `TateCurve.equation_of_defectCoeff_eq_zero` (25): vanishing defect coefficients put the point on the
  curve — the converse of SET-AF110C's defect expansion (insertion).

## 2. The scaffolds

Ten files are touched before any order starts: **six new** and **four insertions**. All elaborate at the
200 k edit-loop cap, silent but for their `sorry`s.

| order | module | new | scaffold `check_port` |
|---|---|---|---:|
| A | `AutomorphicForm/Adelic/PolyDecay.lean` (new) | 1 | **1 ok** |
| B | `ModularCurve/FullLevelSlotAlgHom.lean` (new) | 1 | **1 ok** |
| B | `ModularCurve/FullLevelFunctionField.lean` (insert ×2) | 2 | **8 ok** (6 before) |
| C | `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (insert) | 1 | **2 ok** (1 before) |
| C | `AlgebraicCurve/Genus/ResiduePowerKrullDim.lean` (new) | 1 | **1 ok** |
| D | `NumberTheory/AdelicFourier/TraceDual.lean` (insert ×2) | 2 | **19 ok** (17 before) |
| D | `NumberTheory/AdelicFourier/PoissonNormalized.lean` (new) | 1 | **1 ok** |
| D | `AutomorphicForm/Adelic/StdAddCharNormalization.lean` (new) | 1 | **1 ok** |
| E | `LanglandsTunnell/TateLocal/AddCharLevelDifferent.lean` (new) | 1 | **1 ok** |
| E | `TateCurve/SeriesIdentities.lean` (insert) | 1 | **17 ok** (16 before) |
| **total** | **10 files** | **12 rows** | **52 ok / 0 / 0 / 0 / 0** |

### 2.1 What the scaffold pass caught

* **the `Norm (mixedSpace F)` instance is behind `Classical`**: order A's headline writes
  `‖mixedEmbedding F ξ‖`, and the instance search for the norm on `NumberField.mixedEmbedding.mixedSpace F`
  only succeeds with `open scoped Classical` in scope (the port's own modules that use that norm carry it;
  `RightConvRegularity` does, `PolyDecay` did not). One `open scoped Classical` at file level fixes it, with
  the statement text unchanged — the pin's wrapper attaches the same scope to the declaration
  (`open scoped Classical in`).
* **three imports the edit loop added**: `NumberTheory/NumberField/MixedEmbedding` (for the norm),
  `NumberTheory/AdelicFourier/Space` (idem, and the Schwartz layer), `AutomorphicForm/Adelic/RightConvolution`
  (the row-isometry/`NormedAddCommGroup` dictionary). The scaffold's own premise list was otherwise exact.
* **the home direction, measured**: `tmp/af111/homes_audit.py` reads **57 premise edges over the 12 rows,
  `problems 0`**. The first-cut table (`tmp/af111/homes.py`) prints `candidates: NONE` for four of the
  twelve (A, B's 906-row, C's 249-row, E's 252-row) and names the insertion site for the rest.
* **no insertion site is shared between two orders**: `FullLevelFunctionField.lean` takes B's two rows and
  `TraceDual.lean` takes D's two, each from a single order, so all five orders can run concurrently.

## 3. The pricing

| figure | value |
|---|---:|
| raw `S_` lines (the 12-row cut) | 6,525 |
| declaration lines | 6,237 |
| of which duplicate copies | 132 |
| boilerplate (imports/attrs/`p2m`) | 288 |
| distinct declaration groups | 400 |
| **already in the port (vetted)** | **471** |
| **net new math lines** | **5,634** |
| substitutions | 39 trusted / 9 suspect |

The nine suspects are the parser's type-only `def` matches (six `archIdele`, three `cplxCenter`); both are
**real definitions** in order A's pin, not types, so the assignment to order A's work order is "read the
body". The shelf's reuse is concentrated in order C's 286-row and order D's two Fourier insertions, whose
premises are the previous set's own modules.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own**; the engine diff by hash; `#print axioms`; the silent
edit loop and one locked `lake build`; `dedup --within`; `move_dead --dry-run`. For build time the gate
is **the low-cap iterate-and-fix loop, not a measurement** (playbook §"Bound, do not measure" and §"The
edit loop runs on a deliberately low cap"): a blow-up is found by aborting fast at the low cap, isolated
to its declaration, and fixed at its inference — no heartbeat ladders, no threshold bisection, no "probe
pairs", and a genuine long proof is restructured rather than exempted. The house policies carry unchanged (surface gate at review, **no `import
Mathlib`**, declaration-scoped linter options only, **no `set_option maxHeartbeats` ever installed**).

## 5. Not cut — named and deferred (FR-0040)

* **`TateCurve.lineCoeff_eq_zero` (142)** — the only row of the shelf whose *statement* is def-gated:
  `Def_TateCurve_QShift` (48 declarations, 43 absent) **and** `Def_TateCurve_DefectLines` (128 declarations,
  all absent). Porting 176 declarations to state a 142-line row is a definition-layer wave; the row is
  registered for one.
* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)** — the false ready whose premise
  (`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, 261) is unported and whose chain is ~3,040
  silo of `ModularForm`-level rational structure (CARRY-FORWARD).
* **`ModularCurve.rep_tateModule_jOne_comm` (24)** — held for `Def_EllipticCurve_TateModule` (883 pin
  lines / 69 declarations) and `Def_ModularCurve_X1HeckeModule` (14 absent), i.e. the padic-Tate-module
  programme.
* **The five leaves (13,761 silo)** — unchanged (all def-gated).
* **Withheld by the FR-0044 guard (6 rows / 1,970):** the prunable subject's work.

## 6. The landing

**LANDED (2026-11-27).** Ten files (six new modules, four insertion sites, six rows), **12 rows / 6,525
silo**, **183 checked declarations** (12 of them the rows), 9,170 lines / 455 declarations across the ten
files, no `sorry`, no `sorryAx`, every module silent at the 200 k edit loop and every one built.

| order | module(s) | lines | checker | engine diff | axioms | dedup | move_dead |
|---|---|---|---|---|---|---|---|
| A | `AutomorphicForm/Adelic/PolyDecay.lean` (new) | **3,814** | **1 ok / 0 / 0** (216 `private`; the pin has no public helper) | pin decls 241 → 217: **209 by hash**, 7 unaccounted (the premise substitute below), 30 prelude rows imported public | 1 clean | 1 (the pin's own `real_botRowNormSq_pos`/`realRadSq_pos` pair) | **16 / 90** — dead in the pin too, recorded |
| B | `ModularCurve/FullLevelFunctionField.lean` (insert ×2) | **776** (+374) | **60 ok / 0 / 0** (6 before) | 92 pin publics → 86 declared + 2 imported + 4 folded, **0 MISSING** | 60 clean | 0 | 0 / 0 |
| B/G | `ModularCurve/FullLevelSlotAlgHom.lean` (new) | **991** | **64 ok / 0 / 0** | 64 pin rows → 64 declared, **empty diff** (63 distinct hashes; the pin repeats `jF`/`jNF`) | 64 clean | 0 | 0 / 0 |
| C | `AlgebraicCurve/Pic0/BaseChangeDescent.lean` (insert) | **498** (+264) | **6 ok / 0 / 0** (2 before) | 16 rows: 6 declared + 8 imported (1 alpha) + 2 folded, **0 MISSING** | 6 clean | 0 | 0 / 0 |
| C | `AlgebraicCurve/Genus/ResiduePowerKrullDim.lean` (new) | **300** | **8 ok / 0 / 0** | 11 rows: 8 declared + 2 imported + 1 folded, **0 MISSING** | 8 clean | 1 (the pin's own `main` ↔ headline pair) | 0 / 0 |
| D | `NumberTheory/AdelicFourier/TraceDual.lean` (insert ×2) | **776** (+331) | **24 ok / 0 / 0** (19 before) | 39 pin publics → 26 declared + 6 imported (alpha) + 5 folded, **2 MISSING** (one is the pin's own dual spelling, FR-0336; one the AF110E merge) | 24 clean | 4 (all the pin's own pairs) | 0 / 0 |
| D | `NumberTheory/AdelicFourier/PoissonNormalized.lean` (new) | **112** | **1 ok / 0 / 0** | 1 pin decl → 1, **1 hash** | 1 clean | 0 | 0 / 0 |
| D | `AutomorphicForm/Adelic/StdAddCharNormalization.lean` (new) | **170** | **1 ok / 0 / 0** (2 `private`) | 3 pin decls → 3, **3 hash** | 3 clean | 0 | 0 / 0 |
| E | `LanglandsTunnell/TateLocal/AddCharLevelDifferent.lean` (new) | **304** | **1 ok / 0 / 0** (8 `private`; surface probe 9 ok) | 10 pin decls → 9, **9 by hash** | 9 clean | 0 | 0 / 0 |
| E | `TateCurve/SeriesIdentities.lean` (insert) | **1,428** (+10) | **17 ok / 0 / 0** (16 before) | 118 pin decls (27 sources) → 62; **55 hash**, 1 name (pre-existing), 6 `solution`s | 17 clean | 0 | 0 / 0 |
| **set** | **10 files** | **9,170** (455 declarations) | **183 ok / 0 / 0 / 0 / 0** | 183 by hash; 0 own; the engine diffs' only non-credit is order D's pin-internal dual spelling (FR-0336) | **183 clean, no `sorryAx`** | 7 clusters, all the pin's own pairs | 0 / 0 everywhere except order A's 16 / 90 (dead in the pin too) |

The set-level gates, run on the landed tree:

* **wave build** — every module built in its order's locked run (24 s to 72 s apiece after FR-0339's fix),
  `0 warning lines` from any file;
* **collision probe** — `lean/tmp/af111/collision-probe.lean` over all ten: **silent, exit 0**;
* **home audit** — **57 premise edges over the 12 rows, `problems 0`**;
* **cross-module `dedup`** over the ten (471 declarations, `--cross --min-cost 8`): **0 clusters, 0 removable
  lines**;
* **consumer zone** — `spec/SetAF111Consumer.lean`, two zones, **exit 0**.

The row-2 insertion's cost is worth recording: its 10 lines move nothing (the module's pair is AF110C's
2,500/3,000), because the fifteen `private` prelude rows it calls were already there.

### 6.1 Three premises the readiness test credited that the port does not have

`tmp/af111/premcheck.py` (the statement-level premise check, run over the twelve rows) reads **54 premises
ported, 3 SHADOW**, and all three were hit by the orders that needed them:

| premise | port copy | what happened |
|---|---|---|
| `MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left` | `AutomorphicForm/Adelic/LocalIntertwiningFinprod.lean` (`∀ K, ρ (K ×ˢ univ) < ⊤`, a **finite** second marginal) | order A: the pin asks for a σ-finite *exhaustion* `∃ B, ⋃ n, B n = univ ∧ ∀ n K, ρ (K ×ˢ B n) < ⊤`, and the difference is load-bearing for `adelicAddHaar`. The pin's own 149-line proof was transcribed `private` in the module (7 declarations, the engine diff's "unaccounted"). |
| `AlgebraicCurve.KummerCover.finrank_eq` | `LinearAlgebra/Matrix/SimultaneousEigenbasis.lean` (a different `finrank_eq`) | order C: inlined the one-line mathlib proof at its single use site. |
| `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | `NumberTheory/NumberField/GlobalAddChar/Circle.lean` | the same shadow SET-AF109's 2,468-line row met; there the substituted copy was close enough to be used, here order A does not touch it. |

**The instrument should have run at scoping, not at landing** (FR-0338): the shelf read's `needed = 1`
counts a premise as present *by last name*, and three of this set's premises are not the pin's statement.
The recipe's §4 already says to run `premcheck.py` "before cutting any shelf whose rows are consumers";
this set did not, and paid for it inside the orders (one substitute engine written under time pressure).

### 6.2 The build-time fix, as the policy's worked example

Order A's row is the column's largest, and the pin buys it with `set_option maxHeartbeats 8000000 in` on the
headline. Transcribed verbatim it aborted at 200 k on two `whnf`/`isDefEq` blow-ups, both at the two
`integrable_phaseAt_mul_of_isReal/isComplex` applications in `hΦint`: the integrand's `G` was left to
higher-order unification, which then had to check `w.Completion =?= ℂ` (a `dite` unfolding; `-Ddiagnostics`
named 186 k `AdeleRing` and 23 k `Classical.choice` unfolds). Fixed **at the bound site** — the inner
integrability hoisted into a named `hG` and `G` given explicitly in the volume variable — after which the
module is silent at 200 k with nothing installed. No ladder, no probe pair, no threshold: exactly the loop
the playbook's §3.5 now prescribes (FR-0337), and the reason the 8 M pin budget was unnecessary.

**The fallback cure, with its precedent.** Order B's 906-row module is the set's one remaining build-time
question: fully transcribed and statement-green (64 ok), but its *proofs* carry ~10 `whnf`/`isDefEq` sites
that compare two coercion towers — `↥(modularFunctionFieldFullC K N)` against
`↥K⟮jqModC K⟯⟮jqNModC K N⟯` — and the first of them (`coe_jTr`, a three-line `unfold jTr; rfl`) does not fit
the cap. The fixes tried first are proof-side and free of statement cost: write the structure fields with the
projection already applied (`⟨x.1, …⟩` instead of `⟨x, …⟩`, which removes the re-inserted coercion), and bind
each carrier's syntactic form once in a `private` coercion lemma to `rw` instead of unfolding. If that is not
enough, the remaining cure is the one this repo already uses twice —
`spec/decl_markers.tsv`'s `PiPoissonSummation.LocSum` / `periodizeCM` rows: *name the type at its bound site,
record an `own:` row with the measured reason, and keep `check_port` green*. That is the manager's write, in
the playbook's `§3.5 "give the type one syntactic form"` — a registered deviation, never a `maxHeartbeats`
bump.

**Policy change from this set onward (the reviewer's ruling, 2026-11-27): a build-time blow-up is
isolated and *fixed* at the low cap, never *measured*.** The earlier briefs' "probe pair recorded and never
installed" gate is withdrawn: no heartbeat ladders, no threshold bisection, no "silent at X / fails at Y"
tables. The loop is the playbook's `§"Bound, do not measure"` + `§"The edit loop runs on a deliberately low
cap"`: abort fast at 200 k (or lower on the suspect declaration), isolate, fix the inference (blocked
unification, a coercion-unfolding search, an instance diamond, a zeta-`let`), restructure a genuinely long
proof, and never install `set_option maxHeartbeats`. A report states *what blew up, what changed, and that
the module is silent at 200 k* — nothing else. The orders of this set that reported ladders did so under the
old gate; their numbers are recorded in `lean/tmp/af111/` and are not part of the set's acceptance.

### 6.3 The consumer zone

`spec/SetAF111Consumer.lean` elaborates at **exit 0**, two zones, both *hypothesis-discharging*:

* **Zone 1 — Poisson summation at the standard character**: order D's
  `tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one` at `ψ := stdAddChar F`,
  with `NumberField.StandardAddChar.isGlobalAddChar_stdAddChar` supplying the character hypothesis — the
  pin's statement, one hypothesis lighter;
* **Zone 2 — the polynomial decay at the standard character**: order A's 3,747-line headline at the same
  `ψ`, same composition. This is the set's real API test: it re-states the pin's `let α` binder block and
  applies the headline at a *named* character (what the Eisenstein assembly does), and it compiles only
  because the headline's `ψ` is a plain binder and the standard-character fact is public.

Both zones draw on four modules across two orders; neither is a `#check`.

### 6.4 The slot module's real defect, and why every reading missed it (FR-0339)

The order that first "completed" the slot row reported it complete and statement-green, with only wall time
open. The follow-up order measured the pristine state and found **2 elaboration errors** in it: a
`(kernel) deterministic timeout` on `phiRF_algebraMap` (215 s of type checking, essentially the whole
≥280 s build) and two `failed to synthesize CoeT …` at the `AlgHom` call sites of
`Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`. A file with errors writes **no `.olean`**, so the
build could never have exited 0 at any timeout — "wall time only" was the wrong diagnosis.

Root cause: `Algebra K (LaurentSeries K)` has two instances (`HahnSeries.instAlgebra` and
`HahnSeries.powerSeriesAlgebra`); the imported lemma's statement was elaborated with the first, this file's
search picks the second, and the `AlgHom` telescopes are not `isDefEq`. The port already documented that
diamond and ships the instance-free cure (`AlgebraicCurve/Place/LaurentSeriesRingHom.lean`,
`Place.exists_ord_mul_eq_order_of_ringHom` with an explicit `algebraMap`-compatibility hypothesis): one import
and two re-spelled proof terms, **no instance installed and nothing pinned**. The `rfl` was fixed by splitting
it into the two projection rewrites (`IntermediateField.coe_algebraMap_apply` twice). Result: file-wide type
checking **230 s → 3.5 s**, locked build **exit 0 in 24 s**, `.olean` written, `check_port` 64 ok, axioms
clean on all 64, `dedup` 0, `move_dead` 0/0, edit loop silent.

**Why every earlier reading missed it** — and the three are worth carrying: `check_port` hashes *statement
text* and read 64 ok; the prefix probes cut the file before the failing declarations; and the failing build
wrote no `.olean`, which is exactly the symptom the old order read as "slow". The gate that sees it is the
**whole-file edit loop, whose exit code is the reading** (FR-0339).

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' $(cat ../../lean/tmp/af108/unport_final.txt)) > build/shelf_af111_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` | 226 / 142,553 | **214 / 136,028** |
| ready rows | 15 / 6,727 | **13 / 6,132** |
| leaves | 5 / 13,761 | 5 / 13,761 |
| withheld (FR-0044 guard) | 6 / 1,970 | 6 / 1,970 |

The delta is **−12 nodes / −6,525 lines**, exactly the cut, and the correction list is unchanged (the same
20 names).

**Ten of the thirteen ready rows are genuinely ready (5,930 silo)** — the other three are the standing
non-rows (the def-gated `lineCoeff_eq_zero` 142, the false ready `exists_sum_smul_eq_of_isIntegralQExp_gamma1`
36, and the padic-Tate-module `rep_tateModule_jOne_comm` 24). The new head is *order A's payoff*, and it is
the shape the next scoping has to reckon with:

* **`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` (1,133, 20
  premises)** — order B's root statement in `WeierstrassCurve` form: the `j`-invariants of the
  cyclic-quotient family are the roots of the modular polynomial;
* **`AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace` (1,071)** and
  **`…whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace` (1,070)** — two
  consumers of order A's polynomial-decay bound (integrability plus summability of the Whittaker
  coefficient);
* **`AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary` (1,038)** —
  the same family's Bruhat–Eisenstein form;
* **`AutomorphicForm.exists_localComponents_of_isGlobalAddChar` (440, leverage 6)** — order D's
  `stdAddChar` normalization applied to the local components;
* **`AlgebraicCurve.Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero` (444)** and
  **`NumberField.AdelicFourier.fourierIntegral_fourierIntegral_finiteAdeleRing_eq` (394)** with
  `…isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing` (260) — orders C's and D's
  consumers;
* **`NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet` (57)** and
  **`TateCurve.equation_pointX_pointY_of_defectCoeff_eq_zero` (23)** — the small consumers of order D's
  normalized Poisson summation and order E's defect equation.

## 8. What the set leaves behind

**The shelf is now a Whittaker-coefficient shelf**: three of its ten viable rows are the 1,000-line
summability/decay consumers of order A, and the two largest single rows of the column (the 3,747 just
landed, the 1,133 now on the shelf) are one story — the archimedean decay of the Whittaker coefficient and
the `j`-invariant dictionary that feeds the Eisenstein bound. Two consequences for the next scoping:

* the next set is again **one giant row plus consumers**: `bijOn_cyclicQuotientJ_isRoot…` (1,133, 20
  premises) is the Weierstrass-curve form of what order B just landed, and the three AutomorphicForm rows
  (2,141 silo combined) are orders A's and D's consumers;
* the definition-layer option is unchanged and now the only thing standing between the shelf and two of its
  rows: `Def_TateCurve_QShift` + `Def_TateCurve_DefectLines` (176 declarations, §5) for `lineCoeff_eq_zero`,
  and `Def_EllipticCurve_TateModule` for the padic-Tate row.

Five things carried beyond the files:

* **nine new frictions** (FR-0331…FR-0339), and the set's own lesson is the most important one: **FR-0338** — run
  `premcheck.py` **at scoping**, because the readiness test credits a premise by last name and three of this
  set's premises are not the pin's statement (one of them cost order A a 149-line private transcription).
  The others: **FR-0336** (one pin statement spelled two ways in two pin files — the omission tool can never
  credit it, and "de-qualifying to match" breaks the other wire), **FR-0331/0332/0335** (an alias making a
  term ambiguous, `compAddMonoidHom_apply` under the `AdeleRing` `defeq`, a universe-0 substitution), and
  **FR-0337**, the reviewer's build-time ruling now at the top of the playbook, and **FR-0339** — the
  `Algebra K (LaurentSeries K)` instance diamond, whose real lesson is about *evidence*: `check_port` (text),
  a prefix probe (cut before the failure) and `wall time` (a build that never exits 0 writes no `.olean`) were
  all blind to two genuine elaboration errors, and the whole-file edit loop's exit code is the only reading
  that saw them.
* **the build-time policy's first worked example** (§6.2): a 3,747-line row whose pin installs an 8 M
  heartbeat budget, fixed *at the bound site* (a hoisted `hG` and an explicit `G`) inside the 200 k cap —
  no ladder, no probe pair, nothing installed.
* **the `port once` rule fired inside one set again** (order B's two insertions share a 26-declaration
  prefix, declared once), and **order A imported 30 prelude rows** rather than re-proving them — the
  largest single substitution of the column.
* **three CARRY-FORWARD items**: the mathlib-supplement row
  `Measure.exists_eq_prod_of_forall_map_add_left` (149 lines, with its two weaker namesakes),
  `mem_compositeRing_iff` (still deferred from AF109), and the parser `ENCLOSE_RE` fix (which this set hit
  twice — order A restructured its module, order B named its sections, both to dodge it).
* **the consumer zone** (`spec/SetAF111Consumer.lean`, §6.3) is the set's only artifact that *uses* the rows
  together, and this time both zones are hypotheses-discharging instantiations: the standard character's
  global-character fact removes one hypothesis from orders A's and D's headlines.
