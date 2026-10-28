# SET 8 — the `AlgebraicCurve` shelf after SET 7: four rows, three homes, and the reciprocity chain behind them

**Status (2026-10-27): landed.** This is the `AlgebraicCurve` set read off the D–S shelf after
SET 7 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), and then
ported: four ready rows / 390 silo / **265 net new math lines**, three homes reached by three
one-line imports, **no new module, no definition gate, no promotion, no migration, and no worker
dispatch**: 265 net is a manager lane, not a wave to fan out.  The set is one session, three
steps (WR → SPAN/POLE), and the two rows it makes ready are `ell_mapDomain_eq_…` (151) and the
general `weilReciprocity` (100).  §0 the read and its delta; §0.1 the corrected shelf and its two
markers; §0.2 the definition layer; §0.3 the pricing; §1 the cut and the landing; §2 the rows;
§3 the homes; §4 ground prep; §5 per-row traps; §6 the gates; §7 the calls; §8 reproduce, the
measured numbers and the forecast; §9 what the set does not do.

No whole-tree build was run (the AGENTS rule); the set needs no new definition and no migration,
so the work was three module edits plus the wires.  The read is `frontier.py`'s cached graph
(≈5 s), the pricing is `port_advise`/`port_plan` (text only), and the home checks are the port
tree's own import lines.  The one tool change made while reading is the `--unport` flag of §0.1
(SET 7's call 7), so the corrected shelf is now one command.

| figure | instrument | corrected (§0.1) |
|---|---:|---:|
| ready candidates, all namespaces | 88 / 20,455 silo | 88 / 19,973 |
| leaves, all namespaces | 296 / 72,205 | 296 / 72,205 |
| `AlgebraicCurve` ready rows | 4 / 828 | **4 / 390** |
| `AlgebraicCurve` leaves | 0 | 0 |
| `AlgebraicCurve` demand | 56 / 20,696 | 58 / 20,854 |
| `needed [F terminal]` | 1,021 / 405,122 | 1,024 / 405,316 |
| frontier F | 1,386 / 721,252 | 1,384 / 721,116 |
| (cone / avoided) | 2,103 / 982,173 · 140 / 74,620 | unchanged |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |

## 0. The read, and the delta against SET 7

Canonical, as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf8.json
python3 frontier.py --selfcheck
# the corrected read: the two live false ported markers removed from F (see §0.1)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 \
  --unport AlgebraicCurve.weilReciprocity > build/shelf8-corrected.json
```

**The delta is zero on every figure.** SET 7's §8 after-read is the instrument's
1,021 / 405,122, 88 ready, 296 leaves, `AlgebraicCurve` 4 / 828 and demand 56 / 20,696, frontier
1,386 / 721,252; the corrected after-read is 1,024 / 405,316, 88 / 296, AC 4 / 390 and 58 /
20,854, frontier 1,384 / 721,116. This read reproduces all of them to the line, which is the
first confirmation that SET 7 landed exactly what it recorded. The tree has not moved since
(no other column landed between the two reads).

**The `AlgebraicCurve` block is the four rows of §0.1 and nothing else.** There is again **no
`AlgebraicCurve` leaf**: the leaves block is 296 candidates / 72,205 silo, entirely outside the
family, so the recipe's `--include-leaves` clause costs nothing here and its leaves table is
empty. The ready block carries 88 rows / 19,973 silo (corrected; 20,455 instrument).

**`--selfcheck` names MD-001 alone.** The three source claims SET 6 found were reduced to one by
SET 7's landing: the 33-line `Divisor.evalFun_pullback` and the 214-line
`Place.inertiaDeg_pos` are now true ported nodes, and the live source claim is
`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36), the deferred C2 row of the
ModularCurve column, which the AC column does not edit. The FR-0047 shadow is not visible to
`--selfcheck` and is the second marker of §0.1.

**The withheld block, quoted.** The FR-0044 guard still withholds four rows / 831 silo:

| withheld row | silo | blocking premise (in the avoided set R) |
|---|---:|---|
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` | 327 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `ModularCurve.moduleFinite_padicInt_tateModule_jOne` | 283 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice`, `exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice` |
| `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | `Pic0.natCard_torsion_prime_eq_pow_genus_complex` |

The two `AlgebraicCurve` entries (221 silo) are the prunable complex-analytic subject's consumers
and stay deferred to the RR column's phase 3 (SET 6 §9,
[../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md)); the
two `ModularCurve` entries are the same subject's Tate-module consumers and are the MC column's.
None is cut by this set.

## 0.1 The corrected shelf: two markers, and the four rows

The instrument's four `AlgebraicCurve` rows include one that cannot be transcribed
(`DivisorialWeilPairingData.toHom_injective_of_divisible`, 496) and hide one that can
(`weilReciprocity_algebraMap`, 58). The correction set is now **two** markers — SET 7 made the 33
and the 214 true, so the four-marker correction of its §0.1 has shrunk:

| node | silo | marker | why it is false | treatment |
|---|---:|---|---|---|
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | `spec-pin:` in `ModularCurve/X1/IntegralityJqNModC.lean:64,68` | the module's prose says "Not ported here" (MD-001); its own premise is the `ModularForm`/`CuspForm` row discussed below | unport for the read; MC column fixes the wire |
| `AlgebraicCurve.weilReciprocity` | 100 | **name shadow** (FR-0047) | the ℙ¹ node `RationalFunctionField.weilReciprocity` shares its last name, so the last-name tier reads the general node ported; its own premise `weilReciprocity_algebraMap` (58) is then hidden, and its consumer `toHom_injective_of_divisible` (496) reads ready while the premise is unported | unport for the read; the cure is to **port** the general node (§8, SET 9) |

Removing both from `F` gives `needed` **1,024 / 405,316**, frontier **1,384 / 721,116**, **88**
ready rows and the corrected four-row `AlgebraicCurve` shelf of **390 silo**:

| row | silo | why it is on the corrected shelf | becomes |
|---|---:|---|---|
| `lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed` | 170 | four premises ported; the LSpace-level lift of SET 7's 872-line char-free span theorem | the 151-line `ell_mapDomain…` row (§8) |
| `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` | 118 | four premises ported (the `ell` growth is SET 7's 103 row) | — |
| `weilReciprocity_algebraMap` | 58 | four premises ported (SET 7's PAIR lane landed two of them) | the general `weilReciprocity` (100, §8) |
| `exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed` | 44 | five premises ported (the degree identity is SET 7's 32 row) | — |

`toHom_injective_of_divisible` (496) is the row that leaves; `weilReciprocity_algebraMap` (58) is
the row that enters; the corrected `AlgebraicCurve` demand is 58 / 20,854 and the instrument's 56
/ 20,696 is short by exactly the 58 and the shadow's general `weilReciprocity` (100) — 158 lines —
while its shelf carries the 496 it cannot transcribe.

**`--unport` is now the command.** SET 7's call 7 (add a repeatable flag that removes a name from
`F`) is implemented in `tools/deps/frontier.py` while preparing this brief: `--unport NAME`
subtracts the resolved node from the ported frontier, the default read is untouched, and the
selftest gained one assertion (`unport({4}, [4])` restores the demand the marker hid).
`tools/deps/README.md` records it and the two limits below. The recipe's §0 should use it; the
post-set re-read of §8 does.

**A third false marker, and a new instrument limit (for the MC column).** The corrected read's
MC block is the 36-line `exists_sum_smul_eq_of_isIntegralQExp_gamma1` — but it is not port-true
either: its premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` (261) is read
ported through the *`CuspForm` twin's* last name in `ModularForms/WeightOne/Gamma1IntegralBasis.lean`
(the pin has both a `ModularForm` and a `CuspForm` node with that last name, and the plan's §7
records that the twin cannot substitute). This is MD-001's "deeper undercount", a last-name
shadow of the FR-0047 class on a *premise*; unporting it too reads `needed` **1,025 / 405,577**,
frontier 1,383, and swaps the 36-row for a 261-row on the ready shelf. **The `AlgebraicCurve`
block and its demand are identical under both corrections** (4 / 390, 58 / 20,854), so this brief
quotes the SET-7-compatible two-marker read for the delta and leaves the 261 to the MC column.

**And one limit the next wave will hit.** Readiness is computed over the `S_` file's **graph
premises** only; the **statement's own vocabulary** (a structure or class from a `Definitions/` 
module the wrapper imports, which is not a graph node) is not read. After `weilReciprocity` lands
(SET 9), `toHom_injective_of_divisible` will read `needed = 1` although its statement needs
`DivisorialWeilPairingData`/`e.toHom`, whose carrier part is unported (the port has only that
`Def_` module's support block, in `Defs/WeilDatum.lean`). The mitigation is the recipe's: read the
wrapper's `import Definitions.…` lines and `twin_scan --node` before believing `needed = 1`. The
frontier README's "Notes and limits" now records it.

## 0.2 The definition layer — nothing to create

`port_advise --with-defs` on the four rows puts **six** pin `Definitions/Def_*.lean` modules in the
closure: `AdelicIndex` (68 declarations), `DivisorClassGroup` (63), `DivisorPushPull` (70),
`IsCurveOver` (10), `PlaceEvaluation` (14), `Repartitions` (19). **All six are ported at their
statement layer**: the probe finds 218 of their declarations / ≈1,678 lines already in the port
(214 public and importable, 4 of them `private` in the port), 0 to create. The
`DivisorClassGroup` declarations are not in a module of that name: the probe maps them to
`Defs/Divisor.lean`, `Defs/Place.lean`, `Defs/SemilinearAut.lean` and a few further homes (e.g.
`Place.smulRingEquiv` is in `WeierstrassCurve/Velu/MapEquation.lean`) — the port's existing
arrangement, not a gate.

So this set has **no definition gate** and **no promotion**:

* the four `S_` files have **no private prelude** (`port_advise` "drags" reports `0 helpers` for
  every one of the eight files; the four `solution`s are public);
* row 1's three `W7XChildJ` helpers are **already in the port**, public and checked at their own
  wires: `Place.ord_nonneg_of_mem_vs` (`Canonical/WeilDifferential.lean`), and
  `Place.mem_iff_ord_nonneg_vs` / `Place.one_le_ord_of_mem_of_inv_not_mem`
  (`Place/ConstantFieldExtension.lean`, verified `ok` against
  `S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean`). They are
  imported, not restated;
* no home is a legacy module (`spec/old_check_stmts.py`'s `PORT_FILES`), so there is **no
  migration** either.

The surface gate still applies to what is written: row 2's two helpers
(`fd_lSpace_nsmul_poleDivisor`, `exists_mem_lSpace_nsmul_of_forall_ord_nonneg`) are public in the
pin's `S_` file, so they are transcribed **public** in the home module, at their pin names; the
`check_port` pass is `--force` after the module settles, and every added declaration must be `ok`.

## 0.3 The pricing — 390 raw, 265 net

The four rows, priced one by one and as a set:

| row | silo | raw `S_` | declaration lines | boilerplate | in port | **net new** | substitutions |
|---|---:|---:|---:|---:|---:|---:|---|
| `lSpace_mapDomain…_of_isAlgClosed` | 170 | 170 | 145 | 25 | **43** (3 helpers) | **102** | 3 trusted / 0 suspect |
| `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` | 118 | 118 | 96 | 22 | 0 | **96** | 0 |
| `weilReciprocity_algebraMap` | 58 | 58 | 44 | 14 | 0 | **44** | 0 |
| `exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed` | 44 | 44 | 23 | 21 | 0 | **23** | 0 |
| **set** | **390** | **390** | **308** | **82** | **43** | **265** | **3 trusted / 0 suspect** |

The 82-line boilerplate is high for four rows because each is a separate pin file (import block,
`set_option`s, the pin's attribute walls); it is not mathematics. The 43 in-port lines are exactly
row 1's three helpers.

The other three sections of the instrument:

* **port once** — no name is proved in two or more of the four target files. Two names have one
  target copy and many external ones (`ord_nonneg_of_mem` in 35 pin files, `mem_iff_ord_nonneg` in
  28, both row 1's helpers); the port's public copies are those to import, so nothing is written
  twice.
* **generalise** — nine names share a conclusion with different binders across the def closure;
  the two that matter are `mem_iff_ord_nonneg` (three pin statements) and `ord_nonneg_of_mem` (two).
  Take the port's `_vs` binders: they are the `S_` copies' shape (`(f : F)` without the `hf`
  hypothesis), which is what row 1's proof calls.
* **the FR-0041 check** — `twin_scan --node` says all four are `new` (no statement twin), and
  reading each pin proof's first lines confirmed there is no port theorem with *weaker*
  hypotheses to rebuild on: row 1 **is** the LSpace-level lift of the 872-line span theorem (it
  calls it, it does not restate it); row 2 is the pole-bound consequence of the `ell` growth;
  row 3 is the evaluation-pairing chain; row 4 is the support-sum form of the degree identity.
  The instrument's 265 is therefore the work, not a fragment of it.

## 1. The cut

Four rows, one manager lane, three story-steps. No worker order: 265 net new lines is a fifth of
the recipe's smallest dispatch, and there is no definition layer, no promotion and no migration to
hand to a manager separately.

| step | story | rows | silo | net | home(s) |
|---|---|---:|---:|---:|---|
| **WR** | the reciprocity transport: `evalFun` reciprocity is preserved by a finite separable constant extension | 58 | 58 | **44** | insert `Place/EvalAtNorm.lean` (+1 import) |
| **SPAN** | the span lift: the LSpace-level form of the char-free span theorem | 170 | 170 | **102** | insert `IsCurveOver/ConstantFieldExtensionSpan.lean` (+1 import) |
| **POLE** | the pole consequences: the pole bound and the pole-sum form of the degree identity | 118 + 44 | 162 | **119** | insert `Genus/ConstantFieldExtensionConsequences.lean` (+1 import) |
| | | **4** | **390** | **265** | 3 modules, 3 imports, 8 wire lines |

**Why one lane.** The recipe's "one story per order, ≈1,300–1,600 silo" is a dispatch-size rule,
not a floor: with the family's shelf empty (4 rows, 0 leaves) a 390-silo set is what the column
has. SET 7 set the precedent for a manager-only set at 1,658 silo; this one is smaller still, and
its three steps are one session because each is at most 120 net lines and they share the one file
that couples them: **SPAN's module gains `import FLTForHuman.AlgebraicCurve.Place.EvalAtNorm`,
WR's module. WR must land first**, so that SPAN's build sees the final `EvalAtNorm`; after that
SPAN and POLE are file-disjoint and can be done in either order (only the build lock is shared).

**Wires.** Each row adds its `Theorems/Thm_…` line plus its `P2M/Sol/S_…` line (`-- comparable
copy`). Row 1's `S_` line is provenance, not a transcription: its three helpers stay in their
own modules and are checked at their own wires (`check_port` checks the module's declarations
against the wire, so an undisclosed pin declaration is not a `missing`; only a port declaration
absent from the wire is). The four `Theorems/` wrappers and four `S_` copies are the pin's
`aa2d8b3` files named in §2.

**If the reviewer prefers workers.** Three orders, `WORKORDER-WR` first, then `WORKORDER-SPAN`
and `WORKORDER-POLE` in parallel, with the same gates as §6; the two later orders touch disjoint
modules and only need WR's build to have landed.

### 1.1 The landing, and the set's numbers

**Landed 2026-10-27, one session; the manager took all three steps** (the set is below the
~1,500-line dispatch size, so no worker subagents were used).  Every module was built at the
project cap (module build, not a tree build); the checker is `spec/check_port.py --force`.

| step | module(s) | tree lines | checker | build | axioms |
|---|---|---|---:|---|---|
| WR | `Place/EvalAtNorm.lean` (+74) | +74 | 29 → **30 ok** / 0 mismatch / 0 missing | silent (27 s) | `weilReciprocity_algebraMap` clean |
| SPAN | `IsCurveOver/ConstantFieldExtensionSpan.lean` (+129) | +129 | 35 → **36 ok** / 0 / 0 | silent (23 s; the module's pre-existing 200k offender, FR-0048, keeps the project-cap gate) | the LSpace headline clean |
| POLE | `Genus/ConstantFieldExtensionConsequences.lean` (+159) | +159 | 2 → **6 ok** / 0 / 0 | silent (3.7 s) | both headlines and both helpers clean |
| consumer | `spec/AlgebraicCurveSet8Consumer.lean` (114) | — | **0 errors, 0 warnings** | — | — |

**What the set consumed**: the four rows / 390 silo; 265 net new math lines (the three modules
carry +362 source lines including docstrings, statements and wires); three one-line imports;
eight wire lines; the consumer zone.  No new module, no definition, no promotion, no migration.

**The measured deltas** (the read of §8, before → after):

| figure | instrument before | instrument after | corrected before | corrected after |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 1,021 / 405,122 | **1,018 / 404,790** | 1,024 / 405,316 | **1,020 / 404,926** |
| ready rows | 88 | **86** | 88 | **86** |
| `AlgebraicCurve` ready | 4 / 828 | **2 / 647** | 4 / 390 | **2 / 251** |
| `AlgebraicCurve` demand | 56 / 20,696 | **53 / 20,364** | 58 / 20,854 | **54 / 20,464** |
| frontier F | 1,386 / 721,252 | **1,390 / 721,642** | 1,384 / 721,116 | **1,388 / 721,506** |

The instrument falls by 3 rows / 332 lines (the rows it could see: the 58 was hidden); the
corrected figure by 4 / 390.  The corrected shelf is the 151 plus the 100 — the two rows the set
readies — and the instrument's is the 151 plus the spurious 496.

**Deviations held for review** (none changes a statement; every `check_port` hash matched):

- The 170 proof's `hlift_new` binder is **unused** (the pin's own proof does not use it either: it
  is carried for the row's consumer, the 151).  The zero-warning rule is met with the tree's
  `have _ := hlift_new` idiom rather than renaming the binder, because the checker's normaliser
  keeps binder names and the pin's wrapper spells `hlift_new`.
- The pin's two `push_neg` calls in the 170 proof are the deprecated spelling; they are written
  `push Not` (FR-0036's rule).
- The span module's gate is the **module build at the project cap**, not the 200k edit loop: the
  pre-existing `finrank_le_finrank` aborts the low cap (FR-0048), and the set's addition is after
  it.  The module built in 23 s; `EvalAtNorm` and `CFEConsequences` passed the 200k loop (49 s and
  6 s).
- `dedup.py --within` reports 0 clusters in `CFEConsequences`; on the span module it reports the
  pre-existing 51-line `Span` three-copy cluster and on `EvalAtNorm` the pre-existing 23-line
  `conductorIdeal` cluster — both SET 6/7's recorded wrapper-over-engine patterns, and neither
  contains a declaration added here.  `move_dead.py` was not run: it relocates a dead declaration
  to a shelf module (it needs a `--target`), and the four headlines are now referenced by the
  consumer zone.
- Row 2's two helpers are public at the pin's names (`fd_lSpace_nsmul_poleDivisor`,
  `exists_mem_lSpace_nsmul_of_forall_ord_nonneg`), as the surface gate requires; the checker
  matches them against the pin's `S_` file (lines 23 and 37).

## 2. The rows

`silo` is the pin `S_` file's line count (the rank key); `prem` the pin's `import Theorems.Thm_*`
premise count; `lev` the corrected read's cone / project consumers; `net` the measured
`port_plan` figure.

| step | node (`AlgebraicCurve.` dropped) | silo | prem | lev | net | pin file (S_ / Thm_) |
|---|---|---:|---:|---:|---:|---|
| SPAN | `lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed` | 170 | 4 | 1 / 3 | 102 | `S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed.lean` (170) |
| POLE | `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` | 118 | 4 | 1 / 2 | 96 | `S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean` (118) |
| WR | `weilReciprocity_algebraMap` | 58 | 4 | 1 / 1 | 44 | `S_AlgebraicCurve_weilReciprocity_algebraMap.lean` (58) |
| POLE | `exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed` | 44 | 5 | 1 / 7 | 23 | `S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean` (44) |

Demand is again inverted relative to size: the 44-line pole-sum row carries 7 project consumers,
the 58-line reciprocity row 1 (the general `weilReciprocity`, §8), while the 170-line span row
carries 3. The 58 is the largest *unblocking* row of the four: it is the first link of the
`58 → 100 → 496` chain that FR-0047 has been mis-reading since SET 6.

**What each row says, in one line.**

* 170 — for `K ⊆ F ⊆ F'`, `K ⊆ K' ⊆ F'`, `F'` generated over `K'` by the image of `F`, both
  curves and both constants algebraically closed: if `f' ∈ LSpace(K', D.mapDomain lift)` then `f'`
  lies in the `K'`-span of the image of `LSpace(K, D)`. The proof builds the `K`-basis of `K'`,
  reads `f'` through it (`g : basis →₀ F`), and uses the 872-line span theorem plus
  `mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain` to land each coefficient in
  `LSpace(K, D)`.
* 118 — for `D` the pole divisor of a separating `x` and `K` algebraically closed: there is `M₁`
  with every `h` whose order is non-negative at the poles of `x` lying in
  `span K {x ^ j * y | y ∈ LSpace(M₁ • D)}`. The proof is the `ell` growth (SET 7's 103 row), the
  finite-dimensionality of every `LSpace(M • D)`, and the one-step dimension count
  `lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` (`Defs/AdelicIndex`).
* 58 — for a finite separable constant extension `F' / F` with `HasPrincipalDivisors` on both
  sides, given `WeilReciprocity K F` as a hypothesis: `evalFun f Dg = evalFun (algebraMap g) Df`
  under the pin's disjointness and rationality hypotheses. The proof is the chain
  `evalFun_pullback` → `place.ord_norm_eq_zero_of_forall_fiber`/`pushforward_div` → the base
  reciprocity → `evalFun_algebraMap_pushforward`.
* 44 — for `k` algebraically closed and `x` transcendental with finite `[k⟮x⟯ : F]`: the pole set
  `{P | P.ord x < 0}` is a finset and `∑ P ∈ S, (-P.ord x) = [F : k⟮x⟯]`. The proof is
  `exists_poleDivisor_of_transcendental` plus the degree identity (`Divisor.degree_eq_sum_support`
  against `degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental`).

## 3. Homes — three inserts, three one-line imports, no new module

Method as in the recipe §4: pin `S_` premises → statement-identical port module (the ports' own
declarations, checked by hand against the proof's first lines) → the modules above all of them in
the port's import closure. The closure was rebuilt from the tree's `import FLTForHuman.…` lines
(a short `rglob` script over `lean/FLTForHuman`, nothing else); the table and the reading agree.

| node | premises → port modules | above-all check | home | why |
|---|---|---|---|---|
| `lSpace_mapDomain…_of_isAlgClosed` (170) | `IsCurveOver/ConstantFieldExtensionSpan` (itself), `Place/EvalAtNorm` (`mem_riemannRochSpace…`), `Place/FromValuationSubring` (`Place.exists_toValuationSubring_eq_comap…`), `IsCurveOver/PerfectField` (`exists_separating_transcendental…`) | **no module above all four**; span and `EvalAtNorm` are siblings, both above the last two | **insert** `IsCurveOver/ConstantFieldExtensionSpan.lean` + `import …Place.EvalAtNorm` | the module *is* the port's span development, and this row is the LSpace-level lift of the theorem it already hosts; the generalisation lives next to the theorem it generalises. The import is one line, acyclic (`EvalAtNorm` does not reach the span module) |
| `exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` (118) | `Defs/AdelicIndex` (`lSpace_nsmul_succ…`), `Genus/ConstantFieldExtensionConsequences` (itself, `exists_ell_nsmul_eq…`), `Genus/Index` (`finiteDimensional_lSpace`), `IsCurveOver/Transcendental` (`isCurveOver_of_isAlgClosed…`) | **exactly one**: `Genus/ConstantFieldExtensionConsequences` | **insert** same module | the row opens with the module's own `ell` growth and is a further consequence of the same isAlgClosed/transcendental setting; the module has 0 importers, so the edit is cascade-free |
| `weilReciprocity_algebraMap` (58) | `Place/OrderArithmetic` (`Place.ord_norm_eq_zero_of_forall_fiber`), `PrincipalDivisors/Transcendence` (`Divisor.pushforward_div`), `Place/EvalAtNorm` (`evalFun_pullback`, `evalFun_algebraMap_pushforward`) | **no module above all three**; `OrderArithmetic` and `EvalAtNorm` are siblings (each above `Transcendence`) | **insert** `Place/EvalAtNorm.lean` + `import …Place.OrderArithmetic` | two of its four premises are that module's own laws and its conclusion is an `evalFun` identity; `EvalAtNorm` has **0** in-tree importers, so the import is acyclic and the edit touches nothing else. Alternative: a new `WeilExchange/WeilReciprocity.lean` (§7 call 2) |
| `exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed` (44) | `IsCurveOver/Transcendental` (`isCurveOver…`), `Genus/ConstantFieldExtension` (`constantsAreBase…`), `Genus/Index` (`Divisor.degree_eq_sum_support`), `PrincipalDivisors/PoleDivisor` (`exists_poleDivisor_of_transcendental`), `Genus/ConstantFieldExtensionConsequences` (itself, the 32 row) | **no module above all five**: `ConstantFieldExtensionConsequences` is above the first four except `PoleDivisor` | **insert** `Genus/ConstantFieldExtensionConsequences.lean` + `import …PrincipalDivisors.PoleDivisor` | the row is the finset/support-sum form of the degree identity the module already hosts; `PoleDivisor` has 0 importers and imports only `IsCurveOver/Transcendental` + `Defs/PoleDivisorPackage`, so the import is acyclic |

**The import-direction check, by hand.** `ConstantFieldExtensionSpan` gains `Place/EvalAtNorm`,
which imports `Place/ConstantFieldExtensionRamification` → `WeilExchange/Bifibre`, `Defs/…`,
`Place/FromValuationSubring`; none of them imports the span module, so the edge is acyclic. It
already imports `Place/ConstantFieldExtension` (which imports `IsCurveOver/ConstantFieldExtension`),
so the new edge only adds the Place-level norm engine to the span module's closure. `EvalAtNorm`
gains `Place/OrderArithmetic`, which imports `PrincipalDivisors/Transcendence`, `Defs/…`,
`Place/OrdCalculus`, `WeilExchange/FiberOverCount`; none imports `EvalAtNorm`. `ConstantFieldExtensionConsequences`
gained `PrincipalDivisors/PoleDivisor` the same way.

**No row of the set cites another row of the set.** The 170 feeds the 151 (not cut, §8); the 58
feeds the general `weilReciprocity` (100, not cut); the 118 and 44 are independent of each other
and of the 58.

**Build cost, for the order.** The span module is the only hub in the set: 2 in-tree importers
(`Differential/CorrespondenceRegularCFE`, `Differential/ConstantFieldExtension`) and a ~21 s
module build at the project cap (SET 7's measurement). `EvalAtNorm` and
`ConstantFieldExtensionConsequences` have **0** in-tree importers; `OrderArithmetic` and
`PoleDivisor` are only imported by modules outside this set, so the new edges cost one rebuild of
the edited module, not a cascade.

## 4. Ground prep — the manager's three imports and four wires

Nothing in this set is a `Def_` node, a promotion or a migration; the ground prep is the import
edges and the wires, both the manager's:

1. `IsCurveOver/ConstantFieldExtensionSpan.lean`: add
   `import FLTForHuman.AlgebraicCurve.Place.EvalAtNorm` (sorted into the `FLTForHuman` block);
   extend the header's subject sentence to say the module also carries the **LSpace-level** span
   theorem, whose `K'`-coefficients descend through `EvalAtNorm`'s basis engine.
2. `Place/EvalAtNorm.lean`: add `import FLTForHuman.AlgebraicCurve.Place.OrderArithmetic`; extend
   the header to name the reciprocity transport as its third subject.
3. `Genus/ConstantFieldExtensionConsequences.lean`: add
   `import FLTForHuman.AlgebraicCurve.PrincipalDivisors.PoleDivisor`; extend the header to say the
   module also carries the pole bound and the support-sum form of the degree identity.
4. Each of the three modules gets `spec-pin:` lines for the wrapper and the `S_` copy of every
   node it adds (§1: eight lines; row 1's `S_` line is provenance — its helpers are checked at
   their own wires, not re-declared here).

The pins are `anthropics/fermats-last-theorem@aa2d8b3` (Lean 4.33.1 / mathlib v4.33.0); the port
is mathlib v4.34.0, so the known drift rules apply (no `import Mathlib`, no `set_option
maxHeartbeats`, `push_neg` → `push Not` only where the pin wrote it — see FR-0031 and FR-0036).

## 5. Per-row traps

**170.** (i) Do not re-declare the three `W7XChildJ` helpers: `Place.mem_iff_ord_nonneg_vs`,
`Place.one_le_ord_of_mem_of_inv_not_mem` (both `Place/ConstantFieldExtension.lean`) and
`Place.ord_nonneg_of_mem_vs` (`Canonical/WeilDifferential.lean`) are the same statements, public
and already checked; row 1's proof calls `mem_iff_ord_nonneg` with the `S_` copy's `(f : F)` binder,
which is the port's `_vs` form. (ii) The pin file sets `maxHeartbeats 4000000`; the port's gates
forbid the option, and this is the row to watch at the 200k default (the proof expands a
`Module.Basis.ofVectorSpace` index and a `Finsupp.ofSupportFinite` construction; the pin's option
is defensive, but the `Finsupp` block is where elaboration cost will show). (iii) The `hnew`
argument is the pin's: `Finsupp.mapDomain_notin_range` gives `(mapDomain lift D) v' = 0`, then
`mem_iff_ord_nonneg_vs` twice with `hlift_ord`. (iv) The 872-line span theorem is called at the
pin's binders (`[IsCurveOver K F] [IsCurveOver K' F']` are instances in the port), and its `hz`
is the same `∀ v', (∀ v, …) → z ∈ v'.toValuationSubring` shape the row constructs.

**118.** (i) The pin file sets `maxHeartbeats 8000000`; this is the set's most likely elaboration
stall (the `hup` induction unfolds the AdelicIndex dimension-count engine at `genusFF`). If the
200k cap aborts, stop and record the deviation — do not raise the cap. (ii) The port's
`finiteDimensional_lSpace` requires the instance `FiniteDimensional K (LSpace (0 : Divisor K F))`,
which the row's `fd_lSpace_nsmul_poleDivisor` obtains from `ell 0 = 1` via
`FiniteDimensional.of_finrank_eq_succ`; keep that order. (iii) The two helpers are **public** in the
pin's `S_` file and must be transcribed public at their names (`fd_lSpace_nsmul_poleDivisor`,
`exists_mem_lSpace_nsmul_of_forall_ord_nonneg`) — the surface gate reads them. (iv) `hD0 : 0 ≤ D`
and `(0 : ℤ) ≤ degree D` are derived from `hD`; the `hup` step's `ell` hypothesis is
`fun N hN => by rw [hell N hN, Int.toNat_of_nonneg hdegD]`.

**58.** (i) The statement takes `WeilReciprocity K F` **as a hypothesis** (`hbase`), not the
general theorem: the row is the compatibility used *to prove* the general one, so there is no
cycle with the unported `weilReciprocity`, and the port's `Defs/PlaceEvaluation.lean` already
defines the predicate. (ii) The module gains `import …Place.OrderArithmetic` for
`Place.ord_norm_eq_zero_of_forall_fiber`; `Divisor.pushforward_div` comes through
`Place/IntegralClosureAtFiber` → `PrincipalDivisors/Transcendence` (already in the closure), and
the two `evalFun` laws are the module's own. (iii) The proof's order is the pin's:
`hfib` (from `hdisj` + `ord_restrict` + `ramificationIndex_pos`), `hres`, then `hdisjF` through
`ord_norm_eq_zero_of_forall_fiber`, then `hstep1`–`hstep5`. (iv) The `[CharZero F]` binder is
used by the norm engine; do not drop it. (v) If the reviewer chooses the new module instead
(§7 call 2), it must import all three premise modules; the body is unchanged.

**44.** (i) The wrapper's `hfin` is an **explicit** argument
(`(hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)`), not an instance;
take the wrapper's binders and `haveI := hfin` inside. (ii) The module gains
`import …PrincipalDivisors.PoleDivisor` for `exists_poleDivisor_of_transcendental`; the degree
identity is the module's own 32 row and `Divisor.degree_eq_sum_support` is in `Genus/Index`
(imported). (iii) `IsCurveOver.deg_eq_one_of_isAlgClosed` is the port's `Defs/IsCurveOver.lean`
statement; it rewrites each degree-one factor to `1` in the sum. (iv) The support case split is
`Finsupp.mem_support_iff` + `max_eq_left`/`max_eq_right` on `D P = max 0 (-P.ord x)`; the pin's
`by_contra h'; exact h (max_eq_left (by omega))` is the shape to keep.

## 6. The gates, per step

As in SET 6/7 and the recipe §6, unchanged:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row). Run the recipe's **surface
   experiment** on each home once: every declaration this set transcribes is already public at
   the pin's name, so the expected delta is zero; a `MISMATCH` or `MISSING` is then a genuine
   transcription error, not a private helper.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The step's own modules only, under `flock`/`timeout`: no tree build, no dependents, the module
   silent at the 200k cap. The span module is the one with a pre-existing 200k offender
   (`finrank_le_finrank`, FR-0048); its gate is the module build at the project cap (~21 s), and
   the set's additions are all before the offender.
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters stay with the
   reason recorded.
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`; no
   worker writes a `spec/decl_markers.tsv` row.
6. Each module's `spec-pin:` block gains the wrapper and the `S_` copy of every node it adds;
   no false wire is added, and none of the set's modules is a metadata entry's module (MD-001 is
   the MC column's).
7. A `spec/` consumer zone with a real cross-module composition (no `#check`s), whose error count
   is the deliverable metric: `spec/AlgebraicCurveSet8Consumer.lean` — Zone A applies the 170 row
   at `D = 0` to put the constants of `F'` in the span of the image (with
   `algebraMap_mem_lSpace_zero` from `Defs/AdelicIndex`); Zone B reads the 58 row in product form
   by `Divisor.evalFun_def` (`Defs/PlaceEvaluation`); Zone C composes the 44, the 32 and the 118
   rows at the pole divisor of `exists_poleDivisor_of_transcendental`
   (`PrincipalDivisors/PoleDivisor`) into one statement (divisor, degree, pole set, span bound).
   The zone is run with the project cap, not in the edit loop.

## 7. The calls this brief asks the reviewer to settle

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **the four rows / 390 silo / 265 net**, all ready, no definition gate | the set is a manager lane, not a dispatch; the family has no other ready row |
| 2. the 58 home | **insert `Place/EvalAtNorm.lean`** (+1 import) rather than a new `WeilExchange/WeilReciprocity.lean` | 0 in-tree importers, two of four premises are that module's laws, no new file; the general `weilReciprocity` of SET 9 will want its own home anyway (it needs `P1/Dictionary` + `AlgebraicCurve/FunctionField.lean`) |
| 3. the 118 + 44 home | **insert `Genus/ConstantFieldExtensionConsequences.lean`** (+1 import) rather than a new `Genus/PoleBound.lean` | the module is the home of the same isAlgClosed/transcendental consequences and the rows open with its engines; the alternative is subject-exact but adds a 264-line module's worth of new surface for 119 net lines |
| 4. the general `weilReciprocity` (100) | **defer to SET 9**: it is one edge behind the 58 and its landing retires the FR-0047 shadow and the spurious 496 | the cut is 4 rows, not 5; SET 9 is then 151 + 100 + 496 with its definition gate (§8) |
| 5. the dispatch | **one manager session, WR then SPAN/POLE**; no worker subagents | 265 net is below the recipe's dispatch size, and the span module imports WR's module |
| 6. the instrument | `--unport` is implemented (SET 7 call 7); the corrected read is a command; record the statement-vocabulary limit (§0.1) for SET 9 | no change to the default read; the post-set re-read uses the same two-marker baseline as SET 7's |
| 7. the MC 261 shadow | **leave to the MC column**; the AC figures are unaffected | the corrected `needed` is 1,024 / 405,316 on the two-marker baseline; a full correction reads 1,025 / 405,577 and swaps a 36-row for a 261-row on the MC shelf |

Calls 1–6 were taken as recommended and are recorded in §1.1; call 7 (`--unport`) was implemented
while preparing the brief, so the corrected figures of §0 and §8 are one command rather than an
API read.

## 8. Reproduce, the measured numbers, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json          # §0
python3 frontier.py --selfcheck                                                           # MD-001 alone
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 \
  --unport AlgebraicCurve.weilReciprocity                                                  # §0.1
python3 port_advise.py --with-defs --nodes <each row> --json build/set8-defs.json         # §0.2
python3 port_advise.py --nodes <each row> --json build/set8.json                          # §0.3
python3 port_plan.py --json build/set8.json                                               # 265
python3 twin_scan.py --node <each row>                                                    # §0.3, all new
python3 spec/check_port.py --force <module>                                               # §6.1
```

**The three measured numbers.**

1. **What the set consumes**: 4 rows / 390 silo; **265 net new math lines** (390 raw, 82
   boilerplate, 43 already in the port), plus the manager's three import lines and eight wire
   lines; the three modules carry **+362 source lines** including docstrings, statements and
   wires. 0 new definitions, 0 promotions, 0 migrations, 0 new modules.
2. **The read it starts from** (the corrected baseline of §0.1, identical to SET 7's after-read):
   `needed` **1,024 / 405,316**; 88 ready / 19,973 silo; 296 leaves / 72,205; the four FR-0044
   withholdings (831); `AlgebraicCurve` ready **4 / 390** and demand **58 / 20,854**; frontier
   **1,384 / 721,116**. The instrument reads 1,021 / 405,122 and 4 / 828 with the spurious 496,
   hiding the 58.
3. **What it leaves** (the same corrected baseline, the landed read of §1.1): `needed`
   **1,020 / 404,926** (−4 / −390); ready **86** / 19,834 (88 − 4 + 2); `AlgebraicCurve` ready
   **2 rows / 251** and demand **54 / 20,464**; frontier **1,388 / 721,506** (+4 declarations'
   worth of surface). The instrument's after-read is 1,018 / 404,790, 86 / 20,274, AC 2 / 647
   (the spurious 496 plus the 151), AC demand 53 / 20,364, frontier 1,390 / 721,642.  The landed
   read reproduced the forecast of this section to the line.

**The forecast — the rows this set makes ready.** Two `AlgebraicCurve` rows, both read off the
same graph and both confirmed on the landed shelf (they are the recipe §7 answer; nothing else
enters):

| row that becomes ready | silo | unblocked by | what it is |
|---|---:|---|---|
| `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | 151 | SPAN's 170 | the `ell` of a `mapDomain` divisor under a constant extension — one of the four consumers `TOPIC-constant-field-extension.md` §11 names for the linear-independence and span rows |
| `weilReciprocity` | 100 | WR's 58 | the general function-field reciprocity, from the ℙ¹ capstone and the 58 — it makes the FR-0047 shadow true and retires the spurious 496 row |

One row behind the first: `le_genusFF_of_constantFieldExtension_of_isAlgClosed` (151) and
`genusFF_le_of_constantFieldExtension_of_isAlgClosed` (148), the genus-preservation pair, which
the 151 feeds; one behind them, `genusFF_eq_of_constantFieldExtension_of_isAlgClosed` (27). One
behind the second: `DivisorialWeilPairingData.toHom_injective_of_divisible` (496), which the 100
readies on the graph but which still needs the carrier of
`Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial` (the port has only its support block), so
it is **not** a row of SET 9's ready shelf as the instrument will show it (§0.1).

So the wave after this set is **SET 9 = 151 + 100 (+ the 496 and its definition gate)**: 251 silo
of ready rows plus the `DivisorialWeilPairingData` carrier block (the structure, `toChar`, `toHom`,
`toHom_apply_apply` and the two pairing laws those consume — ≈250 lines), ≈1,000 silo with the
definition gate, near the recipe's dispatch size. The column's next sets are thereby visible: this
one (the four consequences), SET 9 (the reciprocity and the genus equality), and the 496/656 pair
behind their definition gates.

## 9. What this set does not do

- **The general `weilReciprocity` (100), the 496 and the 656.** The 100 is one edge behind the 58
  and is SET 9 (§7 call 4); the 496 is one behind the 100 and carries the
  `DivisorialWeilPairingData` carrier gate; `Pic0.exists_antisymmWeilPairing` (656) also needs
  `Pic0.exists_nsmul_eq` (130), whose demand is the Abel–Jacobi block — not near.
- **The two `AlgebraicCurve` withholdings (221 silo).** `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`
  (126) and `Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95) are the prunable
  complex-analytic subject's consumers, the RR column's phase 3; they return to this shelf by
  themselves if that subject lands.
- **The four `ModularCurve` rows SET 7 forecast for the same wave (591 silo).** They are the MC
  column's (272, 265, 27, 27); the recipe's re-read reports them but this set does not cut them.
- **The MD-001 wire and the `CuspForm`/`ModularForm` last-name shadow (36 and 261).** Both are the
  MC column's; MD-001 waits for that module's next edit, and the 261 shadow is the fuller
  correction of §0.1 that does not move the AC block.
- **No surface promotion, no migration, no new module, no definition module.** The set's homes
  are existing non-legacy modules, its statements are the pin's public ones, and its only surface
  is the four headlines plus row 2's two helpers.
- **No tree build.** Every module is gated on its own build at the project cap; the span module's
  pre-existing 200k offender (FR-0048) keeps its exception, and the set's declarations are all
  before it.
