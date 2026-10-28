# SET 7 — the `AlgebraicCurve` shelf after SET 6: seven rows, four false ported markers, and the wave behind them

**Status (2026-10-27): landed.** This is the `AlgebraicCurve` set read off the D–S shelf
after SET 6 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), and
then ported: seven rows / 1,658 silo, the manager taking all three lanes in one session.  The
gates are met except the pre-existing 200k edit-loop overrun of the span module (FR-0048; its
build and checker pass, and the set's declarations are all before the offender). The read itself needed correcting: the instrument printed six `AlgebraicCurve`
ready rows, but **four ported markers in it were false** — three wires and the
`weilReciprocity` name shadow — and the corrected shelf was seven rows, not six. §0 the read
and the correction; §0.1 the four markers; §0.2 the definition layer; §0.3 the pricing; §1
the cut and the landing; §2 the rows; §3 the homes; §4 the manager's ground prep; §5
per-order traps; §6 the gates; §7 the calls; §8 reproduce, the measured numbers and the
forecast; §9 what the set does not do.

No whole-tree build was run (the AGENTS rule); each edited module was built at the project
cap, and the set's declarations were checked by the low-cap edit loop (with the pre-existing
span exception, FR-0048). The read is `frontier.py`'s cached graph (4.5 s), the pricing is
`port_advise`/`port_plan` (text only, no Lean), and the wire and import-direction checks are
the tools' own APIs.

| figure | instrument | corrected (§0.1) |
|---|---:|---:|
| ready candidates, all namespaces | 86 | **87** |
| leaves, all namespaces | 296 | 296 |
| `AlgebraicCurve` ready rows | 6 / 1,907 silo | **7 / 1,658 silo** |
| `AlgebraicCurve` leaves | 0 | 0 |
| `AlgebraicCurve` demand | 61 / 22,107 | 65 / 22,512 |
| `needed [F terminal]` | 1,026 / 406,533 | 1,031 / 406,974 |
| frontier F | 1,381 / 719,841 | 1,377 / 719,458 |
| (cone / avoided) | 2,103 / 982,173 · 140 / 74,620 | unchanged |

## 0. The read, and what SET 6 left

Canonical, as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf7.json
python3 frontier.py --selfcheck
```

The cone, the avoided set and the four pruned-set withholdings are SET 6's: 2,103 / 982,173
in the cone, 140 / 74,620 avoided, four rows / 831 silo still withheld under the FR-0044
guard. `needed [F terminal]` is **1,026 / 406,533** and the shelf has **86** rows — the
same 86 the post-SET-6 read had after the readiness fix. The `AlgebraicCurve` block is six
rows / 1,907 silo, and there is again **not one `AlgebraicCurve` leaf**; the leaves block
(296) is entirely outside the family, so the recipe's `--include-leaves` clause costs
nothing here and the leaves table is empty.

**The delta against SET 6's landing read is four rows smaller on the shelf and zero on the
demand.** SET 6's §8 forecast named six rows that should become ready (1,469 silo), of
which it said one would be invisible and one spurious (the `weilReciprocity` shadow); its
§8 "after" figure was 1,026 / 406,533 and 90 rows. The FR-0044 readiness fix now withholds
four of those 90, which is this read's 86. The six forecast rows are the instrument's five
non-spurious `AlgebraicCurve` rows plus the `weilReciprocity_algebraMap` row that the shadow
hides; the spurious row is `toHom_injective_of_divisible`. The instrument's six `AlgebraicCurve` rows are therefore
**not** a clean shelf, and this brief does not read them as one (§0.1).

**What the six visible rows are, in one reading.** The 872-line `mem_span_range…` row is
the char-free `IsCurveOver` spanning theorem — the generalisation of the port's char-0
`ConstantFieldExtensionSpan` development, and the one big row of the set. The 381-line
pairing row is the existence of the Weil-pairing hom on `Pic0.torsion` — the row SET 6's
`WeilDatum` laws and `Pic0/WeilPairing.lean` were built to feed. The 103-line `ell` growth,
the 32-line degree identity and the 23-line semilinear law are small successors of SET 6's
`constantsAreBase` promotion and its TL lane. The 496-line divisibility row is the spurious
one (§0.1).

### 0.1 Four false ported markers, and the corrected shelf

`frontier.py --selfcheck` names three nodes the source tier claims and the name tier does
not cover. `twin_scan.py --node` says all three are **new** — the statements exist nowhere
in the port — and one more node is read ported by a last-name collision the check cannot
see:

| node | silo | marker | why it is false | fix |
|---|---:|---|---|---|
| `Place.inertiaDeg_pos` | 214 | `old_check_stmts.py:376` (`SOURCES`) | the port declares only the **stronger** `inertiaDeg_pos_of_finiteDimensional`; its own header says the weak node is deliberately omitted | 2-line alias at the pin name + wire (M) |
| `Divisor.evalFun_pullback` | 33 | `spec-pin:` in `Defs/PlaceEvaluationAlgebra.lean:25` | no declaration anywhere; the proof's premise module is above a `Defs/` module, so it cannot host it | transcribe in `Place/EvalAtNorm.lean` (PAIR) and delete the false wire |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | `spec-pin:` in `ModularCurve/X1/IntegralityJqNModC.lean:64,68` | the module's prose says "Not ported here" (the deferred C2 row) | delete the two wires on that module's next edit (MC, not this set) |
| `AlgebraicCurve.weilReciprocity` | 100 | **name shadow** (FR-0047) | the ℙ¹ node `RationalFunctionField.weilReciprocity` shares its last name, so the last-name tier reads the general node ported; its premise `weilReciprocity_algebraMap` (58) is hidden and its consumer `toHom_injective_of_divisible` (496) reads ready while the premise is unported | land the general node, not a wire fix (wave after this set) |

The three source-claimed nodes are recorded in
[../../spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md) (MD-001/002/003); the shadow
is a frontier tier limitation (frontier README, "Notes and limits"), not tree metadata.
Note that `check_port.py` reports **0 missing** on all three wired modules: it checks the
module's declarations against the wire, not the wire's declarations against the module, so
the false wires are invisible to it and live to the frontier.

**The corrected reading.** Removing the three source claims and the shadow node from `F`
gives `needed` **1,031 / 406,974**, `frontier` 1,377 / 719,458, **87** ready rows, and a
seven-row `AlgebraicCurve` shelf of **1,658 silo**:

| row | silo | why it is on the corrected shelf |
|---|---:|---|
| `mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed` | 872 | five premises ported; the char-free generalisation of the char-0 `ConstantFieldExtensionSpan` theorem |
| `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` | 381 | five premises ported (the `WeilDatum` laws and `Pic0/Torsion`) |
| `Place.inertiaDeg_pos` | 214 | one premise ported; a 2-line consequence of the port's stronger theorem (MD-003) |
| `exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental` | 103 | eight premises ported (the `Genus`/`RiemannRoch` block and `constantsAreBase`) |
| `Divisor.evalFun_pullback` | 33 | three premises ported; the false wire of MD-002 hides it |
| `degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental` | 32 | three premises ported; the statement is already in `Genus/DegreeIdentity` under the general name |
| `SemilinearAut.pic0_correspondence_smul` | 23 | one premise ported (SET 6's `correspondence_smul`) |

The 496 row leaves (it is not ready: it needs `weilReciprocity` 100), the 872/381/103/32/23
stay, and the 33 and 214 enter. `weilReciprocity_algebraMap` (58) is **not** on this shelf:
it needs the 33-line pullback, so it is one row behind the set (§8). The corrected AC
demand is 65 / 22,512; the instrument's 61 / 22,107 is missing the 33, the 214, the 58 and the shadow's general
`weilReciprocity` (100).

### 0.2 The definition layer — no definition module to create, one abbreviation

`port_advise --with-defs` on the seven rows puts **ten** pin `Definitions/Def_*.lean`
modules in the closure (`AdelicIndex`, `Correspondence`, `DivisorClassGroup`,
`DivisorPushPull`, `IsCurveOver`, `JacobianH1Autoduality`, `PlaceEvaluation`,
`PlacesOverDVR`, `Repartitions`, `WeilDatum`). Nine are already ported at their statement
layer. The tenth, `JacobianH1Autoduality` (337 lines / 51 declarations), is **not**: the port
has none of its `H1Gm`/`HomPic0Gm`/`WeilPairingData`/`autodualityEquiv` declarations. This
set needs exactly one line from it, the `HomPic0Gm` abbrev below; the rest of the module is
the next wave's definition gate, not this set's. The def probe's residue is six new private
helpers; only one is written here:

* `evalFun_one_i` (11 lines, pin-private) in the pairing row's own `S_` file — write it
  locally (it is the pin's `_i` copy convention; SET 6's §1.2 review already established
  that the pin states these private);
* `congrHom` / `congrHom_apply` (20 lines) in `Def_AlgebraicCurve_JacobianH1Autoduality` —
  not used by any row of this set; they belong to the later `WeilPairingData`/autoduality
  wave;
* three helpers of `Def_AlgebraicCurve_DivisorPushPull` — the port already carries them
  publicly under the same statements in `Defs/PushPull.lean` (SET 6 §0.2; no row here
  consumes them).

The **one definition this set must add** is `HomPic0Gm` from
`Def_AlgebraicCurve_JacobianH1Autoduality`: the pairing row's statement is
`… →+ Additive (HomPic0Gm K F n)`, and `HomPic0Gm K F n` is the one-line abbrev
`AddChar (Pic0.torsion K F n) K`. It goes in `Defs/Divisor.lean`, beside `Pic0.torsion`
(the module already imports it), with the mathlib `AddChar` import. The rest of that
337-line `Def_` module (`H1Gm`, `ofPic0`, `autodualityEquiv`, `WeilPairingData`,
`PrincipalPolarization`) is **not** needed by any of the seven rows and is the **next**
wave's definition gate.

So the set has **no definition gate** beyond that one line, and no `Def_` module to create.

### 0.3 What the pricing instruments say — and the one row they misprice

The seven rows, priced as two slices:

| slice | rows | raw `S_` | net new (`port_plan`) | substitutions |
|---|---|---:|---:|---:|
| CFE | 872 + 103 + 32 | 1,007 | **90** (per-row 16 / 78 / 0) | 33 trusted / 0 suspect; one 8-declaration block, 339 lines, all in-port |
| PAIR | 381 + 33 + 23 | 437 | **324** | 9 + 2 trusted suspect (the `_Right_i` shape matches) |
| M | 214 | 214 | **2** (alias) + 589 promoted surface | 13 trusted; 175 lines in-port |
| total | 7 rows / 1,658 silo | | **≈430** | |

The PAIR slice is read here without the 58 row: the full three-row slice is 340, of which
the 58 is one row behind the 33 (§8). The pairing row alone is **280** net; the pullback is
**28**; the semilinear law **16**. The CFE slice is **90** (its own 4-line dedup); the per-row reads are the 872 row
**16** (the `solution` wrapper — the generalisation's residue is not in it), the 103 **78**
(the only substantial new CFE proof), the 32 **0** (its statement is already the port's, so
the row is a 7-line wrapper).

**The one correction: the 872 row is a generalisation, not a 16-line alias.** The pin ships
two files: `S_…_mem_span_range_algebraMap_of_constantFieldExtension.lean` (859 ln, with
`[CharZero K]`) and its char-free `…_of_isAlgClosed.lean` (872 ln). The port transcribed the
**char-0** file (`ConstantFieldExtensionSpan.lean`; its public theorem carries
`[CharZero K]`). The 872 row is the char-free generalisation, a `diff` of about 100 lines over six declarations:
`transcendental_algebraMap`, `algebraMap_mem_of_new`, `trace_mem`, `exists_basis`, the
headline and the `solution` lose or change a typeclass hypothesis, `exists_valuation…` is replaced by
`exists_toValuationSubring_eq_comap_ringHom_of_isSeparable` at two places, and the headline
swaps in the char-free comap theorem and the separating-transcendental route. The
instrument's shape tier counts the row's declarations as "already in the port" because it
normalises the `[CharZero K]` instance binder away — the FR-0041 false negative the recipe
warns about (a port theorem with *stronger* hypotheses is invisible to a statement-anchored
tier). The row is the same pattern as SET 6's 620-line `cfe_isAlgClosed` ground prep, one
level up: state the general theorem, derive the char-0 one, leave the char-0 statement
untouched. The 16-line `solution` is only the wrapper.

Read the set's net as **≈430–445**, not 414; the manager lane below carries the 872
generalisation (≈25 net added lines of proof/statement edits) and the 589-line surface
promotion. The 872 row's *silo* is still 872 (the rank key), but its **cost** is the diff,
not the file.

## 1. The cut — one manager lane and two worker orders

| lane | story | rows | silo | net new | homes | gate |
|---|---|---:|---:|---:|---|---|
| **M** | the 872 char-free generalisation, the 589-line surface promotion, `HomPic0Gm`, the `inertiaDeg_pos` alias, and the MD-002/003 wire fixes | 2 | 1,086 | **≈28 + 589 surface** | `IsCurveOver/ConstantFieldExtensionSpan.lean`, `Defs/Divisor.lean`, `WeilExchange/FiberOverCount.lean`, `Defs/PlaceEvaluationAlgebra.lean` (wire only) | 1 generalisation, 1 promotion, 1 def, 1 alias, 2 metadata wire fixes + the 872 wire |
| **CFE** | the `isAlgClosed`/transcendental RR consequences: the `ell(N·D)` growth and the degree identity, in one new module | 2 | 135 | **78** | **new** `Genus/ConstantFieldExtensionConsequences.lean` | — |
| **PAIR** | the pairing hom on `Pic0.torsion`, its `evalFun` pullback premise, and the semilinear law on `Pic0` | 3 | 437 | **324** | insert `Pic0/WeilPairing.lean`, `Place/EvalAtNorm.lean`, `WeilExchange/GaloisRamification.lean` | — |

Totals: **7 rows / 1,658 silo / ≈430 net new**, plus the 589 lines of already-proved
surface the manager makes public. Five worker-visible module files are edited (the span
module by both M and CFE, serialized by the M-first dispatch; CFE's new module; PAIR's
three), the manager touches four, and one new module is created.

**Why the two workers can run concurrently after M.** PAIR edits `Pic0/WeilPairing.lean`
(M does not), `Place/EvalAtNorm.lean` (M removes a wire from
`Defs/PlaceEvaluationAlgebra.lean`, a different file) and
`WeilExchange/GaloisRamification.lean` (M edits `FiberOverCount.lean`). CFE edits the new
module and, after M, the span module for the 872 wrapper; M's span edit must land first
because it moves the private declarations public and derives the char-0 theorem. Only the
build lock is shared.

### 1.1 The manager lane, item by item

| item | module | what | measured |
|---|---|---|---|
| the 872 generalisation (§0.3) | `IsCurveOver/ConstantFieldExtensionSpan.lean` | state the char-free headline at the pin's name over the port's char-0 development; derive the char-0 theorem (statement untouched); swap the two remaining char-0 lemmas and the two valuation-subring routes | the pin's ~100-line diff over six declarations; ≈25 net added lines; the `W7XH` prelude keeps its shape |
| the surface promotion | same module | drop `private` from the 20 pin-faithful prelude declarations and expose the 2 generalised ones; run the surface experiment | 589 lines of surface; the pin states all 33 public; 11 are public now |
| `HomPic0Gm` | `Defs/Divisor.lean` | one-line abbrev `AddChar (Pic0.torsion K F n) K` beside `torsion`; `import` the mathlib `AddChar` module; wire the pin `Def_…_JacobianH1Autoduality` line | 1 line; the only missing definition of the set |
| the `inertiaDeg_pos` alias (MD-003) | `WeilExchange/FiberOverCount.lean` | 2-line alias at the pin's binders, applying `inertiaDeg_pos_of_finiteDimensional`; wire the weak `Thm_` + `S_` | 214 → 2 lines; `check_port` 3 → 4 ok |
| the `evalFun_pullback` wire (MD-002) | `Defs/PlaceEvaluationAlgebra.lean` | delete the false `spec-pin` line; the row moves to `Place/EvalAtNorm.lean` (PAIR) | no declaration change; `check_port` stays 17 ok |

The MD-001 wire is **not** in this set: it is in the ModularCurve module, whose next edit
is the MC column's; the metadata doc records it.

### 1.2 The landing, and the set's numbers

**Landed 2026-10-27, one session; the manager took all lanes** (the set is below the
~1,500-line dispatch size, so no worker subagents were used).  Every module was built at the
project cap (module build, not a tree build).

| lane | module(s) | tree lines | checker | build | axioms |
|---|---|---|---:|---|---|
| M | `Defs/Divisor.lean` (+6), `IsCurveOver/ConstantFieldExtensionSpan.lean` (+97/−48), `WeilExchange/FiberOverCount.lean` (+11), `Defs/PlaceEvaluationAlgebra.lean` (+4/−2) | +118/−50 | 19 / **35** / 4 / 17 ok, all 0 mismatch / 0 missing | silent | the span and inertia headlines clean |
| CFE | **new** `Genus/ConstantFieldExtensionConsequences.lean` (145) | +145 | **2 ok** / 0 / 0 | silent | both clean |
| PAIR | `Pic0/WeilPairing.lean` (+271), `Place/EvalAtNorm.lean` (+36), `WeilExchange/GaloisRamification.lean` (+28/−1) | +335/−1 | 17 / 29 / 12 ok, all 0 / 0 | silent | all three clean |
| consumer | `spec/AlgebraicCurveSet7Consumer.lean` (142) | — | **0 errors, 0 warnings** | — | — |

**What the set consumed**: the seven rows / 1,658 silo; ≈430 net new math lines (the tree
carries ~600 added source lines including docstrings and wires); the 27 pin-public
declarations the span work makes public (24 promoted by the surface sweep, 3 generalised in
place) are already-proved surface, not new mathematics.

**The measured deltas** (the read of §8, before → after):

| figure | instrument before | instrument after | corrected before | corrected after |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 1,026 / 406,533 | **1,021 / 405,122** | 1,031 / 406,974 | **1,024 / 405,316** |
| ready rows | 86 | **88** | 87 | **88** |
| `AlgebraicCurve` ready | 6 / 1,907 | **4 / 828** | 7 / 1,658 | **4 / 390** |
| `AlgebraicCurve` demand | 61 / 22,107 | **56 / 20,696** | 65 / 22,512 | **58 / 20,854** |
| frontier F | 1,381 | **1,386** | 1,377 | 1,384 |

The instrument's `needed` falls by 5 rows / 1,411 (the five rows it could see); the corrected
figure by 7 / 1,658.  The remaining gap between the two after-columns is exactly two of the
four markers: MD-001 (the MC 36 node, still read ported, −1 / −36) and the shadow (the 58 and
100 hidden, −2 / −158); the other two markers (the 33 and 214 wires) are now *true* ported
nodes.
The instrument's AC ready shelf is the spurious 496 plus the three new AC rows (170, 118,
44); the 58 is still hidden.  The corrected shelf is 170, 118, 58, 44.  **The metadata
inventory is now MD-001 alone**: `--selfcheck` prints only the MC node; MD-002 and MD-003
are resolved by the landing (the metadata doc records the checks).

**Deviations held for review** (none changes a statement; every `check_port` hash matched):

- The plan's 22 private declarations in the span module became **27** public ones: five
  more pin-public declarations than the pricing's substitution list counted
  (`mem_span_range_algebraMap_of_constantFieldExtension` itself, `irreducible_coe_ne_zero`,
  `ord_coe_isUnit`, `coe_iota`, `linearIndependent_pow_of_transcendental`); three were
  generalised in place and 24 promoted by the surface sweep, and `check_port` matched all of
  them (`--force` after dropping `private`: 35 ok).
- The 381 row added 271 lines, not 381: SET 6's `WeilPairing.lean` already held its private
  prelude and three public laws, as the §0.3 pricing said; the row's new content is the four
  class laws, the two datum existentials, `evalFun_one_i` and the headline.
- The `Place/EvalAtNorm.lean` pullback theorem is stated with the pin's two lines of
  `hratw`/`hord`; the checker matches at the wrapper's line 11.
- The edit loop's 200k cap aborts on the **pre-existing** `finrank_le_finrank` in the span
  module (also aborts on the file at `HEAD`); the module build at the project cap is the
  gate used, and the set's declarations are all before the abort.  FR-0048.
- Call 7 (`--unport`) was **not** implemented: the corrected read remains an API read, and
  the two figures are reported side by side.
- `dedup.py --within` reports 0 clusters in the new module and `Pic0/WeilPairing.lean`; on the
  other six it reports three shape clusters, all kept: the `Span` 51-line three-copy cluster
  (the char-0 theorem, its `W7XH` engine and the `_of_isAlgClosed` wrapper — the pin's own
  859/872 duplication plus its wrapper), the `EvalAtNorm` three-copy `conductorIdeal` cluster
  (pre-existing SET 5/6 declarations with different statements — a shape false positive), and
  the `FiberOverCount` two-copy cluster (the weak `inertiaDeg_pos` alias over the strong form,
  the pin's own arrangement, MD-003).  `move_dead.py` was not run: it *relocates* a dead
  declaration to a shelf module (it needs a `--target`), and no declaration added here is
  unreferenced.

## 2. The rows

`silo` is the pin `S_` file's line count (the rank key); `prem` the pin's
`import Theorems.Thm_*` premise count; `lev` cone / project consumers in the corrected
read; `net` the measured `port_plan` figure (the 872's is the corrected generalisation
residue).

| lane | node (`AlgebraicCurve.` dropped) | silo | prem | lev | net | note |
|---|---|---:|---:|---:|---:|---|
| M | `Place.inertiaDeg_pos` | 214 | 1 | 1 / 13 | 0 + 2 alias | a 2-line consequence of the port's stronger `_of_finiteDimensional` (MD-003) |
| M | `mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed` | 872 | 5 | 2 / 2 | ≈25 + 16 alias | the char-free generalisation of the port's char-0 span theorem (FR-0041) |
| CFE | `exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental` | 103 | 8 | 3 / 10 | 78 | the `ell(N·D)` growth through `indexOfSpecialty`/Stichtenoth |
| CFE | `degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental` | 32 | 3 | 4 / 25 | 0 + 7 alias | a wrapper over `Genus/DegreeIdentity`'s public theorem |
| PAIR | `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` | 381 | 5 | 1 / 4 | 280 | the pairing hom; needs `HomPic0Gm` |
| PAIR | `Divisor.evalFun_pullback` | 33 | 3 | 3 / 8 | 28 | the fibre computation for `evalFun`; MD-002 moved it here |
| PAIR | `SemilinearAut.pic0_correspondence_smul` | 23 | 1 | 4 / 6 | 16 | the `Pic0` wrapper of SET 6's `correspondence_smul` |

Demand is again inverted relative to size: the 872 row carries only 2 project consumers,
while the 32-line degree row carries 25 and the 23-line law 6. The 33-line pullback carries
8 project consumers and is the premise of the whole reciprocity wave.

## 3. Homes — checked against the import direction, per row

Method as in the recipe §4: pin `S_` premise nodes → statement-identical port module
(`twin_scan`'s `PortIndex`) → the modules above all of them in the port's import closure;
then each home confirmed against the pin proof's subject and first lines. The machine table
and the reading agreed except for the two rows that need a new module (below).

| node | premises → port modules | home | why |
|---|---|---|---|
| `mem_span_range…_of_isAlgClosed` | `Place/ConstantFieldExtension`, `Place/FromValuationSubring`, `IsCurveOver/PerfectField`, `IsCurveOver/ConstantFieldExtension` (5 nodes) | **insert** `IsCurveOver/ConstantFieldExtensionSpan.lean` | the module *is* the port's span development, above all five premise modules; the generalisation lives next to the theorem it generalises |
| `Place.inertiaDeg_pos` | `Defs/PushPull` (`ord_nonneg_of_mem`) | **insert** `WeilExchange/FiberOverCount.lean` | the module of the strong theorem and the recorded omission; above `Defs/PushPull` |
| `exists_ell…` | `IsCurveOver/Transcendental`, `Genus/ConstantFieldExtension`, `IsCurveOver/EssFiniteType`, `RiemannRoch/Assembly`, `Genus/Index` | **new** `Genus/ConstantFieldExtensionConsequences.lean` | no existing module is above both `Genus/ConstantFieldExtension` and `Genus/DegreeIdentity` (§ below); the new module imports both and the `ell`/index block |
| `degree_poleDivisor…` | `Genus/DegreeIdentity`, `IsCurveOver/Transcendental`, `Genus/ConstantFieldExtension` | **new** same module | `Genus/DegreeIdentity` is *below* the constants module, so it cannot host the row; the new module is above both |
| `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` | `Pic0/Torsion`, `Pic0/WeilPairing`, `Defs/WeilDatum` | **insert** `Pic0/WeilPairing.lean` | the module of the pairing laws; above `Pic0/Torsion` and `Defs/WeilDatum`; the private `_i` helpers are reusable in the same file |
| `Divisor.evalFun_pullback` | `Place/EvalAtNorm` (`evalAt_norm_eq_prod_fiber`), `Defs/PushPull` (2 nodes) | **insert** `Place/EvalAtNorm.lean` | the fibre/norm module; above all three; the false wire's `Defs/PlaceEvaluationAlgebra` does not import `Place/EvalAtNorm` (a `Defs/` module must not sit above the Place layer), so it cannot host it (MD-002) |
| `SemilinearAut.pic0_correspondence_smul` | `WeilExchange/GaloisRamification` (`correspondence_smul`) | **insert** same module | the module of the along-laws it consumes; `Defs/Correspondence` is below it |

**The new module is forced.** No existing module is above both
`Genus/ConstantFieldExtension.lean` and `Genus/DegreeIdentity.lean` (the port's import graph
was rebuilt for this check): the two are incomparable siblings, and the two rows need one
of each plus `IsCurveOver/Transcendental`. A single new
`Genus/ConstantFieldExtensionConsequences.lean` importing `Genus/ConstantFieldExtension`,
`Genus/DegreeIdentity`, `Genus/Index`, `RiemannRoch/Assembly`, `IsCurveOver/Transcendental`,
`IsCurveOver/EssFiniteType` and `Defs/AdelicIndex` is the cascade-free answer; the 103 row
would fit alone in `Genus/ConstantFieldExtension.lean`, but the 32 row cannot, and one home
for the two stories is cheaper than two.

**No row of the set cites another row of the set.** The 103 row feeds the 118 row (not in
the set); the 33 feeds the 58 (not in the set); the 381 feeds the 496 (not in the set); the
872 and the 32 are independent.

## 4. Ground prep — the manager's lane, before any order dispatches

### 4.1 The 872 generalisation — state the general, derive the char-0 special

`ConstantFieldExtensionSpan.lean` carries the char-0 development (the pin's 859-line file):
its public headline has `[CharZero K]`, and its prelude holds the 22 private copies of the
pin's public declarations. The pin's 872-line `_of_isAlgClosed` file is the same development
with `[CharZero K]` dropped; the `diff` is ~100 lines over six declarations. The lane:

1. state the char-free headline at the pin's name (the `W7XH` theorem, plus the
   `Theorems/` wrapper name `…_of_isAlgClosed` that the graph node is keyed by),
2. rewrite the char-0 headline's proof as a short corollary of it, its **statement
   untouched** (it has 2 cone / 2 project consumers),
3. generalise the two remaining char-0 prelude lemmas (`transcendental_algebraMap`,
   `algebraMap_mem_of_new`) and swap the two valuation-subring routes
   (`exists_of_valuationSubring` → `exists_toValuationSubring_eq_comap_ringHom_of_isSeparable`,
   at both call sites),
4. run the surface experiment: drop `private` from the 22, `check_port`, promote every `ok`
   (the pin states all 33 public), and add the 872 `S_`/`Thm_` lines to the wire.

The risk is the known FR-0041 pattern: the port's char-0 proof may use a `CharZero` step the
pin's char-free text does not (the pin's diff says it does not, but read the two files).
The 620-line SET 6 generalisation of the neighbouring node is the worked precedent, and the
port already has the char-free comap theorem and the char-free linear-independence engine
this development calls.

### 4.2 The surface promotion — measured, not guessed

`port_advise` reports 22 of the 872 slice's declarations "only as a port-private
declaration", 589 lines. The pin states all 33 public (both 859 and 872 files have zero
`private`), so the surface gate applies. The 20 prelude declarations that are byte-identical
in the two pin files are straightforward promotions; the 2 generalised ones (§4.1) are
exposed only after the generalisation. The current `check_port` baseline on the module is
**7 ok**; the probe's predicted post-promotion surface is the whole 33 plus the wrapper.
Record every retained `private` with its reason; there should be none after the sweep.

### 4.3 `HomPic0Gm` and the `inertiaDeg_pos` alias

* `HomPic0Gm K F n := AddChar (Pic0.torsion K F n) K` in `Defs/Divisor.lean`, after
  `torsion`, with `import Mathlib.Algebra.Group.AddChar` and a
  `spec-pin` for `Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean`. One line.
* `Place.inertiaDeg_pos` in `WeilExchange/FiberOverCount.lean`: state the pin's two-line
  statement (the `[Algebra.IsSeparable F F']` binder is unused) as
  `theorem inertiaDeg_pos … : 0 < w.inertiaDeg F := inertiaDeg_pos_of_finiteDimensional w`,
  wire the weak `Thm_`/`S_` pair. This retires MD-003 and the 214 row together.

### 4.4 The wire fixes — MD-002, MD-003, and MD-001 left for MC

* MD-002: delete `spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_evalFun_pullback.lean` from
  `Defs/PlaceEvaluationAlgebra.lean`; the PAIR order adds the row's own wire in
  `Place/EvalAtNorm.lean`.
* MD-003: solved by the alias's wire (above).
* MD-001: `IntegralityJqNModC.lean` is ModularCurve; the two false `spec-pin` lines wait for
  that module's next edit. The metadata doc names them; do not edit the module from this
  set.

## 5. Per-order notes — the traps recorded so far

**M.** (i) The 872 row is not an alias: the instrument's 16 lines are the `solution` wrapper,
while the row's cost is the char-free `diff` (~25 net lines over six declarations). Read the two
pin files side by side before ordering; the `W7XH` namespace means the promoted names are
`AlgebraicCurve.W7XH.*`, not `Place.*` — no clash with `Defs/PushPull`'s public names.
(ii) The promotions are 589 lines of *surface*, not new proofs; do not price them as new
math. (iii) `transcendental_algebraMap` and `algebraMap_mem_of_new` are the two prelude lemmas
whose proofs may genuinely use `CharZero`; `trace_mem` and `exists_basis` only carry the
hypothesis and lose it. If the port's proof needs `CharZero` in a third place, record the
deviation instead of weakening the pin's statement. (iv) The `HomPic0Gm` abbrev must be visible to `Pic0/WeilPairing.lean`; that
module imports `Defs/Divisor`, so put it there, not in the pairing module (the later
`WeilPairingData` rows will want it from a Def). (v) The `inertiaDeg_pos` alias's
`[Algebra.IsSeparable]` binder is unused but must be stated to match the pin's wrapper.

**CFE.** (i) The 32 row is a wrapper over `Genus/DegreeIdentity`'s public theorem; copy the
wrapper's binders, not the `S_` copy's section variables. (ii) The 103 row's pin file sets
`maxHeartbeats 4800000`; the port's gates forbid `set_option maxHeartbeats` — the proof is
expected to elaborate at the 200k cap (the pin's option is defensive), and the row is the
one place to watch. (iii) The 103 proof's `indexOfSpecialty`/`RiemannGenusReachedAt` engine
is in `Genus/Index.lean` and `RiemannRoch/Assembly.lean`; import them, do not restate.
(iv) The new module has no `PORT_FILES` legacy status; give it its own `spec-pin:` block for
the two wrappers and their `S_` files, and check the import graph: `Genus/ConstantFieldExtension`
is *not* above `Genus/DegreeIdentity`, so the new module is the only acyclic home for the
pair.

**PAIR.** (i) The pairing row's pin `S_` file has 11 substituted declarations (83 lines) and
8 private `_i` helpers already in `Pic0/WeilPairing.lean`: import/use them, do not restate.
(ii) The two **suspect** shape matches are traps: the pin's `classRight_i` is the `d.symm`
mirror of `classLeft_i` and `degZeroRight_i` of `degZeroLeft_i`; the shape tier's
`classRight_i -> classLeft_i` is a false identity. State both right-hand defs explicitly.
(iii) `evalFun_one_i` (11 lines, pin-private) is the one new helper; write it locally.
(iv) The `evalFun_pullback` row belongs in `Place/EvalAtNorm.lean` and its three premises
are ported (`evalAt_norm_eq_prod_fiber`, `pairwiseDisjoint_fiber`,
`support_pullback_subset`); the pin's 33-line proof is the whole file, and the 28 net is the
measured figure. (v) The 23-row's `correspondence_smul` premise is SET 6's; the `pic0_`
wrapper is 16 lines, and `HasPrincipalDivisors` is a hypothesis, not an import. (vi) The
pairing row's `HomPic0Gm` is the manager's one-line def; the rest of the pin's autoduality
`Def_` module is not needed here.

## 6. The gates, per lane

As in SET 6 / the recipe §6, unchanged:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row).
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The lane's own modules only, under `flock`/`timeout`: no tree build, no dependents, the
   module silent at the 200k cap (the 103 row is the one to watch).
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters stay
   with the reason recorded.
5. Zero warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no worker
   writes a `spec/decl_markers.tsv` row.
6. Each lane appends the wrapper and the `S_` file of every node it adds to its module's
   `spec-pin:` block, and removes the false wire of a metadata entry it closes.
7. A `spec/` consumer zone with a real cross-module composition (no `#check`s), whose error
   count is the deliverable metric. Natural composition: PAIR's pairing hom (381) fed by
   the `WeilDatum` laws and evaluated on a torsion class, plus CFE's ell growth at
   `N = 1` against the genus; a second zone composes the char-free span theorem (M) with
   the degree identity (CFE) at the `constantsAreBase` setting.

## 7. The calls this brief asks the reviewer to settle

| call | recommendation | what it changes |
|---|---|---|
| 1. the four false ported markers | **fix the three source claims and read the shadow as unported** (MD-001 left for MC): the corrected shelf is 7 rows / 1,658; the instrument's 6 minus the spurious 496 is 5 rows / 1,411 and misses the 33 and 214 | the cut is 7 rows, not 5; the manager's wire work is a handful of lines |
| 2. the 214 `inertiaDeg_pos` row | **2-line alias**, not a deferral — the port's header already says it is a three-line consequence, and the alias retires a false marker | +2 lines, −214 silo from the shelf |
| 3. the 872 row | **generalise in place** (the SET 6 `cfe_isAlgClosed` precedent), keep the char-0 statement and derive it; price it at the ≈25-line residue of the ~100-line diff, not the instrument's 16 | the row is the manager's, and the set's net is ≈430, not 414 |
| 4. the 103 + 32 home | **one new `Genus/ConstantFieldExtensionConsequences.lean`** — no existing module is above both `Genus/ConstantFieldExtension` and `Genus/DegreeIdentity` | one new module, two small rows |
| 5. the 58 `weilReciprocity_algebraMap` | **defer one wave**: it is not ready (it needs the 33-line pullback, which this set lands); after the set it is ready, and it then unlocks `weilReciprocity` 100 and the spurious 496 | the cut is 7 rows, not 8; the next wave is 58 → 100 → 496 |
| 6. the cut and its dispatch | **one manager lane + two worker orders, one wave**: M first (the span generalisation and promotions), then CFE and PAIR concurrently; PAIR's files are disjoint from M and CFE, and the span module is serialized by M-first | §1 as written |
| 7. a `--unport NAME` flag for `frontier.py` | **add it before the re-read**: the corrected shelf is a manual API read today (§8); one repeatable flag (remove NAME from `F`) makes it a command and gives the post-set read the same corrected baseline | one flag + one `--selftest` assertion; the default read is untouched |

Calls 1–6 were taken as recommended and are recorded in §1.2; call 7 (`--unport`) was **not**
implemented, so the corrected figures remain an API read and are reported beside the
instrument's.

## 8. Reproduce, the measured numbers, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json  # §0
python3 frontier.py --selfcheck                                                   # the three MD entries
python3 port_advise.py --with-defs --nodes <each row> --json build/set7-defs.json  # §0.2
python3 port_advise.py --nodes <CFE rows> --json build/set7-cfe.json
python3 port_plan.py --json build/set7-cfe.json                                   # 90
python3 port_advise.py --nodes <PAIR rows> --json build/set7-pair.json
python3 port_plan.py --json build/set7-pair.json                                  # 340 (with 58), 324 set
python3 spec/check_port.py --force <module>                                       # §6.1
```

**Reproducing the corrected read.** There is no flag for it yet: it is
`frontier.analyze` with `ported = fr.frontier('union') - {the three `--selfcheck` nodes,
AlgebraicCurve.weilReciprocity}` and the `--ds` avoided set.  The four are a manual
correction today; `--unport NAME` (call 7) would make the shelf a command, and the post-set
read should use the same corrected baseline so the delta means one thing.

**The three measured numbers.**

1. **What the set consumes**: 7 rows / 1,658 silo; ≈430 net new math lines, plus 589 lines
   of already-proved surface promoted and ~25 lines of aliases/wrappers.
2. **The corrected read it starts from**: `needed [F terminal]` 1,031 / 406,974,
   `AlgebraicCurve` demand 65 / 22,512, frontier 1,377 / 719,458, 87 ready, 296 leaves,
   the four pruned-set rows still withheld (831 silo).
3. **What it left** (the corrected, shadow-aware reading): `needed`
   **1,024 / 405,316** (−7 nodes / −1,658), the ready shelf **88** (87 − 7 + the **eight**
   rows the set unblocks), `AlgebraicCurve` ready **4 rows / 390 silo** (170, 118, 58, 44),
   `AlgebraicCurve` demand **58 / 20,854**, and `weilReciprocity_algebraMap` (58) ready at
   `needed = 1`.  The **instrument** reads **1,021 / 405,122** — lower by the shadow's two
   hidden rows (−158) and by MD-001's still-ported MC node (−36) — and its AC shelf is the
   spurious 496 plus 170 / 118 / 44, with the 58 hidden.  Quote the corrected figure in a
   shelf brief; use the instrument's only for the delta.

**The forecast, as landed (read off the same graph, not a promise).** The set made **eight**
rows ready, four `AlgebraicCurve` and four `ModularCurve` — the recipe §7's "which rows became
ready because of the set" answer:

| row that became ready | silo | unblocked by |
|---|---:|---|
| `AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed` | 170 | M's 872 generalisation |
| `AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` | 118 | CFE's `exists_ell_nsmul_eq…` (103) |
| `AlgebraicCurve.weilReciprocity_algebraMap` | 58 | PAIR's `Divisor.evalFun_pullback` (33) |
| `AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed` | 44 | CFE's `degree_poleDivisor…` (32) |
| `ModularCurve.JOne.galois_smul_heckeAlgOne_smul` | 272 | PAIR's `pic0_correspondence_smul` (23) |
| `ModularCurve.galois_smul_genOpH_comm` | 265 | PAIR's `pic0_correspondence_smul` (23) |
| `ModularCurve.heckeOperatorHAlong_diamondHBar_comm` | 27 | PAIR's `pic0_correspondence_smul` (23) |
| `ModularCurve.heckeOperatorOneBar_comm_diamondOneBar` | 27 | PAIR's `pic0_correspondence_smul` (23) |

The four `AlgebraicCurve` rows are the AC shelf's next set (390 silo); the four
`ModularCurve` rows are the same wave's MC block (591 silo) and belong to the MC column, not
this one, but the recipe's re-read must report them.  One row behind the first AC chain:
`AlgebraicCurve.weilReciprocity` (100), whose landing makes the FR-0047 shadow true; one
behind that, `DivisorialWeilPairingData.toHom_injective_of_divisible` (496).
(`Pic0.exists_antisymmWeilPairing` 656 also needs `Pic0.exists_nsmul_eq` 130, whose 28-node
demand is the Abel–Jacobi/267-row block; it is not near.)  So the wave after this set is
**8 rows / 981 silo** (4 AC / 390, 4 MC / 591), with the reciprocity chain
58 → 100 → 496 starting inside it — the first wave in the column whose size is read off a
metadata correction rather than off the instrument's shelf.

## 9. What this set does not do

- **`weilReciprocity_algebraMap` (58) and the general `weilReciprocity` (100)**: the 58 is
  one row behind the 33-line pullback and is deferred; the 100 is one behind the 58. The
  general reciprocity node is the FR-0047 shadow's subject; porting it makes the shadow
  true and retires the spurious 496. That is the next wave, not this one.
- **`toHom_injective_of_divisible` (496) and `exists_antisymmWeilPairing` (656)**: the 496
  is the row the shadow falsely readies; it needs `weilReciprocity` and the pin's
  `DivisorialWeilPairingData`, whose `Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial`
  module is not ported and is the definition gate of the next wave (the `WeilPairingData`
  block of `JacobianH1Autoduality` is the other half). The 656 is further out: it needs the
  130 row, whose 28-node demand is the Abel–Jacobi block.
- **`Pic0.exists_nsmul_eq` (130) and the 267-row block**: not ready, not cut; the
  28-node demand is the Abel–Jacobi/267-row work SET 6 §9 already names as the RR column's.
- **The MC `exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)**: its false wire is MD-001,
  left for the ModularCurve next edit; it is not an `AlgebraicCurve` row.
- **The 589-line surface promotion is not new mathematics**: it is the pin's public surface
  the port holds private; the set's checked surface grows, its proof content does not.
- **The four pruned-set withholdings (831 silo)**: unchanged; they are the RR column's
  phase 3, still off this shelf.
