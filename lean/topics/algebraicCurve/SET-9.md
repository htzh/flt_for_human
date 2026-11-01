# SET 9 — the reciprocity chain of the `AlgebraicCurve` shelf: rationality → reciprocity → the perfect pairing, plus the ℓ-invariance row

**Status: landed (2026-10-31).** Read off the D–S shelf after SET 8 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). It is a
different set from the one SET 8 forecast: the forecast was `151 + 100 + 496`, and the read finds
that **the 100's own premise `Place.isRational_of_isAlgClosed` (119) is unported** — hidden from
every shelf by a same-last-name twin (`AlgebraicCurve.RationalFunctionField.isRational_of_isAlgClosed`,
which is in the port). So the set is **4 rows / 866 silo**, one *chain* and one independent row,
plus **one definition gate** (the `DivisorialWeilPairingData` carrier, in the port's
`Pic0/WeilPairing.lean`):

| step | rows | story | silo | net |
|---|---|---:|---:|---:|
| **RAT** | 119 | every place over an algebraically closed constant field is rational, from a finite `RatFunc K`-model | 119 | 103 |
| **REC** | 100 | Weil reciprocity for that function field | 100 | 70 |
| **PAIR** | 496 (+ the carrier gate) | the divisorial Weil pairing is injective when `Pic⁰` is divisible | 496 | 452 |
| **ELL** | 151 | `ℓ(D)` is invariant under an algebraically closed constant extension | 151 | 122 |
| | **4** | | **866** | **747** + gate ≈ 113 |

§0 the read, three shelves and the delta; §0.1 the two name shadows and why the set is four rows;
§0.2 the definition gate, measured; §0.3 the pricing, and one instrument failure it produced;
§1 the cut; §2 the rows; §3 the homes; §4 ground prep; §5 per-row traps; §6 the gates; §7 the
calls; §8 reproduce and the forecast; §9 what this set does not do.

No whole-tree build was run (the AGENTS rule) and no Lean was run at all while scoping: the read
is `frontier.py`'s cached graph (≈5 s per pass), the pricing is `port_advise`/`port_plan` (text
only, ≈16–20 s), `twin_scan` is statement-level, and the home checks are the port tree's own
`import FLTForHuman.…` lines (a short `rglob` script, nothing else).

## 0. The read, and the delta against SET 8

Canonical, as the recipe requires, in three passes — the instrument's, the one-marker correction
(SET 8's baseline), and the two-marker correction this pass found:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf9.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AlgebraicCurve.weilReciprocity > build/shelf9-corrected.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AlgebraicCurve.weilReciprocity \
  --unport AlgebraicCurve.Place.isRational_of_isAlgClosed > build/shelf9-corrected2.json
```

| figure | instrument | one marker | two markers (corrected) |
|---|---:|---:|---:|
| `needed [F terminal]` | 942 / 380,709 | 943 / 380,809 | **944 / 380,928** |
| ready rows, all namespaces | 68 / 13,294 | 68 / 12,898 | 68 / 12,917 |
| leaves, all namespaces | 262 / 64,874 | 262 / 64,874 | 262 / 64,874 |
| `AlgebraicCurve` ready rows | 2 / **647** | 2 / **251** | 2 / **270** |
| `AlgebraicCurve` leaves | 0 | 0 | 0 |
| `AlgebraicCurve` demand | 53 / 20,364 | 54 / 20,464 | **55 / 20,583** |
| frontier F | 1,473 / 746,657 | 1,472 / 746,557 | **1,471 / 746,438** |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | 4 / 831 |
| (cone / avoided) | 2,103 / 982,173 · 140 / 74,620 | unchanged | unchanged |

**The delta against SET 8's after-read is entirely outside `AlgebraicCurve`.** SET 8's landed read
was: instrument `1,018 / 404,790`, frontier `1,390 / 721,642`, 86 ready; corrected `1,020 /
404,926`, frontier `1,388 / 721,506`, 86 ready, `AlgebraicCurve` ready 2 / 251, demand 54 /
20,464. Today's instrument reads `942 / 380,709` (−76 nodes / −24,081 lines), frontier `1,390 →
1,473` (+83 / +25,015), 68 ready (−18 / −7,161). **Every `AlgebraicCurve` figure is identical**
(ready 2 / 251 and demand 54 / 20,464 on the one-marker basis), so the AC column has been frozen
since SET 8 and the whole movement is the five **MC waves** of 2026-10-28/29 (`3d6ad61`, `f2748c9`,
`a45976a`, `a3591ab`, `999feec`, `b0d29f4`, ≈15k new port lines) plus `503f9a8`'s Kaehler
clarifications. The direction is the expected one: as the MC column lands, `needed` falls and the
ported frontier F **grows**.

**`--selfcheck` now passes clean, so the false-marker set is empty — and the shadow set is two.**
SET 8's read had MD-001 live (`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`, whose wire
claimed 36 lines the module did not port) plus one FR-0047 shadow; the MC wave that touched
`ModularCurve/X1/IntegralityJqNModC.lean` fixed that wire, and
[spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md) records the inventory as **empty**. The
36-line row is now an honest ready row on the MC shelf (7 rows / 1,273), not a false marker. Name
shadows are invisible to `--selfcheck` by construction, which is why this pass could *find* one
more rather than lose one: the count of live shadows went from one to **two** (§0.1).

**The withheld block, quoted (unchanged, 4 rows / 831 silo).**

| withheld row | silo | blocking premise (in the avoided set R) |
|---|---:|---|
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` | 327 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `ModularCurve.moduleFinite_padicInt_tateModule_jOne` | 283 | `AlgebraicCurve.Pic0.abelJacobiCard_genus` |
| `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` |
| `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | `Pic0.natCard_torsion_prime_pow_genus_complex` |

The two `AlgebraicCurve` entries are the prunable complex-analytic subject's consumers (RR column's
phase 3, [../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md));
none is cut here.

**The `AlgebraicCurve` leaves block is empty again** (0 rows): the 262 leaves / 64,874 silo are all
outside the family, so the recipe's `--include-leaves` clause costs nothing on this shelf and its
leaves table is empty. The ready block is 68 rows / 12,917 silo on the corrected basis.

## 0.1 The two name shadows, and why the set is four rows

The instrument's AC shelf is **`toHom_injective_of_divisible` (496) + `ell_mapDomain_eq_…` (151) =
647 silo**, which is the same block SET 8 saw — and it is wrong in both directions. The correction
set is two markers, both of the FR-0047 class (a pin node with a same-last-name twin whose
statement is a different one):

| node | silo | the twin that shadows it | why the read is false | treatment |
|---|---:|---|---|---|
| `AlgebraicCurve.weilReciprocity` | 100 | `AlgebraicCurve.RationalFunctionField.weilReciprocity` (ported, `P1/Dictionary.lean`) | the ℙ¹ capstone shares the last name, so the last-name tier reads the general node ported | unport for the read; the cure is to **port** the general node (REC, this set) |
| `AlgebraicCurve.Place.isRational_of_isAlgClosed` | 119 | `AlgebraicCurve.RationalFunctionField.isRational_of_isAlgClosed` (ported, `P1/Dictionary.lean:697`) | same: the port holds only the ℙ¹ form `(v : Place K (RatFunc K))`, the pin's node is `(v : Place K F)` from a `RatFunc K`-algebra tower — **without `IsCurveOver`** | unport for the read; the cure is to **port** the general node (RAT, this set) |

Removing both from `F` gives the corrected shelf, **2 rows / 270 silo**:

| row | silo | prem | lev | why it is ready | becomes |
|---|---:|---:|---:|---|---|
| `Place.isRational_of_isAlgClosed` | 119 | 3 | 4 / **40** | all three premises ported (`RationalFunctionField.deg_eq_one_of_isAlgClosed`, `Place.isRational_iff_deg_eq_one`, `Place.mem_of_ord_nonneg`) | — |
| `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | 151 | 5 | 2 / 2 | five premises ported (four of them SET 8's) | the genus pair (299, §8) |

**…and the 100 and the 496 are one and two edges *behind* the corrected shelf**, not on it:

* `weilReciprocity` (100) is ready the moment **RAT** lands — its tenth premise is
  `Place.isRational_of_isAlgClosed`;
* `toHom_injective_of_divisible` (496) is ready the moment **REC** lands — its tenth premise is
  `weilReciprocity` — and its statement needs the `DivisorialWeilPairingData` carrier, which no
  graph read can see (§0.2).

So the set is the **closure of the corrected shelf by one, in the chain order**:
`RAT (119) → REC (100) → PAIR (496)`, plus `ELL (151)`, which is independent. The instrument's
496 is a row the corrected shelf does not carry, and the corrected shelf's 119 is a row the
instrument does not carry: **the two shelves' unions are the set**, 4 rows / 866 silo.

**Why the 119 was never on any brief.** Three separate instruments were misreading it at the same
time — the first two hide it from the shelf, the third prices it at zero:

1. `frontier.py`'s last-name tier reads it ported (the ℙ¹ twin);
2. `frontier.py --selfcheck` cannot see it (it checks `Thm_` source claims against port
   declarations, and the *last name* is declared — this is the limitation
   [TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) §0 already records as
   "it checks the module's declarations against the wire, not the wire against the module");
3. `port_advise`'s shape tier prices it at **0 net new lines** (§0.3) — a false substitution onto
   the port's *stronger*-hypothesis `Place.isRational_of_isCurveOver` (5 lines, `[IsCurveOver K F]`).

`twin_scan --node` says `relative ~ AlgebraicCurve.RationalFunctionField.isRational_of_isAlgClosed`
for the 119 and prints `prelude 0/1`; for the 100 it says `relative ~
…RationalFunctionField._root_…weilReciprocity`. Both are the "same name, different statement"
verdict, which is the signal that a **new** theorem has to be written, not imported.

`RAT` is also the most connected row in the family — **4 in-cone / 40 project consumers** — so it
is not a gate to be dodged; it is the row this column was missing.

## 0.2 The definition layer — one gate, and it is smaller than SET 8 forecast

`port_advise --with-defs` on RAT + REC puts the pin `Definitions/` closure at **119 declarations,
102 of them already in the port byte-identically** (`AdelicIndex` 68, `Repartitions` 19,
`PlaceEvaluation` 14, `IsCurveOver` 10 — all four `Def_` modules ported at their statement layer,
≈658 lines of surface already matched, 0 to create). So RAT and REC have **no definition gate**.

**PAIR has one.** Its statement is about `e : DivisorialWeilPairingData K F n` and `e.toHom`, from
`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean` (790 lines, 68
declarations). The port already matches **18** of those statements (in `Defs/WeilDatum.lean` and
`Pic0/WeilPairing.lean`), holds **4** more only as port `private`
(`degree_D₁_eq_zero_i`, `degree_D₂_eq_zero_i`, `degZeroLeft_i`, `degZeroRight_i`), and spells **4**
differently (`addLeft_pairing`, `pairing_ne_zero`, `smul_mem_torsion`, and the `not_mem_range_of_pow_eq`
of the 496's own file). The gate is the **carrier block** — what the 496's statement and proof
actually touch:

| pin block | pin lines | what the port already has | net new |
|---|---:|---|---:|
| `Divisor.evalFun_one` (17–22) | 6 | `evalFun_one_i`, **private** in `Pic0/WeilPairing.lean:104` | 1 (promote) |
| `degZero{Left,Right}`, `coe_degZero*`, `mk_mem_torsion` (52–83) | 32 | same mathematics as port `_i` names (`Pic0/WeilPairing.lean:160–190`), 2 of them `private` | 0 (relabel) |
| `class{Left,Right}`, `coe_class{Left,Right}`, `class*_symm`, `class*_addLeft` (84–116) | 33 | port `_i` names, public and checker-`ok`; `coe_class*` missing | 4 |
| `structure DivisorialWeilPairingData` (448–458) | 11 | — | 11 |
| `exists_witness`, `exists_datum`, `exists_datum_pair` (467–573) | 107 | the port's *generalised* `Pic0` engine (`exists_ord_eq_mul_of_mk_mem_torsion`, private) and `exists_datum_i`/`exists_datum_pair_i` (`hmove`-parameterised) | 8 (three delegations) |
| `pair_ne_zero`, `pair_{add_left,mul_pair_swap,zero_left,zero_right,swap_eq_inv,add_right}` (574–642) | 69 | the port's `have`-block inside `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` (`Pic0/WeilPairing.lean:610–675`), **not** public | 68 |
| `toChar`, `toChar_apply`, `toHom`, `toHom_apply_apply` (689–709) | 21 | the port's `chr`/`AddMonoidHom.mk'` block inside the same proof | 21 |
| **gate** | **279** | | **≈113** |

**Home: `Pic0/WeilPairing.lean` itself.** It has **0 in-tree importers**, it is the module whose
subject is exactly "the divisorial pairing is a class invariant", and everything the carrier's
definitions consume (`exists_datum_i`, `addLeft_pairing`, `WeilDatum.pairing_ne_zero`,
`evalFun_one_i`, `Pic0.torsion`) is already there or already imported. No new module, no new
import.

**The one thing the gate forces is a relabel.** The pin spells the datum block **twice**: the
`Def_` module has the clean names (`degZeroLeft`, `classLeft`, …) and its own `S_` file
`S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean` carries the same declarations
under the pin's `_i` suffix (`degZeroLeft_i`, `classLeft_i`, … — the suffix is the *pin's*, not the
port's invention). The port transcribed the `_i` spelling, and the carrier's `compatible` field is
stated at the `Def_` spelling (`pair d.classLeft d.classRight = d.pairing`), so the 15 declarations
of that block must be relabelled to the clean names and the `Def_` file added to the module's wire
(the checker matches statements, and the pin's own `classLeft` / `classLeft_i` pair has identical
text modulo the name). Privacy follows the pin, which is *not* the port's current split:
`isPrincipal_smul_left` is the only one the pin keeps private, so `isPrincipal_smul_right`,
`degree_D{1,2}_eq_zero`, `degZero{Left,Right}` and `evalFun_one` all become public at the pin's
names (the port has all seven `private` today). `evalFun_one` is public in the pin, so promoting it
is part of the surface gate, not an extra. The relabel is mechanical, cascade-free, and it is the
reason the gate is a *manager* task.

**What the gate deliberately stops short of:** `Perfect` (`Function.Bijective e.toHom`),
`toWeilPairingData`, `ExistsPerfectDivisorialWeilPairing`,
`nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing`, and the Galois block
(`galSmul`, `galSmul_pairing`, `pair_smul`). None is needed by the 496; `toWeilPairingData` also
needs `WeilPairingData`, which the port does not have at all (that `Def_` is the next set's gate),
and `Perfect` needs the *surjectivity* half, which is not in this set.

## 0.3 The pricing — 866 raw, 747 net, and a false substitution

The four rows, priced separately and as a set (`port_advise --nodes … --json`, `port_plan`):

| step | row (`AlgebraicCurve.` dropped) | silo | decl lines | boilerplate | net new | pin file (`S_`, `Thm_`) |
|---|---|---:|---:|---:|---:|---|
| RAT | `Place.isRational_of_isAlgClosed` | 119 | 103 | 16 | **103** | `S_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean` (119) |
| REC | `weilReciprocity` | 100 | 70 | 30 | **70** | `S_AlgebraicCurve_weilReciprocity.lean` (100) |
| PAIR | `DivisorialWeilPairingData.toHom_injective_of_divisible` | 496 | 452 | 44 | **452** | `S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible.lean` (496) |
| ELL | `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | 151 | 122 | 29 | **122** | `S_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed.lean` (151) |
| | **set** | **866** | **747** | **119** | **747** | |

**The instrument prints 644, and the 103-line gap is a false substitution — record it.** `port_plan`
reports `already in the port (vetted) 103 → NET NEW 644`. The 103 is RAT's `solution`, matched by
`port_advise`'s shape tier onto `AlgebraicCurve.Place.isRational_of_isCurveOver`
(`Place/OrdCalculus.lean:110`, 5 lines). That theorem is *not* a substitute: it assumes
`[IsCurveOver K F]`, and the pin's statement has no such hypothesis (RAT's whole content is
`IsAlgClosed K` + a finite `RatFunc K`-model, in **arbitrary characteristic** — `IsAlgClosed` does
not give `CharZero`, so separability is not free and `IsCurveOver` is not derivable). The cause is
in `port_advise.shape_of`: **every `[...]` instance binder is skipped** (`port_advise.py:543`), so
two theorems that differ only in their *instance* hypotheses have the same shape. This is the exact
inverse of FR-0041 (which is about a port theorem with *weaker* hypotheses being invisible): here a
port theorem with *stronger* hypotheses masks the pin node. The work is **747 net**, not 644.

The other two sections of the instrument:

* **port once** — no name is proved in two or more of the four target files. (`not_mem_range_of_pow_eq`
  has one target copy and one port copy, both `private` — §5.4.)
* **generalise** — no target name carries two statements. RAT's own ℙ¹ twin is a *different pin
  node*, not a binder variant: take the pin's `(v : Place K F)` binders, not the ℙ¹ ones.
* **the FR-0041 check** — `twin_scan --node` says RAT `relative`, REC `relative`, PAIR `new`, ELL
  `new`; the two `relative`s are the shadows of §0.1 (different statements, nothing to rebuild on).
  Reading each pin proof's first lines confirms there is no port theorem to rebuild on:
  RAT's 103 lines are the residue-field/order-min argument (`IsLocalRing.residue_surjective` +
  a transcendence-basis minimum), REC's 40-line `solution` is the `hconst` case split plus the
  descent through `weilReciprocity_algebraMap`, PAIR's 439-line private prelude is the Kummer-cover
  engine, ELL's 73-line `solution` is the basis/span composition on top of SET 8's 170.

## 1. The cut

Four rows, one story (the chain RAT → REC → PAIR) and one independent row. The recipe's "one story
per order, ~1,300–1,600 silo" is a dispatch-size rule; this set is 866 silo + a 279-line gate
(≈860 net), i.e. **one manager lane and one worker order**, and the chain forces the order.

| step | story | rows | silo | net | home(s) |
|---|---|---:|---:|---:|---|
| **RAT** | rationality: `[IsAlgClosed K]` + a finite `RatFunc K`-model forces every residue field to be `K` | 119 | 119 | 103 | insert `Place/DegreeOne.lean` (+1 import) |
| **REC** | reciprocity: the general `WeilReciprocity K F`, from the ℙ¹ capstone and the base-extension transport | 100 | 100 | 70 | **new** `WeilExchange/WeilReciprocity.lean` (3 imports) |
| **PAIR** | perfectness: the divisorial pairing is injective when `Pic⁰` is divisible | 496 | 496 | 452 | **new** `Pic0/DivisorialPairing.lean` (2 FLT + 2 Mathlib imports) |
| **ELL** | invariance: `ℓ` of a `mapDomain` divisor under a constant extension | 151 | 151 | 122 | insert `IsCurveOver/ConstantFieldExtensionSpan.lean` (+0 imports) |
| **gate** | the `DivisorialWeilPairingData` carrier + bridge | — | — | ≈113 | insert `Pic0/WeilPairing.lean` (+0 imports, +1 wire, 15 relabels) |
| | | **4** | **866** | **747 + ≈113 ≈ 860** | 2 new modules, 3 inserts, 9 wire lines |

**The order is forced by import direction, not preference.** `REC` imports `Place/DegreeOne` (RAT)
and `PAIR` imports `WeilExchange/WeilReciprocity` (REC); `PAIR` also needs the carrier, so the gate
must land first. `ELL` touches only `IsCurveOver/ConstantFieldExtensionSpan.lean` and is disjoint
from all of the above, so it can go in parallel — but it is 122 net lines, i.e. manager-sized.

**The dispatch.**

* **manager lane (§4):** the carrier gate + relabel in `Pic0/WeilPairing.lean`; **RAT** in
  `Place/DegreeOne.lean`; **REC**'s new module; **ELL** in the span module; the imports and the
  nine wires. (≈408 net lines, four files edited or created — above the recipe's usual "give the
  manager the definition layer" but well under a dispatch.)
* **one worker order (§5):** **PAIR** — `Pic0/DivisorialPairing.lean`, 452 net, 12 premises, one
  module, the 226-line Kummer engine. It must be dispatched **after** REC's module builds.

If the reviewer prefers to fan out, the only clean split is `ELL` as its own order (disjoint file,
no dependencies) and the chain RAT → REC → PAIR as a second; two orders touching disjoint files may
run concurrently, only the build lock is shared. The gate is never a worker's.

**Wires.** Nine `spec-pin:` lines: two for each inserted/created row (`Theorems/Thm_…` +
`P2M/Sol/S_…`, the second marked `-- comparable copy`), and one for
`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean` in
`Pic0/WeilPairing.lean` (the relabelled block and the carrier are diffed against it).

### 1.1 The manager's part — the gate, the migration and the frames

**The gate landed first** (§0.2's carrier block, in `Pic0/WeilPairing.lean`), because the PAIR row's
statement cannot be written without it.  One manager session, one module:

| what | lines | checker | build | axioms |
|---|---|---:|---|---|
| the 16-name relabel of the datum block to the pin's `Def_` spellings + privacy per the pin | 0 net | 17 → **38 ok** / 0 mismatch / 0 missing / 2 own | silent (6.7 s, module) | — |
| `Divisor.evalFun_one` (promoted at the pin's name), `coe_classLeft`/`coe_classRight` | +9 | see above (all `ok` at the pin's `Def_` lines 17/92/95) | — | clean |
| `DivisorialWeilPairingData` + `exists_witness`, `exists_datum`, `exists_datum_pair`, `pair_ne_zero`, the six `pair_*` laws, `toChar`, `toChar_apply`, `toHom`, `toHom_apply_apply` | +183 | all 18 at the pin's `Def_` lines 448–709 | — | clean |

Three findings from doing it, worth carrying:

* **The two `S_`-file datum lemmas needed an `own:` row.** `exists_datum_i` and
  `exists_datum_pair_i` are stated at the pin's `_i` spelling of `classLeft`/`classRight`, and the
  module now carries the `Def_` spelling (the carrier's `compatible` field forces it, and `rw`
  cannot see through a `def`-alias — the first attempt with a `classLeft_i := classLeft` alias built
  the module and then failed in the pre-existing `exists_addMonoidHom_eval_eq_pairing` proof at two
  `rw`s). They are 2 rows in `spec/decl_markers.tsv`, `own:`, with the reason stated.
* **`dedup.py --within` on the module: 0 clusters** (49 declarations), so the relabel introduced no
  duplicate.  `move_dead.py` was not run — it needs a `--target` shelf (SET 8's reason); the one
  declaration with no in-module consumer, `exists_witness`, is the pin's public API and is named in
  the next set's export list (`S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing.lean`), so it stays.
* **`Place/DegreeOne.lean` is a legacy module and adding the RAT wire migrated it** (the recipe §4
  rule, paid in the same touch): its 6-line `spec-pin:` wire now lists every pin source it
  transcribes, the `PORT_FILES` row is gone (its `SOURCES` rows stay), the module builds silently
  (3.9 s) and checks **2 ok / 0 mismatch / 0 missing**.  Had the wire been added without the
  migration, the checker would have read its two pre-existing declarations as `missing` — that is
  the trap, and it is the first thing to check on any legacy module this set touches.

**The ground prep is otherwise the frames**: the span module's two wires (36 ok / 0 / 0 unchanged),
the two new modules' headers, imports and wires, and `Place/DegreeOne.lean`'s
`import …Defs.PlaceEvaluation`.  The four proof bodies are the worker order
[WORKORDER-SET9.md](WORKORDER-SET9.md), in the chain order ELL → RAT → REC → PAIR.

### 1.2 The landing of the four rows (one worker order)

`WORKORDER-SET9.md` went to a single worker as one order, in the chain order; it landed all four
rows with no blocker.  Re-verified by the manager: the checker lines below were re-run, the build
re-run, the axioms re-probed, the consumer zone re-elaborated.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| ELL | `IsCurveOver/ConstantFieldExtensionSpan.lean` (+137, 1808 → 1945) | 36 → **39 ok** / 0 / 0 | silent, 26 s (module at the project cap; the pre-existing FR-0048 offender keeps the edit loop at 2M) | clean |
| RAT | `Place/DegreeOne.lean` (+120, 188 → 308) | 2 → **3 ok** / 0 / 0 | silent, 4.4 s | clean |
| REC | **new** `WeilExchange/WeilReciprocity.lean` (127) | **1 ok** / 0 / 0 | silent, 3.0 s | clean |
| PAIR | **new** `Pic0/DivisorialPairing.lean` (540) | **1 ok** / 0 / 0 (marker, §1.2 below) | silent, 8.0 s | clean |
| consumer | `spec/AlgebraicCurveSet9Consumer.lean` (Zones A/B/C) | **0 errors, 0 warnings** | — | — |

**What the set consumed**: 4 rows / 866 silo; 866 net new math lines from the `S_` files (the
instrument's 747 plus RAT's falsely-substituted 103, §0.3) plus the 183-line carrier gate and its
relabel — **≈1,050 net new math lines**; the four modules carry **+924 source lines** including
docstrings, statements and wires; **two new modules, three inserts, ten wire lines** (nine plus the
`Def_` gate wire), **one 16-name relabel with privacy taken from the pin, one promotion**
(`Divisor.evalFun_one`), **one legacy migration** (`Place/DegreeOne.lean`, §1.1), **two `own:`
marker rows**, **one `pin:` marker row**, 0 new `Def_` modules.

**The read it leaves** (the recipe §7 answer, measured, no forecast left): the plain instrument read
and the corrected read now **coincide**, because both shadows became true positives:

| figure | before (two-marker basis) | after (no flags) | forecast (§8) |
|---|---:|---:|---:|
| `needed [F terminal]` | 944 / 380,928 | **940 / 380,062** | 940 / 380,062 ✓ |
| `AlgebraicCurve` demand | 55 / 20,583 | **51 / 19,717** | 51 / 19,717 ✓ |
| frontier F | 1,471 / 746,438 | **1,475 / 747,304** | 1,475 / 747,304 ✓ |
| `AlgebraicCurve` ready | 2 / 270 | **2 / 299** (the genus pair) | 2 / 299 ✓ |
| ready rows, all namespaces | 68 / 12,917 | 68 / 12,946 | — |
| withheld | 4 / 831 | 4 / 831 | — |

The `--unport` flags of §0.1 now *inflate* the figures (942 / 380,281 with both), which is the
proof that the two nodes are genuinely ported: the flags have retired.

**Deviations held for review** (no statement changed; every `check_port` hash matched):

- **RAT's ℙ¹ step** is *not* the pin's `RationalFunctionField.deg_eq_one_of_isAlgClosed`: it is the
  home module's own `Place.deg_eq_one_of_isAlgebraic_adjoin` at `t = RatFunc.X`, with
  `haveI : Algebra.IsAlgebraic K⟮X⟯ K⟮X⟯` from `RatFunc.adjoin_X`, inlined as a `have` (a public
  helper there would be `MISSING` against the module's wire).  That is the trap (ii) option: it
  keeps the home below `P1/Dictionary` and is the subject-truer route.  One import was needed,
  `Mathlib.FieldTheory.RatFunc.IntermediateField` (the module did not import `RatFunc` at all).
- **REC** is the pin's text, `@`-spellings and `let algφ := …` wall included; one module-level
  `set_option linter.style.haveILetI false` (the precedent is `Place/DegreeOne.lean` and the span
  module).  No `maxHeartbeats`.
- **PAIR needed one private helper the gate did not have**: the engine's `Place.evalAt_smul` is in
  the `Def_` module's **Galois block**, which §0.2 deliberately left out (`galSmul`, `pair_smul`,
  `Place.{isRational_smul, mem_smul_toValuationSubring_iff, residue_smul, evalAt_smul}`).  It is
  reconstructed privately as `Place.evalAt_smul_of_forall_isRational` (28 lines) at the
  `∀ w, w.IsRational` shape the engine actually has.  Nothing was promoted; the pin's public
  `Place.evalAt_smul` and its four siblings are still unported and are a **carry-forward for the set
  that ports the Galois block** (`pair_smul` and the MC pairing rows want them).
- **PAIR's headline carries a marker because the checker cannot index it** (FR-0076): the pin spells
  it `…toHom_injective_of_divisible.{u, v}`, the corpus parser reads the name as `…divisible.`, and
  a row with an empty last name is invisible to every tier.  The marker lives in
  `spec/decl_markers.tsv` and **its key must carry the trailing dot** — keyed without it, the row
  reads `MISSING` and the marker as stale (that was the first attempt).
- **FR-0033 recurred at review**: after the worker's build the ELL module's `.olean` was absent
  while its `.hash`/`.trace` said built, so the axioms probe could not even import it.  An explicit
  `lake build` of the module produced it (26 s).  A `.hash` is not an `.olean` — the review gate is
  a real build, not a replay.
- **`dedup.py --within`**: 0 clusters in REC, PAIR and `Place/DegreeOne`; 1 **pre-existing** `shape`
  cluster in the span module (`mem_span_range_algebraMap_of_constantFieldExtension` ×2 +
  `…_of_isAlgClosed`, 51 removable lines, SET 6/7's recorded wrapper-over-engine pattern) and 0 in
  the gate module.  Nothing of this set's is inside a cluster.

## 2. The rows

`silo` is the pin `S_` file's line count (the rank key); `prem` the pin's `import Theorems.Thm_*`
premise count; `lev` the cone / project consumers of the read that carries the row (the instrument's
for PAIR, the corrected one otherwise); `net` the measured figure of §0.3. The pin is `anthropics/fermats-last-theorem@aa2d8b3`.

| step | node (`AlgebraicCurve.` dropped) | silo | prem | lev | net |
|---|---|---:|---:|---:|---:|
| RAT | `Place.isRational_of_isAlgClosed` | 119 | 3 | 4 / 40 | 103 |
| REC | `weilReciprocity` | 100 | 10 | 2 / 11 | 70 |
| PAIR | `DivisorialWeilPairingData.toHom_injective_of_divisible` | 496 | 12 | 1 / 10 | 452 |
| ELL | `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | 151 | 5 | 2 / 2 | 122 |

Demand is inverted relative to size again: the 119-line RAT row carries **40** project consumers
(the largest leverage in the family) and the 100-line REC row 11, while the 496-line PAIR row
carries 10 and the 151-line ELL row 2.

**What each row says, in one line.**

* **119** — for `K` algebraically closed, `F` a field with `[Algebra K F]`, a compatible
  `[Algebra (RatFunc K) F]` scalar tower and `[FiniteDimensional (RatFunc K) F]`: **every place of
  `F` over `K` is rational**, i.e. `K → v.ResidueField` is surjective. No `IsCurveOver`, no
  `CharZero`. The proof restricts `v` to `RatFunc K` (rational by the ℙ¹ theorem), then takes
  `x` with `K(X)[x]` algebraic, a coefficient of minimal `v`-order, clears denominators to put
  `x` in the valuation ring, and concludes that the residue of any element is the residue of a
  constant.
* **100** — for `K` algebraically closed and **char 0**, `F` finite over `RatFunc K` with
  `HasPrincipalDivisors K F`: `WeilReciprocity K F`, i.e. `evalFun f Dg = evalFun g Df` for
  functions with disjoint-support divisors. The proof splits on `g ∈ range (algebraMap K F)`
  (then `Dg = 0` and the sum of `Df`'s coefficients is `0` by the rationality of its support);
  otherwise a `K`-algebra map `RatFunc K → F` with `X ↦ g` is produced, `F` is re-read as a finite
  separable extension of `RatFunc K` under it, and the general law descends from
  `RationalFunctionField.weilReciprocity` through `weilReciprocity_algebraMap`.
* **496** — for `K` algebraically closed, char 0, `F` finite over `RatFunc K` with principal
  divisors, `n ≠ 0`, a `DivisorialWeilPairingData K F n`, and the hypothesis that **`Pic⁰` of every
  finite extension of `K` is divisible**: `e.toHom` is injective. The proof picks `x ≠ 0` in
  `Pic0[n]` with witness `D`, `f` (orders `= n·D`), forms the Kummer cover `L = F(h)`, `h^n = f`,
  a nontrivial `σ` with `σ h = ζ·h`, uses divisibility of `Pic⁰(L)` to take an `n`-th root of the
  two-place class `(τ·w₀) − w₀`, pushes the resulting principal divisor down by the norm, and
  produces `y` with `e.pair x y ≠ 1`; injectivity then follows from `toHom_apply_apply`.
* **151** — for `K ⊆ F ⊆ F'`, `K ⊆ K' ⊆ F'` with `F'` generated over `K'` by the image of `F`,
  both constants algebraically closed, and a `lift : Place K F → Place K' F'` with
  `(lift P).ord (algebraMap f) = P.ord f`, injective and with the "new place" property: for a
  divisor `D` with `[FiniteDimensional K ↥(riemannRochSpace D)]`,
  `ell (K := K') (D.mapDomain lift) = ell (K := K) D`. The proof shows `algebraMap` carries
  `LSpace D` into `LSpace (mapDomain lift D)`, takes the image of a `K`-basis of `riemannRochSpace D`,
  proves it `K'`-linearly independent (SET 7's 103-row engine) and spanning (SET 8's 170 row), and
  reads off `finrank`.

## 3. Homes — two new modules, three inserts, and the import-direction check

Method as in the recipe §4: pin `S_` premises → statement-identical port module → the modules above
all of them in the port's import closure (a `rglob` script over `lean/FLTForHuman`'s `import
FLTForHuman.…` lines), then confirm by hand against the pin proof's first lines.

| node | premises → port modules | above-all check | home | why |
|---|---|---|---|---|
| RAT (119) | `P1/Dictionary` (`RationalFunctionField.deg_eq_one_of_isAlgClosed`), `Defs/PlaceEvaluation` (`Place.isRational_iff_deg_eq_one`), `Defs/PushPull` (`Place.mem_of_ord_nonneg`, `restrictInclusion`, `restrictResidueMap_residue`, `algebraMap_residueField_eq`) | several: `P1/Dictionary` (3 importers), `Place/ChartedSpace` (0), `Place/OrbitCardinality` (2), `Genus/ConstantFieldExtension` (3) — but **`Place/DegreeOne` lacks `Defs/PlaceEvaluation`** | **insert** `Place/DegreeOne.lean` + `import …Defs.PlaceEvaluation` | the module *is* the "degree-one / rational residue field over an algebraically closed base" block (`Place.deg_eq_one_of_isAlgebraic_adjoin`, private `surjective_algebraMap_residueField`); RAT is the same statement one level up, and its ℙ¹ step is the module's own engine at `F = RatFunc K`. 5 in-tree importers, so the insertion cascades to their rebuilds |
| REC (100) | `P1/Dictionary`, `PrincipalDivisors/RatFuncDegree`, `Defs/PlaceEvaluation`, `Defs/Place`, `FunctionField`, `Place/EvalAtNorm` (`weilReciprocity_algebraMap`), `Place/DegreeOne` (RAT) | **0 modules above all of them** | **new** `WeilExchange/WeilReciprocity.lean`, imports `Place/DegreeOne`, `Place.EvalAtNorm`, `AlgebraicCurve.FunctionField` | it is *the* reciprocity law of the function field, the capstone the `WeilExchange/` family serves; no existing module is above the ℙ¹ dictionary and `Place/EvalAtNorm` (they are siblings), so a new module is forced. 0 importers, and the two imports are acyclic |
| PAIR (496) | `WeilReciprocity` (REC), `Pic0/WeilPairing` (the carrier), and transitively `Place/ConstantFieldExtension` (`inertiaDeg_eq_one_of_isRational`), `Place/EvalAtNorm`, `WeilExchange/{Transport,Bifibre,GaloisRamification}`, `PrincipalDivisors/Transcendence`, `Defs/SemilinearAut`, `Pic0/Torsion`, `P1/Dictionary` | **0 modules above all of them** (the minimal generating set is `{Place/EvalAtNorm, Pic0/WeilPairing, FunctionField}` — `Place/EvalAtNorm`'s closure already covers nine of the twelve premises) | **new** `Pic0/DivisorialPairing.lean`, imports `WeilExchange.WeilReciprocity` + `Pic0.WeilPairing` (+ `Mathlib.FieldTheory.KummerExtension`, `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`) | subject: the nondegeneracy of the divisorial pairing, beside `Pic0/WeilPairing.lean` (which cannot host it: it is below `P1/Dictionary`). The row's later siblings (`toHom_injective_of_isCurveOver` 130, `exists_antisymmWeilPairing` 656, `exists_weilPairing` 553) belong to the same module or beside it |
| gate | `Pic0/WeilPairing` | **itself** | insert `Pic0/WeilPairing.lean` | §0.2 |
| ELL (151) | `IsCurveOver/ConstantFieldExtensionSpan` (itself, the 170), `Place/EvalAtNorm` (`mem_riemannRochSpace…`), `Place/FromValuationSubring`, `IsCurveOver/PerfectField` | **exactly one**: `IsCurveOver/ConstantFieldExtensionSpan` | **insert** the span module (+0 imports) | the module already imports all of them, and it hosts the theorem this row's proof consumes (the 170 row of SET 8) |

**The import-direction check, by hand.**

* `Place/DegreeOne` gains `Defs/PlaceEvaluation`; `PlaceEvaluation` imports `Defs/Place`, and nothing
  in its closure imports `Place/DegreeOne`. Acyclic. The module's 5 importers
  (`Place/SeparableUniformiser`, `IsCurveOver/PerfectField`, `MC/XH/HeckeInputs`, `MC/Degree/PlaceDegree`,
  `MC/X1/Inputs`) re-elaborate only if built.
* `WeilExchange/WeilReciprocity` gains `Place/DegreeOne` + `Place/EvalAtNorm` + `FunctionField`, none
  of which reaches it (it is new). `Place/EvalAtNorm` has 1 importer
  (`IsCurveOver/ConstantFieldExtensionSpan`), `Place/DegreeOne` 5, `FunctionField` 0.
* `Pic0/DivisorialPairing` gains `WeilExchange/WeilReciprocity` + `Pic0/WeilPairing`; neither reaches
  it. `Pic0/WeilPairing` has **0** importers, `WeilReciprocity` is new.
* No row of the set cites another row's *home module* in a cycle: RAT → REC → PAIR is a chain,
  ELL is disjoint.

**Legacy homes — none.** No home is in `spec/old_check_stmts.py`'s `PORT_FILES`, so there is **no
migration** in this set. There is also **no promotion** outside the gate's `evalFun_one`, and no
new `Def_` module.

**Build cost.** `Pic0/WeilPairing.lean` is the gate's only edit and has 0 importers (703 lines today,
≈950 after the carrier). `Place/DegreeOne.lean` (170 lines) and
`IsCurveOver/ConstantFieldExtensionSpan.lean` (1,806 lines, the module with the pre-existing 200k
offender, FR-0048) are the two hub edits; the span module's gate is the module build at the project
cap (SET 8 measured ≈23 s).

## 4. Ground prep — the manager's gate, imports and wires

1. `Pic0/WeilPairing.lean`: relabel the datum block to the pin's `Def_` spellings
   (`degZeroLeft`, `degZeroRight`, `coe_degZeroLeft`, `coe_degZeroRight`, `mk_mem_torsion`,
   `classLeft`, `classRight`, `classLeft_symm`, `classRight_symm`, `classLeft_addLeft`,
   `classRight_addLeft`, `degree_D₁_eq_zero`, `degree_D₂_eq_zero`, `isPrincipal_smul_left`,
   `isPrincipal_smul_right`, `evalFun_one`); add
   `spec-pin: Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`; then add the
   carrier block at the pin's names: `Divisor.evalFun_one` (public), the structure, the three datum
   lemmas (delegating to `exists_ord_eq_mul_of_mk_mem_torsion` / `exists_datum_i` /
   `exists_datum_pair_i`), `coe_classLeft`/`coe_classRight`, the six `pair_*` laws, `pair_ne_zero`,
   and the bridge (`toChar`, `toChar_apply`, `toHom`, `toHom_apply_apply`). Extend the header to
   name the carrier as its third subject. **Expect the checker to stay at 0 mismatch / 0 missing
   and to grow from 17 to ≈28 `ok`.**
2. `Place/DegreeOne.lean`: add `import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation`; RAT at the
   pin's name and binders; two `spec-pin:` lines; header sentence extended (the module also carries
   the rationality theorem for a finite `RatFunc K`-model, not only the `deg = 1` form).
3. `WeilExchange/WeilReciprocity.lean`: new module, header with the pin §3 provenance and two
   `spec-pin:` lines; REC at the wrapper's binders; the two anchor lemmas private in a local
   namespace.
4. `IsCurveOver/ConstantFieldExtensionSpan.lean`: ELL at the pin's name, `algebraMap_mem_lSpace`
   public at the pin's name, the `algebraMap_mem_of_new` specialisation public at the pin's name
   (3 lines, delegating to the module's generalised copy at line 341); two `spec-pin:` lines.
5. `Pic0/DivisorialPairing.lean`: new module (worker, §5), header + two `spec-pin:` lines.

The pins are `anthropics/fermats-last-theorem@aa2d8b3` (Lean 4.33.1 / mathlib v4.33.0); the port is
mathlib v4.34.0, so the known drift rules apply (no `import Mathlib`, no
`set_option maxHeartbeats`, `push_neg` → `push Not` only where the pin wrote it — FR-0031/FR-0036).

## 5. Per-row traps

**RAT (119).** (i) Do **not** reach for `Place.isRational_of_isCurveOver`
(`Place/OrdCalculus.lean:110`): it assumes `[IsCurveOver K F]`, which the pin's statement does not
have and which `IsAlgClosed K` alone does not provide in characteristic `p` (this is exactly the
false substitution of §0.3). (ii) The ℙ¹ step is `Place.restrict (RatFunc K)` plus rationality of
the ℙ¹ place; `Place/DegreeOne` does not import `P1/Dictionary`, so either add the
`Defs/PlaceEvaluation`-only route through the module's own
`Place.deg_eq_one_of_isAlgebraic_adjoin` (take `t = RatFunc.X`, `IntermediateField.adjoin K {X} =
⊤`), or bring `RationalFunctionField.deg_eq_one_of_isAlgClosed` in with the import; the pin uses the
latter, the module's own engine is the cheaper and subject-truer one. (iii) The order-min argument is
`Finset.exists_min_image` on `p.support` for a polynomial `p` annihilating `x`; `p.coeff j` is then
the denominator-clearing constant and `v.mem_of_ord_nonneg` (port `Defs/PushPull:73`, note the
`hf : f ≠ 0` argument) is what puts each `coeff i / coeff j` in the ring. (iv) The residue argument
is `IsLocalRing.residue_surjective` + `Place.algebraMap_evalAt` (`Defs/PlaceEvaluation:78`) +
`Place.restrictInclusion` / `restrictResidueMap_residue` / `algebraMap_residueField_eq`
(`Defs/PushPull:430/462/471`); all five are in the port at the pin's names. (v) The pin opens
`AlgebraicCurve Polynomial`; `autoImplicit false` and no `maxHeartbeats`.

**REC (100).** (i) The `hconst` branch needs `Dg = 0` from `Place.ord_algebraMap` and the sum of
`Df`'s coefficients to be `0` — that is `degree_eq_sum_of_rational` against
`deg Df = 0`; the two anchor lemmas (`finsupp_prod_zpow_const`, `degree_eq_sum_of_rational`) are
**not** in the pin's `p2m_export` list, so they are private prelude (the second has a near-twin in
`IsCurveOver/ConstantFieldExtensionSpan:293` under `[IsAlgClosed K] [IsCurveOver K F]` — do not
import that one, the hypotheses differ). (ii) The descent wall is instance-heavy: the pin creates a
**second** `Algebra (RatFunc K) F` (`algφ`), its `IsScalarTower` (`stφ`), `finφ`, `CharZero (RatFunc K)`,
`IsAlgebraic`, `IsSeparable`, and then applies `weilReciprocity_algebraMap` with `@`-explicit
arguments. Keep every `@` and every `let algφ := …` exactly as pinned: Lean's instance synthesis for
the re-bound structure is what the pin's `@`-spellings are for, and the port's
`weilReciprocity_algebraMap` is at the same binders (SET 8 landed it). (iii) `hXg` is
`algφ RatFunc.X = g`; the rewrite at the end (`rw [hXg] at key`) is load-bearing. (iv) The
`hratAll : ∀ w, w.IsRational` comes from RAT (the general theorem) — *not* from the ℙ¹
`RationalFunctionField.isRational_of_isAlgClosed`. This is the row that proves the 119 was needed.

**PAIR (496).** (i) The row is 439 private prelude lines; the 226-line
`exists_pair_ne_one_of_pow_eq_of_smul_eq` is the work and it wants its own wall time. (ii) The
universe binders are `{K : Type u} {F : Type v}` and the `hdiv` hypothesis quantifies
`(L' : Type v)` — the same universe as `F`; take the wrapper's `. {u, v}` verbatim or the statement
will not diff. (iii) `Algebra.norm F u`, `Polynomial.rootOfSplitsXPowSubC`, `SplittingField`,
`HasEnoughRootsOfUnity.exists_primitiveRoot` and `IsGalois.of_separable_splitting_field` all exist
in mathlib v4.34 at the pin's names (checked in `.lake/packages/mathlib`); the module needs
`import Mathlib.FieldTheory.KummerExtension` and
`import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`, and `open Polynomial` for `X^n - C f`.
(iv) `not_mem_range_of_pow_eq` is **private** in the pin's `S_` file and the port already has a
private copy in `Place/OrderArithmetic:412`; keep the 18-line private copy in
`Pic0/DivisorialPairing.lean` (the pin's own prelude spelling — the recipe's rule) and record the
`dedup.py` cluster rather than promoting the `OrderArithmetic` one. (v) The proof's `push Not` is the
pin's deprecated `push_neg` (FR-0036: write `push Not`). (vi) `set_option Elab.async false` is not
needed in the port and `maxHeartbeats` is forbidden; watch the `SplittingField`/`Basis` blocks at
the 200k cap and record a deviation rather than raising it.

**ELL (151).** (i) `algebraMap_mem_of_new` **already exists** in the home module (line 341) in a
generalised form (`x` with `[FiniteDimensional]`/`[IsSeparable]` instances and a
`RingHom.id F`-typed call), so the pin's 19-line version is an ≈5-line specialisation through
`exists_separating_transcendental_of_perfectField`; do not restate the general one. (ii)
`algebraMap_mem_lSpace` (26 lines) is new and **public in the pin's `S_` file** — transcribe it
public at the pin's name (the surface gate reads it). (iii) The pin sets `maxHeartbeats 4000000`;
the port forbids it, and the module already carries the pre-existing 200k offender `finrank_le_finrank`
(FR-0048) — the gate is the module build at the project cap, and the added declarations are after
the offender. (iv) The `he` definitional equality
(`⟨algebraMap (b i).1, algebraMap_mem_lSpace …⟩`) is where elaboration will show; the rest is
`Submodule.span` bookkeeping. (v) `hfg'`/`hgen` are both consumed (by the 103-row linear
independence engine), so they are not removable binders. (vi) `D.mapDomain lift` and `LSpace` are
the port's `Finsupp.mapDomain` form; `ell` is a `ℕ`.

## 6. The gates, per step

As in SET 6–8 and the recipe §6, unchanged:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row). Run the surface experiment on each
   home once: this set's transcribable declarations are the pin's public ones
   (`algebraMap_mem_lSpace`, `evalFun_one`, the carrier, the six `pair_*` laws, `toHom_apply_apply`),
   so the expected delta is zero and a `MISMATCH` is a genuine mis-transcription.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The step's own modules only, under `flock`/`timeout`: no tree build, no dependents, silent at the
   200k cap. `IsCurveOver/ConstantFieldExtensionSpan.lean` is the one with a pre-existing 200k
   offender; its gate is the module build at the project cap. `Pic0/WeilPairing.lean` (703→≈950
   lines) and the two new modules are checked at the 200k loop.
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters stay with the
   reason recorded. Expected: the `not_mem_range_of_pow_eq` two-module cluster (§5.4), and the
   `Place/DegreeOne`'s existing `valuation_aeval_eq_one`/`surjective_algebraMap_residueField`
   private pair — neither contains a declaration's mathematics twice.
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`; no
   worker writes a `spec/decl_markers.tsv` row.
6. Each module's `spec-pin:` block gains the wrapper and the `S_` copy of every node it adds (nine
   lines, §1); no false wire is added, and none of the set's modules is a metadata entry's module.
7. A `spec/` consumer zone with a real cross-module composition (no `#check`s), whose error count is
   the deliverable metric: `spec/AlgebraicCurveSet9Consumer.lean` — Zone A composes RAT with the ℙ¹
   dictionary at `F = RatFunc K` (rationality of a `placeOfPoint` from the general theorem); Zone B
   applies REC to `f = RatFunc.X` and `g = 1 - X` with the principal divisors from
   `PrincipalDivisors/RatFuncDegree` and reads the reciprocity identity in product form; Zone C
   composes PAIR with the carrier and `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing` at a
   `DivisorialWeilPairingData` constructed from a `move` hypothesis; Zone D applies ELL at `D = 0`
   to put the constants of `F'` in the span of the image. Run with the project cap, not in the edit
   loop.

## 7. The calls this brief asks the reviewer to settle

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **the four rows / 866 silo (+ the ≈113-line gate)**, not SET 8's forecast three | the 119 is a premise of the 100 and was hidden by a name shadow; without it REC cannot be written faithfully |
| 2. RAT's home | **insert `Place/DegreeOne.lean`** (+1 import `Defs/PlaceEvaluation`) rather than a new `Place/Rationality.lean` | the module is the same subject (rational residue field over an algebraically closed base) and already holds the engine; 5 in-tree importers to rebuild |
| 3. REC's home | **new `WeilExchange/WeilReciprocity.lean`** (3 imports), as SET 8's call 2 anticipated | no existing module is above the ℙ¹ dictionary *and* `Place/EvalAtNorm`; alternative `PrincipalDivisors/WeilReciprocity.lean` if the reviewer reads the subject as principal divisors rather than exchange |
| 4. PAIR's home | **new `Pic0/DivisorialPairing.lean`** (2 FLT + 2 Mathlib imports) | `Pic0/WeilPairing.lean` cannot host it (it is below `P1/Dictionary`); the later nondegeneracy rows (130, 656, 553) can join this module |
| 5. the gate | **taken** — carrier + bridge in `Pic0/WeilPairing.lean`, 16 names relabelled to the pin's `Def_` spellings, `evalFun_one` promoted, 2 `own:` rows (§1.1) | the relabel is the only way to state `compatible` at the pin's text; it came out cascade-free (0 importers) at 38 ok / 0 / 0 / 2 own |
| 6. the two shadows | `--unport` both for the reads; **the cure is this set** (REC makes `weilReciprocity` true, RAT makes `Place.isRational_of_isAlgClosed` true) | after the set the two `--unport` flags retire; the corrected and instrument reads converge on the AC block |
| 7. the dispatch | **manager lane for RAT + REC + ELL + the gate; one worker order for PAIR** (§1) | the worker's module imports REC's, so REC must build first |
| 8. the instrument | record the **`port_advise` shape-tier false substitution** (§0.3, instance binders are skipped) as FR-0075 in [../../logs/frictions.md](../../logs/frictions.md), and add it to the recipe's "false negatives to carry" | a row can be 103 net new lines and price at 0; the `--with-defs` "already in the port" figure is not a gate either way |
| 9. the 496's private helper | keep the pin's 18-line `not_mem_range_of_pow_eq` private copy and record the dedup cluster | promoting `Place/OrderArithmetic`'s copy would make a pin-prelude helper public for no consumer |

Calls 1–7 and 9 were taken as recommended; they are recorded as landed in §1.1–§1.2 (call 2 with
the ℙ¹-step deviation, call 9 with the extra private helper the gate did not have).  Call 8 is
recorded as **FR-0075** (the shape tier's instance-blind substitution) plus its checker sibling
**FR-0076** (the universe-suffixed row), both in [../../logs/frictions.md](../../logs/frictions.md).
The recipe's own §0 bullet list still wants the premise-shadow class and the shape-tier failure —
that edit is the reviewer's.

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json          # §0 instrument
python3 frontier.py --selfcheck                                                           # clean (MD-001 fixed)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport AlgebraicCurve.weilReciprocity \
  --unport AlgebraicCurve.Place.isRational_of_isAlgClosed                                 # §0.1 corrected
python3 port_advise.py --with-defs --nodes <each row> --json build/set9-defs.json         # §0.2
python3 port_advise.py --nodes AlgebraicCurve.Place.isRational_of_isAlgClosed \
  --nodes AlgebraicCurve.weilReciprocity \
  --nodes AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible \
  --nodes AlgebraicCurve.ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed \
  --json build/set9-four.json                                                             # §0.3
python3 port_plan.py --json build/set9-four.json                                          # prints 644, the work is 747
python3 twin_scan.py --node <each row>                                                    # relative, relative, new, new
python3 spec/check_port.py --force <module>                                               # §6.1
```

**The three measured numbers.**

1. **What the set will consume**: 4 rows / 866 silo; **747 net new math lines** from the `S_` files
   (866 raw − 119 boilerplate) **plus ≈113 net for the carrier gate** — call it **≈860 net new math
   lines**; two new modules (`WeilExchange/WeilReciprocity.lean`,
   `Pic0/DivisorialPairing.lean`), three inserts (`Place/DegreeOne.lean`,
   `IsCurveOver/ConstantFieldExtensionSpan.lean`, `Pic0/WeilPairing.lean`), nine wire lines, two
   import edges, one 15-name relabel, one promotion (`Divisor.evalFun_one`), 0 migrations,
   0 new `Def_` modules.
2. **The read it starts from** (the two-marker baseline of §0): `needed` **944 / 380,928**; 68 ready
   / 12,917 silo; 262 leaves / 64,874; the four FR-0044 withholdings (831); `AlgebraicCurve` ready
   **2 / 270** and demand **55 / 20,583**; frontier **1,471 / 746,438**. The instrument reads
   942 / 380,709 and AC 2 / 647; the one-marker read of SET 8's baseline reads AC 2 / 251.
3. **What it leaves** (the forecast below was exact — measured in §1.2): `needed` **940 / 380,062**; `AlgebraicCurve` demand
   **51 / 19,717**; frontier **1,475 / 747,304**; the AC ready shelf **2 rows / 299** (the genus
   pair, below). **The two bases now converge**, and this is the set's cleanest diagnostic: the
   instrument reads `942 − 2 = 940 / 380,709 − 647 = 380,062` (only the 496 and the 151 leave its
   `needed`; the 119 and the 100 were already — spuriously — in its F, and its frontier grows by
   those 647 lines), while the two-marker basis reads `944 − 4 = 940 / 380,928 − 866 = 380,062`.
   Same state, counted two ways, because the two shadowed nodes are now *genuinely* ported and the
   last-name tier has become a true positive. The `--unport` flags of §0.1 retire with this set;
   the instrument needs no new correction until the next same-last-name pair appears.

**The rows this set makes ready** — two, the genus-preservation pair, both off ELL's 151 (nothing
else enters; the 496's own consumers stay behind the prunable subject):

| row that becomes ready | silo | unblocked by | what it is |
|---|---:|---|---|
| `le_genusFF_of_constantFieldExtension_of_isAlgClosed` | 151 | ELL's 151 | genus does not drop under an algebraically closed constant extension |
| `genusFF_le_of_constantFieldExtension_of_isAlgClosed` | 148 | ELL's 151 | the reverse inequality |

One behind them, `genusFF_eq_of_constantFieldExtension_of_isAlgClosed` (27), which needs both. That
is the AC column's next set (299 + 27 = 326 silo, ≈a manager lane), and it is the last of the
constant-field-extension story that
[TOPIC-constant-field-extension.md](TOPIC-constant-field-extension.md) §11 names.

**What the set makes *reachable* but not ready.** The pairing family —
`Pic0.exists_weilPairing` (553), `Pic0.exists_antisymmWeilPairing` (656),
`DivisorialWeilPairingData.toHom_injective_of_isCurveOver` (130),
`Pic0.exists_weilPairing_tateModule_of_isCurveOver` (398), and the MC column's Hecke-pairing rows —
all consume the 496, but each also needs `Pic0.exists_nsmul_eq` (130), whose own premise is
`Place.exists_natCast_dvd_ord_sub_single_sub_single` (267), which needs the **withheld**
`…_complex` row (126). So the divisorial-pairing cone stays behind the prunable complex-analytic
subject (140 nodes / 74,620 lines) and the RR column's phase 3, exactly as SET 6 §9 and
[../deligneSerre/PRUNABLE-complex-analytic.md](../deligneSerre/PRUNABLE-complex-analytic.md)
record. The 496's landing is the last cheap link in that chain; the rest is the prunable subject's.

## 9. What this set does not do

- **`Pic0.exists_nsmul_eq` (130) and everything the pairing family needs beyond the carrier.** They
  are behind `Place.exists_natCast_dvd_ord_sub_single_sub_single` (267) → `…_complex` (126), the
  prunable withheld row. Do not port around it.
- **The other route to the same pairing — `toHom_injective_of_divisible_coprime_of_isAlgClosed` (502)
  and `weilReciprocity_of_isAlgClosed` (253).** They need `weilReciprocity_algebraMap_of_isSeparable`
  and two separability rows; that is a second, independent story (the "separable reciprocity"
  lane) and it is not on any ready shelf.
- **`Perfect`, `toWeilPairingData`, `ExistsPerfectDivisorialWeilPairing`,
  `nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing`, and the Galois block of the
  carrier module.** `toWeilPairingData` needs `WeilPairingData`
  (`Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean:170`), which the port does not have
  (it holds only that `Def_` module's `HomPic0Gm` abbrev, `Defs/Divisor.lean:118`); `Perfect` needs
  the surjectivity half.
- **The `Def_` module's Galois block** — `galSmul`, `galSmul_pairing`, `Place.isRational_smul`,
  `Place.mem_smul_toValuationSubring_iff`, `Place.residue_smul`, `Place.evalAt_smul`,
  `Pic0.smul_mem_torsion`, `pair_smul`, `pair_pow_eq_one`, `pair_self_eq_one`.  It is the reason
  PAIR carries a private `Place.evalAt_smul_of_forall_isRational` (§1.2).  This block is the next
  `Def_` gate's natural work: `pair_smul` and the MC column's pairing-equivariance rows want it.
- **The two `AlgebraicCurve` withholdings (221 silo)** and the four `FR-0044` rows — unchanged, the
  prunable subject's consumers and the MC column's Tate-module rows.
- **The 36-line MC row `exists_sum_smul_eq_of_isIntegralQExp_gamma1` and the MC shelf (1,273 silo).**
  MD-001 is now resolved (the row is honestly ready); the MC column owns it.
- **No surface promotion beyond `Divisor.evalFun_one`, no migration, no new definition module, no
  tree build.** The gate's relabel is a renaming at the pin's own spellings, not a promotion of new
  mathematics.
