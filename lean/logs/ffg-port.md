# The `functionFieldGeneration` effort — record

**Status: Layer 0 complete.** This is the running record for
the second port, parallel to [card-torsion-port.md](card-torsion-port.md) for the
first: what *this* effort did, what it cost, and what it decided. Lessons that
generalize go to [porting-playbook.md](../porting-playbook.md); decisions and
measurements stay here.

The blueprint is [PORTING-FFG.md](../PORTING-FFG.md) — it holds the scope
argument, the deferral menu, and the §7 plan for the theorem. The completed topic
work order is [TOPIC-jq-coefficients.md](../TOPIC-jq-coefficients.md). The
deliverable measure is [spec/ModularCurveConsumer.lean](../spec/ModularCurveConsumer.lean),
and [spec/check_flt_statements.py](../spec/check_flt_statements.py) diffs the
port's statements against the pin.

This record is self-contained: the per-layer work orders were used and then
deleted, and everything durable they carried is either here or in
[porting-playbook.md](../porting-playbook.md) §7. Nothing below points at a file
that no longer exists.

FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 0. Where the effort stands

| layer | scope | status | measure |
|---|---|---|---|
| 0a | `qExpand`, `coeffMap`/`coeffEmb`, `qTwist`, the `j`-series, `FunctionFieldGeneration` | **done**, 4 modules, 68 decls, 627 lines | consumer **Zone A at 0 errors** |
| 0b | the two fields, the polynomial datum, the slot vocabulary, `TS`, the §2 collapse | **done**, 5 modules, 69 decls, 622 lines | consumer **0 errors**; `TS` and the collapse bound |
| topic | the low coefficients of `jq` (`744`, `196884`) | **done**, 1 module, 24 decls, 207 lines | consumer Zone C bound; only the capstone `sorry` remains |
| theorem | PORTING-FFG §7's 24-node remainder behind the Φ_p input | **deferred**, not scheduled | — |

The tree was restructured once, after 0b: the definitions had lived in a separate
`lean_lib ModularCurveX0`, and since Layer 0 landed with no `sorry` that reason
disappeared, so they were merged into the single `FLTForHuman` library as
`FLTForHuman/ModularCurve/`, beside `FLTForHuman/Elliptic/`. Module paths became
`FLTForHuman.ModularCurve.*`; the namespace stayed `ModularCurve`. Commands in
the historical tables below refer to the two-library layout as it was when the
measurement was taken.

## 1. Why this effort is definitions-only

The gain test in [PORTING-FFG.md](../PORTING-FFG.md) §2 governs everything here.
Truth is not in doubt; the question was what a port buys. The first port bought
four things: organization (197 importers of one 1869-line engine → 13
role-named modules), clutter never written (~650 lines, 18% of its cone), mathlib
alignment (its interface *is* mathlib's), and truth.

For FFG only the first survives. Its 144-file, 24402-line cone is ~2% removable
clutter, mathlib absorbs **nothing** (`jq`, `qExpand`, `qTwist`,
`modularFunctionField`, `ModularPolynomial` all return no hits), and the two
cones share zero theorem nodes and zero definition modules. Porting the theorem
would cost 12605 lines at the playbook's measured ~1:1 ratio, buying no clutter
and no API dividend — so the *definitions* were taken as the deliverable, where
the gain is a usable, mathlib-only vocabulary for math/010, and the theorem kept
as a menu (§7 of the blueprint).

## 2. Layer 0a: what it cost

Measured from the session that did it:

| | |
|---|---|
| goal rounds | **1** (of the 20 budgeted) |
| tool calls | 89 |
| wall clock | ~7 minutes (17:37:10 → 17:44:31) |
| declarations | 68 |
| lines written | 627 across 4 modules, plus a 231-line consumer |
| build | `lake build` 2086 jobs; `lake build ModularCurveX0` 2581 jobs; both green, 0 warnings, no `sorry` |

| module | lines | decls | FLT source (`aa2d8b3`) |
|---|---|---|---|
| `Defs/Laurent.lean` | 286 | 28 | `Def_ModularCurve_X0` 25–105, 340; `Def_ModularCurve_LaurentCoeff` 16–123 |
| `Defs/Twist.lean` | 131 | 11 | `Def_ModularCurve_PhiGen` 18–96 |
| `Defs/Jq.lean` | 165 | 27 | `Def_ModularCurve_X0` 111–212 |
| `Defs/Target.lean` | 45 | 2 | `Def_ModularCurve_X0` 233–242 |

Two side facts about the tree, both from this effort's period:

- the smoke-test modules `FLTForHuman/Basic.lean` and `FLTForHuman/CountableModule.lean`
  were removed; they were the only `import Mathlib` in the tree, and removing them
  took the default build from **8936 to 2086 planned jobs**;
- `spec/ModularCurveConsumer.lean` is deliberately in no library, so it cannot
  break either build and `lake build` never sees it.

## 2b. Layer 0b: what it cost

| | |
|---|---|
| goal rounds | **1** (of the 4 budgeted) |
| declarations | 69 |
| lines written | 622 across 5 modules, plus the consumer and a new statement checker |
| build | `lake build` 2086 jobs; `lake build ModularCurveX0` 2586 jobs; both green, 0 warnings, no `sorry` |

| module | lines | decls | FLT source (`aa2d8b3`) |
|---|---|---|---|
| `Defs/Polynomial.lean` | 52 | 2 | `Def_ModularCurve_X0` 215–232 |
| `Defs/Fields.lean` | 143 | 17 | `Def_ModularCurve_X0` 246–348 |
| `Defs/PhiGen.lean` | 274 | 39 | `Def_ModularCurve_PhiGen` 111–309 |
| `Defs/TS.lean` | 103 | 10 | `P2M/Sol/S_ModularCurve_functionFieldGeneration` 39–101 |
| `Collapse.lean` | 50 | 1 | `Thm_…_iff_full_eq` 6 / `S_…_iff_full_eq` 11–21 |

The split (as built) puts `ModularPolynomialData` apart from
the fields because it is the *type* of the Φ_p input rather than a field, and
`TS` is the one block taken from a **solution** file rather than `Definitions/`.

## 2c. Topic: the low coefficients of `jq` — what it cost

The first *proof* layer of this effort, and the first whose proof is ours rather
than a transcription — the statement is base/004's and FLT has no declaration of
it, so there is no FLT name to keep.

| | |
|---|---|
| goal rounds | **1** (of the 4 budgeted; the round-1 scouting checkpoint passed on the first try) |
| declarations | 24 in the module: 2 public (`coeff_jq_zero`, `coeff_jq_one`), 22 `private` helpers |
| lines written | 207 (`FLTForHuman/ModularCurve/JqCoefficients.lean`) |
| build | `lake build` green, 0 warnings, no `sorry`; **2632 planned jobs** against 2086 before |
| axioms | `#print axioms` on both: only `propext, Classical.choice, Quot.sound` |
| checker | `spec/check_flt_statements.py`: 137 identical, 0 mismatched, 0 missing, **2 own-proof exemptions** |

**The hybrid held.** `etaProd` is definitionally `∏' n, (1 - X ^ (n + 1))`, and
mathlib's `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` identifies that product
with `pentagonalSeries`, whose coefficients are explicit
(`coeff_pentagonalSeries_pentagonal`); `coeff_pentagonalSeries_eq_zero` covers the
rest. From there the computation is finite and low-order: `coeff_one_pow` for the
first coefficient of a power, a hand-written `coeff_two_mul` / `coeff_two_pow` for
the second, and `Δ * Δ⁻¹ = 1` (not `coeff_invOfUnit`'s recursion) for the inverse.
No part of FLT's modular-form cluster is ported. The only friction the plan did
not name was that mathlib has no `coeff`-at-`2` power formula, so the two
`coeff_two_*` helpers are written out — 12 lines, the whole of the extra API.

**The cost ratio, and a correction to the topic's premise.** The topic priced this
against "the modular-form q-expansion cluster (44 nodes, ~11k lines)". That is not
where FLT proves these coefficients. FLT has a dedicated, standalone file —
[`P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean),
**237 lines / 21 declarations**, importing only `Mathlib`,
`Definitions.Def_ModularCurve_X0` and `P2M.Util` — which proves the first *six*
coefficients of `jNum` (our `744` and `196884` among them) by truncating the
product and convolving hard-coded coefficient lists. That file, not the cluster,
is the like-for-like analogue, so the measured ratio is **207 / 237 ≈ 0.87 : 1**
in lines (24 / 21 ≈ 1.14 : 1 in declarations). Against the 11k-line cluster the
topic feared the ratio is ~0.02 : 1, but the cluster was not FLT's route either.
The honest reading is the same lesson as §8.1, one layer on: the coefficients are
cheap, but *which* FLT code is the analogue was mis-identified, and FLT itself did
not spend the 11k lines on them.

One measured side effect: the pentagonal import adds ~546 mathlib modules to the
default build's planned job count (2086 → 2632). They are covered by the shared
oleans, so the warm build is unchanged at a few seconds; nothing in this tree
compiles them from source.

## 3. What was verified

Independent QA of 0a after it landed:

| check | result |
|---|---|
| every declaration name present in the pinned sources | 68 of 68 |
| **every statement text identical to the pinned source** (whitespace-normalised) | **68 of 68** |
| port set vs FLT's 0a source ranges | equal, 68 = 68 — no omission, no creep |
| `sorry` / `admit` / `axiom` / `native_decide` | none |
| `import Mathlib` | none |
| `#print axioms` on `FunctionFieldGeneration`, `functionFieldGeneration_one`, `qTwist_qExpand`, `jq` | only `propext, Classical.choice, Quot.sound` |
| consumer | Zone A 0 errors; 10 remaining are exactly Zone B (8) and Zone C (2) |

Layer 0b, on landing:

| check | result |
|---|---|
| every port statement identical to the pinned source (`spec/check_flt_statements.py`) | **137 of 137** (68 from 0a, 69 from 0b), 0 mismatched, 0 missing |
| the checker is non-vacuous | a mutated statement is caught |
| `sorry` / `admit` / `axiom` / `native_decide` in `FLTForHuman/ModularCurve/` | none |
| `#print axioms` on `functionFieldGeneration_iff_full_eq` | only `propext, Classical.choice, Quot.sound` |
| consumer | **0 errors**: Zone A, Zone B and the `TS` half of Zone C bound; 3 deliberate `sorry`s (the capstone and the two Zone C `jq.coeff` claims) |

The topic, on landing:

| check | result |
|---|---|
| `sorry` / `admit` / `axiom` / `native_decide` in `FLTForHuman/ModularCurve/` | none (checked by `grep`) |
| `import Mathlib` (bare) anywhere in the tree | none |
| `#print axioms` on `coeff_jq_zero`, `coeff_jq_one` | only `propext, Classical.choice, Quot.sound` |
| `spec/check_flt_statements.py` | 137 identical, 0 mismatched, 0 missing, 2 own-proof declarations exempted |
| checker non-vacuity | an unlisted new declaration is caught as `MISSING IN FLT` |
| consumer | **0 errors**; the only remaining `sorry` is the capstone |

The statement-identity result is the one to carry forward: with a pinned source
dictating the statements, faithfulness is *mechanically checkable*, and it should
be checked every time rather than assumed. A script in `spec/` that diffs the
port's statements against the pinned files would be a welcome addition to 0b.

## 4. Decisions taken, and why

| decision | reason |
|---|---|
| Definitions, not the theorem | the gain test, §1 above |
| `FunctionFieldGeneration` inside 0a | the target's content is a `def` mentioning only `jq`, `qExpand`, `IntermediateField.adjoin` — so 0a can *state* the target and *prove* its `M = 1` case |
| `TS` out of scope for 0a, decided **in** for 0b | it is in the *solution* file, not `Definitions/`, so it needed a deliberate call; it is ten declarations, depends only on 0a, and is math/010 §1's central notation |
| `functionFieldGeneration_iff_full_eq` in for 0b | the smallest node in the deferred manifest (22-line proof, `cites = 0`), math/010 §2's collapse, and the only theorem in Layer 0 |
| Namespace `ModularCurve`, FLT names verbatim | keeps `#check` comparison against the pin and math/010's §9 map mechanical. Recorded as a *trade*: the safety comes from the mathlib pin, not the choice |
| Two libraries, `spec/` in neither | keeps `FLTForHuman`'s green, no-`sorry`, seconds-warm build meaningful |
| Never `import Mathlib` | see the job-count fact in §2 |

## 5. Friction (mathlib `v4.34.0` against FLT's `v4.33.0`)

Twelve entries, kept in full at the tail of the consumer file.

The 0a half — five entries plus one non-event:

1. `HahnSeries.embDomain_notin_range` → `HahnSeries.embDomain_of_notMem_range`
   (drop-in; hit in `Laurent.lean` and `Jq.lean`).
2. `if_pos` → `ite_eq_left` (already on the first port's list; hit in
   `dedekindPsi_one`).
3. `linter.style.haveILetI` flagged FLT's `haveI := hne` in
   `functionFieldGeneration_one`; dropping the line keeps the proof and clears
   the warning (the `intro`'d `NeZero d` is already a local instance).
4. Two Zone A examples in the *consumer* were wrong as first drafted — our spec
   bug, not FLT's (see §7).
5. No drift in the rest of the API leaned on.
6. The predicted rewrite-search gap did not occur (see §6).

The 0b half — consumer entries 7–12:

7. `if_neg` → `ite_eq_right` alongside `if_pos` → `ite_eq_left`, again in
   `PhiGen.lean`'s `cosetA`/`cosetB` lemmas.
8. `linter.style.haveILetI` twice more, in `Fields.lean`; both `haveI`s were
   unnecessary — an `intro`/`rintro`-introduced `NeZero` is already an instance,
   and `NeZero (ℓ * d)` follows from `[NeZero ℓ] [NeZero d]` by search. The
   `haveI` inside the `def cosetSubst` is not flagged (the linter only fires on
   `Prop` goals) and was kept.
9. Two expected signatures in the *consumer's comments* were wrong: Lean
   auto-omits unused section variables, so `modularFunctionFieldFull` and
   `divisorExpansions` carry no `[NeZero N]` (FLT's are the same). A spec bug,
   like entry 4.
10. `TS` is `ModularCurve.TS` in the port but `ModularCurve.W1.TS` in FLT — a
    per-file namespace, never exported to `ModularCurve`. A recorded divergence
    in *name* only; all ten statements are FLT's verbatim.
11. The three shape risks named for 0b all failed to appear (the table in §6).
12. Statement correspondence became mechanical: `spec/check_flt_statements.py`,
    137 of 137 identical, 0 mismatched, 0 missing.

## 6. Predictions vs measurements

The plan's model was wrong twice, in opposite directions, and both are worth
remembering:

| prediction | measured |
|---|---|
| 10–14 goal rounds expected, 20 budgeted | **1 round**, 89 tool calls, ~7 minutes |
| the `def`-as-ring-hom rewrite-search gap would be the dominant obstacle (playbook §3.5) | **did not occur** — FLT proves these lemmas coefficientwise, and its own `[simp]` coefficient lemmas (`qExpand_coeff_mul`, `coeffMap_coeff`, `qTwist_coeff`, …) *are* the named bridges |
| ~57 declarations | 68 |

The budget lesson: transcribing a definitions file is cheap when the target is a
pinned source and the statements are dictated. The cost lives in *shape*
mismatches — typeclass, coercion, defeq, renamed API — not in volume, so a budget
for this kind of work should be set in "number of shape risks", not lines. That
is why 0b's work order budgeted four rounds where this one budgeted
twenty. The checkpoints keep their value as a *diagnostic*: they say when a stall
means a structural problem rather than slowness.

The non-event lesson: a confidently predicted obstacle that never appears is
information. The rewrite-search gap is real (the first port hit it), but it is
triggered by proving *through* a generic lemma, not by using a `def`-as-ring-hom
at all.

Layer 0b made the same point a second time, on all three of its named risks:

| prediction (0b) | measured |
|---|---|
| 4 goal rounds budgeted, checkpoint at 2 | **1 round** |
| ~60 declarations | 69 |
| `swapInner`/`swapBivar` would finally trigger the rewrite-search gap | **did not** — both proved verbatim, `swapBivar_X`/`swapBivar_C_X` by `eval₂_X`/`eval₂_C` + `aeval_X` |
| `Subalgebra` vs `IntermediateField` (`adjoinJq`, `jAdj`, `evalAtJAdj`) would need coercion work | **none needed** |
| finite products and `data.monic.map` would be new friction | **none** — `monic_prod_of_monic`, `natDegree_prod_of_monic`, `Polynomial.eval_prod`, `Monic.map` all worked as transcribed |
| `TS_injective`, the one proof in `TS` with content, might resist | **worked first try** |

That is two layers in a row where the budgeted cost was shape risk that did not
materialize. The honest calibration is that transcribing a pinned, definitional
source with the statements dictated is now measured cheap: **2 rounds total for
Layer 0**, against 24 budgeted.

## 7. What the consumer caught

The consumer is the definition of done, and executing it found two genuine errors
in its own Zone A examples:

- the twist-coefficient example omitted `[Algebra ℚ L]`, which `coeffEmb`
  requires, so it could not elaborate;
- the `qTwist_qExpand` example applied `qExpand ℚ N` to a `LaurentSeries L` (a
  universe/type mismatch) and, on the right, dropped the `u ^ (N : ℤ)` twist,
  which makes the statement false.

Both were corrected to the intended and FLT forms. The lesson is recorded in the
work order's post-mortem: a specification is an artifact like any other and needs
review by execution, not just by writing.

Layer 0b's execution caught a second spec bug of the same kind: the consumer's
expected-signature *comments* for `modularFunctionFieldFull` and
`divisorExpansions` claimed a `[NeZero N]` that Lean auto-omits (FLT's signatures
have none either). Same lesson, one layer on: the consumer is executable, so its
claims are testable.

## 8. Next

Layer 0b is done: `Defs/Polynomial.lean`, `Defs/Fields.lean`, `Defs/PhiGen.lean`,
`Defs/TS.lean` and `Collapse.lean` are green, the consumer is at **0 errors**,
and none of the three shape risks named for it appeared (the table in §6).

The effort has reached the floor it set itself: Layer 0 is complete and
mechanically verified — 137 of 137 statements identical to the pin, no `sorry`,
no `import Mathlib`, `#print axioms` clean. Two `jq.coeff` claims in consumer
Zone C (`744`, `196884`) were expected to stay red because they live inside the
deferred Φ_p subtree. The final check found that expectation to be wrong, the
topic below was taken, and it finished in one round (§2c). Zone C is now closed:

- **[TOPIC-jq-coefficients.md](../TOPIC-jq-coefficients.md)** — **done**.
  `coeff_jq_zero` and `coeff_jq_one` are proved in
  `FLTForHuman/ModularCurve/JqCoefficients.lean`. `etaProd` *is* mathlib's
  topological product, so `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` gives
  `∏' n, (1 - X ^ (n+1)) = pentagonalSeries`, with explicit coefficient lemmas, and
  the route is a finite low-order computation — `1 + 744q + 196884q² + ⋯` — with no
  part of the 44-node subtree. The hybrid held; the measured ratio against FLT's
  closest analogue is ≈0.87 : 1. What remains is the deferred theorem of §7, to be
  taken only if a future session picks a topic out of it.

### 8.1 Two findings from the final check

Both change the plan, and both are corrections to the record rather than to the
code.

**The manifest double-counts near-duplicate proofs.** PORTING-FFG §7.3 lists
`Polynomial.mem_range_of_unique_common_root`, `Polynomial.mem_range_of_eval_eq_const`
and `Polynomial.irreducible_of_transitive_ringAut` as three 182-line nodes. They
are three *files* of 182 lines each, but each file contains the same three
`private theorem`s plus a two-line `solution`: the distinct content is one
182-line file, not 546. Their md5s differ only in namespace and the `solution`
line. The playbook's own rule applies — *diff before porting the second* — so any
future sum over the remainder should be de-duplicated first. The 24-node count is
right; the 12420-line sum is an upper bound, not a work estimate.

**The `jq.coeff` claims were mis-classified as unreachable.** They were placed in
Zone C because FLT proves them inside the Φ_p subtree. But Zone C was defined as
"what the Definitions layer does not deliver", and these two facts are reachable
from the Definitions layer *plus mathlib*, by a route FLT does not use. The
lesson, worth carrying: **an item's cost is a property of the route, not of the
node it sits under in FLT's graph.** The same reasoning that justified the first
port's hybrid should be applied to every Zone C item before accepting it.

### 8.2 A note on the metric

The consumer's error count measures *unbound names*, not *unproved claims*: the
two Zone C `jq.coeff` items never contributed to it, because their statements
elaborated from the start and only the proofs were `sorry`. So "0 errors" was
reached at 0b while three `sorry`s remained (the capstone and the two
coefficients). The count is still the right primary metric — it tracks exactly
what the port is for, namely that the vocabulary exists and composes — but any
future definition of done should state the expected `sorry` set explicitly rather
than inferring it from the error count, as 0b's definition of done did.

### 8.3 A third finding, from the topic's execution

**The coefficients were never in the 11k-line cluster.** The topic was justified
by the belief that FLT reaches `η`'s coefficients through
`S_ModularCurve_StarBank_deltaNorm` and the modular-form cluster, and that
avoiding FLT's route therefore saved ~11k lines. FLT actually proves them in a
standalone 237-line file,
[`P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean)
(six coefficients, importing no cluster), by truncating the product and convolving
hard-coded lists. The 11k-line figure was the *cluster's*, not this item's — §8.1's
lesson once more: cost is a property of the route, not of the node. It is worth
recording because the 11k figure was the topic's whole justification for diverging
from FLT, and the correct analogue is a quarter of the assumed size; future topics
should locate the actual FLT proof of the specific statements before pricing it by
the subtree it appears under.

### 8.4 The option space after the topic

The effort has reached a plateau: everything cheap and clearly motivated is done.
This survey is recorded because the surveying is the expensive part and should
not be redone.

**The wider development is vast and mostly irrelevant.** The FLT clone holds
**7,711 `S_ModularCurve_*` solution files**; the capstone's cone is 144 of them.
Of the rest, **659 are ≤ 300 lines and self-contained** — mathlib plus one
`Definitions/` module plus `P2M.Util`, e.g.
`S_ModularCurve_twelve_mul_genusFormula` (12 lines) or
`S_ModularCurve_laurentBaseChange_mono` (11). They are cheap but *unchosen*:
porting one would be "because the graph has nodes", which is what the gain test
forbids. They become relevant only when a note asks a question one of them
answers. (`S_ModularCurve_coeff_jNum_le_six`, the analogue of the `jq`
coefficients, is one of them.)

**The theorem's remainder** is unchanged: 24 nodes below the capstone, behind the
Φ_p input (PORTING-FFG §7). Its per-node line sum is 12,420, and that is an
*upper bound*, for two reasons now measured: §8.1's three `Polynomial` nodes
share one proof, and §8.3 shows the same statements can live in a far smaller
standalone file than the subtree they appear under. Pricing it properly means
scouting each node's actual FLT proof.

**The conditional capstone is the one remaining cheap item with a clear gain.**
`hall_all` — the single strong induction carrying `Tight ∧ Gen` over the divisor
lattice, which is math/010 §2 and §7 — is 86 lines of the solution file, sitting
on about 190 lines of private helpers (`jqN_congr`/`full_congr`/`mff_congr`,
the `dedekindPsi` arithmetic, `tight_one`/`gen_one`, `relfinrank_full_of`,
`full_le_adjoin_chain`, `jqN_pow_not_mem_full`, `root_shape`, `htw_of`, `hsp_of`).
Stated with the 24 remainder nodes as the fields of an `Inputs` structure, that
would check the *architecture* of the proof — and make every input a first-class
named assumption — for a few hundred lines instead of ~10k, and it is exactly the
"sound conditional capstone" PORTING-FFG §7.4 describes. It needs the same
scouting as any topic: whether the helpers are glue over the inputs or carry
work of their own is not yet known.

**Stop-and-harvest is a real option.** The library now supplies the vocabulary of
math/010 and base/004, with the statement landscape mechanically checked and two
concrete claims proved. What it does not supply is proof-level clarity of §§4–7;
that is the one thing left, and it is the expensive one.

## 9. Records map

| file | role |
|---|---|
| [PORTING-FFG.md](../PORTING-FFG.md) | the top plan: scope argument, gain test, deferred theorem menu |
| [TOPIC-jq-coefficients.md](../TOPIC-jq-coefficients.md) | the completed topic plan: the `jq` coefficients |
| [spec/ModularCurveConsumer.lean](../spec/ModularCurveConsumer.lean) | the deliverable measure, and the friction log |
| [spec/check_flt_statements.py](../spec/check_flt_statements.py) | diffs every port statement against the pin |
| this file | the record: what the effort did, cost, and decided |
| [porting-playbook.md](../porting-playbook.md) | lessons for the next port, independent of this one |

**The layer work orders were used and then deleted.** Layer 0 ran as two of them,
0a and 0b, each finishing in a single goal round. Deleting them was the plan from
the start: a work order is scaffolding, and once a layer is done its content is
either in the code (the module list, the statements, the proofs), in the
playbook (the principles, the overlap, the calibration — now §7), or in this
record (the measurements, the decisions, the friction). What was kept is only
what a later session cannot re-derive: `PORTING-FFG.md` as the top plan,
`TOPIC-jq-coefficients.md` as the completed topic record, the playbook, and this
file.

Nothing durable was lost in the move. The principles and the overlap section —
the most reusable things this effort has produced, more so than the module list,
which is derivable from the code — are §7.1 and §7.2 of the playbook, and the
post-mortem with the measured cost is §6 above.
