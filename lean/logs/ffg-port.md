# The `functionFieldGeneration` effort — record

**Status: Layer 0 complete.** This is the running record for
the second port, parallel to [card-torsion-port.md](card-torsion-port.md) for the
first: what *this* effort did, what it cost, and what it decided. Lessons that
generalize go to [porting-playbook.md](../porting-playbook.md); decisions and
measurements stay here.

The Φₚ splitting / R1 sub-effort that gates the deferred theorem
([PORTING-PhiGen.md](../topics/PORTING-PhiGen.md)) keeps its own measured record in
[phiGen-port.md](phiGen-port.md); its first topic, R1's constancy kernel, is
complete. It shares no declaration with this effort, so its cost is not counted
in the tables below.

The blueprint is [PORTING-FFG.md](../PORTING-FFG.md) — it holds the scope
argument, the deferral menu, and the §7 plan for the theorem. The topic work
orders are [TOPIC-jq-coefficients.md](../topics/functionFieldGeneration/TOPIC-jq-coefficients.md),
[TOPIC-conditional-capstone.md](../topics/functionFieldGeneration/TOPIC-conditional-capstone.md),
[TOPIC-interface-tier.md](../topics/functionFieldGeneration/TOPIC-interface-tier.md) and
[TOPIC-generic-kernel.md](../topics/functionFieldGeneration/TOPIC-generic-kernel.md), all completed. The
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
| topic 1 | the low coefficients of `jq` (`744`, `196884`) | **done**, 1 module, 24 decls, 207 lines | consumer Zone C bound |
| topic 2 | the conditional capstone (`Spine.lean`) | **done**, 1 module, 29 decls, 494 lines | consumer Zone B bound; `Inputs` is the remaining debt |
| topic 3 | the cone's outbound interface | **done**, 9 public lemmas added to 2 existing modules; `Inputs` 10 → 8 | consumer unchanged (0 errors, 1 `sorry`) |
| topic 4 | the generic kernel (`FLTForHuman/FieldTheory/CommonRoot.lean`) and the `relfinrank` peel | **done**, 1 new module, 3 public lemmas + 3 instantiations; `Inputs` 8 → 7 | consumer unchanged (0 errors, 1 `sorry`); checker 150 |
| T14 | the shared slot prelude, written once | **done**, 2 new modules + 3 extended; 32 declarations, 503 port lines | consumer **Zone L** (0 errors); checker 276 |
| T15 | descent by one prime and the one-prime reduction | **done**, 1 new module; 2 declarations, 252 port lines; `Inputs` 7 → 5 | consumer **Zone M** (0 errors); checker 278 |
| T16 | the degree of one prime-power step | **done**, 1 new module + 4 extended; 10 declarations, 605 port lines; `Inputs` 5 → 4 | consumer **Zone N** (0 errors); checker 288 |
| T17 | the non-membership tower and the two-prime separation | **done**, 1 new module; 2 declarations + 14 private declarations, 843 port lines; `Inputs` 4 → 3 | consumer **Zone O** (0 errors); checker 290 |
| T18 | one new generator per prime power (node 1 only; the squarefree block deferred) | **done**, 1 new module + `Defs/Fields` move; 1 public node + 2 private helpers, 309 module lines + 36 net; `Inputs` 3 → 2; `gen_prime` landed | consumer **Zone P** (0 errors); checker 293 |
| T19 | the slot product and the prime non-membership | **done**, 1 new module; 2 public nodes + the private M-arbitrary lemma, 1,502 port lines; `Inputs` 2 → 0 (total) | consumer **Zone Q** (0 errors); checker 297 |
| T20 | the unconditional capstone and the interface tail | **done**, 1 new module; 11 declarations + `hall_all` promoted, ≈300 port lines; the headline is unconditional | consumer **Zone R** (0 errors); checker 304 |
| **theorem** | PORTING-FFG §7's 24-node remainder behind the Φ_p input | **complete (2026-09-22)**: the Φ_p cone (T5–T13) and T14–T20 all landed; `Inputs` total; `ModularCurve.functionFieldGeneration` unconditional; out-of-cone tier **100%** | — |

The tree was restructured twice, neither time touching the mathematics.

**Once, after 0b, to merge the libraries.** The definitions had lived in a
separate `lean_lib ModularCurveX0`, and since Layer 0 landed with no `sorry` that
reason disappeared, so they were merged into the single `FLTForHuman` library as
`FLTForHuman/ModularCurve/`, beside `FLTForHuman/Elliptic/`. Module paths became
`FLTForHuman.ModularCurve.*`; the namespace stayed `ModularCurve`. Commands in
the historical tables below refer to the two-library layout as it was when the
measurement was taken.

**Once, after topic 2, to name the theory.** `Spine.lean`, `Collapse.lean` and
`Defs/Target.lean` were generic names — "the spine", "the collapse", "the target"
of *what*? — and a second `ModularCurve` theory would have inherited them as
collisions. They moved to `ModularCurve/FunctionFieldGeneration/`, a directory
named for the theorem (and for math/010's title), leaving `Defs/` as the shared
X₀(N) vocabulary (`qExpand`, `jq`, the two function fields, the slot vocabulary)
that any later theory reuses, and `JqCoefficients.lean` where it was. Paths in the
tables below were updated to the new locations so nothing is stale; the *namespace*
is unchanged at `ModularCurve`, so declaration names, the checker, the consumer
and math/010 §9's map were unaffected. The pattern for the next theory is
therefore: share `Defs/`, add your own `<Theory>/`.

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
| `FunctionFieldGeneration/Target.lean` | 45 | 2 | `Def_ModularCurve_X0` 233–242 |

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

## 2d. Topic 2: the conditional capstone — what it cost

`FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` is the `PORTING-FFG.md` §7.4 artifact: a
**proved** conditional capstone with FLT's significant remaining statements
bundled as the structure `Inputs`. It is the first module whose public surface is
tiny (5 declarations) while the work lives in private glue.

| | |
|---|---|
| goal rounds | **1** (of the 4 budgeted; the round-1 scouting checkpoint passed) |
| declarations | 29: 5 public (`Tight`, `Gen`, `Hall`, `Inputs`, `functionFieldGeneration_of`), 24 `private` |
| lines written | 494, of which 74 are the `Inputs` field statements and 38 the header — about **382 proved lines** |
| build | `lake build` green, 0 warnings, no `sorry`; **2890 planned jobs** against 2632 after topic 1 |
| axioms | `#print axioms functionFieldGeneration_of`: only `propext, Classical.choice, Quot.sound` |
| checker | 137 identical, 0 mismatched, 0 missing, **7 own-proof exemptions** (2 from topic 1, 5 here) |

**The route held, and the auxiliaries were glue.** FLT's scouted closure for
`hall_all` is 32 declarations / 286 lines plus `hall_all` itself (87 lines) ≈ 373
lines; the port's proved content is ≈377 lines, a ratio of ≈1.0 : 1. Every helper
transcribed with at most a rename. `full_le_adjoin_chain` and
`jqN_pow_not_mem_full` are set/tower manipulation; `root_shape`, `htw_of` and
`hsp_of` are polynomial-root bookkeeping *over* the assumed
`minpoly_jqN_map_eq_prod_slots`. None needed machinery outside the port and
mathlib. The one unanticipated ingredient was `Nat.exists_eq_pow_mul_and_not_dvd`
(mathlib) for `dedekindPsi_mul_prime_dvd`; the only shape friction was
`Fact`-vs-instance plumbing and one pinned universe (see the module header).

**What is left is exactly `Inputs`.** With `hall_all` proved and
`functionFieldGeneration_of` applying Layer 0's collapse, the whole distance to
the unconditional theorem is the `Inputs` fields — 10 when this topic landed, 8
after topic 3 (§2e, §8.4). That is the artifact's payload: the remainder is no
longer "the 24-node subtree" but a named, ordered list of statements to discharge
one at a time.

### 2d.1 Post-review corrections

A review of the finished module, after the agent's turn had ended, raised four
points. Two were real and are fixed; two were mistaken and are recorded as such
so the same flags are not raised again.

1. **Two dead declarations, removed.** `iota_jq` (FLT 110–112) and `cycUnit_pow`
   (FLT 213) were transcribed but had no consumer in the spine — `cycUnit_pow`
   was not even in the scouted closure. The project's own rule ("no self-consumed
   lemmas", playbook §7.1) says they are not ported, so both were deleted; the
   declaration count went 31 → 29 and the module header now says so. This is the
   one change to the agent's output, and the build, warnings, consumer and
   checker were all re-run afterwards.
2. **The `Hall`-form fields are now documented.** Two of the ten `Inputs` fields
   state the pin's `hall : ∀ d ∣ M, ⋯ = dedekindPsi d ∧ ⋯` hypothesis as
   `Hall M →`. `Hall` is an `abbrev` for exactly that conjunction, so they are
   definitionally the pin's, and the abbreviation is the shape the induction
   consumes; the module header now records this rather than leaving the claim
   "stated as in the pin" unqualified.
3. **Mistaken: "no pruning record".** The 24 → 10 pruning is in §8.4 below, with
   a reason for each surviving field and the 13 dropped nodes named together with
   why they drop (they occur only inside the proofs of the assumed fields).
4. **Mistaken: "`hall_all` must be public".** The work order's definition of done
   asks for `#print axioms` on `functionFieldGeneration_of` only, and that is
   satisfied; `hall_all` is `private` by a recorded design choice ("the auxiliary
   block is `private`"), and since the capstone depends on it, a `sorry` inside it
   would surface as `sorryAx` in the capstone's own axiom list anyway. No change.

## 2e. Topic 3: the outbound interface — what it cost

Nine public lemmas added to existing modules, placed with the objects they
concern: `coeffMap_qExpand`, `coeffEmb_qExpand`, `coeffMap_injective`,
`coeffEmb_injective` in `Defs/Laurent.lean`; `dedekindPsi_prime`,
`dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`, `aeval_jq_eq_zero`,
`transcendental_jq` in `Defs/Jq.lean`.

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted; the checkpoint at 1 passed) |
| declarations added | **9** public (4 + 5), every statement verified against its `Theorems/` wrapper |
| lines written | ~60 in `Defs/Laurent.lean`, ~130 in `Defs/Jq.lean` (proofs + docstrings; the pin's own proofs are 5–50 lines each) |
| `Spine.lean` | −4 private lemmas, `Inputs` 10 → 8 fields, the `ψ` helpers lost `h : Inputs`; 494 → 478 lines, 29 → 25 declarations |
| build | `lake build` green, 0 warnings, no `sorry`; **2890 planned jobs**, unchanged (both new mathlib imports were already in the closure) |
| axioms | `#print axioms functionFieldGeneration_of`: only `propext, Classical.choice, Quot.sound` |
| checker | **146** identical (137 → +9), 0 mismatched, 0 missing, 7 own-proof exemptions; `SOURCES` gained the 9 wrappers, `OWN_PROOFS` unchanged; a mutated `dedekindPsi_prime` is caught |

**Exposure was free.** Every lemma transcribed on the first try from its pin
proof. The only shape issue was *source selection*: `coeffEmb_qExpand` exists
twice in the pin — the public wrapper with explicit `(L : Type*)` and the
`solution` file's `W1` copy with implicit `{K}` — and the wrapper is the interface,
so the nine wrappers now precede the solution file in `SOURCES`. The one
substantive port remained `dedekindPsi_mul_of_coprime`, whose ψ section needs
`ArithmeticFunction` (mathlib); as scouted, that file's remaining ~399 lines are
an off-path resultant development and were skipped.

**Two of the four `Spine` deletions were duplicates, not moves.** Besides the two
`qExpand` transport facts (which moved to `Defs/Laurent.lean`), two private
helpers turned out to be verbatim copies of lemmas the port already had or had
just gained and were deleted outright: `qExpand_congr'` ≡ Layer 0a's
`qExpand_congr`, and `dedekindPsi_prime'` ≡ the `dedekindPsi_prime` this topic
made public. Both came from FLT's solution file, where they are local copies
because the public versions are imported under different names, so transcribing
the helper block by transitive closure reproduces them. The lesson for scouting:
a closure over a pinned *solution* file will include the file's private
re-derivations of already-ported facts; diff each candidate against the port
before transcribing, exactly as the playbook's "diff before porting the second"
rule says. The audit after this cleanup found no remaining `Spine` private lemma
without a consumer.

### 2e.1 The interface table

Indegrees re-derived from the doc-site graph (`tools/deps`, `FltData.indeg`),
pinned `aa2d8b3`:

| declaration | indeg | FLT proof (lines) | module |
|---|---|---|---|
| `coeffMap_qExpand` | **194** | 15 | `Defs/Laurent.lean` |
| `dedekindPsi_prime` | 72 | 13 | `Defs/Jq.lean` |
| `coeffEmb_qExpand` | 66 | 5 | `Defs/Laurent.lean` |
| `transcendental_jq` | 56 | 13 | `Defs/Jq.lean` |
| `dedekindPsi_mul_of_coprime` | 46 | 23–72 | `Defs/Jq.lean` |
| `dedekindPsi_prime_pow` | 33 | 38 | `Defs/Jq.lean` |
| `coeffMap_injective` | 32 | 10 | `Defs/Laurent.lean` |
| `coeffEmb_injective` | 19 | 9 | `Defs/Laurent.lean` |
| `aeval_jq_eq_zero` | 2 | 28 | `Defs/Jq.lean` |
| **sum** | **520** | ~181 | |

The cone — the `cites`-closure of `ModularCurve.functionFieldGeneration`, 70
nodes — has **40 nodes with indeg ≥ 5, summing to 946**, and 1007 over indeg ≥ 1.
The nine above therefore expose **520 of 946, 55%**, of the ≥5 tier: a majority,
but not "most" in the strong sense the work order's parenthetical suggested. The
unexposed mass is concentrated and named; the next interface candidates are
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (66, the modular-form
cluster), `PhiGen.splits_prime_at_slot` (42), `exists_phiIrreducible_evalSymm`
(29), `hasSum_qParam_mul_laurent` (24), `qExpansion_E4_eq_map_eisenstein4` (20)
and `minpoly_jqN_map_eq_prod_slots` (20). The last is an `Inputs` field, so
exposing it would raise the ratio *and* shrink the debt — but it is a 2,002-line
node, the opposite trade to this topic.

## 2f. Topic 4: the generic kernel — what it cost

`FLTForHuman/FieldTheory/CommonRoot.lean` is the port's first *generic* module:
three lemmas about an arbitrary `F ⊆ L`, no `jq`, no `LaurentSeries`, no import
from the port at all (the pin's two mathlib imports, plus
`Mathlib.Analysis.Complex.Basic` for the instantiations).

**A third top-level area.** `FLTForHuman/` now has three: `Elliptic/` (the first
port), `ModularCurve/` (this one's definitions and theory modules) and
`FieldTheory/`, which is where future **generic prerequisites** go — anything that
is neither `Elliptic/` nor `ModularCurve/`. `CommonRoot.lean` is its first
member and sets the pattern: mathlib-only, no curve-specific name, statements
generic over the field extension. A future `ModularCurve` theory's generic
prerequisites therefore land here, not inside a theory directory; the theory
directory keeps only what mentions the curve.

The topic's second
deliverable is the peel: `relfinrank_modularFunctionField`, the third `cites = 0`
`Inputs` field.

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted; the checkpoint at 1 passed) |
| declarations | 3 public in `CommonRoot` (= the three kernel lemmas) + 3 anonymous instantiation `example`s; 1 public in `Defs/Fields.lean` |
| lines written | 346 in `CommonRoot.lean` (≈170 the three proofs, ≈90 the instantiations and their prose); +29 in `Defs/Fields.lean` (the peel); `Spine.lean` −4 (`Inputs` field and the `h` threading) |
| `Spine.lean` | `Inputs` 8 → 7 fields; `relfinrank_full_of` lost its `h : Inputs` and calls the real lemma; 478 → 474 lines, 25 declarations |
| build | `lake build` green, 0 warnings, no `sorry`; **2891 planned jobs**, one more than 2890 (the new module; the `Complex` import was already in the closure) |
| axioms | `#print axioms` on the three lemmas, the peel and `functionFieldGeneration_of`: only `propext, Classical.choice, Quot.sound` |
| checker | **150** identical (146 → +4), 0 mismatched, 0 missing, 7 own-proof exemptions; `SOURCES` gained the three `Thm_Polynomial_*` wrappers and `Thm_ModularCurve_relfinrank_modularFunctionField`, `PORT_FILES` gained `CommonRoot.lean` |
| wire tests | (1) three concrete `example`s over `ℚ ⊆ ℂ` in the module; (2) the peel, proved in `Defs/Fields.lean` and *used* by `Spine.lean` — a cross-module composition |

**The kernel was as self-contained as scouted.** All three lemmas proved on the
first try from the pin's text, with no private helper needed and no statement
change: the only edits were `private` → public and dropping the `p2m_*` lines.
The distinct generic content is the pin's *one* 182-line file (the three
`S_Polynomial_*` files are copies), and the three proofs are ≈170 lines here — a
ratio of ≈0.93 : 1, and the 182 lines are genuinely 182, not "182 looking like
182". The module header, the docstrings and the instantiation section are the
overhead above the pin.

**The peel was exactly two mathlib lemmas.** `relfinrank_eq_finrank_of_le` and
`extendScalars_adjoin`, applied to the port's own `adjoin_jq_le`, transcribed from
the pin's 31-line proof, with no restatement. `Inputs` therefore went 8 → 7 by
*subtraction only*: one field deleted, `relfinrank_full_of` simplified, nothing
else in the spine moved. The `#print axioms` result is unchanged.

**Where the instantiation lives, and what it exercises.** The three `example`s are
in `CommonRoot.lean` itself (not the consumer, which the definition of done keeps
at "0 errors, one `sorry`"), and being anonymous they are invisible to
`spec/check_flt_statements.py`. Lemmas 1 and 2 are fully concrete over `ℚ ⊆ ℂ`.
For lemma 3 the automorphism is `RingEquiv.refl`: a *nontrivial* `σ` instance needs
a cubic with exactly one real root — so that complex conjugation fixes that root
and 2-cycles the other two, which is the only shape `n = 2` can take over `ℂ` —
and mathlib has no explicit real cube roots, so that instantiation is not
available cheaply. The identity satisfies `hσ` and `hcycle` (with `n = 1`) and the
example does conclude `Irreducible (X² + 1)`.

## 2g. T14: the shared slot prelude — what it cost

T14 is the parent effort's first topic after the Φ_p cone. Its job was to write
the pin's ~370-line shared prelude **once** — the block
`P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` (and its
`_pow_not_mem_adjoin_full` sibling) repeat in up to thirteen of the seventeen
remaining files — so T15–T19 import it instead of each re-copying it.

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted) |
| declarations | **32**: 6 promotions + 21 fresh upstream + 5 downstream |
| new modules | `Defs/PhiAtSlot.lean` (237 lines), `ModularCurve/PhiSlotRoots.lean` (153) |
| extensions | `Defs/TS.lean` +51, `Defs/Twist.lean` +56, `Defs/Jq.lean` +6; `Spine.lean`/`PhiGenSplits.lean` lose their six `private` twins and their imports are re-pointed |
| **port lines** | **503** against the pin's ~306, ratio **≈1.64** (the row's `~250` was pre-scouting; two new modules carry headers + docstrings) |
| build | full `lake build` green, 0 warnings, no `sorry`; **3865 jobs** |
| axioms | `#print axioms` on all **32** public T14 declarations: only `propext, Classical.choice, Quot.sound` |
| checker | **276** identical (244 → +32; **12** promoted, +1), 0 mismatched, 0 missing, 8 own-proof exemptions (284 checked) |
| wire | consumer **Zone L**, 0 errors; chosen wire `roots_phiProd_conj_nodup` at `p = 2`, `K = ℂ`, `ζ = -1` |

**One home per declaration held.** The six promotions are public in
`Defs/TS.lean` (`iota_jqN`, `qExpand_qTwist_TS`), `Defs/Jq.lean` (`jqN_congr`),
`Defs/PhiAtSlot.lean` (`iota_jq`, `conj_zero_eq`, `conj_succ_eq`), and `Spine.lean`
and `PhiGenSplits.lean` import them (adding `Defs/PhiAtSlot` to the latter) with no
private copy left. The remaining 26 fresh declarations have one home each.

**The prelude was already public in the pin — the work order's premise was
wrong.** §2.1 of the work order says every T14 declaration is `private` in the
pin and that the checker must therefore reach them through the `S_`-carrier
dotted route. In fact `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` —
already a checker `SOURCES` entry from the FFG spine — carries almost the whole
block **publicly**: the `TS` lemmas, `iota_jqN`/`iota_jq`/`conj_zero_eq`/
`conj_succ_eq`, `qTwist_iota_of_pow_eq_one`, `qTwistEquiv`, `coeff_qTwistEquiv`,
`qTwist_TS_one_cycle`, `phiProd_conj_eq`, `roots_phiProd_conj(_nodup)`, the
cyclotomic roots, `qExpand_qTwist_TS`, `roots_prime_at_slot*` and
`isRoot_prime_at_slot_iff`. So 30 of the 32 verified immediately by a direct
first-source last-name match; only `prod_form_ne_zero` (private in both carriers)
took the dotted fallback. The two new `S_` sources were still needed for the five
declarations absent from the spine file (`aeval_intermediateField_eq_zero`,
`phiAtSeed_eval_of_injective`, `phiAtSeed_eval_symm`,
`phiAtSeed_jqN_eval_down`, `qExpand_qTwist_notMem_range_qExpand`; all public in
`…_pow_not_mem_adjoin_full`), and they are appended **after** the
`Theorems/`/`Defs` sources so no existing match flips.

**The layering constraint bit earlier than §4 predicted.** The work order's §4
split puts `iota_jqN` in `Defs/Jq.lean` and the seven twist items in
`Defs/Twist.lean`. But `Defs/TS.lean` already imports `Defs/Twist.lean`, and
`iota_jqN`/`qTwist_TS_one_cycle`/`qExpand_qTwist_TS`/
`qExpand_qTwist_notMem_range_qExpand` all mention `TS`; putting them in
`Twist`/`Jq` would create an import cycle. They live beside `TS` in
`Defs/TS.lean` instead, and the four `TS`-free twist items
(`qTwist_iota_of_pow_eq_one`, `qTwistEquiv`, `qTwistEquiv_apply`,
`coe_qTwistEquiv`) are in `Defs/Twist.lean` as planned. The rest of the split
held: `Defs/PhiAtSlot.lean` upstream of the cone, `PhiSlotRoots.lean` the one downstream
module, so nothing in `Defs/` imports a cone module.

**Routes: two positive, one negative, one unchanged.**

- **`RingEquiv.ofBijective` closed** (the audit's positive ingredient). The
  bijectivity proof is the pin's left/right-inverse pair, and
  `coe_qTwistEquiv`'s coercion still closes by `RingHom.ext fun _ => rfl`
  because `RingEquiv.coe_ofBijective` is `rfl`; `qTwistEquiv_apply` is `rfl`
  via `ofBijective_apply`. The pin's 11-line `where` was the fallback and was
  not needed.
- **`IntermediateField.aeval_coe` did *not* collapse
  `aeval_intermediateField_eq_zero`.** The lemma's first argument `S` is
  explicit in this mathlib version and its right side is the coercion
  `↑(aeval x P)`, so the pin's 8-line subtype-injection argument is kept
  verbatim; the collapse attempts either fail to rewrite or need an extra
  `simpa` that the subtype coercion blocks.
- **`phiAtSeed_eval_symm` closed verbatim.** The `hhom` coercion
  `Polynomial.eval₂RingHom (Int.castRingHom _) z = (Polynomial.aeval z).toRingHom`
  through `ringHom_ext'` + `simp [Polynomial.coe_eval₂RingHom]` worked on the
  first build, so the named monomorphic bridge the work order held in reserve was
  **not** needed — the one coercion-family risk that did not bite.
- **`qTwistEquiv_apply` needed a one-line checker fix.** The pin writes it
  `@[scoped simp] theorem qTwistEquiv_apply ...` on one line, and the checker's
  `DECL_RE` anchors at a line start, so neither the pin nor the port copy was
  read. The port keeps the pin's spelling (the work order forbids promoting the
  attribute), and `DECL_RE` gained an optional leading-attribute group
  (`(?P<attrs>(?:@\[[^\]\n]*\]\s*)*)`) so the declaration is visible on both
  sides. Re-running confirmed the change flips nothing: the count went 275 → 276,
  still 0 mismatched and 0 missing, and no other port declaration was hidden by
  an inline attribute.

**Two friction notes.** The `RingEquiv.ofBijective` route needed a separate
section for `qTwist_iota_of_pow_eq_one` (the only member that uses
`[Algebra ℚ K]`), or the unused-section-variable linter fires on
`coe_qTwistEquiv`; and the pin's `convert h using 2 <;> try rfl` trips
`linter.unnecessarySeqFocus`, so the port writes `convert h using 2; try rfl`
(friction entry 2's family, the statement unchanged).

## 2h. T15: descent by one prime, and the one-prime reduction — what it cost

T15 is the parent effort's first topic whose output is proof content rather than
vocabulary. It proves the two `Inputs` fields that are math/010 §4–§5, so the
conditional capstone's debt drops **7 → 5**.

| | |
|---|---|
| goal rounds | **1** |
| declarations | 2 (both public, both `Inputs` fields) |
| new module | `FunctionFieldGeneration/Descent.lean`, **252 lines** |
| **port lines** | **252** against the 173-line pin tail, ratio **≈1.46** (within the scouted ~200–280; the row's `~350` priced the whole 735-line file before T14) |
| build | full `lake build` green, 0 warnings, no `sorry`; **3866 jobs** |
| axioms | `#print axioms` clean on both: only `propext, Classical.choice, Quot.sound` |
| checker | **278** identical (276 → +2), 0 mismatched, 0 missing, 8 own-proof exemptions (286 checked) |
| wire | consumer **Zone M** (0 errors): a partially discharged `Inputs` with the two T15 fields filled |

**The dedup premise held.** `S_ModularCurve_jqN_div_mem_modularFunctionField.lean`
and `S_ModularCurve_modularFunctionField_eq_full_of.lean` are byte-identical
except for the `solution` line — one development shipped twice — and their lines
28–542 are T14's prelude. The port re-copies **none** of it: `Descent.lean`
imports `Defs/PhiAtSlot`, `PhiSlotRoots`, `Defs/TS`, `Defs/Fields` and
`PhiGenSplits`. Every mathematical ingredient is a ported theorem (T14's
`phiAtSeed*`/`isRoot_prime_at_slot_iff`/`roots_prime_at_slot_roots_nodup`/`iota_jqN`,
T13's `splits_prime_at_slot`, T12's `exists_phiIrreducible_evalSymm`, T4's
`Polynomial.mem_range_of_unique_common_root`) or a mathlib call, so T15 adds no
promotion and no new engine.

**The route risks all resolved on the first build — none of the four bit.**

- **The `Algebra F (LaurentSeries K)` instance and the `ι₀`/`hcomp` bridge closed
  as transcribed.** The pin's `letI : Algebra F (LaurentSeries K) := (…).toAlgebra`
  and `hcomp : (algebraMap F _).comp ι₀ = (…).comp (algebraMap _ _) := RingHom.ext
  fun x => rfl` both elaborated without `respectTransparency` and without a named
  bridge — the transparency family that bit T8 (`mapGL`) and T5 (`FunLike`) did
  **not** bite here.
- **`isRoot_prime_at_slot_iff`'s call shape fired** at `rw [Polynomial.aeval_def,
  ← Polynomial.eval_map, hmapA, hseed]; exact isRoot_prime_at_slot_iff (M*p) ζ hζ p
  hpN data (M*p*M) 1 y`; the T14 statement needed no repair.
- **`Polynomial.mem_range_of_unique_common_root`'s argument order matched** the
  pin's `A B hA0 hAs hAnd x₀ hxA hxB huniq` with no repair.
- **The `minpoly`/`map` strip transcribed** in the pin's re-ordered form
  (`aeval_def`, `← eval_map`, `map_map`, `hcomp`, `← map_map`, `eval_map`,
  `eval₂_hom`, `minpoly.aeval`).

**Two small friction items.** The `letI`/`haveI` pair tripped
`linter.style.haveILetI` twice — both instances are genuinely consumed by
typeclass search (`algebraMap F (LaurentSeries K)` and the `modularFunctionField`
family), so the module uses the same local disable as `PhiGenSplits.lean`. And the
`htw`/`hsp` binders are kept exactly as the wrapper writes them (the wrapper's
`hp : Fact (Nat.Prime p)` for the descent, a bare `p.Prime` for the reduction), so
the checker matches by direct name.

## 2i. T16: the degree of one prime-power step — what it cost

T16 is the last purely field-theoretic topic. It proves the degree half of the
strong induction — the two prime-power degree statements and the tower dispatcher
— and discharges the third `Inputs` field, so the capstone's debt is **5 → 4**.

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted) |
| declarations | 3 public nodes + 7 promoted bridges; 3 private helpers (`phiAtSeed_iota_jq_eq_phiProd`, `rUnit`, `range_map_eq_rUnit`) |
| new module | `FunctionFieldGeneration/DegreeStep.lean`, **455 lines** |
| extensions | `Defs/Laurent.lean` +70, `Defs/Fields.lean` +34, `Defs/Twist.lean` +25, `Defs/TS.lean` +21 |
| dedup | `PhiGenDescent.lean` −11, `PhiGenSplits.lean` −13, `PhiGenIntegrality.lean` −4 (the private transport twins) |
| **port lines** | **605** (455 + 150) against ≈435 pin lines, ratio **≈1.39** — inside the scouted `~500–650` |
| build | full `lake build` green, 0 warnings, no `sorry`; **3869 jobs** |
| axioms | `#print axioms` clean on all three nodes and all seven promotions |
| checker | **288** identical (278 → +10; **14** promoted, +2), 0 mismatched, 0 missing (296 checked) |
| wire | consumer **Zone N** (0 errors): a partially discharged `Inputs` with the three proved fields filled |

**The pow-succ node transcribed on the first build.** The whole of the hard node
— the factor peel `Q /ₘ (X - C jkF)`, the `p - 1` multiset re-indexing
`range_map_eq_rUnit`, and the cyclotomic coefficient automorphism block — went in
verbatim and compiled with no stall. `coeffMapEquiv` took
`RingEquiv.ofBijective` (the audit's positive ingredient); the pin's explicit
`where` was the fallback and was not needed. The only warnings were the two
`if_pos`/`if_neg` deprecations (friction entry 2's family), fixed with
`ite_eq_left`/`ite_eq_right`.

**The promotions, and a third layering correction.** The work order's §4 put all
three `coeffMap_*` bridges in `Defs/Laurent.lean`, but the import layering forbids
it a third time (after T14's `iota_jqN` and T15's `Algebra` instance):
`coeffMap_qTwist` mentions `qTwist` (downstream of `Laurent`), so it lives in
`Defs/Twist.lean`; `coeffMap_TS` mentions `TS`, so it lives in `Defs/TS.lean`; only
`coeffMap_coeffEmb_algHom` (with `coeffMapEquiv` and `iota_injective`) is
genuinely in `Defs/Laurent.lean`. `w1_relfinrank_insert` went to `Defs/Fields.lean`
beside `modularFunctionFieldFull`. No cycle was introduced, and the three private
twins are gone. The redundant `coeffEmb_injective'` and `jqN_congr'` were dropped
in favour of the public `coeffEmb_injective` and `jqN_congr`.

**The checker needed the `S_` carriers, not just the wrappers.** §6.2 named only
the three `Them_` wrappers, but `coeffMapEquiv`, `coeffMapEquiv_apply` and
`iota_injective` are not exported by a wrapper (they are public in the pow-succ
`S_` file) and `w1_relfinrank_insert` is `private` in the relfinrank `S_` file, so
the three `S_` carriers were appended to `SOURCES` (last, after every existing
source, so no existing match flipped). The checker moved 278 → 288 with 0
mismatched and 0 missing.

**The `p = 3` non-vacuity test for `irreducible_of_transitive_ringAut` is still
out of reach.** A concrete instance needs a cubic over `ℚ` with Galois group `S₃`
whose roots mathlib can name — `X³ - 2` is canonical, with complex conjugation
fixing the real root and 2-cycling the other two — but mathlib has no explicit
cube roots (log §8.6's finding stands). The engine is not vacuous in the
mathematics — T16's pow-succ node applies it over the abstract `F` with the
non-identity `σ = coeffMapEquiv τ` — so the open question is recorded, not
resolved, and Zone N documents the obstruction.

## 2j. T17: the non-membership tower and the two-prime separation — what it cost

T17 completes the non-membership half of the strong induction. It proves the
prime-power tower (the fourth `Inputs` field, so the capstone's debt is
**4 → 3**) and the public Finset base lemma, in one new module, tower first.

| | |
|---|---|
| goal rounds | **1** session, two build rounds (tower, then base); both halves green on their first `lake env lean` |
| declarations | 2 public nodes; 14 private declarations (`nat_ne_of_mul`, `mem_range_qExpand_of_mul`, `range_qExpand_congr`, `chainField` + its five lemmas, `chain_extend`, `chain_endgame`, the tower key, `step_contradiction`, the base key) |
| new module | `FunctionFieldGeneration/Nonmembership.lean`, **843 lines** (tower ≈528, base ≈223) |
| dedup | none re-copied: the pin's ~370-line prelude is T14's; the six tower and two base helpers are imported |
| **port lines** | **843** against the scouted ≈741 new pin lines, ratio **≈1.14** — inside the estimated 750–950 |
| build | module green, 0 warnings, no `sorry` |
| axioms | `#print axioms` clean on both public nodes |
| checker | **290** identical (288 → +2; still **14** promoted), 0 mismatched, 0 missing (298 checked) |
| wire | consumer **Zone O** (0 errors): a partially discharged `Inputs` with the four proved fields filled |

**Both route risks closed on the first build.** `chain_extend`'s explicitly built
`RingHom` — `{ toFun := fun z => ψ ⟨z.1, hle z.2⟩, … }` with the
`adjoin_induction` coercion `hle` — typed as the pin wrote it, so the work order's
`FunLike`/`DFunLike.coe` stall family (T5's log §2.2) did not bite and no
monomorphic bridge was needed. `chain_endgame` — the longest and least structured
proof, with the `TS_injective` comparisons and the final `q^{-p^a}` coefficient
clash — closed under the global `maxHeartbeats 4000000`; the pin's two local
`set_option maxHeartbeats 3200000 in` were omitted, as directed. The
`Algebra F (LaurentSeries K) := σ.toAlgebra` device copied from T15 unchanged.

**One drift, mechanical.** `Set.mem_setOf_eq` is deprecated in `v4.34.0` (friction
entry 2's family); the base's `hsets` `simp only` now names `Set.mem_ofPred_eq`.
That was the only edit the transcription needed beyond dropping the pin's
namespace scaffolding and `set_option`s.

**Privacy, not scope.** The pin's `step_contradiction` and
`jqN_prime_not_mem_adjoin_key` are public in the pin's local `W1` namespace but
have no `Theorems/` wrapper, and the pin's own `S_` carrier is not one of the
checker's `SOURCES`; the port keeps both `private` (as it does the tower's
`jqN_pow_not_mem_adjoin_full_key`), so there is nothing for the checker to look up
and no self-consumed public interface is added. The tower's `chainField` remains
`private` for the same reason. The base's `step_contradiction` imports T4's
`mem_range_of_eval_eq_const` from `FieldTheory/CommonRoot.lean` rather than
restating it — the engine T19's private M-arbitrary lemma also uses; **T17 landed
first**, and T19 should import the same theorem, with its own `ψ(M)`-slot root
list rather than T17's `p + 1` roots of `Φ_p(jq, ·)`.

## 2k. T18: one new generator per prime power — what it cost

T18's mandatory scope is the single `Inputs` field `full_eq_adjoin_full_div_prime`
(the debt is **3 → 2**) plus the two-prime descent `jqN_mem_of_div_primes` ported
once. The original topic's squarefree generation/degree block (nodes 2–6) was
deferred to an optional API tail by the 2026-09-22 route audit, whose
`gen_prime` substitution landed here as T19's prerequisite.

| | |
|---|---|
| goal rounds | **1** (the work order's one-round budget) |
| declarations | 1 public node + 2 private helpers in `Generation.lean`; 3 invariants + `tight_one`/`gen_one`/`gen_prime` public in `Defs/Fields.lean` |
| new module | `FunctionFieldGeneration/Generation.lean`, **309 lines** |
| extensions | `Defs/Fields.lean` +71 (the `Tight`/`Gen`/`Hall` move + `tight_one`/`gen_one`/`gen_prime`); `Spine.lean` −35 (abbrevs and `tight_one`/`gen_one` removed) |
| **port lines** | **309 module + 36 net** against ≈221 mandatory pin lines + ≈50 promotion, ratio **≈1.27** (module alone 309/221 ≈ 1.40) |
| build | full `lake build` green, 0 warnings, no `sorry` |
| axioms | `#print axioms` clean on `full_eq_adjoin_full_div_prime`, `tight_one`, `gen_one`, `gen_prime` |
| checker | **293** identical (290 → +3; **16** promoted), 0 mismatched, 0 missing (302 checked); `gen_prime` exempted as our own |
| wire | consumer **Zone P** (0 errors): a partially discharged `Inputs` with the five proved fields filled, plus a `gen_prime` example |

**The descent transcribed as-is.** `jqN_mem_of_div_primes` (133 pin lines) and the
strong induction `w1_jqN_mem_adjoin_top_insert` (68) went in verbatim against
T14's slot API; the only edit was the port's usual `jqN_congr'` → `jqN_congr`. No
stall. The node's `full_degeneracy_le` half is the `Defs/Fields` degeneracy lemma.

**The dedup, counted.** `grep -c "theorem jqN_mem_of_div_primes"` is 1 in each of
six pin `S_` files — three in T18's scope (`full_eq_adjoin_full_div_prime`,
`full_eq_adjoin_primes`, `modularFunctionField_eq_full_of`) and three in the
squarefree cluster — so the port's **one** copy drops five. The pin's `jqN_congr'`
(2 grep hits in `full_eq_adjoin_full_div_prime`) is dropped for `jqN_congr`;
`psi_prime_pow_aux`, the local `dedekindPsi_prime_pow`,
`phiIrreducible_of_squarefree` and `exists_pow_eq_of_coprime` are all in the
deferred tail and were not ported.

**The scope decision.** Nodes 2–6 have exactly one external consumer — the pin's
`functionFieldGeneration_of_squarefree p` call at
`S_ModularCurve_jqN_prime_not_mem_full.lean:1638` — and `Gen p` is definitional
(`modularFunctionField p = modularFunctionFieldFull p = ℚ(j, j(q^p))`), so
`gen_prime` replaces it. `tight_one`/`gen_one` cover the `d = 1` branch of the
pin's `hallp`. `gen_prime` is our own declaration (hence the `OWN_PROOFS`
exemption); `tight_one`/`gen_one` are FLT's and verify through the pin's `private`
copies in `S_ModularCurve_functionFieldGeneration.lean` via the checker's dotted
fallback. The `Tight`/`Gen`/`Hall` abbreviations moved with them and stay exempted
as before.

**The one API cost.** `relfinrank_adjoin_primes` and `relfinrank_full_mul_prime`
are not ported; neither is in §2.1's measured outbound tier, and either can be
added later for ≈150 pin lines without the `IsLevel`/`eq_of_isRoot_of_isLevel`
work. `TOPIC-generation.md` §2 keeps the full inventory.

## 2l. T19: the slot product and the prime non-membership — what it cost

T19 is the last topic before the capstone. It proves the slot list
(`minpoly_jqN_map_eq_prod_slots`, the pin's `rval_aux`) and the prime
non-membership (`jqN_prime_not_mem_full`), the last two `Inputs` fields, so the
structure is **total (debt 2 → 0)** and T20 only has to construct it.

| | |
|---|---|
| goal rounds | **1** session, several build rounds during the splice (slot count, `sv` helpers, `rval_aux`, M-arbitrary); each phase green before the next |
| declarations | 2 public nodes; the private M-arbitrary `jqN_prime_not_mem_adjoin`; ≈25 private helpers (slot count, `sv`/`sv_inj`/`map_qExpand_minpoly_eq`, the `rval_aux` internals) |
| new module | `FunctionFieldGeneration/SlotProduct.lean`, **1,502 lines** |
| dedup | `jqN_mem_of_div_primes`-style reuse: T14's prelude, `tight_one`/`gen_one`, `mem_range_of_eval_eq_const` and the `ψ` lemmas are all imported; the pin's `slotAt_mul`/`gcd_mul_*`/`gcd_eq_of_modEq`/`slotCond_mod_iff` and four `dedekindPsi_*` re-proofs are dropped |
| **port lines** | **1,502** against the scouted ≈1,387 pre-win pin lines, ratio **≈1.08** (wins offset by the port's fuller header/docstrings) |
| build | full `lake build` green, 0 warnings, no `sorry`; the module alone 44 s |
| axioms | `#print axioms` clean on both public nodes |
| checker | **297** identical (295 → +2; 16 promoted), 0 mismatched, 0 missing (306 checked) |
| wire | consumer **Zone Q** (0 errors): the fully discharged `Inputs` and the derived unconditional `FunctionFieldGeneration N` |

**The closed-form slot count held.** `slotAt n d = slotH (n/d, d)` with
`slotH (a,d) = (d / gcd a d) * φ (gcd a d)`, from mathlib
`Nat.periodic_coprime`/`Nat.count_eq_card_filter_range`; `slots_mul` via
`Nat.Coprime.divisors_mul`. Net drop: `slotAt_mul` (108), `gcd_mul_left/right_of_dvd`
(17), `gcd_eq_of_modEq`/`slotCond_mod_iff` (8), the four `dedekindPsi_*` re-proofs
(64); the prime-power spine (`slotAt_prime_pow_mid`, `slots_prime_pow`) is kept
verbatim (already mathlib-driven). One detail the audit's sketch omitted: after
`Nat.Coprime.divisors_mul` + `Finset.sum_map`, the `attach` body must be `change`d
to the projected pair and `Finset.sum_attach` given its `f` explicitly, otherwise
the rewrite cannot see through the embedding. The audit's single public export,
`card_slotFilter_eq_dedekindPsi`, is kept (it is `OWN_PROOFS` — our own addition;
FLT's nearest is the different triple-shaped `card_primCosetReps_eq_dedekindPsi`),
so a consumer of the slot list has one statement to cite; the in-module `hTcard`
sites still use the pin's private `slotAt`/`slots` route, so that ≈30-line
consumer collapse was not taken.

**`rval_aux` transcribed as-is, and did not stall.** The 493-line `hslot_root` and
the `¬ p ∣ a * d''` branch went in verbatim. The pin's local
`set_option maxHeartbeats 6400000 in` was **not** transcribed: the module builds
under the project's global `4000000` via `lake build`. A build-discipline note:
`lake env lean <file>` uses the default `200000`, not the lakefile's global, so the
`timeout 60 lake env lean` probe is red for this module (two `rval_aux` steps need
more) even though `lake build` is green — the probe under-reports only because it
bypasses `leanOptions`.

**Two route details.**
- **`Module.Free` supplied explicitly.** The `synthInstance` search for
  `Module.finrank_mul_finrank` over the adjoin tower `ℚ⟮jq⟯⟮jqN (a*d'')⟯` timed out
  at 20 000 heartbeats; `haveI : Module.Free … := Module.Free.of_divisionRing _ _`
  closed it immediately. This is Friction entry 19's family and the recommended
  remedy (supply the instance, do not raise a cap).
- **The M-arbitrary `hallp` uses T18's substitution.** The pin's
  `functionFieldGeneration_of_squarefree p` line became `gen_prime p`, and the
  `d = 1` branch is `⟨tight_one, gen_one⟩`; no squarefree-block declaration is
  referenced. `mem_range_of_eval_eq_const` is imported from
  `FieldTheory/CommonRoot.lean`, not restated.

**The statements.** Both public nodes are the `Theorems/` wrappers' verbatim, with
the explicit `hall` conjunction (not the port's `Hall M` abbreviation) — this is
what makes the checker match, since the wrappers write the conjunction out.

**What T20 now needs.** Zone Q already exhibits the total `Inputs` and the derived
`FunctionFieldGeneration N`; T20 has only to replace the consumer's Zone A `sorry`
and record the unconditional theorem. The optional tail
(`exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq`, ≈250)
is unchanged.

## 2m. T20: the unconditional capstone — what it cost, and the effort closes

T20 assembles what T15–T19 proved. `FunctionFieldGeneration/Capstone.lean` defines
`inputs : Inputs` (the port's own assembly — FLT has no counterpart) from the
seven theorems, then `functionFieldGeneration` (verbatim from its wrapper) as
`functionFieldGeneration_of inputs N`, the corollary layer, and the interface
tail. **The headline is now unconditional**, and the consumer's Zone A `example`
is that theorem rather than a `sorry`.

| | |
|---|---|
| goal rounds | **1**; the mandatory half built first try, the fraction-ring tail second try (one instance-signature adaptation) |
| declarations | `inputs`, `functionFieldGeneration`, 3 corollaries, 3 tail nodes + 3 private evaluation helpers = **11 new**, plus `hall_all` promoted to public |
| new module | `FunctionFieldGeneration/Capstone.lean` |
| **port lines** | **≈300** against the work order's ≈220–280 estimate; the tail's fraction-ring node is ≈130 of it |
| build | full `lake build` green (3874 jobs), 0 warnings, no `sorry` |
| axioms | `#print axioms` clean on all eleven; `functionFieldGeneration` itself is `[propext, Classical.choice, Quot.sound]` |
| checker | **304** identical (301 → +4 wrappers; `inputs`/`hall_all` exempted), 0 mismatched, 0 missing, 12 own-proof exempted |
| consumer | **0 errors**; Zone A's capstone is the theorem; Zone R added; the remaining `sorry`s are Zones M–P's historical partial `Inputs` |

**The `Inputs` literal needed no wrapper.** The work order's one predicted friction
point — the two `Hall M`-typed fields against the standalone theorems' explicit
conjunctions — did not bite: `Hall` is an `abbrev`, so the bare field assignments
elaborated. The literal is seven lines.

**A discovery on the tail: the fraction-ring node closed on the second build.**
The pin's `exists_phiIrreducible_of_finrank_eq` looks formidable (109 lines, an
`IsFractionRing (Polynomial ℤ) ℚ⟮jq⟯` instance built by hand), but its body is a
faithful transcription; the only adaptation v4.34.0 forced was the integrality
instance, where `isIntegral_algebraMap_iff` now takes `FaithfulSMul` rather than an
injectivity proof, so `isIntegral_algHom_iff` with the coercion's injectivity
replaces the pin's argument. The final comparison
`minpoly ℚ⟮jq⟯ (jqN N) = (minpoly (Polynomial ℤ) (jqN N)).map evalAtJGen` then
gives irreducibility for free. This is the last of §2.1's five out-of-cone nodes.

**The effort's definition of done is met.** §7.8's checklist: build green, no
`sorry`, `functionFieldGeneration` axiom-clean, the consumer's capstone `sorry`
gone, the checker extended, and the out-of-cone ≥5-indegree tier at **100%**. The
conditional of math/010 §2 is discharged and the segment's outbound interface — the
analytic declarations included — is ported theorem, not reference.

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

Topic 2, on landing:

| check | result |
|---|---|
| `sorry` / `admit` / `axiom` / `native_decide` in `FLTForHuman/ModularCurve/` | none (checked by `grep`) |
| `#print axioms` on `functionFieldGeneration_of` | only `propext, Classical.choice, Quot.sound` — the point of a conditional artifact |
| `spec/check_flt_statements.py` | 137 identical, 0 mismatched, 0 missing, 7 own-proof exemptions |
| every `Inputs` field referenced | 10 of 10 (the field-use check below) |
| consumer | **0 errors**; `functionFieldGeneration_of` bound in Zone B; `sorry` count still 1 |

Topic 3, on landing:

| check | result |
|---|---|
| 9 interface statements identical to their pin wrappers (`spec/check_flt_statements.py`) | **146** identical, 0 mismatched, 0 missing |
| the checker is non-vacuous on the new sources | a mutated `dedekindPsi_prime` (`p + 2`) is caught |
| `sorry` / `admit` / `axiom` / `native_decide` in `FLTForHuman/ModularCurve/` | none |
| `#print axioms` on `functionFieldGeneration_of` | only `propext, Classical.choice, Quot.sound` |
| `Inputs` field set | **8**, every field still referenced; `ψ` helpers no longer take `h : Inputs` |
| consumer | **0 errors**, one `sorry` (unchanged) |

Topic 4, on landing:

| check | result |
|---|---|
| the 3 kernel + 1 peel statements identical to their pin wrappers (`spec/check_flt_statements.py`) | **150** identical, 0 mismatched, 0 missing, 7 own-proof exemptions |
| `sorry` / `admit` / `axiom` / `native_decide` in `FLTForHuman/` | none (the word `sorry` occurs only in prose) |
| `#print axioms` on the three lemmas, the peel and `functionFieldGeneration_of` | only `propext, Classical.choice, Quot.sound` |
| `Inputs` field set | **7**, every field still referenced; `relfinrank_full_of` no longer takes `h : Inputs` |
| wire test 1 (instantiation) | three checked `example`s over `ℚ ⊆ ℂ` in `CommonRoot.lean`'s last section |
| wire test 2 (cross-module) | `FunctionFieldGeneration/Spine.lean` calls `Fields.relfinrank_modularFunctionField` |
| consumer | **0 errors**, one `sorry` (unchanged) |

### 3.1 Coverage in original FLT lines

The tables above say what is *checked*; this says how much of FLT's own source the
port accounts for, measured as the spans of the pin declarations it transcribes.
One caveat on the method: `JqCoefficients.lean` contributes **zero**, because its
two theorems have no pin counterpart — the statement is base/004's and FLT's
analogue is a different, 237-line file.

| source layer | FLT lines covered | of what |
|---|---|---|
| the three `Def_ModularCurve_*` definition files | **745** | 801 lines; **126 of 126 declarations** |
| `S_ModularCurve_functionFieldGeneration.lean` (the `TS` block and the auxiliary/induction block) | **388** | of 753 |
| the eight small interface proofs (topic 3) | **131** | |
| the ψ section of `S_…_dedekindPsi_mul_of_coprime.lean` | ~35 | of 471; the rest is the off-path resultant development |
| `S_…_functionFieldGeneration_iff_full_eq.lean` | 22 | |
| **total** | **≈ 1,320** | |

Against the cone — 140 theorem-node files plus 4 definition modules: 24,283 lines,
~1,810 declarations — that is **~5.4% of the lines and ~9% of the declarations**;
against the repository (60,474 files, 13.5M lines) it is ~0.01%. The port is
**2,102 lines** for those ~1,320, a **1.6 : 1** expansion: docstrings, headers, the
`Inputs` structure and the interface exposition, i.e. the reorganization made
visible (the first port was ~1 : 1).

Two readings, and the second is the truthful one. The line figure **understates**
the coverage: it is 100% of the *statements* (146 verified identical to the pin at
that point), the target's definition, the collapse, and the proof's whole
architecture. It also **understates the remaining work**: the seven fields left are
only ~3,357 structural lines, but they are gated by the Φ_p subtree — 44 nodes,
11,034 lines, 45% of the cone — so the unconditional theorem sits behind ~59% of
the cone. After four topics and ~1,320 original lines, the distance is **seven
named statements and one input**.

The statement-identity result is the one to carry forward: with a pinned source
dictating the statements, faithfulness is *mechanically checkable*, and it should be
checked every time rather than assumed — which is what
`spec/check_flt_statements.py` now does: 146 statements verified after topic 3, 150
after topic 4.

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
mechanically verified — 137 of 137 statements identical to the pin (146 after
topic 3), no `sorry`,
no `import Mathlib`, `#print axioms` clean. Two `jq.coeff` claims in consumer
Zone C (`744`, `196884`) were expected to stay red because they live inside the
deferred Φ_p subtree. The final check found that expectation to be wrong, the
topic below was taken, and it finished in one round (§2c). Zone C is now closed:

- **[TOPIC-jq-coefficients.md](../topics/functionFieldGeneration/TOPIC-jq-coefficients.md)** — **done**.
  `coeff_jq_zero` and `coeff_jq_one` are proved in
  `FLTForHuman/ModularCurve/JqCoefficients.lean`. `etaProd` *is* mathlib's
  topological product, so `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` gives
  `∏' n, (1 - X ^ (n+1)) = pentagonalSeries`, with explicit coefficient lemmas, and
  the route is a finite low-order computation — `1 + 744q + 196884q² + ⋯` — with no
  part of the 44-node subtree. The hybrid held; the measured ratio against FLT's
  closest analogue is ≈0.87 : 1.

- **[TOPIC-conditional-capstone.md](../topics/functionFieldGeneration/TOPIC-conditional-capstone.md)** — **done**.
  `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` proves the strong induction `hall_all`
  and the conditional capstone `functionFieldGeneration_of (h : Inputs)`, with
  FLT's significant remaining statements bundled as the fields of `Inputs`
  (§2d). The unconditional theorem is now exactly that field set away, and the
  auxiliaries proved to be glue (§8.4).

- **[TOPIC-interface-tier.md](../topics/functionFieldGeneration/TOPIC-interface-tier.md)** — **done**.
  Nine public interface lemmas — the declarations a fifth of FLT reaches this
  segment through — now live in `Defs/Laurent.lean` and `Defs/Jq.lean` beside the
  objects they concern, and two of them discharge `Inputs` fields (§2e). The
  structure is down to **8**. The cone's ≥5-indegree tier sums to 946; the nine
  carry 520 of it, 55%.

- **[TOPIC-generic-kernel.md](../topics/functionFieldGeneration/TOPIC-generic-kernel.md)** — **done**. The
  three `Polynomial.*` lemmas the surveys identify as the segment's mathematical
  engine (math/010 §4 *is* the unique-common-root principle; §6's
  non-membership and degree steps are the other two) are now proved in a new
  `FLTForHuman/FieldTheory/` area — the port's first generic, non-curve-specific
  material — with three concrete instantiations over `ℚ ⊆ ℂ` as their wire test;
  the topic also peeled `relfinrank_modularFunctionField`, the third `cites = 0`
  `Inputs` field, into `Defs/Fields.lean`, taking the debt from 8 to 7. §2f has
  the cost.

What remains is the deferred theorem of §7, no longer an undifferentiated
subtree but a named list of 7 fields to discharge one at a time (§8.4), and
increasingly dominated by the 1,000–2,000-line nodes.

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

**The theorem's remainder** was 24 nodes below the capstone, behind the Φ_p input
(PORTING-FFG §7). Its per-node line sum is 12,420, and that is an *upper bound*,
for two reasons now measured: §8.1's three `Polynomial` nodes share one proof, and
§8.3 shows the same statements can live in a far smaller standalone file than the
subtree they appear under. Pricing it properly means scouting each node's actual
FLT proof. After topic 2 it is no longer an undifferentiated subtree: it is the
10 named fields below.

**The conditional capstone is done, and the remainder is now a structure.**
`Spine.lean` proves `hall_all` and `functionFieldGeneration_of` (§2d), so the
distance to the unconditional theorem is exactly the fields of `Inputs`, each
stated as in the pin. The candidate set started as the 24-node manifest; pruning
left 10, every one of which is referenced by the spine (10 of 10); topic 3
discharged two of them and topic 4 a third, leaving **7**:

| `Inputs` field | why it survives |
|---|---|
| ~~`dedekindPsi_mul_of_coprime`~~ | **discharged** in topic 3 — now a public lemma in `Defs/Jq.lean` |
| ~~`dedekindPsi_prime_pow`~~ | **discharged** in topic 3 — now a public lemma in `Defs/Jq.lean` |
| ~~`relfinrank_modularFunctionField`~~ | **discharged** in topic 4 — now a public lemma in `Defs/Fields.lean` |
| `full_eq_adjoin_full_div_prime` | the `Gen` tower step (`full_le_adjoin_chain`, `hall_all`) |
| `jqN_prime_not_mem_full` | the prime case of `jqN_pow_not_mem_full` |
| `jqN_pow_not_mem_adjoin_full` | the prime-power induction of `jqN_pow_not_mem_full` |
| `minpoly_jqN_map_eq_prod_slots` | the slot description `root_shape` reads the roots off |
| `modularFunctionField_eq_full_of` | the `Gen` step of `hall_all` |
| `jqN_div_mem_modularFunctionField` | the slot-analysis input the `Gen` step calls |
| `relfinrank_full_eq_mul` | the `Tight` tower step of `hall_all` |

The 14 pruned are `functionFieldGeneration_iff_full_eq` (already proved in
`Collapse.lean`) plus the 13 nodes that occur only *inside the proofs* of the
originally assumed fields: `finrank_adjoin_jqN_eq_of_squarefree`,
`finrank_adjoin_jqN_pow_succ_of_not_mem`, `jqN_prime_not_mem_adjoin`,
`full_eq_adjoin_primes`, `relfinrank_full_of_squarefree`,
`finrank_adjoin_jqN_prime_of_not_mem`, the three `Polynomial.*`,
`exists_monic_evalAtJ_jqN_eq_zero`, `dedekindPsi_of_squarefree` and
`functionFieldGeneration_of_squarefree`. Assuming a node discharges its
dependencies, they drop out; `exists_phiIrreducible_of_finrank_eq` is used only by
the trailing `exists_phiIrreducible`, which the spine does not include. Topic 4
then built the three `Polynomial.*` anyway, as a *generic* module rather than a
discharge — they are not `Inputs` fields, and their consumer here is the remainder
(plus `relfinrank_modularFunctionField`'s Tier-1 bridges, which are mathlib's).
Discharging the fields one at a time is now the natural next topic, and §7.3's
per-node line counts are the cost estimate for each.

**The live frontier has its own table in the active plan:**
[PORTING-FFG.md](../PORTING-FFG.md) §7.7 — the seven remaining fields with their pin
sizes and what each says, the de-duplicated structural total (~3,357 lines, ~3,200
of it new), the single gating input `PhiGen.splits_prime_at_slot` (44 nodes, 11,034
lines, 42 dependents), the three ways forward, and the route-check and top-heavy
cautions. This section is the history; §7.7 is the current reference.

**Stop-and-harvest is a real option.** The library now supplies the vocabulary of
math/010 and base/004, with the statement landscape mechanically checked, two
concrete claims proved, and the proof's architecture a checked theorem whose only
hypotheses are the named debt. What it does not supply is the *unconditional*
theorem; that is the one thing left, and it is the expensive one.

### 8.5 The two studies, and what they change

Two independent surveys landed in `studies/` on 2026-09-21:
[flt-ffg-field-theory.md](../../studies/flt-ffg-field-theory.md) (this segment) and
[flt-function-field-theory-and-mathlib.md](../../studies/flt-function-field-theory-and-mathlib.md)
(the repository's whole curve layer). Their measurements were re-derived here
before being relied on, and they change four of this record's conclusions.

**The cone is the floor of FLT's arithmetic tower.** Verified from the doc-site
graph: 70 nodes, of which **26 cite no FLT theorem at all** and **0** are
`AlgebraicCurve`; **500** direct citers and **5,804 transitive dependents** —
19.7% of the 29,511 theorem nodes. Nothing in the Frey, modularity or
Galois-representation layers feeds it. A wrong *statement* here is therefore
maximally expensive and a wrong *proof* maximally cheap to replace, which makes
the statement checker and `#print axioms` a measurement-backed investment rather
than a preference.

**Layer 0's product is the interface, and it is load-bearing.** The outbound
traffic flows through small declarations, not the headline theorem:
`coeffMap_qExpand` **indeg 194** (the most-shared declaration in the cone),
`dedekindPsi_prime` 72, `coeffEmb_qExpand` 66, `qExpansion_discriminant_…` 66,
`transcendental_jq` 56, `functionFieldGeneration` 52 — and the capstone is
consumed as an *input* by `IgusaScheme.exists_mul_mem_adjoin_jFull_jqN` and the
CharP/fibre-model `hdeg` hypothesis. That settles the "will Layer 0 be used?"
question §8 kept reopening: it is used by a fifth of the repository, which the
original pitch ("the transport layer, the pole of `j`, a statable target") badly
undersold. Topic 3 then built this interface out: nine of the declarations above
are now public lemmas in `Defs/Laurent.lean` and `Defs/Jq.lean` (§2e).

**The next target is the generic kernel, and this record missed it.** §8.4 called
the three `Polynomial.*` nodes "cheap but unchosen — porting one would be 'because
the graph has nodes'". That was wrong. They are the *engine* of the segment:
math/010 §4 is `mem_range_of_unique_common_root`, §6's non-membership is
`mem_range_of_eval_eq_const`, §6's `p+1`/`p` degrees are
`irreducible_of_transitive_ringAut`; they are **absent from mathlib** (a grep for
each name over `Mathlib/` returns nothing); they are ~180 distinct lines; and they
are in neither mathlib nor the port. They sit *under* the 24-node remainder and
can be built without discharging it — a third path inside this segment that
§8.4's "stop or grind" framing did not have.

**The remainder is structurally smaller than the 12,420 headline.** Spot-checking
the studies' de-duplication ledger: the stripped `diff` of the two 2,002-line
files is **0 lines** (not the 62 the study reports — the residual is namespace
plumbing), of the two 735-line files **0**, and `grep -l '^def TS '` finds **50**
files carrying the same prelude.

| correction | lines |
|---|---|
| 12,420 headline | |
| −2,002 second copy of the `jqN_prime_not_mem_full` file | |
| −735 second copy of the `modularFunctionField_eq_full_of` file | |
| −364 two extra `S_Polynomial_*` copies | |
| −653 `jqN_prime_not_mem_adjoin`, re-proved inside the 2,002-line file | |
| −399 resultant development off the capstone path, inside the `dedekindPsi` file | |
| −38 duplicate `dedekindPsi_prime_pow` file | |
| de-duplicated remainder | ≈ **8,229** |
| −2,880 eight of the nine copies of the 360-line prelude | |
| prelude written once | ≈ **5,349** |

That is a structural line count, not a proof budget — cost here tracks shape risk
(§6). But it means the deferred remainder, deduplicated, is about the size of the
first port rather than 3.7× it, and that the real bottleneck is the Φ_p slot
subtree (44 nodes, 11,034 lines) — which FLT *proves* and the port chose to cut.

One correction to the studies: `coeff_jqModC_neg_one` (indeg 120, 3,801
dependents) is **not** in this cone, so "the pole is load-bearing everywhere" is
about the characteristic-`p` pole in the ModPForms sector, a different fact from
the char-0 `coeff_jq_neg_one` the port carries.

### 8.6 Open question: a nontrivial instance for `irreducible_of_transitive_ringAut`

The third wire test in `FieldTheory/CommonRoot.lean` instantiates the lemma with
`σ = RingEquiv.refl` and `n = 1`, so `hcycle` degenerates to `r 0 = r 0`. The test
proves the lemma *fires*; it does not exercise the automorphism mechanism, which is
the whole content of that lemma. The module note says so honestly. Two things
sharpen the question.

- **mathlib really has no cube roots.** `Real.cbrt`, `Complex.cbrt` and `cbrt` all
  return **0 hits** over `Mathlib/`. So the natural instance — a cubic over
  `ℚ ⊆ ℂ` with one real root, complex conjugation fixing it and 2-cycling the other
  two — is unavailable without constructing the roots.
- **FLT's own instantiation is nontrivial, and that is the non-vacuity evidence.**
  The lemma is used for real in at least four pin files, with σ = `qTwistEquiv ζ`
  (the cyclotomic twist) at
  `S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean:320` and σ =
  `coeffMapEquiv …` at `S_…_pow_succ_of_not_mem.lean:728`. So the lemma is not
  vacuous in the mathematics; only our *wire test* is weak.

Two routes if it is ever worth closing, neither free:

1. **A finite-field instance** — `𝔽₂ ⊆ 𝔽₈`, `P = X³ + X + 1`, σ the Frobenius
   `x ↦ x²`, which cycles the three roots. mathlib has the pieces (`GaloisField`,
   37 `Frobenius` hits); exhibiting the automorphism and the root cycle is real
   work, not a one-liner.
2. **Port `qTwistEquiv`** — it is in the shared prelude (pin line 130, ~16 lines)
   and is the automorphism FLT actually uses. Our port has `qTwist` but not its
   packaged equivalence, so a nontrivial test could be built from it — but a
   *concrete* `P` still has to be produced, which drags in the slot machinery.

**Recommendation: leave it open.** The lemma is verified character-identical to the
pin, and its nontrivial use is on record in FLT; the wire test's weakness is
documented here and in the module, which is what the wire test was for. Route 1 is
the better small topic if one is ever wanted.

## 9. Records map

| file | role |
|---|---|
| [PORTING-FFG.md](../PORTING-FFG.md) | the top plan: scope argument, gain test, deferred theorem menu |
| [TOPIC-jq-coefficients.md](../topics/functionFieldGeneration/TOPIC-jq-coefficients.md) | the completed topic plan: the `jq` coefficients |
| [TOPIC-conditional-capstone.md](../topics/functionFieldGeneration/TOPIC-conditional-capstone.md) | the completed topic plan: the proof's spine, conditionally |
| [TOPIC-interface-tier.md](../topics/functionFieldGeneration/TOPIC-interface-tier.md) | the completed topic plan: the cone's outbound interface |
| [TOPIC-generic-kernel.md](../topics/functionFieldGeneration/TOPIC-generic-kernel.md) | the completed topic plan: the generic engine lemmas, and a peel |
| [spec/ModularCurveConsumer.lean](../spec/ModularCurveConsumer.lean) | the deliverable measure, and the friction log |
| [spec/check_flt_statements.py](../spec/check_flt_statements.py) | diffs every port statement against the pin |
| this file | the record: what the effort did, cost, and decided |
| [porting-playbook.md](../porting-playbook.md) | lessons for the next port, independent of this one |

**The layer work orders were used and then deleted; the topic plans were kept.**
That split is now the convention, and it is worth stating because it took two
rounds of tidying to arrive at:

- a **layer work order** is scaffolding — 0a and 0b each ran once and their
  content is in the code, in the playbook's §7 (the principles, the overlap, the
  calibration), and here. They were deleted.
- a **topic plan is an executed plan**, not scaffolding: it records a decision and
  its cost, and the log cross-references it. All four moved to
  `lean/topics/functionFieldGeneration/` once finished
  ([the `jq` coefficients](../topics/functionFieldGeneration/TOPIC-jq-coefficients.md),
  [the conditional capstone](../topics/functionFieldGeneration/TOPIC-conditional-capstone.md),
  [the interface tier](../topics/functionFieldGeneration/TOPIC-interface-tier.md),
  [the generic kernel](../topics/functionFieldGeneration/TOPIC-generic-kernel.md)).
- **`logs/` is the linear record** of what happened, in order — this file for the
  FFG effort, `card-torsion-port.md` for the first port.

Nothing durable was lost in the deletions. The principles and the overlap section —
the most reusable things this effort has produced, more so than the module list,
which is derivable from the code — are §7.1 and §7.2 of the playbook, and the
post-mortem with the measured cost is §6 above.
