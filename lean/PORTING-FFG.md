# Blueprint: `ModularCurve.functionFieldGeneration`

**Status (2026-09-22): Layer 0 and its four topics are done; the Φ_p splitting
cone is finishing; the theorem is scheduled.** The library of
`lean/FLTForHuman/ModularCurve/` plus `FLTForHuman/FieldTheory/CommonRoot.lean` and
the `FLTForHuman/ModularForms/` cone modules is green with zero warnings and zero
`sorry`, the deliverable measure `spec/ModularCurveConsumer.lean` reports
**0 errors**, and the effort now owns two halves of the theorem: the proved
conditional capstone `functionFieldGeneration_of (h : Inputs)`, and the Φ_p cone
(T5–T10 landed, T11–T13 planned) that discharges its inputs. **The live plan is
§7.8**: the 17-node remainder, the measured ≈4.5k–4.9k line budget, and topics
T14–T20.

The scope has moved on from Layer 0. §1 is the design rules that still govern the
remaining work; §2 records the decision to finish and why; §3–§6 are the Layer 0
record and its verification conventions (the module inventory itself is the
[README](README.md) table and [logs/ffg-port.md](logs/ffg-port.md)); §7 is the
frontier and the schedule.

**What motivates the push is not line count.** The Φ_p cone is this segment's
**sole bridge to analysis** — R1, the level-one q-expansion principle, has no known
algebraic substitute — and it is the **outbound interface** through which the rest
of FLT reaches a fifth of the repository. Porting lines is the price paid for math
and structural clarity, and that price is accepted; §2 and §2.1 carry the argument
and the measured interface ledger.

Companion records:

- [math/010](../math/010-function-field-generation.md) — the mathematics. Source of
  truth for *what the proof says*.
- [PORTING-PhiGen.md](topics/PORTING-PhiGen.md) — the Φ_p cone: content decomposition,
  corrected size, and the T5–T13 sequence.
- [logs/ffg-port.md](logs/ffg-port.md) — this effort's measured record.
- [logs/card-torsion-port.md](logs/card-torsion-port.md) — the first port
  (`#E[n](K) = n²`, 13 modules, 3362 lines, capstone green).
- [porting-playbook.md](porting-playbook.md) — the reusable method.
- [../studies/flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) — the
  segment survey.
- [README.md](README.md) — the module table and build notes.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`.
mathlib is our pinned `v4.34.0`.

## 0. Scope

**Layer 0 is done.** `jq`, `qExpand`, `qTwist`, `coeffEmb`,
`modularFunctionField`, the target `FunctionFieldGeneration` and the slot
vocabulary are transcribed into a mathlib-only library that compiles, has no
`sorry`, and can be evaluated. Its inventory is the [README](README.md) module
table; its measured cost and decisions are [logs/ffg-port.md](logs/ffg-port.md)
§2–§3.

**The theorem is now in scope.** Layers 1–4 — the statement layer, the induction
spine, the significant lemmas, the counting detours — were deferred while their
cost was gated by the unported Φ_p cone and therefore unknown. The gate is being
removed by the sub-effort: when T11–T13 of [PORTING-PhiGen.md](topics/PORTING-PhiGen.md)
land, `PhiGen.splits_prime_at_slot` is a ported theorem, and the remaining proof is
the **17-node, ≈4.5k–4.9k-line** port of the seven `Inputs` fields and their
internal dependencies. §7.8 is the schedule.

**Why the work is finished rather than harvested.** The remainder buys the first
*unconditional, machine-checked FLT headline the port would own*, and it closes the
outbound interface a fifth of FLT reaches this segment through. §2 is the decision
record; §2.1 is the interface measurement.

## 1. Organization for math clarity

The port's one unambiguous gain is that 144 files of `Thm_`/`S_`/`Def_` triples
become modules named for their mathematical role, readable in dependency order.
The same rules that shaped Layer 0 govern T14–T20; the playbook §7.1–§7.2 carries
the fuller statement.

- **Module = mathematical role, not FLT's file taxonomy.** FLT splits by artifact
  kind (`Def_X` / `Thm_X` / `S_X`); the port splits by concept, one module per
  object or step, so the file list reads as the mathematics.
- **Reading order is dependency order.** A reader walks the directory linearly;
  each module header states its subject, its FLT source and pin, and what it
  assumes from earlier modules.
- **Monomorphic helpers are documentation, not just tactics.** Every generic
  mathlib lemma the proofs rely on gets a monomorphic, named restatement with a
  docstring saying what it transports
  (`polyToField_sub := map_sub polyToField a b`). It names the transport, the
  compiler checks it is the statement the proof uses, and version drift breaks it
  locally and visibly. Catalogues to watch: `map_sub`/`map_neg`/`map_add`/`map_mul`/
  `map_pow` on a `def`-as-`RingHom`, `Jacobian.comp_smul`, and any `abbrev` that
  `rw` will not unfold (playbook §3.5–§3.7).
- **Adopt mathlib's names where mathlib has them; keep FLT's where it does not.**
  `LaurentSeries`, `HahnSeries`, `IntermediateField`, `IsPrimitiveRoot` and
  `CyclotomicField` are mathlib's; everything else keeps FLT's spelling so
  math/010 §9's map and `#check` correspondence stay mechanical. A module header
  says which is which.
- **No self-consumed lemmas; count before dropping.** A lemma whose only consumer
  is itself is not ported, and **a drop is verified by an occurrence count**
  (`grep -c`), recorded, not by inspection.
- **Clarity checklist per module.** Header with subject, provenance (file + line at
  `aa2d8b3`) and assumptions; declarations in dependency order; implicit mathlib
  conversions named; anything not ported counted; zero warnings, zero `sorry`.

## 2. The gain test, and the decision to finish

Truth is not in doubt and is not what we are buying. The first port's gain was
measured, and it was **not volume**: the playbook's own summary is that "a
faithful port is not line-for-line smaller" — 3362 lines written against a
3671-line cone. Its gains were organization (197 → 13 modules), clutter never
written (~650 lines, 18% of the cone), mathlib alignment, and truth. The same
scorecard, applied to this cone, is why the theorem was deferred while the Φ_p gate
stood:

| | `card_torsion` | `functionFieldGeneration` |
|---|---|---|
| FLT cone — files / lines | 4 / 3671 | 144 / 24402 |
| proof layer (`P2M/Sol`) | 1335 in one file, +127 `P2M/Util` | 22892, 71 files |
| theorem nodes in the docs-site graph | 1 (`below` = 0) | 70 (`below` = 69) |
| shared theorem nodes / definition modules | — | **0 / 0** |
| mathlib absorbs the core? | yes (division polynomials, `normEDS`, `torsionBy`) | **no** |
| clutter as a share of the cone | ~18% | **~2%** (505 wrapper lines) |
| cost of the faithful port | 33 rounds, 3362 lines | measured now: §7.8 |

The `card_torsion` row is the shape difference: its weight sat in one definition
module, this cone is a 70-node citation chain. Scored against the four gains, only
**organization** was unambiguous, **clutter** was weak at ~2%, **mathlib alignment**
was zero, and **truth** was zero by assumption — so the original decision was Layer
0 only, and the theorem only if a topic was later measured to support it.

**Reassessment (2026-09-22).** The condition is met. The one unported input, the
Φ_p cone, is being ported, and §7.8 measures the remainder at **≈4.5k–4.9k
deduplicated lines over 17 nodes** — not the 12,605-line headline, and closer to
**1.4×** the first port than the table's "4–10×" proxy. Two rows also move:

- **clutter** stays weak, but the remainder is three shared developments shipped
  repeatedly, not 17 independent proofs;
- **truth** stops being "zero by assumption": discharging the fields makes
  `functionFieldGeneration` an *unconditional, machine-checked* theorem.

**What actually motivates the push.** The line count above is context, not the
argument. The argument is two-part, and neither part is about cost:

1. **The cone is the segment's sole bridge to analysis.** R1 — the level-one
   q-expansion principle — is the only place this part of FLT leaves algebra and
   touches `ℍ`; [base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md)
   shows it has no algebraic substitute, and Φ_p is how the formal proof consumes
   it. §2.1's outbound ledger shows the analysis-facing declarations carry the
   largest external indegrees left in the cone: the Γ₀(N), Fricke,
   cuspidal-divisor, modular-unit and fibre-model layers reach this segment
   *through* the analytic facts.
2. **The port pays lines for math and structural clarity, and that trade is
   accepted.** The return is a module named for its mathematics, a statement a
   reader can compare with the classical one, and a mechanically checked
   correspondence. The line estimates keep the plan honest about scale, not decide
   whether the work is worth doing.

So the decision is to **finish it**: port Φ_p (sub-effort), then T14–T20 (§7.8).
Cost is not the veto; if a topic's route is expensive but the clarity gain is real,
the route is taken and the cost recorded, as T9's Route A was.

### 2.1 The outbound interface, measured

Two independent surveys (2026-09-21) located this cone in FLT from the doc-site
graph: **70 nodes**, of which **26 cite no FLT theorem at all** and **0** are
`AlgebraicCurve` — it sits at the floor of FLT's arithmetic tower — with **500
direct citers** and **5,804 transitive dependents** (19.7% of the 29,511 theorem
nodes), all outbound. A wrong *statement* here is maximally expensive and a wrong
*proof* maximally cheap to replace, which is why `spec/check_flt_statements.py` and
`#print axioms` are the highest-value things the port has built.

**The tier, by total indegree over the 70-node cone.** The nine public interface
lemmas of Layer 0 + topic 3 — `coeffMap_qExpand` (194), `dedekindPsi_prime` (72),
`coeffEmb_qExpand` (66), `transcendental_jq` (56), `dedekindPsi_mul_of_coprime`
(46), `dedekindPsi_prime_pow` (33), `coeffMap_injective` (32),
`coeffEmb_injective` (19), `aeval_jq_eq_zero` (2) — are **520 of the cone's 946**
≥5-indegree tier (**55%**). The unexposed mass was concentrated and named:
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (66),
`PhiGen.splits_prime_at_slot` (42), `exists_phiIrreducible_evalSymm` (29),
`hasSum_qParam_mul_laurent` (24).

**The cleaner measure: the out-of-cone ≥5-indegree tier** — every cone
declaration the rest of FLT reaches the segment through, counting only citers
outside the 70-node cone. That tier is **24 declarations / 701 citations** (plus
the capstone itself, externally cited 52×), and its coverage by effort is:

| status | decls | citations | share | cumulative |
|---|---|---|---|---|
| pre-Φ_p (Layer 0 + topics 1–4, the cheap interface) | 11 | 482 | 69% | 69% |
| Φ_p T5–T13 | 8 | 174 | 25% | **94%** |
| parent T14–T20 (the 5 remainder nodes still above the bar) | 5 | 45 | 6% | **100%** |

Under the total-indegree convention the same three rows read **55% → 82% → 92%**,
the capstone's own 52 citers closing it. Either way the shape is the same:
**pre-Φ_p covered the cheap 55%; Φ_p takes it to the low 90s; the parent remainder
closes it.**

**Promotion gap (closed 2026-09-22).** The Φ_p row above is what T5–T13 covers
now that its two analytic exports are public. As T5–T13 landed, **two of the eight
were still `private`**, so the measured out-of-cone coverage was **572/701 ≈ 82%**,
not 94%; both are now promoted, so the row reads 94%:

| declaration | outbound | port status | action |
|---|---|---|---|
| `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` | 65 | **public** (`ModularForms/JqAnalyticModel.lean`) | promoted; `Thm_` wrapper added to `SOURCES` |
| `qExpansion_E4_eq_map_eisenstein4` | 19 | **public** (same file) | promoted; same |

Both statements were already verbatim from their `Theorems/` wrappers, so the
change was visibility plus two `SOURCES` lines; neither is needed by T14–T20, so
this was purely the outbound interface (the checker moved 242 → 244). The other 31 outbound declarations — including every
Φ_p export the parent remainder imports (`splits_prime_at_slot`,
`exists_phiIrreducible_evalSymm`, `finrank_adjoin_jqN_eq_of_prime`,
`evalAtJ_injective`, `splits_of_prime`, and the `coeffMap_*` / `dedekindPsi_prime`
lemmas) — are public and statement-checked. Three further cone nodes stay private
(`exists_aeval_jq_sub_holomorphicAtInfty`, `hasSum_jNum_qParam`,
`qExpansion_discriminant_eq_X_mul_tprod`) at indeg 1, consistent with the ≥5
interface criterion.

**The char-`p` prelude is not a Φ_p promotion, it is T14.** T13's route proves
`splits_of_prime`/`splits_prime_at_slot` without the pin's ~200-line slot prelude
(`phiAtSeed*`, `qTwistEquiv*`, `phiProd_conj_eq`, `roots_prime_at_slot*`,
`prod_form_ne_zero`, …), correctly leaving it unported — the char-`p`
`*_of_isPrimitiveRoot` variants that use it are outside the cone. The parent
remainder's own files do use it heavily (`phiAtSeed` 22–65 occurrences per file,
`roots_prime_at_slot` up to 8), so §7.8's T14 remains a parent-side need, and its
`Defs/Cyclotomic.lean` component is already landed by T13.

**What Φ_p adds is exactly the analysis-facing half**, which is why the interface
argument and the "sole connection to analysis" argument are the same argument. The
eight ΔΦ_p declarations and their external citers:

| declaration | topic | ext. | what cites it |
|---|---|---|---|
| `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` | T6 | 65 | the modular-unit series (`hasSum_modularUnitSeries_*`), `eisenstein4_*` relations, `exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor` |
| `PhiGen.splits_prime_at_slot` | T13 | 30 | the level-`N`/Γ₀(N) layer (`isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant`, `mem_modularFunctionField_of_hasSum_of_gamma0_invariant`), `FullLevel.AuxLevel*`, the Fricke involution `coe_frickeInvolutionFull_*` |
| `hasSum_qParam_mul_laurent` | T7 | 22 | the modular-unit series and cuspidal-divisor bridges |
| `qExpansion_E4_eq_map_eisenstein4` | T6 | 19 | the same modular-unit/Eisenstein sector |
| `exists_phiIrreducible_evalSymm` | T12 | 15 | `ModularPolynomialData.*`, the level-`N` field layer |
| `hasSum_jq_qParam` | T6 | 9 | the q-expansion bridges |
| `hasSum_qParam_mul` | T7 | 8 | the same |
| `E4_cube_div_discriminant_smul` | T6 | 6 | the same |

The five that remain to T14–T20 are purely field-theoretic —
`minpoly_jqN_map_eq_prod_slots` (19), `jqN_prime_not_mem_full` (7),
`exists_phiIrreducible_of_finrank_eq` (7), `full_eq_adjoin_full_div_prime` (7),
`finrank_adjoin_jqN_prime_of_not_mem` (5) — feeding the degree/corollary layer
(`exists_phiIrreducible`, `finrank_adjoin_jqN_eq_dedekindPsi`,
`relfinrank_full_eq_dedekindPsi`, `modularFunctionField_eq_full`) plus the
CharP/fibre-model and Atkin–Lehner consumers. **No analytic dependency is left
behind once Φ_p lands.** That is the strongest statement of why the cone is the
right thing to finish first.

## 3. Layer 0: what it delivered

Layer 0 transcribed the definitions of `Definitions/Def_ModularCurve_X0.lean`
(348), `Def_ModularCurve_LaurentCoeff.lean` (144) and `Def_ModularCurve_PhiGen.lean`
(309) — the q-substitution and coefficient change, the explicit `jq` series and the
objects read off it, the target `FunctionFieldGeneration`, the two function fields,
and the slot vocabulary — plus `TS` from the solution file. `Def_ModularForm_HeckeOperator.lean`
(204) was **not** in Layer 0; the Φ_p sub-effort later took the 60-line
`heckeMatrix`/`heckeDiagMatrix` subset into `FLTForHuman/ModularForms/Defs/HeckeOperator.lean`
(T8), and the `heckeU`/`heckeT` block stays unported (0 occurrences in the cone).

It was split into 0a (the computable series objects and the target's *definition*,
which 0a can state and whose `M = 1` case it proves) and 0b (the field and
polynomial vocabulary). 0b was built once the conditional capstone fixed the shape
its consumers needed. The module-by-module inventory is the [README](README.md)
table; the measured cost is [logs/ffg-port.md](logs/ffg-port.md) §2.

Two conventions worth keeping:

- **Namespace `ModularCurve`**, matching FLT, so declaration names line up and
  math/010 §9's map applies unchanged. The safety against mathlib collisions comes
  from the mathlib *pin*, not the namespace.
- **One library.** Everything sits under the single `@[default_target] lean_lib
  FLTForHuman`; **work in progress stays out of it**, in the gitignored
  `Scratch.lean`, until it is green, warning-free and `sorry`-free.

## 4. Layer 0a: the computable objects

`FLTForHuman/ModularCurve/Defs/{Laurent,Twist,Jq}.lean` plus
`FunctionFieldGeneration/Target.lean` hold `qExpand`/`qExpandₐ`, `coeffMap`,
`coeffEmb`, `qTwist`, the explicit `eisenstein4`/`etaProd`/`jq`/`jqN`/`dedekindPsi`/
`evalAtJ`, and `FunctionFieldGeneration` + `functionFieldGeneration_one`. That the
target is a `def` mentioning only 0a objects is why 0a can *state* the theorem
before any of Layers 1–4 exists. The declaration-level inventory and FLT source
lines are in the [README](README.md) table.

## 5. Layer 0b: the field and slot vocabulary

`Defs/Polynomial.lean`, `Defs/Fields.lean`, `Defs/PhiGen.lean` and `Defs/TS.lean`
hold `ModularPolynomialData`, `modularFunctionField`/`modularFunctionFieldFull`,
`toAdjoin`, `TS = j(u q^e)`, and the `Prop`-valued vocabulary of the splitting
input (`conj`, `phiProd`, `EvalSymm`, `PhiIrreducible`, `PoleOrderLE` /
`TPoleOrderLE`, `IntCoeffs`, `PhiGenDescends`). These are the words the remaining
theorem and math/010 §3 are stated in; the declaration-level inventory is the
[README](README.md) table. T9–T10 later promoted the shared `TPoleOrderLE` prelude
into `Defs/PhiGen.lean`, which T11 imports unchanged.

## 6. Layout, build, and verification

```text
lean/FLTForHuman/ModularCurve/
  Defs/                 -- the shared X₀(N) vocabulary (Laurent, Twist, Jq, Polynomial, Fields, PhiGen, TS)
  JqCoefficients.lean   -- the low coefficients of `jq`
  FunctionFieldGeneration/
    Target.lean         -- FunctionFieldGeneration + functionFieldGeneration_one
    Collapse.lean       -- functionFieldGeneration_iff_full_eq
    Spine.lean          -- the conditional capstone: `Inputs` + functionFieldGeneration_of
lean/FLTForHuman/FieldTheory/CommonRoot.lean   -- the three generic engine lemmas
lean/FLTForHuman/ModularForms/                 -- the Φ_p cone's analytic area
lean/spec/
  ModularCurveConsumer.lean      -- the consumer; outside every library
  check_flt_statements.py        -- diffs every port statement against the pin
```

`Defs/` is the shared **X₀(N) vocabulary** any later `ModularCurve` theory would
reuse; the modules that exist only for this theorem sit in `FunctionFieldGeneration/`,
so a second theory can add its own directory beside them. Directory and namespace
differ on purpose: the path is `...ModularCurve.FunctionFieldGeneration.Spine`, the
declarations are `ModularCurve.*`.

**Verification.** The library has no `sorry`; the one deferred `sorry` is the
unconditional capstone in the consumer file, outside the build. With T14–T20 in
scope, §7.5's sorry protocol is live again.

```bash
cd lean
lake build                                 # green, 0 warnings, no sorry
grep -rn 'sorry' FLTForHuman/ModularCurve/ # must be empty
```

**The consumer is the deliverable measure.** `spec/ModularCurveConsumer.lean` is a
standalone Lean file — not imported anywhere and not globbed by any library, so it
cannot break the build — that writes down what the port is supposed to make
possible. Where a declaration is missing it does not compile, and the error count
is the metric:

```bash
lake env lean spec/ModularCurveConsumer.lean 2>&1 | grep -c error
```

Its zones record different kinds of claim:

- **Zone A `[0a]`** — the objects, the pole-of-`j` lemmas, the target statement
  `FunctionFieldGeneration N`, and the capstone. Must reach **0 errors**; its one
  remaining `sorry` is the unconditional capstone.
- **Zone B `[0b]`** — `modularFunctionField`, `ModularPolynomialData`. Bound since
  Layer 0b landed.
- **Zones C–H `[topics]`** — the cross-module wire tests of each finished topic
  (`jq` coefficients, conditional capstone, interface tier, generic kernel, R1
  kernel, `jq` model, Hauptmodul, Φ_p descendants, integrality, pole bounds). All
  bound.
- **Zone I and later** — T11–T20, added as the topics land.

The consumer doubles as the FLT correspondence record: every declaration is
`#check`ed against its pinned signature, and the v4.34.0 friction list accumulates
at the tail of the file.

## 7. The frontier and the plan

### 7.1 The one big cut, superseded

The earlier draft cut the Φ_p subtree as a `sorry`-bounded input: 44 nodes below
`S_ModularCurve_PhiGen_splits_prime_at_slot`, 94 files / 11,034 structural lines,
45% of the cone. That is **no longer the plan** — the sub-effort ports it. The
cut's measurement (deduplicated the subtree is 5,811 `S_` lines over 37
developments, of which only the ≈1,909-line level-one q-expansion principle is
analytic) survives in [PORTING-PhiGen.md](topics/PORTING-PhiGen.md).

### 7.2 Verified against `tools/deps`

Re-derived from the doc-site graph FLT's own generator built; the two methods agree
exactly. Capstone closure **69 theorem nodes** matching `meta.below`; slot closure
**44 nodes**; identical file sets between the graph and an import parse; 0 of 180
walked cites with a zero use count. Regenerate with:

```bash
cd tools/deps
python3 explore.py ModularCurve.functionFieldGeneration
python3 explore.py ModularCurve.PhiGen.splits_prime_at_slot
```

### 7.3 The remainder manifest (regenerate, do not hand-maintain)

The 24 nodes below the capstone and outside the slot closure, with per-node `S_`
file sizes, are regenerated by the script below (or by §7.8's richer measurement).
Two facts a future effort must carry:

- math/010 §9's map is **incomplete**: `Polynomial.mem_range_of_eval_eq_const` is on
  the critical path but not named in the note.
- `functionFieldGeneration_of_squarefree` **must not be dropped**, despite math/010
  §8 calling the squarefree case redundant: the graph shows it cited with use count
  10 by both `minpoly_jqN_map_eq_prod_slots` and `jqN_prime_not_mem_full`. A prose
  note's "this is redundant" is a claim about mathematics, not about the formal
  dependency graph.

```bash
cd tools/deps && python3 - <<'PY'
import sys; from pathlib import Path; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData()
FLT = Path.home() / 'proj' / 'fermats-last-theorem'
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
def lines(n):
    s = FLT / f"P2M/Sol/S_{d.stem_of[n]}.lean"
    return sum(1 for _ in open(s, encoding='utf-8')) if s.exists() else 0
cap  = d.index['ModularCurve.functionFieldGeneration']
slot = d.index['ModularCurve.PhiGen.splits_prime_at_slot']
for n in sorted((closure(cap) - closure(slot)) - {cap}, key=lambda n: -lines(n)):
    print(f"{lines(n):5d}  {d.qual(n):60s} cites={len(d.cites(n))}")
PY
```

### 7.4 The three rules

- **R1 — definitions are bottom-up and real.** Never `sorry` a `def`, `abbrev`,
  `structure` or `instance`: a sorry'd *proof* is cited and shows up in
  `#print axioms`, but a sorry'd *definition* is used and is invisible to that
  check.
- **R2 — statements are top-down; proofs may be `sorry`.** Transcribe the `Theorems/`
  wrappers without the `p2m_exact_reverting` delegation.
- **R3 — ground-up only for the significant lemmas.** §7.8's table is the list.

### 7.5 Sorry protocol and drop list

- Every `sorry` carries a **diagnosis**: math/010 section, FLT source and pin, the
  exact failure mode if attempted, the shape of the fix, and what it blocks.
- Count sorries from the **build warning count**
  (`lake build 2>&1 | grep -c warning`), not from a grep: `grep` matches the word
  inside this document's own prose.
- A drop is not verified until `grep -c` has been run and its count recorded.

### 7.6 What the remainder is made of

The segment survey's tiers, corrected against the files. **Tier 0** — the three
`Polynomial.*` lemmas (`mem_range_of_unique_common_root`,
`mem_range_of_eval_eq_const`, `irreducible_of_transitive_ringAut`) — is the
mathematical engine (math/010 §4 is the first, §6's non-membership the second, the
`p+1`/`p` degrees the third); mathlib has none of them, and they are built in
`FLTForHuman/FieldTheory/CommonRoot.lean`. **Tier 1** — `IntermediateField`
degree and transport — is mostly mathlib restated monomorphically, and is the most
likely source of line savings in T16/T18. **Tier 2–3** — `phiAtSeed` and the
cyclotomic roots — are the shared prelude T14 exposes. **Tier 6** — the Dedekind ψ
arithmetic — is number theory; the parts the spine consumes
(`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow`) are already public, leaving
only `dedekindPsi_of_squarefree`.

The curve layer cannot replace this theorem: the cone has zero `AlgebraicCurve`
nodes by design, and the modular `IsCurveOver` and Riemann–Roch instances are
proved *from* the same degree and Φ_p-splitting inputs, so using them here would be
circular.

### 7.7 The frontier: the seven `Inputs` fields

`functionFieldGeneration` follows from `hall_all` + the collapse (proved in
`Spine.lean`) plus the seven named fields of the `Inputs` structure. "Pin proof" is
the whole solution file of the node.

| field | pin | what it says | math/010 |
|---|---|---|---|
| `minpoly_jqN_map_eq_prod_slots` | 2,002 | the explicit slot product for `minpoly ℚ⟮jq⟯ (jqN M)` mapped into `K` | §3–§4 |
| `jqN_prime_not_mem_full` | 2,002 | `jqN p ∉ modularFunctionFieldFull M` for `p ∤ M` | §6 |
| `jqN_pow_not_mem_adjoin_full` | 995 | that non-membership propagated up the prime-power tower | §6 |
| `modularFunctionField_eq_full_of` | 735 | the descent closure, `F_N = F_N^{full}` from one-prime steps | §5 |
| `jqN_div_mem_modularFunctionField` | 735 | descent by one prime: `j(q^M) ∈ ℚ(j(q), j(q^{Mp}))` | §4 |
| `full_eq_adjoin_full_div_prime` | 624 | one new generator at level `Mp^{a+1}` | §5 |
| `relfinrank_full_eq_mul` | 81 | the prime-power degree step: `p + 1`, then `p` | §6 |

Raw sum **7,174**; two pairs are the same file and the shared prelude is written
once, so the fields' own structural content is ≈3,357 — but that is not the
remainder's price, because the fields' proofs also need the internal nodes below
them and the graph closure is import-level. §7.8 is the measured account.

Every field is gated by `PhiGen.splits_prime_at_slot` in FLT's proof. There were
three ways forward — port the subtree (**chosen**, by the sub-effort); make Φ_p an
eighth field (superseded, buys only a two-level conditional); re-route a field so
it never needs Φ_p (not taken: base/013 shows the level-one q-expansion principle
has no algebraic substitute). Two cautions still govern any estimate: **cost tracks
the route, not the subtree** (the `jq` coefficients were priced against this same
11,034-line cluster and turned out to be a 237-line standalone file — a 47× error),
and **the frontier is top-heavy** (three of the seven are the 2,002 / 2,002 / 995
slot cluster).

### 7.8 Reassessment after Φ_p: the measured remainder and the topic plan

**Premise (2026-09-22).** [PORTING-PhiGen.md](topics/PORTING-PhiGen.md) T11–T13 will land,
so `PhiGen.splits_prime_at_slot` becomes a ported theorem. This section assumes that
and re-derives the frontier.

**The gate really is removed, node by node.** The slot's 44-node closure maps
exhaustively onto the sub-effort and the already-landed interface tier:

| source | nodes below the slot |
|---|---|
| interface tier + Layer 0 (`coeffMap_*`, `coeffEmb_*`, `dedekindPsi_prime`, `aeval_jq_eq_zero`, `transcendental_jq`) | 7 |
| T5–T7 (R1: the constancy kernel, the `jq` model, the Hauptmodul form) | 11 |
| T8–T10 ((c) membership and the Hecke layer, (b) integrality, (b) pole bounds) | 9 |
| T11 ((a) descent, the 328 block, (d) assembly) | 8 |
| T12 ((e) the 895 block, `one_le_coeff_jq`, symmetry, existence) | 6 |
| T13 ((d) uniqueness, (f) the splitting; the slot wrapper itself is the 45th) | 3 |

There is no orphan node: 7 + 11 + 9 + 8 + 6 + 3 = 44, matching the graph's
`meta.below = 44`. So porting T11–T13 completes the cone, and with it the whole
gate.

**The frontier is the 24-node remainder minus the seven already done.** Regenerated
from `tools/deps` exactly as §7.3's script does, the remainder below the capstone
and outside the slot closure is 24 nodes. Seven are already discharged — the
`functionFieldGeneration_iff_full_eq` collapse (`Collapse.lean`), both `dedekindPsi`
lemmas (`Defs/Jq.lean`), `relfinrank_modularFunctionField` (`Defs/Fields.lean`) and
the three `Polynomial.*` lemmas (`FieldTheory/CommonRoot.lean`). **Seventeen nodes
remain**, and they are the seven `Inputs` fields *plus the ten internal nodes their
proofs need* — which is why discharging the fields cannot be priced at the fields'
own 7,174 raw lines.

**Fifteen of the seventeen are on the theorem's proof path.** The graph closure is
import-level, and two of the seventeen — `exists_phiIrreducible_of_finrank_eq`
(158) and `exists_monic_evalAtJ_jqN_eq_zero` (108) — are trailing corollaries that
no `Inputs` field cites; the node `ModularCurve.functionFieldGeneration` "cites"
them only because the pin's generator reads the whole solution file. The port's
`Inputs` confirms the pruning. So the theorem's own price is the 15-node one,
**≈4.3k–4.7k**; the two corollaries are worth ~250 lines and buy the downstream API
(`exists_phiIrreducible`, `finrank_adjoin_jqN_eq_dedekindPsi`,
`relfinrank_full_eq_dedekindPsi`) that the rest of FLT consumes. T20 carries them as
an explicit, optional tail.

**Measured (2026-09-22).** For each remaining node, the whole `S_` file, the lines
in declarations shared with at least five of the seventeen (the repeated prelude),
and the remainder ("own"). The shared prelude is ~375 lines / 45 declarations
carried by twelve of the seventeen files — the survey's "≈360-line `TS`/`phiAtSeed`
block", re-measured.

| node | pin file | shared | own | topic |
|---|---|---|---|---|
| `minpoly_jqN_map_eq_prod_slots` | 2,002 | 391 | 1,577 | T19 |
| `jqN_prime_not_mem_full` | 2,002 | 391 | (same file) | T19 |
| `jqN_pow_not_mem_adjoin_full` | 995 | 387 | 580 | T17 |
| `finrank_adjoin_jqN_eq_of_squarefree` | 864 | 385 | 445 | T18 |
| `finrank_adjoin_jqN_pow_succ_of_not_mem` | 758 | 396 | 333 | T16 |
| `modularFunctionField_eq_full_of` | 735 | 383 | 325 | T15 |
| `jqN_div_mem_modularFunctionField` | 735 | 383 | (same file) | T15 |
| `jqN_prime_not_mem_adjoin` | 653 | 376 | 244 | T17 |
| `full_eq_adjoin_full_div_prime` | 624 | 373 | 224 | T18 |
| `full_eq_adjoin_primes` | 600 | 373 | 200 | T18 |
| `relfinrank_full_of_squarefree` | 526 | 373 | 124 | T18 |
| `finrank_adjoin_jqN_prime_of_not_mem` | 348 | 245 | 77 | T16 |
| `exists_phiIrreducible_of_finrank_eq` | 158 | 4 | 135 | T20 (optional) |
| `exists_monic_evalAtJ_jqN_eq_zero` | 108 | 51 | 42 | T20 (optional) |
| `relfinrank_full_eq_mul` | 81 | 4 | 57 | T16 |
| `dedekindPsi_of_squarefree` | 69 | 4 | 51 | T18 |
| `functionFieldGeneration_of_squarefree` | 54 | 4 | 30 | T18 |
| **total (17 nodes)** | **11,312** | **4,523** | **6,346** | |

"Deduplicated" is not the own-column sum, because the duplicate developments of
§7.1/§7.6 reappear here. The ledger:

| correction | lines |
|---|---|
| 17-node structural sum | 11,312 |
| shared prelude (≈375 × 12) written once | −4,143 |
| `minpoly_jqN_map_eq_prod_slots` ≡ `jqN_prime_not_mem_full` (one file, two nodes) | −1,577 |
| `modularFunctionField_eq_full_of` ≡ `jqN_div_mem_modularFunctionField` | −325 |
| one of the two `jqN_prime_not_mem_adjoin` proofs (the 2,002-line file has its own) | −244 (up to −650) |
| **deduplicated structural** | **≈4,600–5,000** |
| less the prelude already in the port (`Defs/TS.lean`, `iota_jqN`, the cyclotomic block ≈ 135) | **≈4,450–4,900** |

So the remainder is **≈4.5k–4.9k genuinely new port lines** including the two
trailing corollaries, or **≈4.3k–4.7k** for `functionFieldGeneration` alone — about
**1.4×** the first port (3,362 lines) and **about the size of the whole Φ_p
sub-effort** (T5–T10 shipped 2,981; T11–T13 budget ~2,800 more). That is a
structural count, not a proof budget — T8 and T9 both showed lines are not effort
— but it is the first measured price this theorem has had, and it is 2.5× below the
12,605 headline.

**The topics (T14–T20).** The cut is by mathematical object, one shared development
per topic, so each proof is written once — but the measured intra-remainder
dependency graph does **not** follow math/010's section order, and the topics below
respect the real order. The surprise is that the two 2,002-line `Inputs` fields sit
*downstream* of everything: both cite `functionFieldGeneration_of_squarefree`, which
cites the squarefree degree nodes. The prime-power *degree* step (T16) is upstream
of the non-membership base (T17), which is upstream of the squarefree
generation/degree block (T18), which is upstream of the slot product (T19). Only
the descent (T15) and the prelude (T14) are independent of that chain.

| topic | object | content | ≈ new lines | prereq |
|---|---|---|---|---|
| **T14** | the slot machinery | expose the shared prelude publicly: `qTwistEquiv` + cycle, `phiProd_conj_eq`, `roots_phiProd_conj(_nodup)`, `qExpand_qTwist_TS`, `prod_form_ne_zero`, `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff`, `phiAtSeed*` and its six lemmas, `qExpand_qTwist_notMem_range_qExpand`; promote the `Spine.lean` `private` cyclotomic block and `iota_jqN`/`jqN_congr` to `Defs/` | ~250 | Φ_p defs |
| **T15** | descent and the collapse (math/010 §4–§5) | `jqN_div_mem_modularFunctionField`, `modularFunctionField_eq_full_of` (one 735-line development) | ~350 | T14, Φ_p T12–T13 |
| **T16** | the degree step (math/010 §6b) | `finrank_adjoin_jqN_prime_of_not_mem`, `finrank_adjoin_jqN_pow_succ_of_not_mem`, `relfinrank_full_eq_mul` | ~500 | T14, Φ_p T13, `CommonRoot` |
| **T17** | non-membership, base and tower (math/010 §6a) | `jqN_pow_not_mem_adjoin_full`, `jqN_prime_not_mem_adjoin` | ~830 | T14, T16 |
| **T18** | generation and the squarefree degree (math/010 §5–§6b) | `full_eq_adjoin_full_div_prime`, `full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`, `relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`, `functionFieldGeneration_of_squarefree` | ~1,150 | T15, T16, T17 |
| **T19** | the slot product and prime non-membership (math/010 §3, §6a) | `minpoly_jqN_map_eq_prod_slots`, `jqN_prime_not_mem_full` (one 2,002-line development; it also contains a second `jqN_prime_not_mem_adjoin`, redundant with T17) | ~1,300–1,600 | T18, Φ_p `splits_prime_at_slot` |
| **T20** | the unconditional capstone | construct `Inputs` from T15–T18 and apply `functionFieldGeneration_of`; replace the consumer's `sorry` with the proved `functionFieldGeneration N`; **optional tail:** `exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq` (+~250, for the downstream corollaries) | ~50 (+250) | T15–T18, plus T19 for two fields |

**Route risks, in the order they will bite.** Each is a candidate for the
"cost tracks the route" treatment before its topic is priced:

- **T14 decides T15–T19's interface.** Every remaining file starts with the same
  block; if the port exposes it in the shape the proofs want (the pin's `TS`,
  `qTwistEquiv` and `phiAtSeed` spellings), the rest are transcriptions. The one
  known trap is Tier 4's `qTwistEquiv` — T8 already hit a `mapGL`-transparency
  issue with this family; T5's log §2.2 has the `FunLike` fallback.
- **T19's 2,002-line development is the riskiest single file.** It is three
  proofs — the slot product, prime non-membership, and the redundant
  `jqN_prime_not_mem_adjoin` — and the survey leaves open which copy is
  load-bearing. Count the named nodes' lines versus the helper chain before
  committing, as the standing rule requires.
- **T16/T18's Tier-1 bridges are the most likely mathlib win.** The survey marks
  `IntermediateField.relfinrank`, `extendScalars_adjoin`, `adjoin.finrank` and the
  tower law as mathlib-present; FLT restates them monomorphically. Import mathlib's
  and write only the named monomorphic restatements the `rw`/`simp` calls need
  (§1).
- **T20's optional `exists_phiIrreducible_of_finrank_eq`** is only 158 lines and may
  now be a short corollary of Φ_p's `exists_phiIrreducible_evalSymm` plus minpoly
  degree; route-check before porting the pin's construction. It is off the
  theorem's proof path, so it can be deferred without blocking T20's capstone.
- **`Inputs` stays frozen.** T20 must *construct* the existing structure, not add
  fields: the internal nodes are proofs, not assumptions. If one resists, the honest
  move is a `sorry` with the playbook's diagnosis (§7.5), not a new field.

**Definition of done for the effort.** `lake build` green, 0 warnings, no `sorry`;
`#print axioms` on `functionFieldGeneration` clean; the consumer's only `sorry`
gone and its capstone unconditional; the statement checker extended with T14–T19's
wrappers and T20's capstone. At that point
`ModularCurve.functionFieldGeneration` is a proved theorem of the port, the
segment's one conditional is discharged, and — by §2.1's ledger — the **out-of-cone
≥5-indegree tier is 100% covered**: every declaration through which the rest of FLT
reaches this segment, the analytic ones included, is a ported theorem rather than a
reference.

## 8. Open questions

- **Will Layer 0a be used? — answered: yes**, narrowly by itself (the transport
  layer, the pole of `j`, the statable target) and fully through the topic modules
  that consume it. The written-down use is `spec/ModularCurveConsumer.lean`.
- **Is the theorem still a "revisit"? — resolved: it is scheduled (§7.8).** The
  graph remainder is 17 nodes / 11,312 structural pin lines / ≈4.5k–4.9k after
  dedup; the theorem's own path is 15 nodes / ≈4.3k–4.7k. What is *not* yet
  measured is the route each heavy development should take; that is each topic's
  own work order, per the standing rule.
- **What if Φ_p slips?** Only T14 (the slot machinery) is independent of the cone's
  *proofs*. Every remaining node cites `exists_phiIrreducible_evalSymm` (T12),
  directly or through T16's finrank chain, and T15–T19 additionally cite
  `PhiGen.splits_prime_at_slot`/`splits_of_prime` (T13). So T14 can proceed in
  parallel and nothing more; the critical path is T12 → T13 → T15–T19, and the
  parent should not start before T12–T13 are green.
- **Stop-and-harvest, restated.** The conditional capstone plus the whole cone is
  already a coherent artifact. Finishing costs ≈4.5k–4.9k lines and buys the first
  unconditional FLT headline the port would own plus a complete outbound interface.
  If that trade were ever refused, the honest stopping point is after T14 (the
  interface exposed) rather than midway through T16.
- **Drift on unchanged mathematics.** Layer 0 produced twelve friction entries,
  kept at the tail of the consumer file; the playbook calls the friction log the
  highest-value artifact because it is the one thing not derivable from the code.
  T14–T20 should keep accumulating there.
- **Transcription risk.** Declarations must be transcribed verbatim in shape
  (names, argument order, instances) or `#check` correspondence fails. This is
  mechanically checked: `spec/check_flt_statements.py` diffs every port statement
  against the pinned source — **205 of 205 identical, 0 mismatched, 0 missing** —
  and the consumer's cross-module compositions are the runtime wire test.
