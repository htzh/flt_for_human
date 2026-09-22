# Blueprint: `ModularCurve.functionFieldGeneration`

**Status (2026-09-22): Layer 0, its four topics, the Φ_p splitting cone and
T14–T18 are done; the theorem's remaining nodes (T19–T20) are the live work.** The
library of `lean/FLTForHuman/ModularCurve/` plus
`FLTForHuman/FieldTheory/CommonRoot.lean` and the `FLTForHuman/ModularForms/` cone
modules is green with zero warnings and zero `sorry`, the deliverable measure
`spec/ModularCurveConsumer.lean` reports **0 errors**, and the effort now owns two
halves of the theorem: the proved conditional capstone
`functionFieldGeneration_of (h : Inputs)`, and the Φ_p cone (T5–T13 landed) that
discharges its inputs. T14 wrote the pin's shared slot prelude once
(`Defs/PhiAtSlot.lean`, `PhiSlotRoots.lean` and the `Defs/` extensions), so
T15–T19 import it; T15 discharged two `Inputs` fields
(`FunctionFieldGeneration/Descent.lean`), T16 the third
(`FunctionFieldGeneration/DegreeStep.lean`), T17 the fourth
(`FunctionFieldGeneration/Nonmembership.lean`) and T18 the fifth
(`FunctionFieldGeneration/Generation.lean`), taking the capstone's debt to **2**.
**The live plan is §7.8**: the remainder, the measured line budget, and topics
T19–T20. T18 also adopted the 2026-09-22 route audit's scope decision: it ports
only `full_eq_adjoin_full_div_prime` and lands the `gen_prime` substitution, so
T19 does not depend on the deferred squarefree generation/degree block.

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
the **17-node, ≈4.8k–5.0k-line** port of the seven `Inputs` fields and their
internal dependencies. §7.8 is the schedule.

**Why the work is finished rather than harvested.** The remainder buys the first
*unconditional, machine-checked FLT headline the port would own*, and it closes the
outbound interface a fifth of FLT reaches this segment through. §2 is the decision
record; §2.1 is the interface measurement.

## 1. Organization for math clarity

The port's one unambiguous gain is that 144 files of `Thm_`/`S_`/`Def_` triples
become modules named for their mathematical role, readable in dependency order.
The same rules that shaped Layer 0 govern T15–T20; the playbook §7.1–§7.2 carries
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
Φ_p cone, is being ported, and §7.8 measures the remainder at **≈4.8k–5.0k
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
change was visibility plus two `SOURCES` lines; neither is needed by T15–T20, so
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
unconditional capstone in the consumer file, outside the build. With T15–T20 in
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
cyclotomic roots — are the shared prelude T14 exposed. **Tier 6** — the Dedekind ψ
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
**≈4.6k–4.8k**; the two corollaries are worth ~250 lines and buy the downstream API
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
| ~~one of the two `jqN_prime_not_mem_adjoin` proofs~~ | **0 — falsified by the 2026-09-22 audit**: the two are distinct statements (public Finset vs private M-arbitrary), and the file's private one is load-bearing, so nothing is redundant |
| **deduplicated structural** | **≈5,270** |
| less the prelude already in the port (`Defs/TS.lean`, `iota_jqN`, the cyclotomic block ≈ 135) | **≈5,130** |
| less the T19 route win the slot-counting audit found (§7.8 "Audit outcomes") | **−≈200 → ≈4,930** |

So the remainder is **≈4.8k–5.0k genuinely new port lines** including the two
trailing corollaries, or **≈4.6k–4.8k** for `functionFieldGeneration` alone — about
**1.4×** the first port (3,362 lines) and **about the size of the whole Φ_p
sub-effort** (T5–T10 shipped 2,981; T11–T13 budget ~2,800 more). The headline is
close to the earlier ≈4.5k–4.9k for two offsetting reasons: the audit voided the
`jqN_prime_not_mem_adjoin` dedup (+244) and found a ~200-line route win in T19.
That is a structural count, not a proof budget — T8 and T9 both showed lines are
not effort — but it is the first measured price this theorem has had, and it is
2.5× below the 12,605 headline.

**The topics (T14–T20).** The cut is by mathematical object, one shared development
per topic, so each proof is written once — but the measured intra-remainder
dependency graph does **not** follow math/010's section order, and the topics below
respect the real order. §7.8 originally read the two 2,002-line `Inputs` fields as
*downstream* of everything, because the pin's private non-membership cites
`functionFieldGeneration_of_squarefree`. The 2026-09-22 route audit showed that
citation is the chain's only real link and is replaceable by the definitional
`Gen p`, so **the serial chain T17 → T18 → T19 disappears**: T18 keeps only its
`Inputs` node, and T19 sits directly on T17. The prime-power *degree* step (T16),
the non-membership tower (T17) and the generation step (T18) are level-0 topics on
T14 and the Φ_p cone; the descent (T15) and the prelude (T14) are independent of
the chain.

| topic | object | content | ≈ new lines | prereq |
|---|---|---|---|---|
| **T14** ✅ | the slot machinery | **done (2026-09-22)** — the shared prelude is written once: `Defs/PhiAtSlot.lean` (the `conj`/`TS` bridges `iota_jq`/`conj_zero_eq`/`conj_succ_eq`, `phiProd_conj_eq`, `roots_phiProd_conj(_nodup)`, `phiAtSeed` + its eight lemmas, `aeval_intermediateField_eq_zero`, `phiAtSeed_eval_of_injective`/`_symm`, `phiAtSeed_jqN_eval_down`), `Defs/Twist.lean` (`qTwist_iota_of_pow_eq_one`, `qTwistEquiv` + `_apply`/`coe_`), `Defs/TS.lean` (`iota_jqN`, `qTwist_TS_one_cycle`, `qExpand_qTwist_TS`, `qExpand_qTwist_notMem_range_qExpand`), `Defs/Jq.lean` (`jqN_congr`), and the downstream `ModularCurve/PhiSlotRoots.lean` (`prod_form_ne_zero`, `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff`). Six `private` twins in `Spine.lean`/`PhiGenSplits.lean` are deleted. The cyclotomic block was already promoted by T13. | **503 measured** (237 + 153 + 51 + 56 + 6; ratio ≈1.64) | Φ_p defs |
| **T15** ✅ | descent and the collapse (math/010 §4–§5) | **done (2026-09-22)** — `FunctionFieldGeneration/Descent.lean`: `jqN_div_mem_modularFunctionField` (the unique-common-root descent, with `htw`/`hsp` left as arguments for T19) and `modularFunctionField_eq_full_of` (the one-prime `Gen` reduction). One 735-line pin development, but ~542 of those lines are T14's prelude; the tail is **173** lines. Both are `Inputs` fields, so the capstone's debt is now **5**. Work order [TOPIC-descent.md](topics/functionFieldGeneration/TOPIC-descent.md) | **252 measured** (ratio ≈1.46) | T14, Φ_p T12–T13 |
| **T16** ✅ | the degree step (math/010 §6b) | **done (2026-09-22)** — `FunctionFieldGeneration/DegreeStep.lean`: `finrank_adjoin_jqN_prime_of_not_mem` (the twist `p + 1`), `finrank_adjoin_jqN_pow_succ_of_not_mem` (the coefficient-automorphism `p`) and `relfinrank_full_eq_mul` (the tower dispatcher). ≈435 pin lines. Three transport bridges promoted once (with `coeffMapEquiv`/`iota_injective`/`w1_relfinrank_insert`), the redundant `coeffEmb_injective'`/`jqN_congr'` dropped, and the private twins in `PhiGenDescent.lean`/`PhiGenSplits.lean`/`PhiGenIntegrality.lean` deleted. `relfinrank_full_eq_mul` is an `Inputs` field, so the debt is now **4**. Work order [TOPIC-degree-step.md](topics/functionFieldGeneration/TOPIC-degree-step.md) | **605 measured** (455 new module + 150 promoted; ratio ≈1.39) | T14, Φ_p T13, `CommonRoot` |
| **T17** ✅ | non-membership, base and tower (math/010 §6a) | **done (2026-09-22)** — `FunctionFieldGeneration/Nonmembership.lean`: `jqN_pow_not_mem_adjoin_full` (the prime-power tower, an `Inputs` field) and `jqN_prime_not_mem_adjoin` (the public Finset lemma; the 2026-09-22 audit confirms it is not reducible to the full-file private lemma and vice versa). One module, tower declared first; `chain_extend`'s explicit `RingHom` literal closed as written and `chain_endgame` needed no heartbeat bump. The tower is an `Inputs` field, so the debt is now **3**. Work order [TOPIC-nonmembership.md](topics/functionFieldGeneration/TOPIC-nonmembership.md) | **843 measured** (ratio ≈1.14 against ≈741) | T14, T16 |
| **T18** ✅ | one new generator per prime power (math/010 §5) | **done (2026-09-22)** — `FunctionFieldGeneration/Generation.lean`: `full_eq_adjoin_full_div_prime` (the fifth `Inputs` field, so the debt is now **2**), on the once-ported two-prime descent `jqN_mem_of_div_primes` and the strong induction `w1_jqN_mem_adjoin_top_insert`. **Scope decision:** the original topic's squarefree generation/degree block (nodes 2–6) is a **deferred optional API tail**; T19 adopts the 2026-09-22 route audit's `gen_prime` substitution instead of `functionFieldGeneration_of_squarefree`, and `tight_one`/`gen_one`/`gen_prime` landed in `Defs/Fields.lean`. Work order [TOPIC-generation.md](topics/functionFieldGeneration/TOPIC-generation.md) | **309 module + 36 net** (`Defs/Fields` +71, `Spine` −35; ratio ≈1.27 against ≈271) | T14, Φ_p |
| **T19** | the slot product and prime non-membership (math/010 §3, §6a) | `minpoly_jqN_map_eq_prod_slots` (= the pin's `rval_aux`) and `jqN_prime_not_mem_full` (one 2,002-line development, which also carries its own **private M-arbitrary** `jqN_prime_not_mem_adjoin` — a different statement from T17's public Finset lemma, not a duplicate). Route win: closed-form `slotAt` + the `CommonRoot` engine import (2026-09-22 audits). **T18's `gen_prime` replaces the pin's `functionFieldGeneration_of_squarefree p` call at `S_ModularCurve_jqN_prime_not_mem_full.lean:1638`**, so T19's prereq is T17, not T18; its `d = 1` branch uses `tight_one`/`gen_one` | **~1,100–1,400** | T17, Φ_p `splits_prime_at_slot` |
| **T20** | the unconditional capstone | construct `Inputs` from T15–T18 and apply `functionFieldGeneration_of`; replace the consumer's `sorry` with the proved `functionFieldGeneration N`; **optional tail:** `exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq` (+~250, for the downstream corollaries) | ~50 (+250) | T15–T18, plus T19 for two fields |

**T14 measured (2026-09-22), and the row corrected.** T14 landed in **one** goal
round (of the two budgeted) as 32 declarations: six promotions (`iota_jqN`,
`jqN_congr`, `iota_jq`, `conj_zero_eq`, `conj_succ_eq`, `qExpand_qTwist_TS`),
twenty-one fresh upstream declarations and five downstream ones. **503 port
lines** (new `Defs/PhiAtSlot.lean` 237, new `PhiSlotRoots.lean` 153, `Defs/TS.lean` +51,
`Defs/Twist.lean` +56, `Defs/Jq.lean` +6) against the pin's ~306, ratio **≈1.64**
— above the §7 band (~320–420) because two new modules carry full headers and
every declaration a docstring. The row's `~250` was a pre-scouting estimate and is
replaced by the measured **503**. Two findings correct the work order:

- **Most of the prelude was already public.** The work order said every T14
  declaration is `private` in the pin. In fact
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` (already a checker source)
  carries the whole block *publicly*, so the checker verified 31 of the 32 by a
  direct last-name match; only `prod_form_ne_zero` needed the dotted fallback.
  (The 31st is `qTwistEquiv_apply`, which the pin writes
  `@[scoped simp] theorem …` on one line; the checker's `DECL_RE` gained an
  optional leading-attribute group so it is visible on both sides.) The two new
  `S_` carriers were still needed for
  `aeval_intermediateField_eq_zero`, `phiAtSeed_eval_of_injective`/`_symm`,
  `phiAtSeed_jqN_eval_down` and `qExpand_qTwist_notMem_range_qExpand`. The checker
  moved **244 → 276** identical (11 → 12 promoted), 0 mismatched, 0 missing.
- **The layering constraint bit one level earlier than §4 assumed.** `Defs/TS.lean`
  already imports `Defs/Twist.lean`, so the three `TS`-dependent prelude members
  (`qTwist_TS_one_cycle`, `qExpand_qTwist_TS`,
  `qExpand_qTwist_notMem_range_qExpand`) and `iota_jqN` **cannot** live in
  `Defs/Twist.lean`/`Defs/Jq.lean` as §4 planned; putting them there would create
  an import cycle. They live beside `TS` in `Defs/TS.lean` instead. Every
  declaration still has exactly one home.

**T15 scouted (2026-09-22), and its row corrected.** The work order is
[TOPIC-descent.md](topics/functionFieldGeneration/TOPIC-descent.md). The two
`Theorems/` nodes are one development shipped twice
(`S_ModularCurve_jqN_div_mem_modularFunctionField.lean` ≡
`S_ModularCurve_modularFunctionField_eq_full_of.lean`, modulo the `solution` line),
and **~542 of its 735 lines are the T14 prelude already written once** — so T15's
own content is only the 173-line tail (`jqN_div_mem_modularFunctionField`
139 + `modularFunctionField_eq_full_of` 34). The row's `~350` was priced from the file
size before T14 landed, and is replaced by **~200–280**. Every prerequisite is
public (T14's prelude, T13's `splits_prime_at_slot`, T12's
`exists_phiIrreducible_evalSymm`, T4's `mem_range_of_unique_common_root`), so T15
is a pure consumer with no promotion and no mathlib-absent lemma. Proving its two
nodes discharges **two** `Inputs` fields, taking the capstone's debt **7 → 5**.
One correction for the note: math/010 §5's link places `jqN_mem_of_div_primes` in
this file, but it is a T18 helper (in `S_ModularCurve_full_eq_adjoin_full_div_prime.lean`
line 397), not T15's.

**T15 measured (2026-09-22), and the row corrected.** T15 landed in **one** goal
round as **252 port lines** against the 173-line tail, ratio **≈1.46** — inside
its scouted `~200–280` band and far under the `~350` the pre-T14 row priced. The
two declarations are public, their statements the `Theorems/` wrappers' verbatim,
`#print axioms` clean, and the checker moved **276 → 278** (0 mismatched, 0
missing). All four route risks resolved on the first build: the `Algebra F
(LaurentSeries K)` `letI` and the `ι₀`/`hcomp` bridge closed by `rfl` exactly as
transcribed (no `respectTransparency`, no named bridge), and
`isRoot_prime_at_slot_iff` and `mem_range_of_unique_common_root` fired at the pin's
call shape with no argument-order repair. The only warning was the
`linter.style.haveILetI` pair on two genuinely-needed local instances, cleared by
the module-level disable T13 also uses. Zone M's wire test builds a partially
discharged `Inputs` with these two fields filled, so **the capstone's debt is
7 → 5**; the five remaining fields are T16–T19's. The dedup premise held: the two
`S_` files are one development and **none of the ~542 prelude lines was
re-copied**.

**Audit outcomes (2026-09-22), reviewed and spot-checked.** Four read-only
engineering audits landed in `logs/` while T15 was being scoped. Their
load-bearing claims were re-derived here before being recorded:

- [audit-slot-counting-mathlib.md](logs/audit-slot-counting-mathlib.md) — **T19's
  slot-counting block (299 pin lines) has a real ≈110–150-line route win.**
  `dedekindPsi` is genuinely absent from mathlib (0 hits) and there is no Γ₀ index
  formula to delegate to, but `slotAt_mul`'s 108-line CRT fibre argument is
  replaceable by the closed form
  `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)` plus mathlib
  `Nat.Coprime.divisors_mul`; and the four `dedekindPsi_*` re-proofs are already
  public in the port. The closed form was checked exhaustively for `n, d ≤ 40`
  (0 mismatches) and `slots n = dedekindPsi n` for `n ≤ 79`; the named mathlib
  ingredients (`Nat.periodic_coprime`, `Nat.filter_coprime_Ico_eq_totient`,
  `Nat.Coprime.divisors_mul`) all exist in `v4.34.0`. The block should shrink to
  ~150–190 lines with one public `Finset.card = dedekindPsi` export and
  `slots`/`slotAt` kept `private`.
- [audit-jqN-nonmemory.md](logs/audit-jqN-nonmemory.md) — **a negative result that
  saves a wasted route: do not try to reduce `jqN_prime_not_mem_adjoin`.** The
  private M-arbitrary lemma inside the 2,002-line file is genuinely independent of
  the public Finset lemma; powerful `M` is load-bearing (`d = 36` at `hall_all`),
  and every separation tool in the repository is keyed to prime generators. Net
  saving **≈ 0**. The port keeps both statements (they are different), and T17's
  estimate stands.
- [audit-rval-aux-compressibility.md](logs/audit-rval-aux-compressibility.md) —
  **T19's `rval_aux` (the slot product, 680-line body) is ~64% irreducible
  mathematics**; the realistic shrink is only ~50–60 lines local plus ~18 outside
  (the private `mem_range_of_eval_eq_const` is a verbatim copy of
  `FieldTheory/CommonRoot.lean`'s engine lemma and should be imported, not
  re-proved). A verbosity cleanup, not a structural reduction.
- [audit-prelude-bridges.md](logs/audit-prelude-bridges.md) — **T14's dedup is the
  dominant win**, larger than measured: 41 files carry the `TS` prelude, 38 of
  them all 41 declarations verbatim (≈10–12k duplicated lines, plus ~2–3k in the
  parallel `jqModC` prelude). Only **two genuine mathlib collisions** exist in it,
  both primitive-roots: the `cycUnit` quartet is mathlib's
  `IsCyclotomicExtension.zeta`/`zeta_spec`/`zeta_pow` + `IsPrimitiveRoot.isUnit`,
  and `isPrimitiveRoot_pow_div` is `IsPrimitiveRoot.pow` (all confirmed present).
  In the bridges, only `coeffMapEquiv` (`RingEquiv.ofBijective`) and
  `exists_pow_eq_of_coprime` (`exists_pow_eq_self_of_coprime`) are mathlib wins;
  the rest is de-duplication.

Two consequences for the schedule:

- **T19's estimate drops, and the ledger's `jqN_prime_not_mem_adjoin` deduction
  is void.** The row's `~1,300–1,600` becomes **~1,100–1,400** (≈110–150 from the
  counting block, ≈18 from the engine import, ≈50–80 from `rval_aux`), and its
  work order must prescribe the closed-form slot route and the `CommonRoot`
  import. The nonmemory audit simultaneously removes the old `−244` "redundant
  proof" line, so the net headline is ≈4.8k–5.0k, not ≈4.5k–4.9k.
- **A T13 follow-up: `Defs/Cyclotomic.lean` — done (2026-09-22).** T13 ported the
  cyclotomic quartet verbatim; the audit showed it was a re-proof of mathlib's
  `zeta` family. The file now sources `exists_isPrimitiveRoot_cyclotomicField` and
  the chosen root `cycUnit`/`cycUnit_spec` from
  `IsCyclotomicExtension.zeta`/`zeta_spec` (so `cycUnit` is defeq to mathlib's
  root), and `isPrimitiveRoot_pow_div` is `IsPrimitiveRoot.pow` +
  `Nat.div_mul_cancel` (9 → 2 lines). All five statements are untouched, so the
  checker stayed at **288** (the concurrent T17 work has since moved it), and the
  build is green. Honest measurement: the file went **70 → 78** lines, of which 12
  are the new header note, so the proof content is **−4 net** — the `haveI`
  instance argument `zeta` needs costs about what the shortened proofs save, and
  T13's redundant `haveI : NeZero ((N : ℕ) : ℚ)` is dropped (mathlib synthesizes
  it from `[NeZero N]`). The larger gain is mathlib alignment — `cycUnit` is now
  defeq to mathlib's chosen root — and the removal of the re-proof; the audit's
  "≈18 lines" was per pin copy, ×40. It also adds a promotion item for the later
  topics: the transfer lemmas (`coeffMap_qTwist`, `coeffMap_TS`, `jqN_congr`,
  `iota_injective`, `w1_relfinrank_insert`) are duplicated across files and want
  one home each — `jqN_congr` was T14's, and the `coeffMap_*` three were T16's.

**T16 scouted (2026-09-22), and its row corrected.** The work order is
[TOPIC-degree-step.md](topics/functionFieldGeneration/TOPIC-degree-step.md). The
three degree nodes are separate files, and most of files 1–2 is again T14's
prelude, so T16's own content is **≈435 pin lines**, not the `~500` the row
carried: the prime node (52) is the twist argument, the pow-succ node (187) the
hard one, `relfinrank_full_eq_mul` (24) a dispatcher over them, plus ~145 helper
lines. Three of those helpers are **redundant** with public declarations
(`coeffEmb_injective'` ≡ `coeffEmb_injective`, `jqN_congr` appears twice), and
three are **promotions**: `coeffMap_qTwist` (the audit's 41-copy lemma),
`coeffMap_TS` (14 copies) and `coeffMap_coeffEmb_algHom` are private in T11/T13's
cone modules and should live once in `Defs/Laurent.lean`. The genuinely new
mathematics is the pow-succ automorphism: not the nome twist but a cyclotomic
coefficient automorphism `coeffMapEquiv τ` cycling the `p - 1` roots of the
degree-`p` factor — mathlib's `IsCyclotomicExtension.autEquivPow` /
`IsPrimitiveRoot.autToPow` API, which nothing in the port exercises yet and is
T16's one real route test. Port estimate **~500–650**, two goal rounds.

**T16 measured (2026-09-22) — one round, and the row corrected.** T16 landed in
**one** goal round as **605 port lines**: the new `DegreeStep.lean` (455) plus
150 promotion lines (`Defs/Laurent.lean` +70, `Defs/Fields.lean` +34,
`Defs/Twist.lean` +25, `Defs/TS.lean` +21), against ≈435 pin lines, ratio
**≈1.39** — inside the scouted `~500–650` band. All three declarations are
public, their statements the wrappers' verbatim, `#print axioms` clean; the
checker moved **278 → 288** (0 mismatched, 0 missing) and the consumer gained
Zone N, whose wire builds a partially discharged `Inputs` with the three proved
fields filled, so **the capstone's debt is 5 → 4**. Every route risk resolved on
the first build: the whole pow-succ node — the factor peel, the multiset
re-indexing `range_map_eq_rUnit` and the cyclotomic automorphism block —
transcribed without a stall, and `coeffMapEquiv` took `RingEquiv.ofBijective` as
the audit predicted. Two corrections:

- **The `coeffMap_*` home is `Defs/Twist.lean`/`Defs/TS.lean`, not
  `Defs/Laurent.lean`.** As with T14's `iota_jqN`, the import layering forbids
  §4's table: `coeffMap_qTwist` mentions `qTwist` (downstream of `Laurent`), so it
  lives in `Defs/Twist.lean`, and `coeffMap_TS` mentions `TS`, so it lives beside
  `TS` in `Defs/TS.lean`. Only `coeffMap_coeffEmb_algHom` (plus `coeffMapEquiv`
  and `iota_injective`) is genuinely `Defs/Laurent.lean`. Every declaration still
  has exactly one home, and no cycle was introduced.
- **The three `S_` carriers join the checker `SOURCES`.** §6.2 named only the
  three `Them_` wrappers, but the promoted `coeffMapEquiv`, `iota_injective` and
  the private `w1_relfinrank_insert` have no wrapper, so the prime/pow-succ/
  relfinrank `S_` files are appended (last, so no existing match flips); they are
  what the checker's direct and dotted routes read for those promotions.

**T17 measured (2026-09-22) — one session, both halves on the first build.** T17
landed as one new module, `FunctionFieldGeneration/Nonmembership.lean`, **843
lines**: the tower (three range helpers, `chainField` + its five lemmas,
`chain_extend`, `chain_endgame`, the key and the public wrapper) declared first,
then the base (`step_contradiction`, `jqN_prime_not_mem_adjoin_key` and the public
wrapper), exactly so a stall would isolate to one half. Both halves compiled green
— 0 warnings, no `sorry` — on their first `lake env lean`, so the two-round budget
was spent as two *builds*, not two debugging rounds; the only drift was
`Set.mem_setOf_eq` → `Set.mem_ofPred_eq` in one `simp only`. Against the scouted
≈741 new pin lines the ratio is **≈1.14** (tower ≈528, base ≈223), inside the
estimated 750–950 band. `#print axioms` is clean on both public declarations; the
checker moved **288 → 290** (0 mismatched, 0 missing) and the consumer gained
Zone O, whose `Inputs` composition fills the four proved fields so **the
capstone's debt is 4 → 3**. Every route risk resolved on the first build:

- **`chain_extend`'s `RingHom` literal closed as written.** The explicit
  `{ toFun := fun z => ψ ⟨z.1, hle z.2⟩, … }` structure with the
  `adjoin_induction` coercion `hle` typed as-is; no `FunLike` bridge and no
  monomorphic coercion restatement was needed, so §1's documented stall family did
  not bite.
- **`chain_endgame` needed no heartbeat bump.** It closed under the global
  `maxHeartbeats 4000000`; the pin's two local `3200000` `set_option`s were omitted
  exactly as the work order directed, and no declaration stalled.
- **The `Algebra F (LaurentSeries K) := σ.toAlgebra` device** was copied from T15
  unchanged, and `algHomAdjoinIntegralEquiv`/`powerBasis.exists_eq_aeval'`
  transcribed without a monomorphic restatement.
- **The base's `hkill` root-pinning** (`isRoot_prime_at_slot_iff` plus
  `qExpand_qTwist_notMem_range_qExpand`, and the `Int.natCast_dvd_natCast` cast)
  transcribed verbatim.

Two corrections for the record: the base's `step_contradiction` and
`jqN_prime_not_mem_adjoin_key` are `private` in the port (they have no `Theorems/`
wrapper, and the pin's own `S_` carrier is not in `SOURCES`), and the tower's
`jqN_pow_not_mem_adjoin_full_key` is `private` too, so the checker verifies only
the two public wrappers — the promoted-declaration count is unchanged at 14.

**T18 measured (2026-09-22) — one round, node 1 only, and the scope decision.**
T18's mandatory scope landed in **one** goal round as **309 port lines** in the new
`FunctionFieldGeneration/Generation.lean`, plus **36 net** lines for the
`Defs/Fields.lean` promotion (`+71`) and the `Spine.lean` removal (`−35`): the
`Tight`/`Gen`/`Hall` invariants and `tight_one`/`gen_one` moved beside the fields
they concern, and the audit's `gen_prime` was added there. Against the scouted
≈221 mandatory pin lines plus the ≈50-line promotion (≈271), the ratio is
**≈1.27**; the module alone is 309/221 ≈ 1.40, inside the estimated 250–320. No
stall: the descent transcribed as-is against T14's slot API, and the only drift
was the port's usual `jqN_congr'` → `jqN_congr`. `#print axioms` is clean on
`full_eq_adjoin_full_div_prime`, `tight_one`, `gen_one` and `gen_prime`; the
checker moved **290 → 293** (0 mismatched, 0 missing; 16 promoted) and the
consumer gained Zone P, whose `Inputs` composition fills the five proved fields so
**the capstone's debt is 3 → 2**.

**The scope decision, recorded.** The 2026-09-22 route audit
([TOPIC-t17-t19-route-audit.md](topics/functionFieldGeneration/TOPIC-t17-t19-route-audit.md) §1)
showed T19's only real use of the squarefree cluster is
`functionFieldGeneration_of_squarefree p` at `S_…jqN_prime_not_mem_full.lean:1638`,
and that `Gen p` is definitional. `TOPIC-generation.md` §1 now adopts the drop:
nodes 2–6 (`full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`,
`relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`,
`functionFieldGeneration_of_squarefree`) are a deferred optional API tail, and T19's
edit is a two-line replacement. The full inventory stays in `TOPIC-generation.md` §2
so a future effort need not re-scout. The one API cost is that
`relfinrank_adjoin_primes` and `relfinrank_full_mul_prime` are not ported; neither
is in §2.1's outbound tier.

**The dedup.** `jqN_mem_of_div_primes` is **one** declaration in the port
(`Generation.lean:85`); the pin's `grep -c "theorem jqN_mem_of_div_primes"` is 1
in each of six `S_` files (three in T18's scope: `full_eq_adjoin_full_div_prime`,
`full_eq_adjoin_primes`, `modularFunctionField_eq_full_of`; three more in the
squarefree cluster), so five copies are dropped. The pin's `jqN_congr'` (2 grep
hits in `full_eq_adjoin_full_div_prime`) is dropped for `Defs/Jq.lean`'s
`jqN_congr`. The dead `psi_prime_pow_aux`/local `dedekindPsi_prime_pow`,
`phiIrreducible_of_squarefree` and `exists_pow_eq_of_coprime` are in the deferred
tail and were not ported.

**Route risks, in the order they will bite.** Each is a candidate for the
"cost tracks the route" treatment before its topic is priced:

- **T14 decided T15–T19's interface, and it held.** Every remaining file starts
  with the same block, now written once (`Defs/PhiAtSlot.lean`, `Defs/TS.lean`,
  `Defs/Twist.lean`, `ModularCurve/PhiSlotRoots.lean`); the rest are transcriptions.
  The one known trap was Tier 4's `qTwistEquiv`; T14 took the
  `RingEquiv.ofBijective` route and it closed (log §2g), so the `FunLike` fallback
  was not needed.
- **T19's 2,002-line development is the riskiest single file.** It is three
  proofs — the slot product (`rval_aux`), `jqN_prime_not_mem_full`, and a private
  **M-arbitrary** `jqN_prime_not_mem_adjoin` that the 2026-09-22 audit showed is
  *not* a duplicate of T17's public Finset lemma and is load-bearing for powerful
  `M`. Count the named nodes' lines versus the helper chain before committing, as
  the standing rule requires; the slot-counting audit's closed-form route is the
  one compression that survived review.
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
gone and its capstone unconditional; the statement checker extended with T19's
wrappers (T14's–T18's are already in) and T20's capstone. At that point
`ModularCurve.functionFieldGeneration` is a proved theorem of the port, the
segment's one conditional is discharged, and — by §2.1's ledger — the **out-of-cone
≥5-indegree tier is 100% covered**: every declaration through which the rest of FLT
reaches this segment, the analytic ones included, is a ported theorem rather than a
reference.

## 8. Open questions

- **Will Layer 0a be used? — answered: yes**, narrowly by itself (the transport
  layer, the pole of `j`, the statable target) and fully through the topic modules
  that consume it. The written-down use is `spec/ModularCurveConsumer.lean`.
- **Is the theorem still a "revisit"? — resolved: it is scheduled and under way
  (§7.8).** The graph remainder is 17 nodes / 11,312 structural pin lines /
  ≈4.8k–5.0k after dedup; **T15's two nodes, T16's three, T17's two and T18's one
  are done**, so 9 nodes remain (T19–T20). The theorem's own path is 15 of those,
  of which 7 remain. What
  is *not* yet measured is the route each heavy development should take; that is
  each topic's own work order, per the standing rule — though the 2026-09-22
  audits have already priced T19's route (§7.8 "Audit outcomes").
- **What gates the remainder now? — nothing external.** T13's
  `PhiGen.splits_prime_at_slot` and T14's prelude are both landed, and every
  remaining node's Φ_p dependency (`exists_phiIrreducible_evalSymm`,
  `splits_prime_at_slot`/`splits_of_prime`) is public and statement-checked. The
  critical path is T19 followed by T20's capstone discharge; there is no
  unported input left.
- **Stop-and-harvest, restated.** The conditional capstone, the whole cone and the
  shared prelude are already a coherent artifact. Finishing costs ≈4.8k–5.0k lines
  and buys the first unconditional FLT headline the port would own plus a complete
  outbound interface. T14 was the clean stopping point (the interface exposed); if
  that trade were ever refused, it would be here rather than midway through T16.
- **Drift on unchanged mathematics.** Layer 0 produced twelve friction entries,
  kept at the tail of the consumer file; the playbook calls the friction log the
  highest-value artifact because it is the one thing not derivable from the code.
  T15–T20 should keep accumulating there.
- **Transcription risk.** Declarations must be transcribed verbatim in shape
  (names, argument order, instances) or `#check` correspondence fails. This is
  mechanically checked: `spec/check_flt_statements.py` diffs every port statement
  against the pinned source — **293 of 293 identical, 0 mismatched, 0 missing** —
  and the consumer's cross-module compositions are the runtime wire test.
