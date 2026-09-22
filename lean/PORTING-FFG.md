# Blueprint: `ModularCurve.functionFieldGeneration` — Layer 0

**Status: Layer 0 and all four topics are done.** The eleven modules of
`lean/FLTForHuman/ModularCurve/` — 68 declarations in 0a, 69 in 0b, 24 in
`JqCoefficients.lean` and 25 in `Spine.lean`, plus 9 public interface lemmas added
to `Defs/Laurent.lean` and `Defs/Jq.lean` — are green with zero warnings and
zero `sorry`, as is the new generic module `FLTForHuman/FieldTheory/CommonRoot.lean`,
and the deliverable measure `spec/ModularCurveConsumer.lean` reports
**0 errors**: Zones A, B and C are all bound. Its only remaining `sorry` is the
deferred theorem's capstone, now the *unconditional* counterpart of the proved
conditional capstone `functionFieldGeneration_of (h : Inputs)`. Layer 0's two work
orders and all four topics each finished in a single goal round, and
[logs/ffg-port.md](logs/ffg-port.md) carries the record, the measured proof cost,
and the calibration. This
file previously planned a sorry-bounded port of the whole theorem; that is now
deferred and kept only as a menu in §7, with the remainder reduced to the 7
fields of `Inputs` (see §7.4). The scope decision and its evidence are
§2, and the v4.34.0 friction list is at the tail of the consumer file, with
`spec/check_flt_statements.py` diffing all 150 transcribed port statements against
the pin (plus the own-proof declarations, exempted explicitly).

Companion records:

- [math/010](../math/010-function-field-generation.md) — the mathematics. It is
  the source of truth for *what the proof says*; this file says *what we build*.
- [logs/card-torsion-port.md](logs/card-torsion-port.md) — what the first port
  did: `#E[n](K) = n²`, 13 modules, 3362 lines, capstone green.
- [logs/ffg-port.md](logs/ffg-port.md) — the running record of *this* effort:
  measurements, decisions, friction, and predictions that were wrong.
- [porting-playbook.md](porting-playbook.md) — what the next port should know.
  Its measurements are used throughout this file.
- [../studies/flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) — the
  segment-scoped survey: how much of this cone is generic field theory versus
  modular instantiation, the three mathlib-absent polynomial lemmas that are the
  proof's engine, and the corrected (smaller) line budget.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`.
mathlib is our pinned `v4.34.0`.

## 0. Scope

**Layer 0 is the definitions.** `jq`, `qExpand`, `qTwist`, `coeffEmb`,
`modularFunctionField`, and the vocabulary around them, transcribed into a
mathlib-only library that compiles, has no `sorry`, and can be evaluated.

**The theorem is out of scope.** Layers 1–4 — the statement layer, the induction
spine, the significant lemmas, the counting detours — are not planned here. §7
records what a future effort would need; it is a menu, not a schedule.

**Why this split.** The two halves have different gains. Layer 0 buys a
*capability*: objects we can compute with, check coefficients against, and
experiment on, which neither FLT's prose nor our notes provide. Layers 1–4 buy
*organization only*, and math/010 already provides most of that organization in
prose. §2 is the full accounting.

**Future topics, judiciously chosen.** If a later session picks up part of the
theorem, it should pick a *topic* — the strong induction of math/010 §7, or the
degree step of §6 — not the whole cone. §7 is arranged so that is possible.

## 1. Organization for math clarity

This is the design principle of the port, and the reason to do it at all. The
first port demonstrated the win: 197+ importers of a single 1869-line engine
became **13 modules named for their mathematical role**, readable in dependency
order, with 292 declarations. The same win is available here — 144 files of
`Thm_`/`S_`/`Def_` triples become a handful of modules — and it is the *only*
win available, so the port should be organized entirely around it.

### 1.1 Module = mathematical role, not FLT's file taxonomy

FLT splits by artifact kind: `Def_X` defines, `Thm_X` states, `S_X` proves. The
port splits by concept: one module per mathematical object or step, so the file
list reads as the mathematics. `Def_ModularCurve_X0.lean`'s 348 lines touch four
different subjects (the q-substitution, the j-invariant series, the polynomial
datum, the two fields); they should not be one file here.

### 1.2 Reading order is dependency order

A reader should be able to open the directory and walk it linearly. Each module
carries a header comment saying (a) its subject, (b) the FLT source and pin,
(c) what it assumes from earlier modules. The first port's module table is the
model for this.

### 1.3 Monomorphic helpers are documentation, not just tactics

The first port kept having to restate mathlib's generic lemmas in a specific
form, because `rw`/`simp` will not fire on `map_sub` when the function argument
leaves implicit instances unresolved:

```lean
-- needed as a rewrite rule, and readable in its own right:
lemma polyToField_sub (a b : Poly) : polyToField (a - b) = polyToField a - polyToField b :=
  map_sub polyToField a b
```

These were introduced tactically, but they are the single best readability
device the port produced, and this plan promotes them to a design rule:

> **Every generic mathlib lemma the port relies on implicitly gets a monomorphic,
> named restatement, with a docstring saying what it transports.**

Why this is worth the lines:

- **It names the transport.** FLT's proof says `simp only [⋯, ← map_dblZ]` and a
  reader must reconstruct why that fails and what the intended map is. Ours says
  `polyToField_dblZ`, and the name states the content.
- **It is checked documentation.** The compiler enforces that the bridge is the
  statement the proof actually uses — unlike a comment.
- **It survives version drift.** A monomorphic helper proved by `exact` keeps
  working when mathlib's generic lemma changes shape, and when it breaks the
  breakage is local and named.

The catalogues to watch for: `map_sub` / `map_neg` / `map_add` / `map_mul` /
`map_pow` applied to a `def`-as-`RingHom`; `Jacobian.comp_smul`; and any
`abbrev` that `rw` will not unfold (playbook §3.5–§3.7).

### 1.4 Adopt mathlib's names where mathlib has them; keep FLT's where it does not

`LaurentSeries`, `HahnSeries`, `IntermediateField`, `IsPrimitiveRoot` and
`CyclotomicField` are mathlib's, so we use them and say so. Everything else here
is FLT's own — keep FLT's names verbatim so that math/010's §9 map and `#check`
comparisons against the pinned source stay mechanical. A module header should
make clear which is which.

### 1.5 No self-consumed lemmas, and count before dropping

The first port declared `coords` dead from a `grep … | head` whose output was
truncated, and lost two rounds when it turned out to be load-bearing. Two rules:
a lemma whose only consumer is itself is not ported, and **a drop is verified by
an occurrence count** (`grep -c`), recorded, not by inspection.

### 1.6 Clarity checklist per module

Before a Layer 0 module is called done:

- the header states subject, FLT provenance (file + line at `aa2d8b3`), and
  assumptions;
- declarations are in dependency order, and a reader needs no earlier module
  than the header names;
- every implicit mathlib conversion the module's proofs use is a named
  monomorphic helper (§1.3);
- anything not ported from the source file has a `grep -c` count recorded in
  §7.5;
- the module compiles with zero warnings and zero `sorry`.

## 2. The gain test, and why the theorem is deferred

Truth is not in doubt and is not what we are buying. The first port's gain was
measured, and it was **not volume**: the playbook's own summary is that "a
faithful port is not line-for-line smaller" — 3362 lines written against a
3671-line cone. Its gains were organization (197 → 13 modules), clutter never
written (~650 lines, 18% of the cone, dominated by a 340-line compat shim),
mathlib alignment (its interface *is* mathlib's), and truth.

| | `card_torsion` | `functionFieldGeneration` |
|---|---|---|
| FLT cone — files | 4 | 144 |
| FLT cone — lines | 3671 | 24402 |
| proof layer (`P2M/Sol`) | 1335 in one file, plus 127 of `P2M/Util` | 22892, 71 files |
| definitions | engine 1869 | 1005, four files |
| theorem nodes in the docs-site graph | 1 (`below` = 0) | 70 (`below` = 69) |
| shared theorem nodes / definition modules | — | **0 / 0** |
| mathlib absorbs the core? | yes (division polynomials, `normEDS`, `torsionBy`) | **no** |
| clutter as a share of the cone | ~18% | **~2%** (505 wrapper lines, ~96 variants) |
| cost of the faithful port | 33 rounds, 3362 lines | **unmeasured; every proxy says 4–10×** |

The `card_torsion` row `below = 0` is not a claim that it has no dependencies:
its proof module cites no *theorem* nodes, so the doc-site theorem graph is flat
there and the weight sits in one definition module. That is the shape difference:
the first port's effort was one big definition file, this one's is a 70-node
citation chain.

Scored against the four gains:

| gain | verdict for the theorem |
|---|---|
| organization | **strong** — but available to Layer 0 as well, and to a note section |
| clutter never written | **weak** — ~2% against 18%; the 22892 `P2M` lines are substance |
| mathlib alignment | **zero or negative** — mathlib absorbs nothing, so a port re-teaches FLT's own API |
| truth | **zero by assumption** |

The only unambiguous theorem-level gain is organizational, and the
*math-clarity* gain depends on how much of the 24-node remainder is actually
ported: the skeleton reads as "FFG follows from these 24 things" (which math/010
§9 already says in prose), while porting the remainder is 12605 FLT lines at the
playbook's measured ~1:1 ratio — roughly 4× the first port, with none of the
clutter or API dividend.

One measured caveat, from the playbook: the earlier draft's "~1500–3000 lines"
for a skeleton assumed ~80% of each `S_` module is helper material that stays an
input. That assumption is load-bearing and **untested**. If a future session
wants to revisit the theorem, it must measure one `S_` module first (count the
named node's proof lines versus its helpers) and record both counts here. Until
then the theorem's price is unknown, which is itself a reason to leave it
deferred.

**Decision (recorded).** Layer 0 now. The theorem only if a specific topic is
chosen later and the measurement supports it.

### 2.1 The gain test was too pessimistic about Layer 0 — measured

The reasoning above scores the *theorem* and concludes Layer 0 is worth it for
organization. Two independent surveys in `studies/` (2026-09-21) measured what
the port could not: this cone's position in FLT. Re-derived from the doc-site
graph:

- the cone is **70 nodes**, of which **26 cite no FLT theorem at all** and **0**
  are `AlgebraicCurve` — it sits at the floor of FLT's arithmetic tower;
- it has **500 direct citers** and **5,804 transitive dependents**, **19.7%** of
  the 29,511 theorem nodes, all outbound: nothing in the Frey, modularity or
  Galois-representation layers feeds it;
- the outbound traffic reaches it through a handful of **interface
  declarations** — `coeffMap_qExpand` (indeg **194**, the most-shared in the
  cone), `dedekindPsi_prime` (72), `coeffEmb_qExpand` (66),
  `qExpansion_discriminant_…` (66), `transcendental_jq` (56) — not through the
  headline theorem, which is itself consumed as an *input* by the Igusa and
  CharP/fibre-model packages.

So Layer 0's real product is that interface, and its gain was understated rather
than overstated: the declarations 0a/0b transcribed are the channel through which
**a fifth of the repository** reaches this segment. That also makes the cone's
position a verification argument: at the floor, a wrong *statement* is maximally
expensive and a wrong *proof* maximally cheap to replace — which is why
`spec/check_flt_statements.py` and `#print axioms` are the highest-value things
the port has built. See [logs/ffg-port.md](logs/ffg-port.md) §8.5.

**The interface is now built (topic 3, 2026-09-21).** Nine of these declarations
are public lemmas in `Defs/Laurent.lean` and `Defs/Jq.lean`, stated verbatim from
their pin wrappers and mechanically checked: `coeffMap_qExpand` (194),
`dedekindPsi_prime` (72), `coeffEmb_qExpand` (66), `transcendental_jq` (56),
`dedekindPsi_mul_of_coprime` (46), `dedekindPsi_prime_pow` (33),
`coeffMap_injective` (32), `coeffEmb_injective` (19) and `aeval_jq_eq_zero` (2) —
**520** of the cone's **946** ≥5-indegree tier (55%). The unexposed mass is
concentrated and named: `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`
(66, the modular-form cluster), `PhiGen.splits_prime_at_slot` (42),
`exists_phiIrreducible_evalSymm` (29), `hasSum_qParam_mul_laurent` (24). Two of
the nine also discharged `Inputs` fields, taking the conditional capstone's debt
from 10 to 8. See [logs/ffg-port.md](logs/ffg-port.md) §2e.

## 3. Layer 0: sources and scope

| source | lines | what it gives |
|---|---|---|
| `Definitions/Def_ModularCurve_X0.lean` | 348 | `qExpand`, `jq`, `jqN`, `dedekindPsi`, the two fields |
| `Definitions/Def_ModularCurve_LaurentCoeff.lean` | 144 | coefficient change of the Laurent series |
| `Definitions/Def_ModularCurve_PhiGen.lean` | 309 | the `q`-twist, the slot vocabulary |
| `Definitions/Def_ModularForm_HeckeOperator.lean` | 204 | **not ported** — belongs to the §7 cut |

Split into two sub-scopes, because they have different consumers:

- **0a — the computable series objects and the target's definition (the
  deliverable).** `qExpand`, `coeffMap`, `coeffEmb`, `qTwist`, the explicit
  series `jq` with its coefficient lemmas, `jqN`, `dedekindPsi`, `evalAtJ`, and
  **`FunctionFieldGeneration`**. The last belongs here for a specific reason:
  the target theorem's content *is* a `def`, and that def mentions only 0a
  objects (`jq`, `qExpand`, `IntermediateField.adjoin`) — not
  `modularFunctionField`. So 0a can *state* the target, and can even *prove* its
  degenerate case `functionFieldGeneration_one`. Neither needs the theorem.
- **0b — the field and polynomial vocabulary (only if the theorem is picked up).**
  `ModularPolynomialData`, `modularFunctionField`, `modularFunctionFieldFull`,
  `conj`, `phiProd`, `EvalSymm`, `PhiGenDescends`, …

Ship 0a. Hold 0b: it is definitions and therefore cheap, but its only consumer is
the deferred theorem, so porting it now would be building the map before deciding
to read it.

**The consumer is `spec/ModularCurveConsumer.lean`** — see §6. It writes down
what Layer 0 is supposed to make possible, section by section, and its error
count is the deliverable metric. The port's record, including the measurement
that settled its cost, is [logs/ffg-port.md](logs/ffg-port.md).

## 4. Layer 0a: object inventory

The point of this table is the *order*: it is dependency order, and the module
split follows it. Line numbers are the declaration's line in the pinned source.

### `FLTForHuman/ModularCurve/Defs/Laurent.lean`

The q-substitution and the coefficient change — the two ring maps everything else
composes. Sources: `Def_X0` 25–105, `Def_LaurentCoeff` 16–123.

| FLT source | declaration | mathematical content |
|---|---|---|
| `Def_X0:25` | `qExpand` | `q ⟼ q^N` on exponents, as a ring endomorphism |
| `Def_X0:34`–`66` | `qExpand_coeff_mul`, `_coeff_of_not_dvd`, `_single`, `_C`, `_injective`, `_one_apply`, `_congr`, `_qExpand` | its effect on coefficients and its injectivity |
| `Def_X0:98` | `qExpandₐ` | the same, as a `ℚ`-algebra map, for `IntermediateField` |
| `Def_X0:105`, `340` | `qExpandₐ_apply`, `qExpandₐ_comp` | agreement with `qExpand`, and composition |
| `Def_LaurentCoeff:16` | `coeffMap` | coefficientwise extension `R →+* S` |
| `Def_LaurentCoeff:34`–`56` | `coeffMap_coeff`, `_single`, `_coeffMap`, `_id`, `_congr` | functoriality |
| `Def_LaurentCoeff:81` | `coeffEmb` | the `ℚ → K` case |
| `Def_LaurentCoeff:85`–`123` | `coeffEmb_coeff`, `coeffMap_coeffEmb`, `laurentBaseChange`, `_mem_`, `mem_…_iff`, `coeffMap_mem_…` | how the base field sits inside |

### `FLTForHuman/ModularCurve/Defs/Twist.lean`

The unit twist. Source: `Def_PhiGen` 18–96.

| FLT source | declaration | mathematical content |
|---|---|---|
| `Def_PhiGen:18` | `qTwistFun` | rescale the coefficient of `q^k` by `u^k`: `q ⟼ uq` |
| `Def_PhiGen:25`–`35` | `qTwistFun_coeff`, `support_qTwistFun`, `qTwist` | coefficients, support, packaged as a ring endomorphism |
| `Def_PhiGen:66`–`90` | `qTwist_coeff`, `support_qTwist`, `_single`, `_one_apply`, `_qTwist`, `_injective` | functoriality and injectivity |
| `Def_PhiGen:96` | `qTwist_qExpand` | the composite is `q ⟼ uq^N` |

### `FLTForHuman/ModularCurve/Defs/Jq.lean`

The explicit q-expansion of the j-invariant, and the objects read off it.
Source: `Def_X0` 111–212.

| FLT source | declaration | mathematical content |
|---|---|---|
| `Def_X0:111`–`152` | `eisenstein4`, `etaProd`, `dedekindEtaUnit`, `dedekindEtaUnitInv`, `jNum`, `jNumQ` (+ `constantCoeff_*`) | `j` assembled as `E₄³ / Δ` from `q`-products, unit-normalised |
| `Def_X0:157` | `jq` | `j(q) ∈ LaurentSeries ℚ` |
| `Def_X0:160`–`190` | `ofPowerSeries_coeff_of_neg`, `jq_pow`, `coeff_jq_pow_self`, `coeff_jq_pow_of_lt`, `coeff_jq_neg_one`, `coeff_jq_of_lt`, `jq_ne_zero` | `jq = q⁻¹ + ⋯`: pole order and leading coefficient |
| `Def_X0:194` | `jqN` | `j(q^N)` |
| `Def_X0:201` | `dedekindPsi` | `ψ(N) = N ∏_{p∣N} (1 + 1/p)` |
| `Def_X0:208`, `212` | `evalAtJ`, `evalAtJ_X` | evaluation at `jq` |

### `FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean`

The target statement's definition, plus the one case of it that 0a can prove.
Source: `Def_X0` 233–242.

| FLT source | declaration | mathematical content |
|---|---|---|
| `Def_X0:233` | `FunctionFieldGeneration` | for every `d ∣ M`, `j(q^d) ∈ ℚ(j(q), j(q^M))` — the theorem's content, as a `def` |
| `Def_X0:237` | `functionFieldGeneration_one` | the `M = 1` case, provable from 0a alone |

This module is the payoff of the 0a scope: with it, the capstone
`ModularCurve.functionFieldGeneration (N) [NeZero N] : FunctionFieldGeneration N`
is *statable* — not provable — using only Layer 0a. That the target is a `def`
mentioning no field-theoretic infrastructure is why 0a can get this far.

## 5. Layer 0b: object inventory (built)

Source: `Def_X0` 215–348, `Def_PhiGen` 111–309. Split (as built) into
`Polynomial.lean`, `Fields.lean`, `PhiGen.lean`, plus `TS.lean` and
`Collapse.lean`; all are built and green.

- **fields** (`FLTForHuman/ModularCurve/Defs/Fields.lean`): `ModularPolynomialData` (215),
  `modularPolynomialDataOne` (225), `modularFunctionField` (250) with
  `jq_mem`/`jqN_mem`/`_one`/`adjoin_jq_le`, `jGen` (268), `evalAtJGen` (270),
  `algebraMap_comp_evalAtJGen` (273), `toAdjoin` (287) + `_monic` (289),
  `divisorExpansions` (297) + `mem_` (301), `modularFunctionFieldFull` (305),
  `jqd_mem_full` (309), `modularFunctionField_le_full` (313),
  `full_degeneracy_le` (321), `full_degeneracy_map_le` (330).
- **slot vocabulary** (`FLTForHuman/ModularCurve/Defs/PhiGen.lean`): `cosetSubst` (111),
  `evalAtJqN` (121) + `_X`/`_def`/`_one`, `EvalSymm` (139),
  `aeval_toRingHom_X` (145), `PoleOrderLE` (151), `ModularPolynomialFamily` (154),
  `PhiIrreducible` (161), `adjoinJq` (168), `jAdj` (170), `evalAtJAdj` (172),
  `swapInner` (179), `swapBivar` (182) + `_X`/`_C_X`, `cosetA`/`cosetB` (204/206)
  + `_zero`/`_succ` + `instNeZeroPhiGenCosetA` (221), `cosetSubst_congr` (231),
  `conj` (237) + `_zero`/`_succ`, `phiProd` (257) + `_monic`/`_natDegree`/
  `_ne_zero`/`_eval_conj`, `TPoleOrderLE` (282) +
  `tPoleOrderLE_iff_poleOrderLE` (285), `JSimplePole` (291), `IntCoeffs` (295),
  `PhiGenDescends` (302).

Note that these are the `Prop`-valued vocabulary of the splitting input. If a
future effort takes up math/010 §3 as a *statement*, this group must be ported
first, because the statement mentions it — the first port's `Universal.lean`
problem in reverse. It is now available: `Defs/PhiGen.lean` carries it.

## 6. Layout, build, and verification

```
lean/FLTForHuman/ModularCurve/
  Defs/Laurent.lean     -- §4
  Defs/Twist.lean       -- §4
  Defs/Jq.lean          -- §4
  Defs/Polynomial.lean  -- §5: ModularPolynomialData
  Defs/Fields.lean      -- §5: the two function fields
  Defs/PhiGen.lean      -- §5: the slot vocabulary
  Defs/TS.lean          -- §5: TS = j(u q^e), from the solution file
  JqCoefficients.lean   -- the low coefficients of `jq` (the first topic)

  FunctionFieldGeneration/          -- the theory; everything named for it lives here
    Target.lean         -- §4: FunctionFieldGeneration + functionFieldGeneration_one
    Collapse.lean       -- §5: functionFieldGeneration_iff_full_eq (Layer 0's only theorem)
    Spine.lean          -- the conditional capstone: `Inputs` + functionFieldGeneration_of

lean/spec/
  ModularCurveConsumer.lean      -- the consumer; not in any library, see below
  check_flt_statements.py        -- diffs every port statement against the pin
```

`Defs/` is the shared **X₀(N) vocabulary** — `qExpand`, `jq`, the two function
fields, the slot vocabulary — which any later `ModularCurve` theory would reuse.
The three modules that exist only for this theorem (`Target`, `Collapse`,
`Spine`) sit in a directory named for it, so a second theory can add its own
`<Theory>/` beside them without either inheriting generic names like "the spine"
or "the collapse". Directory and namespace differ: the path is
`...ModularCurve.FunctionFieldGeneration.Spine`, the declarations are
`ModularCurve.*`, so math/010 §9's map and the checker are unaffected by the
layout.

Namespace `ModularCurve`, so declaration names match FLT's and math/010's §9 map
applies unchanged. This is a **trade**, worth recording: the first port used its
own namespace (`FLTForHuman.Elliptic`) so its names could never collide with
mathlib's. Matching FLT buys mechanical `#check` correspondence, which is the
right call for a map; the safety comes from the mathlib *pin*, not the choice.

There is **one library**, not two. During Layer 0 the definitions lived in a
separate `lean_lib ModularCurveX0` so that a `sorry`-carrying skeleton could not
slow the verified port. Layer 0 landed with no `sorry` at all, so that reason
evaporated and the two were merged: `FLTForHuman/Elliptic/` and
`FLTForHuman/ModularCurve/` now sit side by side under the single
`@[default_target] lean_lib FLTForHuman`. The consequence to keep in mind is that
**work in progress must stay out of the library**: experiment in the gitignored
`Scratch.lean`, and only land code that is green, warning-free and `sorry`-free.

The `spec/` directory is outside every library on purpose, so the consumer cannot
break the build; `lake build` never sees it. Removing the two smoke-test modules
(`FLTForHuman/Basic.lean`, `FLTForHuman/CountableModule.lean`) on 2026-09-21 did
the same for the default target: those two files were the only `import Mathlib`
in the tree and were dragging the whole library into the build plan.

**Verification.** Layer 0 has no `sorry`, so there is no sorry protocol here.

```bash
cd lean
lake build                                 # green, 0 warnings, no sorry
grep -rn 'sorry' FLTForHuman/ModularCurve/ # must be empty
```

**The consumer is the deliverable measure.** `spec/ModularCurveConsumer.lean`
is a standalone Lean file — not imported anywhere, not globbed by any library, so
it cannot break the build — that writes down what Layer 0a is supposed to make
possible. It names declarations that do not exist yet, so it does not compile
today and is not meant to; the error count is the metric:

```bash
lake env lean spec/ModularCurveConsumer.lean 2>&1 | grep -c error
```

It is organised in three zones with different expectations:

- **Zone A `[0a]`** — the objects, the pole-of-`j` lemmas, and the target
  statement `FunctionFieldGeneration N`. This zone must reach **0 errors**.
- **Zone B `[0b]`** — `modularFunctionField`, `ModularPolynomialData`. Stays red
  until the theorem is picked up.
- **Zone C `[--]`** — claims the Definitions layer does *not* deliver: the
  regular coefficients of `jq` (`744`, `196884`) and `TS`. Both are now bound —
  `TS` by Layer 0b, the coefficients by the `jq`-coefficients topic — but by
  modules outside the Definitions layer, so the zone's point stands.

Zone C is the point of the file. It records a finding that only shows up when
the consumer is actually written: **base/004's `j = q⁻¹ + 744 + 196884q + ⋯`
is only half available from Layer 0a.** The pole (`q⁻¹`) is Def-layer
(`coeff_jq_neg_one`, `coeff_jq_of_lt`), but the regular coefficients are not —
`etaProd` is a `∏'` (topological product), so `jNum` is not an evaluable
expression. Writing the consumer therefore answers the "will 0a be used?"
question *before* the 1,000 lines are transcribed: it is used for the pole and for
the ring maps, and it is not used for the classical coefficients. Those were
expected to need the modular-form q-expansion cluster inside the 44-node subtree
§7.1 designates an input; the
[`jq`-coefficients topic](topics/functionFieldGeneration/TOPIC-jq-coefficients.md) then showed that mathlib's
pentagonal theorem reaches them from the Definitions layer alone (via
`PowerSeries.WithPiTopology.tprod_one_sub_X_pow`), and closed Zone C without
touching the cluster. FLT's own proof of these coefficients turns out to be a
standalone 237-line file, not the cluster either — see
[logs/ffg-port.md](logs/ffg-port.md) §8.3.

**Wire test, not just a compile test.** "Green definitions" says nothing about
whether they are *connected*: in the first port `Universal.lean` sat in no import
chain at all, and nothing failed until a round-12 attempt to use `polyEval`. The
consumer's Zone A therefore contains an explicit cross-module composition —
`(qExpand ℚ N jq).coeff (-(N : ℤ)) = 1`, which uses `qExpand` from
`Laurent.lean`, `jq` from `Jq.lean`, and the coefficient formula from
`Laurent.lean`. It is not satisfied by definitions that merely compile.

The consumer also doubles as the FLT correspondence record: each object is
`#check`ed against its pinned FLT signature, so drift is visible in one file. The
playbook calls the friction log the highest-value artifact because it is the one
thing not derivable from the code; this file is where it accumulates.

## 7. Deferred: the theorem (menu, not a plan)

Everything below was the earlier draft of this blueprint. It is kept because it
is measured and `tools/deps`-verified, and because a future session may want one
*topic* of it. It is explicitly not scheduled.

### 7.1 The one big cut, if the theorem is ever attempted

The subtree hanging off `S_ModularCurve_PhiGen_splits_prime_at_slot` is **44 of
the 69 theorem nodes below the capstone** (64% by node count) and **94 files /
11034 lines** with the seed's proof module, `P2M/Util` and the definition modules
counted — about 45% of the cone by lines. It contains the modular-form / Hecke /
q-expansion underbelly (`hasSum_qParam_*`, `qExpansion_*`,
`Def_ModularForm_HeckeOperator`). math/010 §3 calls the modular equation's
splitting "the one genuinely analytic-looking input", so it should be *stated and
stopped*: `sorry`, nothing beneath it ported.

What remains is **24 of the 69 nodes — 48 `Thm_`/`S_` files, 12605 lines** — the
field theory and the strong induction, exactly math/010 §§2, 4, 5, 6, 7. (The 69
account as 44 + 1 + 24: the subtree, the slot itself, the remainder.) The cut also
removes `Def_ModularForm_HeckeOperator` outright.

### 7.2 Verified against `tools/deps`

Re-derived from the doc-site graph FLT's own generator built; the two methods
agree exactly.

- capstone closure **69 theorem nodes**, matching `meta.below`; 144 files, four
  definition modules, 180 citation edges walked.
- `PhiGen.splits_prime_at_slot` closure **44 nodes**, also matching `meta.below`.
- identical file sets between the graph and an import parse (diffs: the seed's
  own `Thm_` vs `S_` module, and `P2M/Util.lean`); **0 of 180 walked cites have a
  zero use count**, so the import over-approximation costs nothing here.
- the two ports' theorem-node sets and definition-module sets are **disjoint**.

```bash
cd tools/deps
python3 explore.py ModularCurve.functionFieldGeneration
python3 explore.py ModularCurve.PhiGen.splits_prime_at_slot
```

### 7.3 The exact remainder manifest

The 24 nodes below the capstone, from `tools/deps`, with the size of each FLT
proof module and its out-degree. `cites = 0` means low **dependency risk** (nothing
must be assumed to state it), not low cost — the playbook's two zero-cite
extremes were a 3-line unfolding and a ~90-line strong induction that took three
rounds. Use the size column for cost.

| node | FLT proof module (lines) | cites |
|---|---|---|
| `minpoly_jqN_map_eq_prod_slots` | 2002 | 8 |
| `jqN_prime_not_mem_full` | 2002 | 8 |
| `jqN_pow_not_mem_adjoin_full` | 995 | 3 |
| `finrank_adjoin_jqN_eq_of_squarefree` | 864 | 8 |
| `finrank_adjoin_jqN_pow_succ_of_not_mem` | 758 | 5 |
| `modularFunctionField_eq_full_of` | 735 | 5 |
| `jqN_div_mem_modularFunctionField` | 735 | 5 |
| `jqN_prime_not_mem_adjoin` | 653 | 8 |
| `full_eq_adjoin_full_div_prime` | 624 | 5 |
| `full_eq_adjoin_primes` | 600 | 5 |
| `relfinrank_full_of_squarefree` | 526 | 6 |
| `dedekindPsi_mul_of_coprime` | 471 | 0 |
| `finrank_adjoin_jqN_prime_of_not_mem` | 348 | 5 |
| `Polynomial.mem_range_of_unique_common_root` | 182 | 0 |
| `Polynomial.mem_range_of_eval_eq_const` | 182 | 0 |
| `Polynomial.irreducible_of_transitive_ringAut` | 182 | 0 |
| `exists_phiIrreducible_of_finrank_eq` | 158 | 2 |
| `exists_monic_evalAtJ_jqN_eq_zero` | 108 | 1 |
| `relfinrank_full_eq_mul` | 81 | 2 |
| `dedekindPsi_of_squarefree` | 69 | 2 |
| `functionFieldGeneration_of_squarefree` | 54 | 5 |
| `dedekindPsi_prime_pow` | 38 | 0 |
| `relfinrank_modularFunctionField` | 31 | 0 |
| `functionFieldGeneration_iff_full_eq` | 22 | 0 |

Two facts a future effort should carry:

- math/010 §9's map is **incomplete**: `Polynomial.mem_range_of_eval_eq_const` is
  on the critical path but not named in the note.
- `functionFieldGeneration_of_squarefree` **must not be dropped**, despite math/010
  §8 calling the squarefree case redundant. The graph shows it cited with use
  count 10 by both `minpoly_jqN_map_eq_prod_slots` and `jqN_prime_not_mem_full`.
  Read fully, §8 is consistent: the *degree-counting* proof is what the slot
  description and the non-membership lemmas consume; the redundancy is the other
  copy. The general lesson is worth keeping: a prose note's "this is redundant" is
  a claim about mathematics, not about the formal dependency graph.

Regenerate rather than hand-maintain:

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

### 7.4 The three rules, if the theorem is attempted

- **R1 — definitions are bottom-up and real.** Never `sorry` a `def`, `abbrev`,
  `structure` or `instance`: a sorry'd *proof* is cited and shows up in
  `#print axioms`, but a sorry'd *definition* is used and is invisible to that
  check.
- **R2 — statements are top-down; proofs may be `sorry`.** Transcribe the 69
  `Theorems/` wrappers (505 lines, median 7, largest 11 — a ready-made skeleton
  whose hypotheses already expose the technical conditions) without the
  `p2m_exact_reverting` delegation.
- **R3 — ground-up only for the significant lemmas.** Use §7.3 for the list.

**The sound conditional capstone is built.** `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean`
proves `functionFieldGeneration_of (h : Inputs)` outright, with `Inputs` a
structure whose fields are the significant lemmas, so the artifact contains no
`sorryAx`. The field set was derived from the 24-node manifest by pruning to the
10 the spine actually consumes; what dropped out is the 13 nodes that occur only
inside the proofs of the 10 (assuming a node discharges its dependencies) plus the
already-proved §2 collapse. Topic 3 discharged two of the ten
(`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow`, now public in
`Defs/Jq.lean`) and the generic-kernel topic discharged a third
(`relfinrank_modularFunctionField`, now public in `Defs/Fields.lean`), so the
structure stands at **7** fields. The field list, with a
one-line reason each, is [logs/ffg-port.md](logs/ffg-port.md) §8.4. Freeze
`Inputs` before Layer 3 starts; input creep is the main threat to such a
deliverable, and a freeze is the only mechanism that catches it.

### 7.5 Sorry protocol and drop list (for reference)

- Every `sorry` carries a **diagnosis**: math/010 section, FLT source and pin, the
  exact failure mode if attempted, the shape of the fix, and what it blocks. The
  first port's one deferral was recoverable in two rounds because it was recorded
  that way; a bare `sorry` would have lost all of it.
- Count sorries from the **build warning count**
  (`lake build 2>&1 | grep -c warning`), not from a grep: `grep`
  matches the word inside this document's own prose. Keep the grep for locating.
- A drop is not verified until `grep -c` has been run and its count recorded. The
  first port lost two rounds to a truncated listing.
- Do not drop `Def_ModularForm_HeckeOperator` by hand — the §7.1 cut removes it
  automatically, and the graph confirms it is absent from the remainder.

### 7.6 Field-theoretic content, and a bottom-up option

[../studies/flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) surveys
what of this cone is field theory and what of that is generic. Three findings bear
on the menu above.

- **The generic core is three lemmas, and mathlib lacks them.**
  `Polynomial.mem_range_of_unique_common_root`,
  `Polynomial.mem_range_of_eval_eq_const` and
  `Polynomial.irreducible_of_transitive_ringAut` — one 182-line file, shipped
  three times as the `S_Polynomial_*` modules — are the engine of math/010 §4–§6:
  descent is the unique-common-root principle, the non-membership lemmas are
  "constant on enough points", and the $`p+1`$ / $`p`$ degree steps are the
  cyclic-automorphism criterion. `grep` over `Mathlib/` finds none of the three,
  and all three are stated over an arbitrary field extension.
  They were the natural first topic of a bottom-up effort, and the layer the spine
  assumed through `Inputs`; the generic-kernel topic has since built them in
  `FLTForHuman/FieldTheory/CommonRoot.lean` (statements verbatim from their
  `Theorems/` wrappers, mathlib-only, with the three concrete instantiations as
  its wire test), so they are in the port now.
- **The §7.3 line counts are a loose upper bound.** The three `S_Polynomial_*`
  files are one file; `jqN_prime_not_mem_full` / `minpoly_jqN_map_eq_prod_slots`
  (2,002 lines each) and `jqN_div_mem_modularFunctionField` /
  `modularFunctionField_eq_full_of` (735 each) are likewise one file each; a
  ~360-line `TS`/`phiAtSeed` prelude is copied into 12 of the 13 remainder files;
  and `dedekindPsi_mul_of_coprime`'s 471-line file spends ~399 lines on a
  resultant development that is not a graph node at all. De-duplicated, 12,420 is
  about 8,200, and about 5,300 with the prelude written once — still a structural
  count, not a proof budget, but a smaller remainder than the headline.
- **The curve layer cannot replace this theorem.** The cone has zero
  `AlgebraicCurve` nodes by design, and the direction is measured, not assumed:
  the modular `IsCurveOver` and Riemann–Roch instances are proved *from* the same
  degree and Φ_p-splitting inputs (`isCurveOver_modularFunctionFieldBar` cites
  `functionFieldGeneration` directly; the other instances cite its corollaries).
  Using the repository's curve theory here would be circular. Survey §7 has the
  dependency table.

The rest of the remainder is instantiated field theory of
$`\mathbb{Q}(j) \subseteq \mathbb{Q}(j_N)`$ and does not generalize: it is the
theorem. So the bottom-up question is not whether the segment's field theory can
be a library — most of it cannot — but whether the 180-line generic kernel is
worth building first, and the survey argues that it is.

## 8. Open questions

- **Will 0a be used?** *Answered: yes, narrowly.*
  `spec/ModularCurveConsumer.lean` is the written-down use, and writing it
  produced a result: the pole of `j` and the two ring maps are Layer 0a
  material, but the classical regular coefficients (`744`, `196884`) are **not**
  available from Layer 0a alone. (The `jq`-coefficients topic later supplied them
  *from* 0a's `etaProd` plus mathlib, so 0a is load-bearing for them after all —
  but only through the topic module, not by itself.) So the honest statement of
  0a's value is narrower than the original pitch: it gives the transport layer
  (`qExpand`, `qTwist`, `coeffEmb`), the pole of `j`, and the ability to *state*
  the target. If that is not enough to justify ~1,000 transcribed lines, the
  consumer is the evidence for saying so, and it should be re-argued before the
  transcription starts.
- **Should `TS` be in scope? — resolved: yes, and built in Layer 0b.** math/010
  §1's `TS K e u`, "the Lean name for `j(uq^e)`", is introduced in the *solution*
  file rather than `Definitions/`, so it needed a deliberate decision. It is in:
  it depends only on 0a, it is ten declarations, it is the note's central
  notation, and without it Consumer Zone C stays unnecessarily red. It is built
  in `Defs/TS.lean` with its provenance recorded as the solution file; the
  reasoning is in [logs/ffg-port.md](logs/ffg-port.md) §8. **Recorded divergence:** FLT keeps `TS`
  inside a per-file `namespace W1` (`ModularCurve.W1.TS`) and never exports it,
  whereas the port puts it at `ModularCurve.TS`; the ten statements are FLT's
  verbatim. The same decision brought in `functionFieldGeneration_iff_full_eq`,
  the 22-line `cites = 0` node from §7.3 that is math/010 §2's collapse and the
  only theorem in Layer 0 — and it is proved, with `#print axioms` showing only
  `propext`, `Classical.choice`, `Quot.sound`.
- **Drift on unchanged mathematics.** The first port's friction list has 12
  entries, two of them pure v4.34.0 API changes on unchanged statements. Layer 0
  touches `LaurentSeries`, `HahnSeries`, `IntermediateField` and `Polynomial`, so
  a comparable list was expected; keep it in the consumer file while it is being
  hit — the playbook calls the friction log the highest-value artifact because it
  is the one thing not derivable from the code. Layer 0 produced twelve entries:
  two API renames, two linter recurrences, two spec-comment bugs the consumer
  caught, one recorded `TS` name divergence, and the non-events (the
  rewrite-search gap and the §4 shape risks all failed to appear).
- **Transcription risk.** The definitions must be transcribed verbatim in shape
  (names, argument order, instances) or `#check` correspondence fails. This is the
  one place where a mistake is silent until much later. It is now mechanically
  checked: `spec/check_flt_statements.py` extracts every port declaration's
  statement and diffs it against the pinned source —
  **150 of 150 identical, 0 mismatched, 0 missing** — and the consumer's
  cross-module compositions remain the runtime wire test.
- **If the theorem is revisited**, the first act is the §2 measurement — one `S_`
  module, named node's proof lines versus helpers — recorded here. Until it is
  made, any line budget for Layers 1–4 is an assumption, not an estimate.
