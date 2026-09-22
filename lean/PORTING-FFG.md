# Blueprint: `ModularCurve.functionFieldGeneration` — Layer 0

**Status: Layer 0 agreed as the current goal.** This file previously planned a
sorry-bounded port of the whole theorem; that is now deferred and kept only as a
menu in §7. The scope decision and its evidence are §2.

Companion records:

- [math/010](../math/010-function-field-generation.md) — the mathematics. It is
  the source of truth for *what the proof says*; this file says *what we build*.
- [logs/card-torsion-port.md](logs/card-torsion-port.md) — what the first port
  did: `#E[n](K) = n²`, 13 modules, 3362 lines, capstone green.
- [porting-playbook.md](porting-playbook.md) — what the next port should know.
  Its measurements are used throughout this file.

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

## 3. Layer 0: sources and scope

| source | lines | what it gives |
|---|---|---|
| `Definitions/Def_ModularCurve_X0.lean` | 348 | `qExpand`, `jq`, `jqN`, `dedekindPsi`, the two fields |
| `Definitions/Def_ModularCurve_LaurentCoeff.lean` | 144 | coefficient change of the Laurent series |
| `Definitions/Def_ModularCurve_PhiGen.lean` | 309 | the `q`-twist, the slot vocabulary |
| `Definitions/Def_ModularForm_HeckeOperator.lean` | 204 | **not ported** — belongs to the §7 cut |

Split into two sub-scopes, because they have different consumers:

- **0a — the computable series objects (the deliverable).** `qExpand`, `coeffMap`,
  `coeffEmb`, `qTwist`, and the explicit series `jq` with its coefficient lemmas.
  These are what makes the library *usable*; nothing here needs the theorem.
- **0b — the field and polynomial vocabulary (only if the theorem is picked up).**
  `ModularPolynomialData`, `modularFunctionField`, `modularFunctionFieldFull`,
  `FunctionFieldGeneration`, `conj`, `phiProd`, `EvalSymm`, `PhiGenDescends`, …

Ship 0a. Hold 0b: it is definitions and therefore cheap, but its only consumer is
the deferred theorem, so porting it now would be building the map before deciding
to read it.

## 4. Layer 0a: object inventory

The point of this table is the *order*: it is dependency order, and the module
split follows it. Line numbers are the declaration's line in the pinned source.

### `ModularCurveX0/Defs/Laurent.lean`

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

### `ModularCurveX0/Defs/Twist.lean`

The unit twist. Source: `Def_PhiGen` 18–96.

| FLT source | declaration | mathematical content |
|---|---|---|
| `Def_PhiGen:18` | `qTwistFun` | rescale the coefficient of `q^k` by `u^k`: `q ⟼ uq` |
| `Def_PhiGen:25`–`35` | `qTwistFun_coeff`, `support_qTwistFun`, `qTwist` | coefficients, support, packaged as a ring endomorphism |
| `Def_PhiGen:66`–`90` | `qTwist_coeff`, `support_qTwist`, `_single`, `_one_apply`, `_qTwist`, `_injective` | functoriality and injectivity |
| `Def_PhiGen:96` | `qTwist_qExpand` | the composite is `q ⟼ uq^N` |

### `ModularCurveX0/Defs/Jq.lean`

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

## 5. Layer 0b: object inventory (held)

Recorded for the future, not to be built now. Source: `Def_X0` 215–348,
`Def_PhiGen` 111–309.

- **fields** (`ModularCurveX0/Defs/Fields.lean`): `ModularPolynomialData` (215),
  `modularPolynomialDataOne` (225), `FunctionFieldGeneration` (233),
  `functionFieldGeneration_one` (237), `modularFunctionField` (250) with
  `jq_mem`/`jqN_mem`/`_one`/`adjoin_jq_le`, `jGen` (268), `evalAtJGen` (270),
  `algebraMap_comp_evalAtJGen` (273), `toAdjoin` (287) + `_monic` (289),
  `divisorExpansions` (297) + `mem_` (301), `modularFunctionFieldFull` (305),
  `jqd_mem_full` (309), `modularFunctionField_le_full` (313),
  `full_degeneracy_le` (321), `full_degeneracy_map_le` (330).
- **slot vocabulary** (`ModularCurveX0/Defs/PhiGen.lean`): `cosetSubst` (111),
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
problem in reverse.

## 6. Layout, build, and verification

```
lean/ModularCurveX0/
  Defs/Laurent.lean     -- §4
  Defs/Twist.lean       -- §4
  Defs/Jq.lean          -- §4
  Check.lean            -- #check correspondence against FLT (see below)
  -- held for 0b: Defs/Fields.lean, Defs/PhiGen.lean
```

Namespace `ModularCurve`, so declaration names match FLT's and math/010's §9 map
applies unchanged. This is a **trade**, worth recording: the first port used its
own namespace (`FLTForHuman.Elliptic`) so its names could never collide with
mathlib's. Matching FLT buys mechanical `#check` correspondence, which is the
right call for a map; the safety comes from the mathlib *pin*, not the choice.

Add a second library so the default target stays the verified port:

```lean
-- lakefile.lean -- leave @[default_target] lean_lib FLTForHuman alone.
lean_lib ModularCurveX0 where
  globs := #[.submodules `ModularCurveX0]
```

Two targets is also two build clocks: anything in the default target would be
re-elaborated on every iteration of the verified library, whose seconds-warm
build is a property worth keeping. Add a pointer in `lean/README.md` naming
`ModularCurveX0/` as a definitions library distinct from the verified port.

**Verification.** Layer 0 has no `sorry`, so there is no sorry protocol here.

```bash
cd lean
lake build                        # FLTForHuman: green, 0 warnings, no sorry
lake build ModularCurveX0         # 0a: green, 0 warnings, no sorry
grep -rn 'sorry' ModularCurveX0/  # must be empty
```

**Wire test, not just a compile test.** "Green definitions" says nothing about
whether they are *connected*: in the first port `Universal.lean` sat in no import
chain at all, and nothing failed until a round-12 attempt to use `polyEval`. So
`Check.lean` must do more than `#check` the names in isolation — it must state at
least one result that *composes* two modules, across a module boundary. The
natural one: `coeffEmb K (qExpand ℚ N jq) = TS`-style composition, i.e. apply
`qExpand` from `Laurent.lean` on `jq` from `Jq.lean` and state the coefficient
formula from `Twist.lean`. That exercises the import graph and the typeclass
assumptions once before anything is built on them.

`Check.lean` is also where the FLT correspondence is recorded: each object
`#check`ed side by side with its FLT signature, so drift is visible in one file.

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

A sound conditional capstone — `functionFieldGeneration_of (h : Inputs)` proved
outright, with `Inputs` a structure whose fields are the significant lemmas — is
the right headline artifact, because it contains no `sorryAx`. Derive the field
set mechanically: put all 24 nodes in, build, then discharge and remove fields
one at a time, so the structure is honest at every instant. Freeze `Inputs` once
Layer 3 starts; input creep is the main threat to such a deliverable, and a
freeze is the only mechanism that catches it.

### 7.5 Sorry protocol and drop list (for reference)

- Every `sorry` carries a **diagnosis**: math/010 section, FLT source and pin, the
  exact failure mode if attempted, the shape of the fix, and what it blocks. The
  first port's one deferral was recoverable in two rounds because it was recorded
  that way; a bare `sorry` would have lost all of it.
- Count sorries from the **build warning count**
  (`lake build ModularCurveX0 2>&1 | grep -c warning`), not from a grep: `grep`
  matches the word inside this document's own prose. Keep the grep for locating.
- A drop is not verified until `grep -c` has been run and its count recorded. The
  first port lost two rounds to a truncated listing.
- Do not drop `Def_ModularForm_HeckeOperator` by hand — the §7.1 cut removes it
  automatically, and the graph confirms it is absent from the remainder.

## 8. Open questions

- **Will 0a be used?** The justification for Layer 0 is that computable `jq`,
  `qExpand`, `qTwist` serve base/004's j-invariant claims and math/010's
  q-expansion statements. If no concrete use appears, 0a is organization without
  a consumer and should be re-argued. The first thing to write, therefore, is the
  `#eval`/`#check` list that 0a is supposed to make possible.
- **Drift on unchanged mathematics.** The first port's friction list has 12
  entries, two of them pure v4.34.0 API changes on unchanged statements. Layer 0
  touches `LaurentSeries`, `HahnSeries` and `IntermediateField`, so expect a
  comparable list; keep it in `Check.lean` while it is being hit — the playbook
  calls the friction log the highest-value artifact because it is the one thing
  not derivable from the code.
- **Transcription risk.** The definitions must be transcribed verbatim in shape
  (names, argument order, instances) or `#check` correspondence fails. This is the
  one place where a mistake is silent until much later; the §6 wire test and the
  side-by-side `Check.lean` are the mitigations.
- **If the theorem is revisited**, the first act is the §2 measurement — one `S_`
  module, named node's proof lines versus helpers — recorded here. Until it is
  made, any line budget for Layers 1–4 is an assumption, not an estimate.
