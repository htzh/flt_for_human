# Porting FLT to mathlib — a playbook

Written after the first port, `#E[n](K) = n²`, whose record is
[logs/card-torsion-port.md](logs/card-torsion-port.md). Read that file for *what* that port
did; read this one before starting the next one. The second effort already has a
blueprint in [PORTING-FFG.md](topics/PORTING-FFG.md).

Everything below is measured from the first port or hit while doing it.

## 1. What the effort cost

| | |
|---|---|
| modules | 13 under `FLTForHuman/Elliptic/` |
| lines written | 3362 |
| declarations | 292 |
| FLT cone consumed | engine 1869 lines / 304 decls; `S_…` 1335 lines / 36 decls |
| rounds | 33 |

Where the 3362 lines went:

| layer | modules | lines | decls |
|---|---|---|---|
| setup | `Basic`, `Universal` | 274 | 41 |
| EDS + `ω` engine | `DivisionPolynomial`, `EDS`, `EllSequence`, `Complement`, `RedInvar`, `Net`, `Omega` | 1207 | 128 |
| multiplication bridge | `MulFormula`, `JacobianMulFormula`, `Bridge` | 717 | 92 |
| counting | `TorsionCard` | 1164 | 31 |

Two things this table says that are worth internalising:

- **Cost tracks mathlib gaps, not FLT line count.** The counting argument is the
  single biggest module (1164 lines) and was the *cheapest* per line: it is
  ordinary field/root algebra with no API archaeology. The expensive part was the
  ~1200 lines of engine, because mathlib dropped the `ω` division polynomial and
  the general complement multiplication property, so those had to be re-derived
  against the parts mathlib *did* keep (`atom`, `atomRel`, `rel`, `normEDS`,
  `complEDS`).
- **A faithful port is not line-for-line smaller.** 3362 written against a cone
  of 3671 lines (3331 once the 340-line 4.30-compat shim is set aside). The saving is not in the volume of mathematics — it is in what never
  had to be written (below) and in the fact that 13 focused modules were written
  instead of 197+ importers inheriting a 1869-line engine.

## 2. Clutter removed, and how each was found

| removed / never written | size | detection method |
|---|---|---|
| `Def_Compat_Mathlib430.lean` (separate file) | 340 lines, 197 importers | we are on the version its renames target, so the unprimed names exist |
| odd-only `smul_surjective` + `card_smul_fiber` (452–550) | 98 | the `_all` versions at 955/1052 have the *same proof*, and `hodd` is unused |
| `smul_surjective_all` + `card_smul_fiber_all` (955–1052) | 98 | byte-identical to the above ⇒ generalise one copy instead of porting two |
| `ΨSq_odd_eq_sq` + `smul_eq_zero_iff_preΨ'_eval` (269–306) | 38 | occurrence count 1: referenced only by themselves |
| `nTorsion` (308–321) + the `solution` bridge (1331–1335) | 20 | it *is* `Submodule.torsionBy` |
| `p2m_exact_reverting` + the `_light` Sol file + 2 `Thm_` files | 44 | we state and prove the theorem directly |
| `evalEval_ωe` (1306) + `polyEval_cusp_ωe` (1329) | 10 | occurrence count 1 |
| inherited import list | ~half of 21 imports | copied from the engine, unused here |

That is ~310 lines of the cone itself (measured spans, not estimates) plus a
340-line compat shim with 197 importers, out of a 3671-line cone.

Two lessons.

**Removing a wrapper is a design decision, not a deletion.** FLT wraps the torsion
in a local `nTorsion` `AddSubgroup` and reconciles with mathlib's
`Submodule.torsionBy` only in the final `solution`. Porting the wrapper would have
meant porting the reconciliation too. Stating every counting lemma over
`Submodule.torsionBy` *from the first lemma* made the capstone a one-line alias.
The cost of that choice was one adaptation — `AddSubgroup.addOrderOf_coe` applied
to `(Submodule.torsionBy …).toAddSubgroup` — against ~30 lines and a whole bridge.
When a target type exists in mathlib, adopt it as the port's interface immediately
rather than mirroring FLT's internal one.

**Deduplicate at the source, not after.** Two FLT declarations with the same proof
should become one general lemma, not two ports. Diff the proofs before porting the
second.

**Caveat, learned the hard way.** I declared `coords` dead code from a
`grep … | head -20` whose output was truncated, and it turned out to be load-bearing
in `exists_double_fiber_card`. Count occurrences (`grep -c`) before dropping
anything; a truncated listing is not evidence.

## 3. Approaches that carried the port

### 3.1 Map to mathlib before writing anything

Build a FLT → mathlib table *first*, and test the entries for **definitional**
equality with `rfl`, not just mathematical agreement. Here `compl₂EDS` is `rfl`-equal
to `complEDS₂`, `addMulSub`/`rel₄`/`net` to `atom`/`atomRel`/`rel` — which is what
makes aliases legal instead of re-proving. The table in
[logs/card-torsion-port.md §3](logs/card-torsion-port.md) is the template.

### 3.2 Trace the capstone top-down with a "nature" column

Walking the dependency tree from the theorem and labelling each node
**plumbing** / **math** / **already mathlib** is what exposed that most of the
height was scaffolding, and it produced the port order. Do this before porting.

### 3.3 Prove for the universal object, then transfer by `aeval`

mathlib has no `IsEllipticSequence (normEDS b c d)`. FLT's trick, reused here for
`normEDS_isEllipticSequence`, `normEDS_mul_complEDS`, `invar₂_normEDS` and
`redInvar_normEDS`: prove the statement for the *universal* EDS over
`MvPolynomial Param ℤ`, where every coefficient is a non-zero-divisor so
cancellation is legal, then push along `aeval`. The transfer lemmas are the
`*_eq_aeval` pair plus the `map_*` lemmas.

If the transfer does not typecheck, it is usually the coercions: `MvPolynomial.aeval`
is an `AlgHom` while the `map_*` lemmas want a `RingHom`.
`simpa only [AlgHom.coe_toRingHom, …] using h` fixes it.

### 3.4 Do not state the goal against an abstract `*_aux` lemma

FLT often ends a computation with `exact foo_aux h`. Ported literally that can blow
the defeq budget — one instance here was a **299 s deterministic `whnf` timeout**.
The fix is to *not* unify the whole goal against the abstract statement: push
everything into normal form first and finish with `field_simp; ring`, supplying the
non-zero hypotheses `field_simp` needs explicitly:

```lean
simp only [polyToField_sub, polyToField_neg, map_add, map_mul, map_pow, map_ofNat,
  polyToField_polynomial, mul_zero, pointedCurve_a₁, pointedCurve_a₃, ψ_two, ψ₂]
have hψ2 : polyToField curve.polynomialY ≠ 0 := by
  simpa [ψᵤ, ψ_two, ψ₂] using ψᵤ_ne_zero two_ne_zero
field_simp
ring
```

Corollary: when a build suddenly takes minutes, suspect a defeq check inside
`exact`/`convert`, not the tactics that came before it.

### 3.5 Monomorphic helper lemmas close the rewrite-search gap

The single most repeated obstacle. mathlib's *generic* `map_sub`, `map_neg`,
`Jacobian.comp_smul`, `Jacobian.map_neg` do **not** fire under `rw`/`simp` when the
function argument leaves implicit instances unresolved, even though the pattern
looks identical:

```lean
-- works:
example (P : Fin 3 → Poly) : polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u
-- silently makes no progress:
example (P : Fin 3 → Poly) : polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) := by
  rw [Jacobian.comp_smul]   -- "did not find an occurrence of ⇑?f ∘ (?u • ?P)"
```

The remedy is a monomorphic helper proved by `exact`, which then rewrites fine:

```lean
lemma polyToField_comp_smul (P : Fin 3 → Poly) (u : Poly) :
    polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
  Jacobian.comp_smul polyToField P u
```

Reach for this the moment a `rw` or `simp only` reports "no progress" on a goal you
can see the pattern in.

### 3.6 Prove the equality once, then rewrite through it

A relative of 3.5: when a lemma is stated with a different but definitionally equal
head (`Jacobian.map curvePoly polyToField` vs `curveField`), `rw` cannot match it.
Prove the identification once by `rfl` and rewrite *through* it so the target
becomes syntactically matchable:

```lean
lemma jacobian_map_curvePoly_polyToField :
    Jacobian.map curvePoly polyToField = curveField := rfl
-- then: rw [dblXYZ_Z, ← jacobian_map_curvePoly_polyToField, Jacobian.map_dblZ …]
```

Trying to `change` the goal to the unfolded form instead can cost a several-minute
`whnf` (it did here).

### 3.7 `rw` and `simp_rw` do not unfold `abbrev`s

Repeatedly bit us (`smlPoly`, `smlRing`, `smlField`, `rel₄`, `net`, `addMulSub`).
Use `change` to state the unfolded goal, or `simp only [name]`.

### 3.8 Pick mathlib's API as the port's interface

See §2: `Submodule.torsionBy` from the first lemma. The same applies to
`Submodule.mem_torsionBy_iff`, `AddSubgroup.card_bot`, `Cubic.*`,
`twoTorsionPolynomial` — mathlib usually already has the shape, and adopting it
early is what keeps the capstone short.

### 3.9 Iterate in a gitignored scratch file

`lake env lean Scratch.lean` (~3 s) against `lake build <module>` (~5 s) and a full
`import Mathlib`-wide build (~150 s). Put experiments, `#check` probes and
type-hunting in `Scratch.lean`, which `lean/.gitignore` excludes. The single most
useful probe when a rewrite or instance fails is a `#check @name` on the lemma you
think you are using.

### 3.10 Keep the friction log *while* you hit friction

The API-drift list in §4 was only cheap to write because it was appended to during
the port. It is the highest-value artefact for the next effort — more than the
module list, because the module list is derivable from the code and the drift list
is not.

### 3.11 Bound every build; a heartbeat blow-up is not a slow build

**This block is the first thing in every work order.** Build time is the one
unbounded cost in this work: a session can lose minutes to a build that will
never finish, and the loss compounds because it re-runs. Copy the following
verbatim to the top of each new `TOPIC-*.md`:

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type (`DFunLike.coe` unfolds without
>   bound) — restate it over the concrete function instead.

The measurements behind it, on this machine with mathlib prebuilt (`v4.34.0`):

| command | expected |
|---|---|
| `lake env lean <module>` on a green port module (~200–350 lines) | **~4 s** |
| `lake build <module>` with dependencies cached | **~2–5 s** |
| `lake build` of the whole `FLTForHuman` after one file edit | under a minute |
| a `whnf`/heartbeat blow-up at the default cap | **~15–20 s**, then an error |

The failure mode is not a long build: the default 200 000-heartbeat cap fires in
under 20 s. The trap is **raising `maxHeartbeats`** — it converts an 18-second
error into a multi-minute wait for the same non-termination. Never do it to "let a
build finish". Instead:

- run every build under a bound (`timeout 60 lake env lean <file>`) and treat
  non-return at 60 s as a blow-up;
- on a `whnf`/heartbeat timeout, find the offending declaration by bisection
  (comment it out; use `set_option diagnostics true` in a *copy*), not by waiting;
- the usual cause is a lemma quantified over `FunLike F ℍ ℂ` (or another
  higher-order instance) instantiated at a bare function type, which unfolds
  `DFunLike.coe` without bound. The worked example is in
  `topics/phiGenSplitting/TOPIC-r1-kernel.md`'s header:
  `UpperHalfPlane.qExpansion_coeff_unique` cost 5.1M `DFunLike.coe` reductions at
  `ℍ → ℂ`, and the fix was to restate its content over the concrete function, not
  to raise the cap.

## 4. v4.34.0 drift checklist

Renames and shape changes hit during this port, with the replacement:

| old / expected | v4.34.0 |
|---|---|
| `if_pos h`, `if_neg h` | `ite_eq_left h`, `ite_eq_right h` |
| `dif_neg h` | `dite_eq_right h` |
| `Polynomial.finite_setOf_isRoot` | `Polynomial.finite_setOfPred_isRoot` |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `Affine.Nonsingular x y` | `W.toAffine.Nonsingular x y` (curve is explicit) |
| `Submodule.card_bot` | does not exist — use `AddSubgroup.card_bot` |
| `Submodule.mem_torsionBy_iff.mp` | takes explicit args: `(… _ _).mp` |
| `mul_cancel_left_mem_nonZeroDivisors` | does not exist — `mul_left_cancel₀` in a domain |
| `Jacobian.map` | a *separate* def from `WeierstrassCurve.map` (they are defeq) |
| `Affine.Point.some_ne_zero` | does not exist — `cases` on the equality |
| `ext i` on `Fin 3 → MvPolynomial …` | recurses into `MvPolynomial.ext`; use `funext i` |
| `nTorsion n` (`n : ℕ`) | `Submodule.torsionBy ℤ M n` takes `n : ℤ`, so `↑2` ≠ `2` syntactically |
| `HahnSeries.embDomain_notin_range` | `HahnSeries.embDomain_of_notMem_range` (same signature, drop-in) |

Also: `Submodule.torsionBy.zmodModule` supersedes FLT's `instModuleZModTorsionBy`,
and `(W.map f).IsElliptic` is all a base-change `IsElliptic` instance needs.

Two non-rename facts from the definitions layer (§7), both warning-related:

- **Unused section variables are auto-omitted.** A `def` whose body never
  mentions a section variable does not take it as an argument, so a declaration
  written under `variable (N : ℕ) [NeZero N]` can come out with no `[NeZero N]`
  (this happened to `modularFunctionFieldFull`/`divisorExpansions`). Transcribe
  verbatim and check the signature; do not "restore" the variable.
- **`linter.style.haveILetI` fires on `haveI` in a `Prop` goal,** even when the
  instance is genuinely used. If the instance came from `intro`/`rintro`, the
  `haveI` is redundant — delete it. If it did not, prefer `have` (typeclass
  search still finds it for a class-typed local). A `haveI` inside a `def`'s
  term is not flagged and can stay.

## 5. Checklist for the next port

1. **Measure the cone first** — files, lines, declarations, importers. Decide from
   those numbers whether the port is a port, a re-derivation, or a both.
2. **Build the FLT → mathlib table** and test each entry with `rfl` where you hope
   for definitional equality.
3. **Trace the capstone top-down**, labelling plumbing / math / already-mathlib.
4. **Adopt mathlib's types as the interface** from the first declaration.
5. **Port bottom-up, build after every module.** Do not batch modules before
   building; a broken layer is much cheaper to bisect than a broken tree.
6. **Grep -c before dropping anything.** Never trust a truncated listing.
7. **Diff before porting a second similar lemma** — generalise one instead.
8. **Expect the rewrite-search gap (§3.5) and the `abbrev` gap (§3.7).** They are
   not bugs in your proof; they are a tactic-level mismatch.
9. **Watch the build clock.** A jump from seconds to minutes is a defeq blowup; go
   looking for an `exact`/`convert` against an abstract statement.
10. **Keep the friction log current**, and at the end split the record from the
    playbook the way this pair is split: one file says what *this* port did, the
    other says what *the next* port should know.
11. **Make faithfulness mechanical when the source is pinned.** Diff the ported
    statements against the source, spelling each public declaration's binders as
    its chosen source does (in practice the `Theorems/` wrapper, §7.4), make the
    consumer do a cross-module composition rather than only `#check`s, and confirm
    `#print axioms` is clean. See §7.4.

## 6. Open questions

Recorded honestly, because they are the parts of the method that are not settled:

- **Hybrid vs faithful is a per-layer choice, and we only ever tested one layer
  mix.** Here the engine was re-derived and the bridge was ported. Nobody has
  measured what happens when mathlib absorbs the *core* but not the periphery, or
  the reverse — which is exactly the situation
  [PORTING-FFG.md](topics/PORTING-FFG.md) describes for the second port.
- **Round counts are not a good cost model.** They depend on how often the agent
  stalled on a defeq or a name. The line and declaration counts in §1 are the
  stable measurements.
- **Nothing here was validated against a third-party port**; the "removed clutter"
  numbers are what this effort avoided writing, measured from FLT's own files, not
  an independent audit of whether the dropped items were truly dead.

## 7. Porting a definitions layer — the `functionFieldGeneration` experience

Layer 0 of [PORTING-FFG.md](topics/PORTING-FFG.md) was the second port and the first
that was *definitions only*: 137 declarations across nine modules, from
`qExpand`/`coeffMap`/`qTwist` to the two function fields, `TS` and the §2
collapse. Its record is [logs/ffg-port.md](logs/ffg-port.md). The reusable part:

### 7.1 Principles for math clarity

The port exists for these, so where they conflict with convenience, they win.

- **A module is a mathematical role, not a source file.** FLT splits by artifact
  kind (`Def_`/`Thm_`/`S_`); split by concept instead. FLT's
  `Def_ModularCurve_X0.lean` covers four subjects and became four modules.
- **Reading order is dependency order.** A reader should be able to walk the
  directory linearly. Each module header says: its subject, the FLT source and
  pin, and what it assumes from earlier modules.
- **Monomorphic helpers are documentation.** When a proof relies on a generic
  mathlib lemma in a specific form, give that form a name and a docstring (§1,
  §3.5). But *measure before assuming you need them*: the rewrite-search gap was
  predicted to dominate this layer and never appeared, because FLT proved every
  one of those lemmas coefficientwise and its own `[simp]` coefficient lemmas
  (`qExpand_coeff_mul`, `coeffMap_coeff`, `qTwist_coeff`, …) were already the
  named bridges. Write the helper the moment a `rw` reports no progress, not
  before.
- **Adopt mathlib's names where mathlib has them; keep FLT's where it does not.**
  `LaurentSeries`, `HahnSeries`, `IntermediateField`, `PowerSeries` are
  mathlib's; everything else in this cone is FLT's, kept verbatim so `#check`
  comparison against the pin stays mechanical. Say which is which in the header.
- **Docstrings carry the mathematics.** A declaration whose name does not state
  its content gets a one-line gloss; a construction (`qExpand`, `jq`, `qTwist`)
  gets a sentence saying what the object *is*.
- **No self-consumed lemmas, and count before dropping.** A lemma whose only
  consumer is itself is not ported, and a dropped item needs a `grep -c` count,
  not an impression.
- **Freedom to reorganize**, with two constraints: FLT's declaration names stay,
  and the consumer's zones keep passing.

### 7.2 Overlap with the first port

At the *lemma* level there is none. The two cones share zero theorem nodes and
zero definition modules, and nothing in `FLTForHuman/` is imported, reused or
renamed. Do not go looking for EDS, division-polynomial or `polyToField`
analogies — they are not there.

At the *process* level there is a lot, and §3–§5 carry it. Two traps worth
repeating:

- **The `Universal.lean` lesson.** A module can be ported, build green, and sit
  in *no import chain at all*; nothing fails until a later attempt to use it. So
  the consumer must contain a cross-module **composition**, not only `#check`s —
  and a `sorry`-terminated composition is not enough either. The wire test here
  is `(qExpand ℚ N jq).coeff (-(N : ℤ)) = 1`, needing `qExpand` from one module
  and `jq` from another, and it is discharged by a real proof.
- **Do not re-import the whole library.** Two `import Mathlib` files took the
  first port's default build from 2086 to 8936 planned jobs. Keep every import
  specific, and keep the definitions library separate from the verified one.

### 7.3 The calibration

| layer | declarations | budgeted rounds | actual |
|---|---|---|---|
| 0a | 68 | 20 | **1** |
| 0b | 69 | 4 | **1** |
| topic (`jq` coefficients) | 24 (2 public + 22 `private`) | 4 | **1** |
| topic (conditional capstone) | 29 (5 public + 24 `private`) | 4 | **1** |
| topic (interface tier) | 9 public added to 2 modules; `Spine` −4 | 2 | **1** |
| topic (generic kernel) | 3 public + 3 instantiations; 1 peel in `Fields`; `Spine` 8 → 7 | 2 | **1** |

Transcribing a pinned, definitional source with the statements dictated is
cheap. The cost lives in *shape* mismatches — typeclass, coercion, defeq,
renamed API — not in volume, so budget in "number of shape risks", not lines.
Both layers' named shape risks failed to materialize; the only real friction was
three renames and two spec bugs the consumer caught by being executed.

The `jq`-coefficients topic is the first *proof* data point, and it was cheap for
a different reason: mathlib had absorbed the hard part (`etaProd` *is* the
topological product that `tprod_one_sub_X_pow` equates to `pentagonalSeries`), so
the whole job was a finite low-order coefficient computation. The lesson that
covers all five rows: **expense is the route's distance from mathlib, and a topic
must be priced against the actual FLT proof of its specific statements — not
against the subtree those statements appear under.** That topic's plan assumed the
latter and overpriced the work by roughly 50×: FLT's real proof of the `744` /
`196884` coefficients is a standalone 237-line file, while the 11k-line cluster the
plan cited is not on the route at all. Locate the analogous FLT declaration first
(it may be a small `S_`/`Thm_` file, as here), and only then quote a size. See
[logs/ffg-port.md](logs/ffg-port.md) §2c, §8.3.

**The conditional capstone is the cheapest way to a theorem-shaped artifact.**
`Spine.lean` proves `functionFieldGeneration_of (h : Inputs)` outright — no
`sorryAx` — by porting only FLT's *glue* (the strong induction and its helper
block, ≈1:1 with the pin's ≈373 lines) and bundling the significant lemmas as the
fields of a structure. Two properties make it worth doing before any of those
lemmas: `#print axioms` comes back clean, so the architecture is checked rather
than asserted; and each field is a first-class named hypothesis, so the remaining
work becomes an ordered list instead of a subtree. When a theorem's proof is a
long induction over largely independent inputs, build this artifact first. Keep
the structure frozen once it lands — input creep is what would silently weaken
it — and keep the capstone *conditional*: do not discharge fields opportunistically.
See [logs/ffg-port.md](logs/ffg-port.md) §2d, §8.4.

**Exposing an interface is cheap when the interface is small — measure it first.**
The interface-tier topic added nine public lemmas that carry 520 of the cone's 946
≥5-indegree weight, and every one transcribed on the first try: they are 5–50-line
leaves, and FLT proves them precisely because downstream code depends on them. The
generalizable move is to read the dependency graph *before* choosing the next
work: the gain test is about what a port buys, and outbound indegree is a
measurable proxy for that. Two cautions from the same topic: an indegree count is
global (a node can be load-bearing elsewhere while irrelevant here — check it is
in the cone), and the *public interface* can be split across namespaces in the pin
(`coeffEmb_qExpand` exists both as a wrapper with explicit `L` and as a `W1` copy
with implicit `K`), so a statement checker must be told which copy is the
interface. See [logs/ffg-port.md](logs/ffg-port.md) §2e.

**A mathlib-absent generic proof is still cheap when the pin dictates it.** The
generic-kernel topic is the clearest case yet: three lemmas that are *not* in
mathlib, with real mathematical content, and all three transcribed on the first
try (the only edits were `private` → public). This is the strongest evidence for
the "statements dictated ⇒ cheap" rule, because nothing about the source being
*ordinary definitions* was doing the work — the pin's proofs were simply good
proofs against the same mathlib API. The topic's actual cost was not the lemmas
but their **wire test**: designing a concrete instantiation of the
cyclic-automorphism lemma that all hypotheses accept took longer than the lemma
itself, because over `ℚ ⊆ ℂ` the only nontrivial base-fixing automorphism is
complex conjugation and a nontrivial cycle then needs a cubic with one real root
and explicit cube roots, which mathlib lacks. Budget a generic lemma's
*instantiation*, not its transcription. See [logs/ffg-port.md](logs/ffg-port.md)
§2f.

### 7.4 Make faithfulness mechanical

With a pinned source, faithfulness is checkable rather than a matter of trust.
Three cheap instruments, all used here:

- a checker that diffs every ported **statement** against the pin
  (`spec/check_flt_statements.py`; 150 of 150 identical at the first effort's
  close, 244 with the Φ_p cone) — and verify the checker
  itself with a deliberately mutated statement. When a declaration is *ours*
  rather than transcribed (`coeff_jq_zero` / `coeff_jq_one`, `Inputs`,
  `functionFieldGeneration_of`) or is a *public promotion of an FLT-private* name
  (`Tight` / `Gen` / `Hall`), add it to an explicit exemption list with the reason,
  so "0 missing" keeps meaning something; a declaration that is merely unlisted
  still fails the check. Keeping the auxiliary block `private` is what makes this
  list short. Two refinements from the interface-tier topic: normalise the pin's
  namespace qualification away (the `Theorems/` wrappers write `ModularCurve.`
  everywhere) and, when a name exists in more than one pin namespace, order
  `SOURCES` so the *interface* copy wins. The third refinement is the one that
  recurred through the cone-algebra topics (recorded from T7's log §7.3): because
  the diff is **textual, not elaborated**, a public declaration must spell its
  binders exactly as the copy the checker will match — in practice the
  `Theorems/` wrapper, not the `S_` file. The two can bind the same statement
  differently (`coeffEmb_qExpand`'s explicit `L` against the `W1` copy's implicit
  `K`; `aeval_jqN_toAdjoin` and `minpoly_jqN_eq` written with the `S_` file's
  section variables where their wrappers are explicit, which is what the checker
  flagged in T12). The file builds either way, because the *elaborated* types
  agree; only the checker notices. So when a wrapper exists, take the signature's
  binders from the wrapper in the first place and use the `S_` file only for the
  proof body;
- a **consumer** outside every library, whose error count is the deliverable
  metric and whose cross-module composition is the wire test;
- `#print axioms` on the layer's result, to confirm no `sorryAx` crept in
  (here: only `propext, Classical.choice, Quot.sound`).

## 8. Directory layout: one directory per theory

§7.1 states the module-level rule ("a module is a mathematical role, not a source
file"). This is its directory-level companion, and it came out of the
`functionFieldGeneration` rename.

A directory holds **one theory**, with that area's shared vocabulary outside it:

```
<Area>/
  Basic.lean        -- setup shared by every theory in the area, mathlib-only
  Defs/*.lean       -- shared vocabulary, when it is big enough to need a directory
  <Theory>/*.lean   -- one theory's modules, whatever role each plays in its proof
```

**The second theory is what triggers the split, not the first.** `ModularCurve/`
grew `Defs/` beside `FunctionFieldGeneration/` when its theory modules — `Spine.lean`
among them — stopped reading as subjects and started reading as positions in one
proof. `Elliptic/` has not: it holds one theory, `Basic.lean` is its only shared
module, and of the other twelve only `Bridge` is a role-flavoured name (`Net`,
`Omega`, `RedInvar`, `Complement` name objects). So no move was made there, and
making one now would be churn — the collision the rule prevents only exists once
there are two theories to collide. (One *module* was renamed anyway, for the
subject-naming reason rather than the collision one: `Fiber.lean`, which had been
named after the fibre device, became `TorsionCard.lean`, matching the name the port
order had already given that content.)

When the split *is* warranted it is mechanical: rename the file, fix the modules
that import it, update the record's module table. Nothing else refers to a module
path, and the lakefile globs the whole namespace with `.submodules`, so a new
subdirectory needs no build-file change. In the first port the import graph is
linear (`Basic → Universal → … → Bridge → TorsionCard`), so a single rename
touches at most one import line plus that module's successor.

One caveat the rename does not fix: **docstrings carry the same role/subject
distinction as filenames**, and they rot faster. `TorsionCard.lean`'s header still
said "the counting argument, part 1" and listed two FLT source sections long after
the whole argument had landed in it. Re-read a module's header when its content
stops matching its name — and again after a rename.
