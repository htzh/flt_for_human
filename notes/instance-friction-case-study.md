# Instance friction, worked: `KernelBaseChange` as a mechanical case study

`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean` (1,414 lines, 244 s
to build at the frozen 4,000,000-heartbeat cap) is the worked example for the
"profile → locate → brick → verify" loop of
[porting-playbook.md](../lean/porting-playbook.md) §6 and
[lean-build-cost.md](lean-build-cost.md) §10. It is big enough to be
representative and small enough to run end to end. This note records the method,
the measured result, and — the point of writing it down — the **failure cases** of
the mechanical procedure, because each one cost a round.

> **Update — the 768 block is fixed; module 244 s → 71 s.** A fresh look at
> `kw_surge_hgf4_bcIota₁_compat` (see
> [The fix that worked on 768](#the-fix-that-worked-on-768-positive)) removed the
> four `show`s that the diagnosis below correctly identified, by replacing each
> with explicit `rw` steps (`AlgHom.comp_apply`, `AlgHom.restrictScalars_apply`,
> then the named generator lemma) and naming the structural map
> `kw_surge_hgf4_tensorUnit`. A clean `lake build` of the module goes from
> **244.1 s → 71.1 s** (CPU 280 s → 101 s), and the one-run low-cap probe drops
> from six blow-up sites to two — both in `bcTensorFracIotaSeam`, which is the
> genuine remaining `FractionRing` diamond. The lesson is that a `show` over an
> `abbrev`/`baseChange` carrier is not a local cost: removing it sped up *later*
> declarations as well (the positive of FC-6).

The loop is three tools:

```bash
cd tools/deps
python3 instance_hotspots.py --module FLTForHuman.X.Y --profile                 # hot classes
python3 instance_hotspots.py --module FLTForHuman.X.Y --at 205 --trace \
        --class DistribMulAction                                                # the goals
python3 instance_hotspots.py --module FLTForHuman.X.Y --at 205 --lowcap 2000    # failing sites
python3 friction_scan.py --scope WeierstrassCurve --synth-cap 2000              # a whole area
```

`instance_hotspots.py` copies the module to `lean/tmp/`, inserts the options,
runs `lake env lean` on the copy (no `.olean`, no cascade), and parses the
output. Every run writes its raw output to `lean/tmp/_hotspots_<module>.log`.

## What the data says

Scoped to one declaration (`set_option profiler true in`, see FC-2), the
profiler attributes the cost to a *class*. For
`ModularCurve.kw_surge_hgf4_bcTensorFracIotaSeam` the baseline top classes were:

| class | ms | # |
|---|---:|---:|
| `GroupWithZero` | 3561 | 6 |
| `DistribMulAction` | 2307 | 47 |
| `HDiv` | 1738 | 2 |
| `Inv` | 1367 | 2 |
| `Nontrivial` | 1312 | 2 |
| `DivisionCommMonoid` | 722 | 2 |
| `StrongRankCondition` | 638 | 1 |
| `IsFractionRing` | 470 | 4 |
| `Algebra` | 465 | 22 |

Two shapes stand out: a few *expensive* searches (`Inv`, `Nontrivial`,
`GroupWithZero`, 0.3–0.6 s each) and a long tail of *repeated cheap* ones
(`DistribMulAction`, 47 × ≈ 49 ms). The trace names the goals exactly —
`Nontrivial T'`, `Inv FrT`, `Inv FrT'`, `HDiv FrT FrT FrT`, `GroupWithZero FrT`,
`DivisionCommMonoid FrT`, `StrongRankCondition FF'`, `IsFractionRing T FrT` —
all on the carriers `FF`, `FF'`, `T`, `T'`, `FrT`, `FrT'` built from
`(E₀⁄F).toAffine.FunctionField ⊗[F] F'`.

## The bulk batch, and how much it bought

Per the "do not try for the minimal set" rule, the first batch added seven bricks
at once, right after the carrier `let`s. Three elaborated; four did not (FC-5).
The three kept are stated at the unfolded `map` spelling of `baseChange`:

```lean
haveI hT'_nontrivial : Nontrivial T' :=
  inferInstanceAs (Nontrivial ((E₀'.map (algebraMap R₀ F)).toAffine.FunctionField ⊗[F] F'))
haveI hFF'_strongRankCondition : StrongRankCondition FF' :=
  inferInstanceAs (StrongRankCondition (E₀'.map (algebraMap R₀ F)).toAffine.FunctionField)
haveI hFrT_isFractionRing : IsFractionRing T FrT :=
  inferInstanceAs (IsFractionRing ((E₀.map (algebraMap R₀ F)).toAffine.FunctionField ⊗[F] F')
    (FractionRing ((E₀.map (algebraMap R₀ F)).toAffine.FunctionField ⊗[F] F')))
```

Measured on the declaration: `Nontrivial` 1312 → 483 ms, `StrongRankCondition`
638 → gone, `Inv` 1367 → 678, `GroupWithZero` 3561 → 1891, `IsFractionRing`
470 → gone; top-class total **≈15.1 s → ≈10.6 s** (−30 %).

Measured on the module: **242.3 s → 242.7 s**. Nothing. The declaration is only
one of several heavy ones; the prefix through line 753 is 57 s and the tail
768–1386 is the other ≈185 s. This is the most important number in the note:
*a 30 % local win is invisible at module scale, so the module build is the only
honest acceptance test.*

## Failure cases of the mechanical procedure

Each of these was hit while running the loop; each is a rule now.

**FC-1 — `-Dtrace.profiler` `[Elab.command]` times double-count.** The first
profiling run reported `local notation "χE" …` at 43.8 s and a term parser at
42.0 s in a prefix that wall-clocks 57 s. Nested async spans are counted at every
level, so `[Elab.command]` is useless for ranking. Use the in-file
`set_option profiler true`; its `typeclass inference of X took Nms` lines are the
trustworthy leaf signal.

**FC-2 — an unscoped profiler attributes the whole prefix to the declaration.**
`set_option profiler true` after the imports profiles every command from line 1.
The first "declaration" report was therefore mostly the *preceding* declarations'
cost, and the batch looked ineffective. The fix is the `in` form, which is what
the tool now inserts:

```lean
set_option profiler true in
set_option profiler.threshold 10 in
theorem kw_surge_hgf4_bcTensorFracIotaSeam … := by …
```

**FC-3 — a low `synthInstance.maxHeartbeats` over-reports and cascades.**
At 1000 the first failures are in *earlier* declarations (`Module.Flat F F'`,
`IsLocalization' …`), and their failure cascades into type mismatches and
`Unknown identifier` errors in the target. The usable band is ≈2000, and even
there some failures are legitimate searches that merely need more budget. Treat
the site list as candidates, not convictions.

**FC-4 — a "cleared" low-cap site can hide a different error at the same line.**
Pinning the `map_smul` at 234 with a `change b.repr.toLinearMap …` made the
synthesis timeout vanish and the next report jump to line 244 — apparently a fix,
actually a *`rw` mismatch* at the same line, which the scanner did not print
because it only parsed `failed to synthesize`. The scanner now also prints "other
errors in the same run", and every candidate must be re-checked at the real cap.

**FC-5 — the unfolded spelling is class-specific.** `inferInstanceAs (Nontrivial X)`
for `X = (E₀'.map (algebraMap R₀ F)).toAffine.FunctionField ⊗[F] F'` synthesizes;
the same trick for `Inv (FractionRing X)`, `GroupWithZero (FractionRing X)` and
`DivisionCommMonoid (FractionRing X)` **fails** — those instances are keyed on the
`⁄` spelling, not the `map` one. The search-friendly spelling has to be
*discovered* per class (from the trace goal), not guessed. This is the direct
consequence of `WeierstrassCurve.baseChange` being a semireducible `def`: search
does not unfold it at reducible transparency, while `inferInstanceAs`'s defeq
check does.

**FC-6 — instance-cache ripple: a local edit can break a *later* declaration.**
The `change`-based attempt at line 234 compiled the declaration but broke
`kw_surge_hgf4_χE_VSR_compat` at line 750, which had been green. Prefer a *named
helper* over an inline `change`/`rw` chain — `hrepr_smul` (below) did not ripple.

**FC-7 — truncating at a declaration's `end_line` swallows the next command's
leading modifiers.** `scan_declarations` ends a declaration one line before the
next, so the range can include a following `include hσ in` (line 818 here). A
truncated scratch ending on that line is a dangling modifier:
`unexpected end of input`. The tool now trims trailing blank/`include`/`variable`/
`open`/`attribute`/`@[…`/comment lines before cutting. It recurred in a hand-cut
scratch (`WeightOne.Basic`): the line after the declaration's last tactic is
`variable (F) in`, and keeping it produced
`Unexpected name `IsIntAuxT` after `end`: The current section is unnamed` — a
misleading scope error, not `unexpected end of input`. Same cause, same trim.

**FC-8 — `?m.`-typed class goals cannot be `#synth`-ed.** The low-cap goals
include `AddHomClass (T' →+* T) ?m ?m`, `MulActionSemiHomClass (FF ≃ₗ[FF'] Fin D →₀ FF') ?m ?m ?m`
and `ZeroHomClass (ℕ →₀ T') ?m ?m`: search is running before the type is fixed,
usually because a generic `map_*`/`simp` lemma is applied at a `FunLike`
coercion. A brick is the wrong fix — supply the *bundled* form in a monomorphic,
named helper instead:

```lean
have hrepr_smul : ∀ (c : FF') (x : FF), b.repr (c • x) = c • b.repr x :=
  fun c x => LinearMap.map_smul b.repr.toLinearMap c x
```

**FC-9 — Prop vs data classes.** `Nontrivial`, `StrongRankCondition`,
`IsFractionRing` are `Prop`s, so `inferInstanceAs` needs no value guard. For a
data-valued class (`Inv`, `GroupWithZero`, `Algebra`) a wrong brick is accepted
at the type and mismatches one context later; the §6 `example : (<brick> : …) = <captured term> := rfl`
guard is required.

**FC-10 — local gains are not build gains.** See the 15.1 → 10.6 s local vs
242.3 → 242.7 s module result above. Rank declarations by module share before
spending a batch on them.

**FC-11 — a failing search costs more than the raise that silences it.** A
`synthInstance.maxHeartbeats` timeout is paid *at every retry of every affected
site*, plus the cascade: `CompletionTraceSum` burned 79 s failing at one line
and builds in 13.4 s with the raise restored — the failure mode cost 6× the
success. So when a cap campaign strips a raise and the build then fails, the
failure is usually more expensive than whatever the raise was hiding. The order
of operations is: measure the search, keep (a scoped form of) the raise if the
module stays under the wall-clock bar, and only then try to buy the search
down. The lowered cap is a diagnostic; the wall clock is the budget.

**FC-12 — `trace.profiler` can itself tip a borderline search into failure.**
Profiler instrumentation counts heartbeats: a search that passes at ~90 % of
`synthInstance.maxHeartbeats` in the real build *fails* under
`set_option trace.profiler true` (observed:
`Algebra.IsSeparable ↥(RFld F t) ↥(KFldT F t S)` at
`WeightOne/Basic.lean` line 706, 1.43 s against the 20,000 cap). A
`failed to synthesize` that appears only under profiling is an artifact —
re-run clean before believing it — and any search above ~50 % of the synth cap
is fragile enough to brick regardless (see `isSeparable_KFldT` below).

## What instances alone do not fix

`kw_surge_hgf4_bcIota₁_compat` (line 768) is the counter-example that motivates
"widen the search". Its scoped profile is nearly all *not* typeclass: total
typeclass inference ≈1.4 s (`Algebra` 222 ms, `DistribMulAction` 182 ms), while
the `whnf`/`isDefEq` work shows up as `show` steps and as the 400,000-heartbeat
probe's timeouts at lines 761, 766, 768 and 795 (`whnf`, `tactic execution`). The
same holds at 975–979 and in the statement of `kw_surge_hgf4_pmop_naturality`
(807, `whnf`). These are the §6 concrete-carrier defeq failures — `show` over
`algebraMap` into `FractionRing (… ⊗[F] F')` — and they need a proof shape that
does not re-unify two syntactically different carrier terms, not more instances.

## The biggest hog, isolated and cut

The §3.5 rule‑1 isolation works once the module builds: **import the built
module** (cheap — the `.olean` is already there), reconstruct the section
variables and the `local notation`s, and re-prove the declaration under a scratch
name. `kw_surge_hgf4_pmop_naturality` (lines 820–1066) is then **173 s on its
own**; its statement alone is 8 s, so the proof body was ~165 s.

The profiler on that scratch put **158 s of 169 s in `tactic execution`**, and
almost all of it in one tactic call:

```
tactic execution of Mathlib.Tactic.Positivity.positivity took 155s
```

That call closes `0 < (ramificationIndexAlong ι₀ w : ℤ) * w.ord f` after
`rw [Place.ord_restrictAlong ι₀ hι₀, …]`, with `hram_pos : 0 < ramificationIndexAlong ι₀ w`
and `hQord : 0 < w.ord f` already in context. `positivity` re-derived the product
by unfolding `ord` over the concrete carrier instead of using them; the explicit

```lean
exact mul_pos (by exact_mod_cast hram_pos) hQord
```

is instant. Both `positivity` sites (module lines 979 and 988) are the same goal,
and the module drops:

| | before | after |
|---|---:|---:|
| isolated declaration | 173 s | **12.8 s** |
| module `lake build` | 242.7 s | **188.1 s** |

Two cautions the numbers teach:

- **The isolated figure overstates the module share.** Cold discrimination tree
  and instance cache make a scratch declaration more expensive than the same
  declaration in situ; the same isolation put `kw_surge_hgf4_bcIota₁_compat`
  (line 768) above 200 s while the whole module is 188 s. Isolation is for
  *naming* the culprit in one run; the module build stays the verdict.
- **A `positivity`/`simp`/`show` is a search you did not write.** 155 s of a
  242 s module hid in a tactic whose inputs the surrounding context had already
  proved. When the low-cap probe points at `positivity` or `whnf`, suspect a
  missing explicit term, not a missing instance.

The next target from the same probe is the `show` block in
`kw_surge_hgf4_bcIota₁_compat` (module 774/779/781/808): the scoped profile puts
four `show`s at 33–36 s each, all `whnf` over `functionFieldTensorFracHomGeneral`
applied to `χE`/`χE'`. Unlike the `positivity`, that one needs the goal restated
in a spelling that does not force the unfold, not a one-line replacement.

### Diagnosis of the 768 block (what the low-cap tools say)

Pinning the wildcard at 774 (`algebraMap … _ …` → explicit `FractionRing …`
codomain) *moved* the timeout within the same line (col 84 → 138) — so the cost
is the `a ⊗ₜ[F] (1 : F')` term, not the wildcard. `set_option diagnostics true`
then names the mechanism:

```
[def_eq] heuristic for solving `f a =?= f b` (max: 202, num: 14):
  [def_eq] Affine ↦ 202
[reduction] unfolded reducible declarations (max: 202, num: 14):
  [reduction] Affine ↦ 202
```

`WeierstrassCurve.Affine` (mathlib `Affine/Basic.lean:74`) and
`WeierstrassCurve.FunctionField` (`Affine/Point.lean:95`, = `FractionRing
CoordinateRing` = `FractionRing (AdjoinRoot …)`) are **`abbrev`s**, so defeq
unfolds them outright, over a carrier whose head `(E₀⁄F)` is the semireducible
`baseChange`. `set_option trace.Meta.isDefEq true` at a 200 k cap (250 k lines
before the abort, so scope it and keep the cap low) ends on

```
(toAffine E₀⁄F).CoordinateRing =?= nonZeroDivisors (toAffine E₀⁄F).CoordinateRing
```

i.e. `FractionRing`/`IsFractionRing` instance resolution comparing the
localisation set with its own ring. So this is **not** a missing instance and not
a wildcard: it is abbrev-unfolding during instance/defeq, the same family as §6's
"concrete `adjoin` carriers" and IF‑003, one layer further down.

The untested hypothesis, and the next experiment: hoist the `FractionRing`
instances (`IsFractionRing`, `Algebra`, `IsScalarTower`, `IsLocalization`) for the
two carriers as named `haveI` bricks at the top of the declaration, at the spelling
the elaborator actually uses, and re-probe at a low cap. If `--heartbeat-cap`
shows 774 clearing, the pattern generalises; if not, the remaining lever is to
restate the two `have` types in a single carrier spelling so no unfolding is
needed at all.

**Tested (negative).** Three instance-level fixes were tried in the Scratch and
none cleared the sites:

1. Pin the wildcard at 774 (`algebraMap … _ …` → explicit `FractionRing …`): the
   timeout moved within the same line (col 84 → 138).
2. Hoist `IsFractionRing` for both carriers as `haveI` bricks: all four sites
   stayed at the 200 k cap.
3. Use one `FunctionField` spelling throughout (drop the `toAffine`, which is
   `abbrev toAffine (W) : Affine R := W`, the identity, with `Affine R :=
   WeierstrassCurve R`): sites unchanged.
4. Pin the `Algebra` structure on each `FractionRing` with `letI`: it is rejected
   with *"synthesized type class instance is not definitionally equal to
   expression inferred by typing rules"*.

The `isDefEq` trace explains why all four fail. The enclosing chain is an
**instance diamond on `FractionRing`** — `OreLocalization.instDistribMulActionOfIsScalarTower`
against `OreLocalization.instAlgebra.toSMul`, `instMulActionOfIsScalarTower`
against `instAlgebra.toSMul`, repeatedly, ending at

```
OreLocalization (nonZeroDivisors (toAffine E₀⁄F).CoordinateRing) (toAffine E₀⁄F).CoordinateRing
  =?= (toAffine E₀⁄F).FunctionField
…
Algebra.toModule =?= Algebra.toModule
```

Both *are* defeq (every node checks `✅️`), but proving it means comparing whole
structure values; `FractionRing`'s `Algebra`/`SMul`/`DistribMulAction` instances
arrive by two different paths, so unification has to compare them. That is a
diamond the standard trick (`letI` one instance) cannot collapse here, because the
two instances are not definitionally equal in this context — precisely the §6
"two `Algebra`-like instances" case, which the playbook calls a hard error rather
than a cost. So the 768 block is *not* a missing-instance problem and the fix has
to be proof-level: avoid the comparison by keeping the carrier and its instances
in one path (which is what "same syntactic term" would buy, one layer up), or
re-derive the block so it never asks for both paths at once.

The standing conclusion for the method: low-cap call-site isolation + profiler
kind + `diagnostics`/`isDefEq` trace names the mechanism reliably, but when the
mechanism is an instance *diamond*, no brick will fix it — the win must come from
restating the proof.

### The fix that worked on 768 (positive)

The four slow sites are the two `show`s inside each `functionField_algHom_ext` of the two
naturality squares (`hκ` in `hκE'` and `hκ` in `hκE`). The two later `show`s (the middle
tensor rewrite and the final restatement) were flagged too, but they clear once the `hκ`s
do — the cost was upstream of them. The principle behind the fix: **do not make the
elaborator prove that a composite `AlgHom` applied to `polyToFunctionField … X` is the
uncomposed generator value.** The `show` is a defeq check through `AlgHom.comp`,
`AlgHom.restrictScalars` and the `⁄` carrier; matching the generator lemma by `rw` is a
syntactic (keyed) match and never unfolds the `baseChange`/`FunctionField` abbrevs.
Concretely, replace

```lean
· show functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
  rw [functionFieldMapAlongGeneral_polyToFunctionField_X,
    functionFieldTensorFracHomGeneral_X]; rfl
```

by the explicit application steps, and state the other side of the square through a
*named* structural map:

```lean
def kw_surge_hgf4_tensorUnit (W : WeierstrassCurve R₀) … :
    (W⁄F).FunctionField →ₐ[F] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  (IsScalarTower.toAlgHom F _ _).comp (Algebra.TensorProduct.includeLeft (R := F))

· rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    functionFieldMapAlongGeneral_polyToFunctionField_X,
    functionFieldTensorFracHomGeneral_X, kw_surge_hgf4_tensorUnit_apply]
```

The same three-line rewrite closes the `yGen` case and both cases of the `E₀` square; the
`kw_surge_hgf4_tensorUnit_apply` lemma (`b ↦ algebraMap (b ⊗ 1)`, proved by
`AlgHom.comp_apply`, `Algebra.TensorProduct.includeLeft_apply`, `rfl`) is the only place
the `algebraMap … (b ⊗ₜ 1)` spelling is elaborated.

Measured, module `lake build` being the only honest acceptance test
(each run alone, clean `.olean` deleted):

| | before | after |
|---|---:|---:|
| module `lake build` (wall) | 244.1 s | **71.1 s** |
| `USER` CPU | 280 s | 101 s |
| low-cap blow-up sites | 6 | 2 (both in `bcTensorFracIotaSeam`) |

The declaration is only ≈10 s in isolation (a scratch that *imports* the built module and
re-proves it under a scratch name, so the prefix is free), so the module-scale win is
about 2.4× larger than the isolated figure — direct evidence that the `show` defeq was
poisoning the instance cache for the rest of the file, not just paying at its own site.
This is the positive counterpart of FC-6: an instance-cache ripple runs both ways, and it
is worth re-running the module verdict even when the isolated win looks small.

### Two more Scratch experiments on 768 (both negative)

- **Inferred type for the AlgHom equality.** Replacing the explicit
  `have hκ : <f = g> := by …` with `have hκ := functionField_algHom_ext
  (f := …) (g := …) ?_ ?_` (so no slow type is written) elaborates the *type*
  cheaply, but changes the `show` goals: the first `show` then fails outright and
  the later ones time out again. The slowness just moves into the extensionality
  subgoals.
- **`includeLeft` for the tensor notation.** Replacing `a ⊗ₜ[F] (1 : F')` with
  `Algebra.TensorProduct.includeLeft (R := F) a` (which needs no `SMul`
  synthesis) is rejected with *"Function expected"* at the application and leaves
  the same four sites. The `Algebra (…) (FractionRing …)` requirement remains.

### The other big unit: declaration 204

`kw_surge_hgf4_bcTensorFracIotaSeam` (204–383, ~50 s of the module) has the same
family at a larger scale. A verbatim Scratch copy at the real cap with
`diagnostics.threshold=1` gives a single reduction running away:

| declaration | total unfoldings | max in one reduction |
|---|---:|---:|
| `inferInstance` | 97,525 | **95,277** |
| `Affine.baseChange` | 91,077 | 90,959 |
| `toAffine` | 90,949 | 90,855 |
| `CoordinateRing` | 58,914 | 56,697 |
| `FractionRing` | 24,261 | 23,728 |
| `Localization` | 24,190 | 23,657 |
| `FunctionField` | 22,618 | 22,125 |
| `def_eq` `Monoid.toMulAction` | 19,476 | 18,970 |

So the mechanism is the same reducible-abbrev chain (`Affine.baseChange` →
`toAffine` → `CoordinateRing` → `FractionRing` → `Localization`) over the
semireducible `baseChange`, with `inferInstance` itself being unfolded ~95 k
times inside one defeq — an instance/`abbrev` unfolding loop, not a search. At
that scale no per-site brick is plausible; the fix is to keep the carrier behind
a local definition (`let`/`opaque`) and never let defeq see the chain, which is a
systematic rewrite of the block.

**Attempted refactor (diamond-bound).** The principled high-level replacement is: keep only
the *direct* base-change spans/independence `hspanT`/`hliT` (they never divide and are
cheap), package them as `eBasis : Basis (Fin D) T' T`, and then get the fraction-field
statement from mathlib — `finrank FrT' FrT = finrank T' T = D` by
`IsFractionRing.finrank_eq`, and `Module.Finite FrT' FrT` from
`Module.finite_of_finrank_pos`. That removes `hint`, `hspanFr`, `hliFr` and the whole
hand-rolled fraction basis. It does **not** elaborate: the two required tower instances
`IsScalarTower T' T FrT` and `IsScalarTower T' FrT' FrT` cannot be built.
`IsScalarTower.of_algebraMap_eq` produces the `Algebra.toSMul` form, while the goal's `SMul`
is resolved to `OreLocalization.instSMulOfIsScalarTower`; the mismatch is the *same*
`FractionRing` instance diamond, one level down, so the standard mathlib route is blocked
by exactly the defeq that blocks the bricks. (Confirmed in a scratch that imports the built
module: the refactor fails on the tower instances, not on the mathematics.) The remaining
option is to restate the seam so the two carriers never meet in one tower — i.e. an
abstract `T'`/`T` lemma whose hypotheses are the towers, instantiated where the towers are
still syntactically matched.

**Plateau (now narrowed).** After the 768 fix, the one-run low-cap probe reports exactly
two sites, both in `kw_surge_hgf4_bcTensorFracIotaSeam`: the theorem statement (`whnf`) and
`obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'` (`isDefEq`). Both are the same
instance/abbrev-unfolding defeq over `baseChange`; the cheap instance-level fixes are
exhausted (six tried, all negative or rejected). The seam is therefore the remaining hog,
and its refactor is *not* a matter of more instances — see the diamond-bound attempt below.

## A second unit: `CyclicQuotientJInjective` (160 s → 10 s)

The same profile-then-low-cap loop, run on a different module, found two *independent*
defects — one a build failure, one a 153 s tactic.

**1. A missing instance from a narrowed import.** The tree build failed with

```
CyclicQuotientJInjective.lean:450:55: failed to synthesize
  AddMonoidWithOne (HahnSeries ℚ (AlgebraicClosure ℚ))
```

The module imports `Mathlib.RingTheory.HahnSeries.Basic` explicitly, but `Basic` carries only
`Zero`/`Inhabited`/`Nontrivial`: the ring instances are one module further
(`HahnSeries.Multiplication` gives `AddCommMonoidWithOne`/`Ring`) and `Field` is in
`HahnSeries.Summable`. It used to see them transitively through the blanket `import Mathlib`
that `FLTForHuman.Algebra.ZModTorsion` carried; narrowing that import (commit `44a3178`)
removed the transitive coverage. The fix is the direct import
`Mathlib.RingTheory.HahnSeries.Summable` — precisely the playbook's "blanket `import Mathlib`
hides transitive dependencies (expect 3–5 missing per file)". Two things make it nasty:

* it is reported as `synthInstanceFailed` (originally billed as a synth failure), not as a
  timeout, and it surfaces only after the *whole expensive module* has been elaborated;
* with the low-cap probe (`--heartbeat-cap 200000`) it is a normal one-run site, so the
  whole diagnosis costs one cheap `lake env lean`, not a 160 s wait.

**2. A `congr` you did not write.** Once the module elaborated, it took **160.3 s**, and the
in-file profiler (`instance_hotspots.py --profile`, *not* `-Dtrace.profiler`) put **153 s of
the 160 s in a single tactic**:

```
tactic execution of Lean.Parser.Tactic.congr took 153s
```

It is `congr 1` in `Pic0_pushforwardAlongHom_comp`, unifying two
`Pic0 K F = Divisor.degZero ⧸ principal.addSubgroupOf` quotients. `Pic0.mk` is a plain
function, so the search is replaced by the explicit term:

```lean
refine congrArg Pic0.mk (Subtype.ext ?_)
```

| | before | after |
|---|---:|---:|
| `lake env lean` (tier 0, 4 M cap) | 160.3 s | **10.0 s** |
| low-cap sites at 200 k | 1 (`whnf` at 178) | **0** |
| tier-1 `lake build` | — | 8.8 s |

This is the `positivity` lesson again: a `congr`/`positivity`/`simp`/`show` is a search whose
inputs the surrounding context already has — name the term instead. It is **not** a sweepable
pattern: `NatCard.lean:476` has the same `congr 1` on `Pic0` and profiles clean (largest
class 300 ms), so it must be profiled, not grepped.

The workflow this sharpened: pay once with the **in-file** profiler on a module that now
builds (`--profile --threshold 100`) to name the tactic *kind*, then one low-cap run
(`--heartbeat-cap 200000`) to name the *call site*. Do not rank with `-Dtrace.profiler`
(FC-1), and do not escalate the cap to hunt for more sites — an aborting declaration just
re-reports its own first one.

## A third unit: `WeightOne.Basic` at the lowered cap — failure costs more than the raise

Context for this one: the lakefile cap was dropped 4,000,000 → 500,000 *to
surface hogs*, and the pin's local `set_option maxHeartbeats` /
`synthInstance.maxHeartbeats` bumps were stripped tree-wide. The 500k tree
build then failed in two modules; both are instructive, and the second is the
headline (FC-11).

**`IsIntAuxT.mem_span_RSet_of_adjoin_simple_transcendental` (line 882).** The
tree build reported `882:0 whnf timeout (500000)` plus the usual
`(kernel) unknown constant` cascade at 1094. The pin
(`P2M/Sol/S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean:364`)
proves this declaration under `maxHeartbeats 51,200,000` with
`synthInstance.maxHeartbeats 4,000,000`; the port's five `haveI` bricks had
already bought that down to ~1.0–1.5M — but 500k is 2–3× too small, and the
declaration genuinely does not fit. Measured anatomy: the low-cap probe reports
a single command-level site (`882:0 whnf`), so the per-block view is a
truncation ladder — `sorry` the proof at successive lines, wall time including
the ~13 s prefix:

| through | wall | Δ block |
|---|---:|---:|
| statement + `sorry` | 15.0 s | ~300k heartbeats (fails 200k, passes 400k) |
| + `set ψ`, five `haveI` bricks, `hrange` stmt | 19.4 s | +4.4 |
| + `hrange` proof, `hxψ` | 23.5 s | +4.1 |
| + poly block (`hrel`…`hbW`) | 29.2 s | +5.7 |
| + `y`/`hyrel` | 30.7 s | +1.5 |
| + `choose B`…`hmrel` | 42.4 s | **+11.7** |
| + `hmint` | 47.0 s | +4.6 |
| full | ~51 s | +4 |

and the scoped profiler attributes it as 13 `rewriteSeq` ≈ 20–23 s plus TC ≈ 7 s
(`Field` ×2, `IsFractionRing` ×2, `DistribMulAction` ×3–5): death by a thousand
cuts over the concrete `FractionRing ((↥(RFa F t S))[X])` carrier, no single
site dominant.

What worked:

1. **A scoped raise, measured not guessed.** `set_option maxHeartbeats 2000000 in`
   on the one declaration — the need was bisected to 1.0–1.5M (fails @1M,
   passes @1.5M) and 2M set for margin. This is the `lean-build-cost.md` §3
   "localize the cap to the declarations that need it" policy, under the rule
   agreed for the campaign: a module that builds in under a minute may carry
   the raise. Module: **372 s (fail) → 51.7 s build**.
2. **Merging five `rw`s into one dot-form chain in `hmrel`** — `rw [map_add ψ _ _]`
   plus three siblings became
   `rw [ψ.map_add, map_pow ψ, map_sum ψ, ψ.map_zero, hm]`, deleting the
   redundant explicitly-spelled `hsum`: −5 s. The un-merged chain was
   FC-8-shaped (generic `map_*` with wildcards at a `RingHom`).
3. **The `isSeparable_KFldT` brick** (hardening, below).

What did **not** work (negative, so the next pass skips them):

- Pinning the `algebraMap` spellings inside the two big `show` types: no effect
  (47.9 s vs 46.7). The stuck-wildcard theory was wrong *here* — pin experiments
  are cheap, but measure before keeping.
- `haveI` bricks for `Field`/`IsFractionRing`/`DistribMulAction` at the
  `FractionRing` carrier spelling: **slower** (50.8 s) — the up-front searches
  cost ~2.5 s and the goals never recurred in that spelling (FC-5 again: brick
  the goal's own spelling or don't brick).
- Named `rfPolyEval_C`/`rfPolyEval_X` computation lemmas: neutral, and `rw`'s
  auto-`rfl` could not close the `algebraMap ↥(RFa) ↥(KFldT) s = ↑s` coercion
  equation that `simp [rfPolyEval]` closes — reverted; the `simp` sites stay.

**The borderline synth search, hardened.** `isDedekindDomain_RFa` (line 706)
synthesizes `Algebra.IsSeparable ↥(RFld F t) ↥(KFldT F t S)` in ~1.43 s —
inside the 20,000 synth cap, but within ~10 % of it, and over it under
`trace.profiler` (FC-12). Probing the sub-instances showed
`CharZero ↥(RFld F t)` is not TC-derivable at all, so the fast path is not the
instance's own; the brick supplies the three steps explicitly:

```lean
private theorem isSeparable_KFldT (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    Algebra.IsSeparable ↥(RFld F t) ↥(KFldT F t S) :=
  haveI : CharZero ↥(RFld F t) := charZero_KFld F (RFld F t)
  haveI : Algebra.IsIntegral ↥(RFld F t) ↥(KFldT F t S) :=
    Algebra.isAlgebraic_iff_isIntegral.mp
      (IntermediateField.isAlgebraic_adjoin fun s hs => (hSint s hs).tower_top)
  Algebra.IsSeparable.of_integral ↥(RFld F t) ↥(KFldT F t S)
```

It elaborates in ~150–190 ms, and `haveI := isSeparable_KFldT F t S hSint`
went into both `isDedekindDomain_RFa` and `isFractionRing_RFa` (the same search
via `integralClosure.isFractionRing_of_finite_extension`). Module under
`trace.profiler` afterwards: zero errors, and ~3 s faster (55 s → 51.7 s) from
the two removed searches.

**`AlgebraicCurve.Tate.CompletionTraceSum` — the headline lesson.** The same
tree build failed it at line 409
(`∀ (i : ↥(fiber F v)), Module.Free v.adicCompletion (↑i).adicCompletion`,
20k synth timeout). The cause was *not* a missing instance — the module's
19-module import closure does not contain `ZModTorsion`, so the narrowed import
did not cascade here — but the campaign having commented out two
`synthInstance.maxHeartbeats 800000` raises (a section-wide one at line 204 and
a scoped one at line 613). The search genuinely needs the budget. Restored;
the module builds in **13.4 s**. The same module took **79 s to fail** in the
tree build: every retry of the search runs to the 20k timeout and cascades
(FC-11). The pin's `synthInstance.maxHeartbeats` bumps are claims that the
search is slow, and here the claim was simply correct.

| | before (500k cap) | after |
|---|---:|---:|
| `lake build` `WeightOne.Basic` | 372 s, ✖ at 882 | **51.7 s** ✔ |
| `lake build` `CompletionTraceSum` | 79 s, ✖ at 409 | **13.4 s** ✔ |

Standing state: both failures from the 500k tree build are cleared. That tree
build was killed at 1 h around `[5266/5394]`, so ~130 modules past the kill
point remain unverified until the next tree build.

## Per-declaration cost, and the one-run call-site list

A note on per-declaration cost: Lean `v4.34` has no "seconds per theorem" table.
`--profile`/`-Dprofiler=true` accumulates by *category*; `-Dtrace.profiler=true`
emits `[Elab.command]` spans (per declaration) but under-reports badly — a 12.8 s
scratch theorem measured 0.45 s — because Lean detaches proof elaboration into
`Elab.async` nodes; the `trace.profiler.output` Firefox export carries those
named async nodes but has **no source positions** (`funcTable.fileName` is
empty), so it can rank declarations, not tactic call sites. `set_option diagnostics true`
reports operation *counts*, not time. Two additions from the WeightOne case:
the `[Elab.async] elaborating proof of <name> [t]` span *is* the honest
proof-body time — the same command whose `[Elab.command]` read 0.81 s had an
async proof node of 42.6 s — and `count_heartbeats in` does not compose with
`set_option … in` in v4.34 (parse error), so "how many heartbeats does this
declaration need" is a cap bisection: 1M fails, 1.5M passes is two
`lake env lean` runs.

The profiler names tactic *kinds* (`tactic execution of Positivity.positivity took
155s`), which is context-dependent: the same tactic is fine elsewhere. The
call-site view comes from the low-cap heartbeat probe, which reports
`line:col` and the failing operation in one run:

```
## unification blow-up sites at maxHeartbeats=200000 (6 sites)
          site  op  (counts: «tactic execution»×3, whnf×2, isDefEq×1)
         331:4  isDefEq
         204:0  whnf
         781:8  whnf
        779:60  «tactic execution»
        774:84  «tactic execution»
         808:2  «tactic execution»
```

That is the reliable one-run "everything" list: the profiler is for the *kind*,
the heartbeat probe is for the *where*. Pair them — profile to learn it is
`positivity`/`whnf`/`isDefEq`, then `--heartbeat-cap` (or `--lowcap`) to get the
call sites — before editing.

## Reproduction

```bash
cd tools/deps
# class-level data for one declaration, scoped so it is that declaration's
python3 instance_hotspots.py --module FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange \
    --at 205 --profile --threshold 10
# the exact goals, ranked by repetition
python3 instance_hotspots.py --module FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange \
    --at 205 --trace --class DistribMulAction
# the module verdict (the only acceptance test)
cd ../lean && /usr/bin/time -f '%e s %U user' timeout 400 \
    lake build FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange
```

The two `instance-friction.md` entries this case produced so far are the
`hrepr_smul` helper (FC-8) and the `baseChange`/`FractionRing` spelling split
(FC-5). Neither is a `synthInstance.maxHeartbeats` bump: at 2000 the searches
still fail, and at 4,000,000 they merely succeed slowly.
