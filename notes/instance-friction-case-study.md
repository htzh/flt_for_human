# Instance friction, worked: `KernelBaseChange` as a mechanical case study

`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean` (1,392 lines, 242 s
to build at the frozen 4,000,000-heartbeat cap) is the worked example for the
"profile → locate → brick → verify" loop of
[porting-playbook.md](../lean/porting-playbook.md) §6 and
[lean-build-cost.md](lean-build-cost.md) §10. It is big enough to be
representative and small enough to run end to end. This note records the method,
the measured result, and — the point of writing it down — the **failure cases** of
the mechanical procedure, because each one cost a round.

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
`open`/`attribute`/`@[…`/comment lines before cutting.

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
