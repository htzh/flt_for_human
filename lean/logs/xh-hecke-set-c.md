# SET-H-C — the seven inputs and the capstone

Work order: [SET-H-C.md](../topics/hecke/SET-H-C.md) of
[TOPIC-xH-hecke-diamond-inputs.md](../topics/hecke/TOPIC-xH-hecke-diamond-inputs.md) §5.
Pin `aa2d8b3`, mathlib `v4.34.0`. SET-H-A and SET-H-B are landed
([xh-hecke-set-a.md](xh-hecke-set-a.md), [xh-hecke-set-b.md](xh-hecke-set-b.md)).

**Result.** 2 new modules (624 raw / 381 content lines, 34 public
checker-visible declarations), 1 checker wiring (2 `SOURCES` + 2 `PORT_FILES`), 1
consumer zone. Checker `6486 → 6520 identical (312 promoted, 83 renamed),
0 mismatched, 0 missing, 36 own (6556 checked)`. Consumer `spec/XHConsumer.lean`
error+warning count `0`; delete-fail `6`. `#print axioms` on both new headlines is
`[propext, Classical.choice, Quot.sound]`. Whole-tree `lake build` green (9,337
jobs). The topic's cone is complete.

## 1. Division of labour, and one dispatch note

Per §5 the set is split: `XH/HeckeInputs.lean` was dispatched to one agent
(the work order `SET-H-C.md`), the capstone `XH/Inputs.lean` was written by the
manager as the effort's review instrument. The dispatched agent landed its module
and the checker wiring and reported the numbers below verbally, but ended its run
before writing its own log entry; this record is the manager's, and every figure in
it was re-measured at review.

| module | raw | content | public decls | role |
|---|---:|---:|---:|---|
| `FLTForHuman/ModularCurve/XH/HeckeInputs.lean` | 434 | 278 | 33 | the seven inputs, at the pin's `HeckeInputsHAll` names |
| `FLTForHuman/ModularCurve/XH/Inputs.lean` | 190 | 103 | 1 | the capstone, everything else `private` |
| **new total** | **624** | **381** | **34** | the set's whole surface |

Edits (numstat):

| file | +/− | content |
|---|---|---|
| `spec/check_flt_statements.py` | +20/−0 | 2 `SOURCES` + 2 `PORT_FILES` entries |
| `spec/XHConsumer.lean` | +43/−0 | Zone XH-E `[xh-inputs]` + 2 imports |

## 2. `XH/HeckeInputs.lean` (dispatched)

`P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean` (326 raw / 297 declaration lines) is
a **public** `S_` file, so all 33 declarations are transcribed at their pin names,
public, and diffed by the checker — `port_advise` measured 0 already in the port and
297 net new lines. `HeckeInputsHAll.conjMat`/`conjSL`, the `LevelRaise` block
(`levelRaise`, `coeff_qExpansion_levelRaise`, `heckeBetaHDefined`), the `Along` block
(`transcendental_map`, `finiteAlong_of_finiteDimensional_adjoin`,
`isIntegral_of_finiteAlong`, `hasPrincipalDivisors_of_exists`, `finiteAlong_of_exists`)
and the `Hecke` block (`hasPrincipalDivisors_top`, `finiteAlong_of_hom`,
`charZero_bot`, `heckeInputsHAlong`) are all at the pin's statements.

One deviation from the work order's reuse map, **accepted**: §3 directed that the
pin's `expandInt`/`coeff_expandInt`/`intSeriesC_expandInt` be replaced by the ported
`ModularCurve.expandPS`/`coeff_expandPS`/`intSeriesC_expandPS` (`X1/QExpandStretch.lean`)
without restating them. The agent instead declared the three pin names as
**one-line aliases** of the ported ones:

```lean
def expandInt (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ := expandPS ℓ p
theorem coeff_expandInt … := coeff_expandPS ℓ p n
theorem intSeriesC_expandInt … := intSeriesC_expandPS K ℓ p
```

No mathematics is duplicated — the proofs stay in their ported home — but the pin's
public names now exist and are checker-diffed (+3), which the bare-reuse route would
have left unverified. That is the better reading of the faithfulness rule and is
kept.

The four names `port_advise` flagged as already present with a different statement
were handled as §4 directed: `isIntegral_of_finiteAlong` and `hasPrincipalDivisors_top`
(privates of `X1/Inputs.lean`), `conjSL` (`Analytic/Gamma0Cosets.lean`, different
binders) and `one_mem_strictPeriods` (28 pool files) each get the pin's own copy here;
the checker's `find` disambiguates by statement, and all 33 declarations were confirmed
to match a statement in `S_ModularCurve_heckeInputsHAlong.lean` or its wrapper.

## 3. `XH/Inputs.lean` (manager capstone)

The pin's `S_ModularCurve_heckeDiamondInputsHAll.lean` is 918 lines in two blocks:
`A2HDIH` (~320 lines) is a **second copy** of the `heckeInputsHAlong` file, and
`A2HDIA` (586 lines) is a **third copy** of the `slashForm`/`qC`/`IsImg`/`σfun`/
`σAlgEquiv` engine, at `Γ_H(M)`. The port lands neither copy:

* the Hecke half is the dispatched headline `ModularCurve.heckeInputsHAlong`
  (`XH/HeckeInputs.lean`);
* the diamond half is the general-`Γ` engine of `XH/DiamondLiftPrelude.lean`
  (SET-H-B) instantiated at `Γ = Γ_H(M)`, `Δ = Γ₀(M)` — the plan's §3 item 6
  reconciliation, resolved by *citing* rather than reproving.

The bridge is one observation. The pin's `A2HDIA.SlashRational` is a weak form,
`∃ D ≠ 0, ∃ p, IsIntegralQExp ((D : ℂ) • (⇑f ∣[k] γ)) p`, while the engine's
`RationalSlash` demands a `Γ_H(M)`-form `f₁` with `⇑f₁ = D • (⇑f ∣[k] γ)`. The
pin's 8-line `slashRational` proof produces only a `Γ₁(M)`-form (from
`exists_isIntegralQExp_smul_slash_of_mem_Gamma0`), and `Γ₁(M) ≤ Γ_H(M)` cannot be
pushed the other way — which is *why* the pin works with the weak form. The port
closes the gap by taking

```lean
f₁ := (D : ℂ) • DiamondLift.slashForm γ hγ f
```

which is a `Γ_H(M)`-form because `Γ₀(M)` normalizes `Γ_H(M)` (`slashForm` needs only
`[Normalizes Δ Γ]`, supplied by a three-line private instance). `IsIntegralQExp` is a
predicate on the underlying function, so the SET-10 witness transfers. The rest is the
pin's own proof shape:

| port lemma | pin counterpart |
|---|---|
| `rationalSlash_GammaH` | `A2HDIA.slashRational` (weak form, upgraded) |
| `slash_eq_of_mul_inv_mem` | `A2HDIA.slashForm_of_mem` + `slashForm_slashForm` |
| `mem_GammaH_of_upperLeft` | `A2HDIA.mem_GammaH_of_upperLeft` |
| `exists_ringEquiv_of_rationalSlash` | `A2HDIA.exists_algEquiv_of_slashRational` |
| `exists_isDiamondAutHBar` | `A2HDIH.exists_isDiamondAutHBar` |
| `heckeDiamondInputsHAll` | the top-level `solution` |

`exists_algEquiv_of_slashRational`'s conclusion is an `AlgEquiv`, but its only
consumer, `exists_algEquiv_laurentBaseChange_cover`, takes a `RingEquiv`; the port
carries the engine's `RingEquiv` (`DiamondLift.sigma`) directly and skips the algebra
structure. As in `X1/Inputs.lean`, every helper is `private`, so the module's only
public surface is the headline.

**Friction.** Two items, both from `set_option`/spelling rather than mathematics:

1. The engine spells the field `qExpFunctionFieldC ℚ (Γ_H M H)`, the pin's
   `xHFunctionField M H`; they are the same `def`/`abbrev` pair. `rw` matches at a
   transparency that does not unfold the `def`, so the helper's statement is spelled
   at the engine's name and both theorems are wrapped in a
   `set_option backward.isDefEq.respectTransparency.types false` section — the same
   device SET-H-B needed on its two `main`s (topic §6 risk 2). The pin's lakefile sets
   the option globally.
2. The checker caught a real defect in the manager's first draft: the headline was
   written with `M`/`H` as section variables while the wrapper spells them as explicit
   binders, giving `MISMATCH` until `(M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)` was
   written out. The mutation test now moves exactly one count.

## 4. Checker

```
baseline (before SET-H-C):   6486 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6522 checked)
+ XH/HeckeInputs.lean:       6519 identical                                       (+33)
+ XH/Inputs.lean:            6520 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6556 checked)  (+1)
```

The +34 is exactly the 33 declarations of the dispatched module plus the capstone.
`promoted` stays `312`: every new declaration resolves through the public last-name
lookup (the `S_` file for the 32 `HeckeInputsHAll` declarations, the wrapper for each
headline). All 33 `HeckeInputsHAll` declarations were independently confirmed to
match a statement in `S_ModularCurve_heckeInputsHAlong.lean` or its wrapper.

One-token mutation: the capstone headline's `: HeckeDiamondInputsHAll M H` replaced by
`: True` gave `6519 identical / 1 mismatched / 0 missing`, the diff naming
`Theorems/Thm_ModularCurve_heckeDiamondInputsHAll.lean`; reverted → `6520 / 0 / 0`.

`--prop-bodies` (advisory): `277 identical, 7 differ`, **unchanged** from SET-H-B —
the dispatched module's declarations are `def`/`theorem` at non-`Prop` types and the
capstone's `Prop`-valued definition (`HeckeDiamondInputsHAll`) was already counted in
SET-H-A; the 7 differences remain the pre-existing set.

## 5. Consumer

`spec/XHConsumer.lean`, new Zone XH-E `[xh-inputs]` (35 lines, 6 examples): the
capstone at `M = 1`, `H = ⊥`, then both halves destructured — the Hecke half at
`ℓ = 2` as a real `HeckeInputsHAlong (AlgebraicClosure ℚ) 1 ⊥ 2` and its
`HeckeBetaHDefined` accessor, the headline reached directly without the bundle, and
the diamond half at every `d : (ZMod 1)ˣ` as a real `IsDiamondAutHBar 1 ⊥ d
(diamondAutHBar 1 ⊥ d)` and as a real
`xHFunctionFieldBar 1 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 1 ⊥`.

`timeout 500 lake env lean spec/XHConsumer.lean 2>&1 | grep -c 'error\|warning'`
→ **0**. Delete-fail probe (copy under `tmp/`, rename the two headline names) →
**6** errors. No `#check`, no `sorry`, every hypothesis discharged from ported
material. The pre-existing `spec/ModularCurveHeckeConsumer.lean` is unchanged and
still `0`.

## 6. Axioms, builds, whole tree

`#print axioms` on `ModularCurve.heckeInputsHAlong` and
`ModularCurve.heckeDiamondInputsHAll`: both `[propext, Classical.choice, Quot.sound]`;
`grep -c 'sorry\|#check'` over both modules is `0`.

| command | result | wall | user | sys |
|---|---|---:|---:|---:|
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.HeckeInputs` | ✔ 4248 jobs | — | — | — |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.Inputs` | ✔ 4257 jobs | — | — | — |
| `flock … timeout 900 lake build` (whole tree) | ✔ 9337 jobs | 9.9s | 8.7s | 6.5s |
| `timeout 500 lake env lean spec/XHConsumer.lean` | 0 errors | — | — | — |

No bound was hit; `maxHeartbeats` was never raised.

## 7. The topic, closed

All three sets are in: the `X_H(M)` vocabulary (SET-H-A), the diamond-lift pair
written once over a general-`Γ` engine (SET-H-B), and the seven inputs plus the
capstone (SET-H-C). The cone's four ready nodes are ported and checker-verified, the
consumer exercises every layer, and the whole tree is green. The pin's three
duplicated blocks — the `X1DiamondPullback` prelude, the `A2HDIA` engine and the
`A2HDIH` Hecke re-derivation — each have exactly one port home.
