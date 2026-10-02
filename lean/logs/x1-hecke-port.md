# Port record — `ModularCurve.heckeDiamondInputsAll` (the X₁ Hecke/diamond inputs)

Effort: [TOPIC-x1-hecke-diamond-inputs.md](../topics/hecke/TOPIC-x1-hecke-diamond-inputs.md).
Pin `aa2d8b3`, mathlib `v4.34.0`. Run as three sets plus the manager's capstone:
[SET-X1-A](x1-hecke-set-a.md), [SET-X1-B](x1-hecke-set-b.md),
[SET-X1-C statements](x1-hecke-set-c.md), then `X1/Inputs.lean`.

## Result

`remaining 0 nodes / 0 raw / 0 content` (from the planning figure
10 / 4,339 / 3,239). Checker `4368 → 4436 identical (150 promoted), 0 mismatched,
0 missing, 30 own-proof exempted`; consumer `spec/ModularCurveHeckeConsumer.lean`
Zones X1-A/B/C/DEF/FF/CAP 0 errors / 0 warnings; `#print axioms
ModularCurve.heckeDiamondInputsAll` = `[propext, Classical.choice, Quot.sound]`;
whole-tree `lake build` green (4,961 jobs); every one of the 11 `X1/` modules is
warning-free.

| set | modules (new lines) | checker delta | written estimate vs actual |
|---|---|---|---|
| A — definitions + AC along-lemmas | `X1/{Defs 144, HeckeOperator 209, Diamond 127, HeckeModule 43}` (523) + 6 edits | +56 | ≈300 defs → 523 |
| B — the two `JOneES` nodes | `X1/{Integral 53, FunctionField 1,141, FunctionFieldBaseChange 357}` (1,551) | +7 | ≈1,115 → 1,551 |
| C — Hecke/diamond face | `X1/{QExpandStretch 218, DiamondAut 739, BaseChangeCover 186}` (1,143) | +4 | ≈950 → 1,143 |
| capstone (manager) | `X1/Inputs` (≈330) | +1 | ≈110 assembly |
| **total** | **≈3,550 new module lines** | **+68** | initial cone estimate 2,100–2,700 |

The written total exceeds the planning range because the pin's helpers are
transcribed `private` in full (the estimate priced content, and the port also
carries module/declaration docs); the *mathematical* budget was accurate: the
only genuine route risk (the general-`L` cover) came in at half price.

## What the effort reused (the reason it was cheap)

- `AlgebraicCurve.Divisor.pushforwardNormFormula`: the port already proved it
  `private` as `…_of_finiteDimensional` (`Transcendence.lean:345`); the 903-content
  node became a public wrapper (SET-A).
- `ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0`: assembly over the
  ported SET-10 headlines (65 content → ≈12 written).
- The pin's `X1HDIGeneric` generics: three of six collapse to the ported
  `AlgebraicCurve.isAlgebraic_adjoin_of_transcendental` and
  `AlgebraicCurve.separableAlong_of_charZero`.
- `linearIndependent_coeffEmb` plus mathlib's scoped
  `IsFractionRing (Algebra.adjoin F S) (adjoin F S)` made the cover
  tensor-product route possible (281 → 135 content).

## Deferred (registered in [CARRY-FORWARD.md](../CARRY-FORWARD.md))

The `Pic0` action/torsion block (`Pic0.torsion`, the `SemilinearAut`
`SMul`/`DistribMulAction`/`torsionRep` actions, `ModularCurve.PicAction`) and the
five declarations it gates (`JOne.torsionGaloisRep{,_apply}`,
`coe_torsionGaloisRep_apply`, `diamondOneBar{,_apply}`). Not on this cone; the
successor targets' first mini-set.

## Refactor-round items (measured duplicates; not cut mid-set)

1. `diamondSlash`/`coe_diamondSlash` now exist as `private` copies in three
   places (`Gamma0Integral.lean:1425,1449` and `X1/DiamondAut.lean`); promote one
   pair to `ModularForm.Level` (`slashOfMemGamma0` is the `CuspForm` sibling).
2. The four `JOneESAlg`/`JOneESAlgBC` A1 `LaurentSeries` lemmas are duplicated
   `private` across `X1/FunctionField.lean` and `X1/FunctionFieldBaseChange.lean`
   (the pin duplicates them too); promote one copy.
3. `Gamma1Basis.lean:810` keeps a `private isIntegralQExp_iff` now shadowed by the
   public `X1/Integral.lean` copy.

## Friction that generalizes (folded into the playbook drift list where reusable)

- **Deprecations in `v4.34.0`:** `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`;
  `ModularForm.coe_sub/add/neg/zero` → `FunLike.coe_*`; `if_neg` → `ite_eq_right`;
  `IsGLPos.coe_smul`/`smul_apply` → `FunLike.coe_smul`/`smul_apply`; `qExpansion_pow`
  and `qExpansion_mcast` are **protected** (`ModularForm.qExpansion_pow`).
- **A pin `private` prelude can be un-importable even when a sibling module has
  it.** The `X1HeckeOperator` supply block, the `JOneESAlg` A1 block, and
  `diamondSlash` all duplicate ported/other-module material; the port resolves
  each by importing (supply block) or by a recorded private duplicate
  (the others).
- **`private` re-declaration over an imported public name is rejected.** The
  `restrictForm` promotion forced deleting a third `private` copy in
  `WeightOne/IntegralWeightOneForm.lean`; the promotion had to sit in the pin's
  `section Restrict`/`variable` block for the textual checker.
- **A failed `private` helper can surface as a kernel `unknown constant _private…`
  on a later declaration**, not at the failing line (the `A12 Γ` binder error).
- **`!![…]`–`SL(2, ℤ)` coercions under a membership goal need
  `backward.isDefEq.respectTransparency.types false`** (the `cocycle` proof; same
  as `Gamma0Integral.lean:1465`).
- **The pin's `variable` structure is load-bearing for the checker.** A promotion
  or transcription under the wrong `variable`/`section` shape mismatches even when
  the elaborated type is identical; the fix is to mirror the pin's block.
