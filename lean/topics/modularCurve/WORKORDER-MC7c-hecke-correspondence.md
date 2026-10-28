# WORKORDER-MC7c — the β/α Hecke correspondence at `ℓ ∤ M`

Status: **landed 2026-10-27** (SET [MC-7](SET-MC7.md), order MC-7c). Module
`lean/FLTForHuman/ModularCurve/X1/HeckeCorrespondence.lean`, **738 lines**, namespace
`ModularCurve.X1HeckeCorrespondence`. Manager-reviewed: `check_port --force` **74 ok / 0 / 0**,
headline at the `Them_` wrapper `:12`; axioms `[propext, Classical.choice, Quot.sound]` on the
headline, `coeff_identity`, `qExpand_trace`, `emb_injective`; build 34 s, silent; `dedup` 0;
32 of the 105 pin declarations imported (the `twistFun` quartet, the whole `Separating` block
from `RelrankSol`/`JOneES.JOneESRat`, `coeffEmb_intSeriesC`, the `AutTrace` five), none re-proved.
Reviewer hygiene edits: the `haveILetI` suppression is gone (ten `haveI` → `have`), and `MC_all`
no longer needs `set_option linter.deprecated false`: `TensorProduct.inductionOn` derives the zero
case from `tmul 0 0`, so the explicit `| zero` branch was redundant — the proof uses the
eliminator directly and is option-free. Heartbeat profile recorded: at 100k hearts only
`key_identity` (and its consumer `coeff_identity`) fail; 200k is comfortable.

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd` | `P2M/Sol/S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean` | 868 | 105 | needed 1, cone consumers 1 / project 2 |

Read [SET-MC7.md](SET-MC7.md) first — §0.3 (the 934↔868 shared block), §5 (this order's traps).

**Pin**: `/home/haitao/proj/fermats-last-theorem` at `aa2d8b3`.
**Port**: `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

## 1. What the mathematics is

For `M` with `[NeZero M]`, `ℓ` prime with `ℓ ∤ M`, `HeckeBetaOneDefined M ℓ`, the diamond lift
data `hσ`, `hσ'`, `ω : Ω[x1FunctionFieldBar M / Qb]` and `n : ℤ`:

```
(diffQExp (correspondence heckeBetaOneBar heckeAlphaOneBar ω)).coeff n
  = (diffQExp ω).coeff (n * ℓ)
    + ℓ * (if (ℓ:ℤ) ∣ n then (diffQExp (correspondence (diamondAutBar M ℓ) id ω)).coeff (n / ℓ) else 0).
```

This is the trace computation over the `ℓ` embeddings: `xBar = E₆²/E₄³` on
`x1FunctionFieldBar M`, the `ℓ`-th roots of unity `ζ` give embeddings `emb` of the β-field into
`AlgebraicClosure (LaurentSeries Qb)`, and the coefficient identity is the sum over them
(`rootSum`, `twist`). The pin's `namespace R1G1H1`, nine sections; the assembly is `S_:665–830`:

| section | content | reuse |
|---|---|---|
| `Twist` | `twistFun` (`(c^n) * x.coeff n`), `support_twistFun`, `twistFun_single`, `twist`, `twist_qExpand_of_pow_eq_one` | `twistFun` is the ported `ModularCurve.qTwistFun` (`Defs/Twist.lean`, binder spelling) — check, then import or restate at the pin's shape |
| `Euler` | `qEuler_qExpand` | `qEuler`, `qExpand`, `qEuler_*` ported (`Defs/HeckeDifferential`, `Defs/Laurent`) |
| `Pull` | `diffQExp_pullbackAlong`, `pullbackAlong_pullbackAlong`, `pullbackAlong_id`, `diffQExp_smul` | `pullbackAlong_pullbackAlong` is ported (`AlgebraicCurve/Differential/PushPull`, `TraceAtPoints`) and `pullbackAlong_id` is written once in `AlgebraicCurve/Differential/AutTrace.lean` — **import both, do not copy**; `diffQExp` ported (`ModularCurve/Defs/HeckeDifferential`) |
| `AutTrace` | `separableAlong_algEquiv`, `trace_one_along_algEquiv`, `traceAlong_algEquiv`, `correspondence_algEquiv_id` | written **once**, in `AlgebraicCurve/Differential/AutTrace.lean` (manager-landed, namespace `AlgebraicCurve.Differential`) — import it; a one-line wrapper at the pin's binder shape is allowed, a second proof is not |
| `RootSum` | `twist_C`, `rootSum`, `rootSum_add/zero/C_mul/mul_of_fixed`, `sum_zpow_pow`, `rootSum_coeff` | new |
| `Separating` | `P4`, `P6`, `isIntegralQExp_E4/_E6`, `A12`, `B12`, `isIntegralQExp_A12/_B12`, the `P4` coefficient block, `intSeriesC_*`, `xq`, `xq_mem` | **all ported** (`X1/FunctionField.lean`, `JOneES.JOneESRat`; `XH/Relrank.lean`) — import, do not restate; the general `xq_mem`/`coeffEmb_intSeriesC` are the port's, so a specialised restatement is a one-line instantiation only |
| `TwistPS` | `intSeriesC_coeff_*`, `twist_intSeriesC`, `coeffEmb_intSeriesC`, `numB`, `denA`, `twist_injective`, `twist_ne_zero`, `PBs`, `PAs`, the `PBs`/`PAs` coefficients, `coeff_one_mul'`, `twist_sep`, `twist_twist` | new |
| `Trace` | `EE`, `ιE`, `ιE_injective`, `FXt`, `FUf`, `FUt`, `bβ`, `bα`, `isScalarTower_beta`, `finrank_beta`, `finiteDimensional_beta`, `separableAlong_beta`, `sigmaTwist`, `ALData`, `sigmaLast`, `zu`, `zu_pow`, `emb`, `xBar`, `coe_xBar`, `emb_injective`, `emb_bijective`, `qExpand_trace` | new; `heckeBetaOneBar`/`heckeAlphaOneBar` ported (`Defs/X1HeckeOperator`), `HeckeBetaOneDefined`, `heckeAlphaC`/`finrankAlong_heckeBetaOneBar` (`X1/HeckeDegree.lean`) |
| `Assembly` | `coeff_C_mul`, `diffQExp_pullback_beta`, `diffQExp_pullback_w_beta/_alpha`, `twist_fix`, `MC`, `MC_base/smul/add/zero/all`, `key_identity`, `coeff_identity` | new |

## 2. Module plan — one new module

**`lean/FLTForHuman/ModularCurve/X1/HeckeCorrespondence.lean`**, imports (per SET-MC7 §4):

```lean
import FLTForHuman.ModularCurve.X1.HeckeDegree
import FLTForHuman.ModularCurve.X1.AtkinLehnerExchange
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.HeckeDifferential
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Differential.TraceDiff
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
```

Wire (leading `/- … -/` block), exactly two lines:

```
spec-pin: Theorems/Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean
spec-pin: P2M/Sol/S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd.lean
```

Statement authority: the `Theorems/` wrapper (33 lines) — its binder block verbatim (`M`,
`[NeZero M]`, `ℓ`, `[Fact ℓ.Prime]`, `hℓM`, `hβ`, `hσ`, `hσ'`, `ω`, `n`). The pin's `solution`
at `S_:837` is the same statement.

**Namespace.** The pin's `namespace R1G1H1` is a search label; do not transcribe it. Use
`namespace ModularCurve.X1HeckeCorrespondence` (or `ModularCurve`, as the checker only needs the
last names to match) — but keep `emb_injective` out of `AutomorphicForm.IwasawaWeyl`'s way: it is
a *different* statement that `port_advise` reports as a binder-skeleton pointer.

## 3. What the port already has — import, do not restate

`port_advise --nodes ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd`
(13 declarations / ≈78 lines): `isIntegralQExp_E6`, `isIntegralQExp_B12`, `xq_mem`,
`intSeriesC_ne_zero_of_constantCoeff`, `constantCoeff_P6` (`X1/FunctionField.lean`,
`JOneES.JOneESRat`); `isIntegralQExp_E4`, `coeff_one_P4`, `constantCoeff_P4` (`XH/Relrank.lean`);
`A12`, `B12` (`X1/FunctionField.lean`); `coeffEmb_intSeriesC` (`JqIntegralRatios.lean`, binder
spelling); `twistFun` (`Defs/Twist.lean`, `ModularCurve.qTwistFun`, binder spelling).

**Two live traps from this list.** `twistFun` ≠ `twist`: the ported `qTwistFun` is the pin's
`twistFun` (coefficient twist); the linear-map `twist` is *not* ported — write it. `A12`/`B12`
in the port are `JOneES.JOneESRat`'s, stated for `Γ` a section variable; the pin's 868 declares
them in its `Separating` section with `(Γ : Subgroup (GL (Fin 2) ℝ))` explicit — check the two
texts before deciding to import or restate.

## 4. Gates

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` on the file → **silent, zero
   warnings**. The pin sets `synthInstance.maxHeartbeats 1600000` and `maxHeartbeats 3200000`;
   **neither is transcribed**. A blow-up is a probe (playbook §6), not a `set_option`;
2. `flock /tmp/dsh-lake.lock timeout 600 lake build FLTForHuman.ModularCurve.X1.HeckeCorrespondence`
   → builds, `.olean` present; no tree build, no dependents;
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/HeckeCorrespondence.lean` →
   **0 mismatch, 0 missing**;
4. `#print axioms` on the headline (probe in `lean/tmp/probe-mc7c.lean`) →
   `[propext, Classical.choice, Quot.sound]`;
5. `python3 ../tools/deps/dedup.py --module …` and `move_dead.py`; the 934↔868 cluster is the
   recorded exception (SET-MC7 §0.3) — report, do not refactor;
6. no `sorry`/`admit`/`axiom`/`native_decide`; no `spec/decl_markers.tsv` row; no edits outside
   this module; do not commit or push.

## 5. Report back

`check_port`'s summary line, the axioms line, the build log's last two lines, the final line
count, the declarations kept `private` and why, the pin declarations skipped (and why), and the
one or two steps that cost wall time (`emb_bijective`, `key_identity`) with their measured
behaviour — that is the input to the next pass's heartbeat plan.
