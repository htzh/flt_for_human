# WORKORDER-I2 — the complex Iwasawa engine, successors (wave 1, tier 3)

Read [TOPIC-iwasawa-analytic-core.md](TOPIC-iwasawa-analytic-core.md) and
[WORKORDER-I1-complex-engine.md](WORKORDER-I1-complex-engine.md) first. I1 lands the six layer-0
kernels in `Complex/Core.lean` and `Complex/Decay.lean`; **this order may not start until I1 is
reviewed and those two modules are frozen**, and it must not edit them.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. Scope

Port the three complex **successors** — the nodes the six layer-0 kernels unblock — into two new
tier-3 engine modules. The six base kernels are **explicitly not this order** (they exist in I1's
modules); also **not** this order: the manager's façade, the real engine (WORKORDER-I3), the
checker, the register, any existing module.

| kernel `AutomorphicForm.ComplexIwasawa.Engine.<name>` | pin `S_` file | own lines | pin internal proof |
|---|---|---:|---|
| `contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact` | `S_…_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean` | 493 | `B2bCL1.main` |
| `exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` | `S_…_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean` | 203 | inline (its `solution` body) |
| `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` | `S_…_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean` | 371 | `continuousOn_integral_G`, `differentiableOn_integral_G`, `decay` |

Each is taken whole (playbook §2.3).

## 2. Source and deliverable

| module | role | kernels |
|---|---|---|
| `FLTForHuman/AutomorphicForm/Iwasawa/Complex/UniformDecay.lean` | the uniform-in-`g` symbol and decay forms | `Engine.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact`, `Engine.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` |
| `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Continuation.lean` | the complex-place Whittaker (Jacquet) integral | `Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` |

`UniformDecay.lean` imports `…Complex.Decay` and the already-ported
`FLTForHuman.MeasureTheory.FourierDecay`; `Continuation.lean` imports `…Complex.Decay` (and
`UniformDecay` if the proof needs it). Neither imports the façade. The base kernels are reached as
`AutomorphicForm.ComplexIwasawa.Engine.<base name>` — the pin's proof references its siblings by
their public wrapper names (`AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact`,
`AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact`,
`AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply`); in the port these
are the `Engine.*` kernels.

The pin's local copy of `B2bCKit.pow_mul_norm_fourierIntegral_le_of_coercive` is the landed
`MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive`: import it, do not
re-transcribe it.

## 3. The transcription rules

The same rules as WORKORDER-I1 §3. In brief: replace the pin's `P2MW.S_<stem>.M4aP3C` chapter by
`AutomorphicForm.ComplexIwasawa`, keep the pin's sub-namespaces and declaration names verbatim, drop
the outer namespace/`p2m_*`/`solution` wrapper, add `set_option autoImplicit false`, do not
redeclare the definition layer (`Complex/Basic`), and add a
`-- pin: <name> (S_<stem>.lean:<line>)` provenance comment to every transcribed declaration. For
each row of §1 declare the public kernel at `AutomorphicForm.ComplexIwasawa.Engine.<name>` with the
`Theorems/` wrapper's statement; do **not** declare it at the `AutomorphicForm.ComplexIwasawa.<name>`
headline spelling (the manager's façade owns that).

## 4. Route, mathlib map, and stop conditions

Identical to WORKORDER-I1 §4: statements are the pin's (stop if one must change); the route is
mathlib's `VectorFourier`/`iteratedFDeriv`/`Real.rpow`/`Complex.cpow`/integrability API with the
same `v4.34.0` renames; no new public helper (re-derive `private` and report); no promotion and no
edit to an existing module (stop and report with a `build_ladder.py --edit` price if one is needed).
Additionally, **stop and report** if a successor needs a base kernel whose statement differs from
the one I1 landed, or if `Continuation.lean` cannot be kept free of an import inversion.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: tier-0 loop until exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Iwasawa.Complex.UniformDecay`
and then `…Complex.Continuation`. No bare `lake build`, no dependent, no façade, and **do not edit
`Core.lean` or `Decay.lean`**.

**Build-time blow-up protocol.** The named risk is the inline proof of
`exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` (the
`M0' * 2^N + MN' * (2/c)^N + 1` case split and the `Real.rpow` comparisons). Diagnose at the low cap
with `diagnostics`/`trace.Meta.synthInstance`, fix the inference, report.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `UniformDecay.lean` then `Continuation.lean` | exit 0, **0 warnings**, no forbidden token |
| tier-1 builds of the two modules | green; record jobs and wall/user time |
| the three `Engine.*` kernels | present, public, statements equal to their `Theorems/` wrappers |
| base-kernel statements unchanged | `Core.lean`/`Decay.lean` byte-identical to I1's landing (`git diff` clean) |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring.

## 7. Report shape

As WORKORDER-I1 §7, plus: the exact base kernels consumed, and confirmation that I1's two modules
were not edited.

## 8. Results as landed

Worker report 2026-10-14; manager review same day.

| module | lines | public | private | tier-0 | tier-1 |
|---|---:|---:|---:|---|---|
| `Complex/UniformDecay.lean` | 524 | 16 | 0 | exit 0, 0 warnings (13.92/16.86 s) | 3,107 jobs, 15.02 s |
| `Complex/Continuation.lean` | 446 | 1 | 40 | exit 0, 0 warnings (6.56/15.75 s) | 3,108 jobs, 9.06 s |

The three kernels are public under `AutomorphicForm.ComplexIwasawa.Engine.*`; the manager
re-verified all three as byte-equal to their `Theorems/` wrappers with the checker's parser (0 diff).
Import DAG `Continuation → UniformDecay → Decay → Core`, no inversion. **No heartbeat blow-up** —
the inline `M0'·2^N + MN'·(2/c)^N + 1` case split and the `Real.rpow` comparisons clear the
200,000 cap. Only v4.34 proof adaptations: `Finset.prod_le_prod` → `Finset.prod_le_prod₀`, the
deprecated `ContinuousLinearMap.{add,smul}_apply` → the root names, `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq` (3 sites), and one redundant `all_goals try …` removed. No statement changed; no
helper invented; no declaration moved; no promotion; **I1's `Core.lean`/`Decay.lean` byte-identical**
(sha256 `e2ca5b11…` / `da8a950a…`, unchanged). Dedup drops: B2bCL1's eleven prelude copies → Core's
`CplxIwasawa`/`KCUnif`, four `cpow` helpers → Decay's `CplxDecay`, the pin's `B2bCKit.pow_mul_…`
→ the landed `MeasureTheory.FourierDecay`.

The manager's half:

| check | result |
|---|---|
| `Complex/Estimates.lean` (tier 1) | the three successors consolidated with I1's six into the nine-headline subject façade; tier-0 exit 0 / 0 warnings, tier-1 green (3,116 jobs, 3.4 s) |
| checker before I2's façade | 9670 identical, 0 mismatched, 0 missing, 38 own (9708) |
| checker after consolidation | **9673** identical — delta **+3**, exactly the three successors |
| one-token mutation (`2 < u.re` → `1 < u.re` on the uniform decay headline) | exactly 1 mismatched (9672), reverted |
| `#print axioms` on all 3 kernels | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep on the two engines | clean |

Wiring: the three successor wrappers then their three `S_` files appended last to `SOURCES`;
`…/Complex/Estimates.lean` appended last to `PORT_FILES`.

**Deviation (recorded).** The order named the successor façade `Complex/SuccessorHeadlines.lean`;
on review the manager consolidated it into the subject-named `Complex/Estimates.lean` instead
(a module is a mathematical role, not an artifact kind; the directory stays open to further
subjects). The parked draft `lean/tmp/IwasawaComplexHeadlines.draft.lean` is superseded.
