# WORKORDER-I3 — the real Iwasawa engine (wave 2, tier 3)

Read [TOPIC-iwasawa-analytic-core.md](TOPIC-iwasawa-analytic-core.md) first; it carries the
mathematics, the measurement, the definition layer and the port structure this order executes. The
shared generic Fourier bound is **landed** at `MeasureTheory/FourierDecay.lean` (tier 1); the real
half has **no definition module** (the pin has no `Def_AutomorphicForm_RealIwasawa`, and no wrapper
statement names a real definition — topic §4c).

This order is **independent of WORKORDER-I1/I2**: the real namespaces are disjoint and the only
shared item is the landed `MeasureTheory/FourierDecay`. It may run in parallel with I1; every
`lake build` is serialized under `flock`.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. Scope

Port **once** the real-Iwasawa development that four self-contained pin `S_` files carry in full
(3,838 raw lines → **1,949 net new** after dedup, 207 declaration groups) into the three tier-3
engine modules of §2.

| kernel `AutomorphicForm.RealIwasawa.Engine.<name>` | pin `S_` file | own lines | pin internal proof |
|---|---|---:|---|
| `contDiff_and_exists_bound_iteratedFDeriv_kR_apply` | `S_…_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean` | 744 | `RealKTower.contDiff_and_exists_bound` |
| `norm_fourierIntegral_cpow_rad_mul_le_polyDecay` | `S_…_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean` | 1,209 | `RealDecay.norm_fourierIntegral_cpow_radR_mul_le_polyDecay` |
| `exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact` | `S_…_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean` | 1,530 | `B2bRUnif.main` |
| `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` | `S_…_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean` | 355 | `clause_i`, `clause_ii`, `clause_iii` |

Each is taken whole (playbook §2.3): the engine is the union of the declarations the four `solution`
proofs drag, written once. The complex engine (I1/I2) is **explicitly not this order**; also **not**
this order: the manager's façade, the checker, the register, any other `S_` file, and any existing
module.

## 2. Source and deliverable

| module | role | kernels |
|---|---|---|
| `FLTForHuman/AutomorphicForm/Iwasawa/Real/Core.lean` | the rotation engine: the real proof-local vocabulary (`rot`, `rotGL`, `weylUnip`, `botNormSq`, `foot`, `center`, `dir`, `botRow`, `rad`, `borel`, `unipR`, `weylR`, `radFloor`, `angle`, `logLine`, `invTower`, `towerD`, `towerRatio`, `prim`, `weight`, `weightFun`, `IsOneParamGroup`, …) and the smoothness/bound kernel | `Engine.contDiff_and_exists_bound_iteratedFDeriv_kR_apply` |
| `FLTForHuman/AutomorphicForm/Iwasawa/Real/Decay.lean` | the decay engine | `Engine.norm_fourierIntegral_cpow_rad_mul_le_polyDecay`, `Engine.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact` |
| `FLTForHuman/AutomorphicForm/Iwasawa/Real/Continuation.lean` | the real-place Whittaker (Jacquet) integral | `Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` |

`Core.lean` imports `FLTForHuman.MeasureTheory.FourierDecay`; `Decay.lean` imports `Core.lean`;
`Continuation.lean` imports `Decay.lean`. None imports the façade. The shared-block structure is in
`tools/deps/build/riwasa4_advise.json` (and its `port_plan` output); the worker re-runs
`port_advise.py --nodes "<the four real nodes>"` at the end for parity. Blocks to write once: the
`kR`/`rot` common block (92 decls / 619 lines, the 3 files) and the non-uniform extension (40 decls /
512 lines, the two `norm` files).

## 3. The transcription rules

Same rules as WORKORDER-I1 §3, with two real-specific decisions:

* Replace the pin's mangled chapter `P2MW.S_<stem>.M4aP3B` by **`AutomorphicForm.RealIwasawa`**,
  keeping the pin's sub-namespaces (`RealIwasawa`, `RealKTower`, `RealDecay`, …) and every
  declaration name verbatim. The real vocabulary is **proof-local** (there is no `Def_` module): it
  is transcribed once, public at the pin's names, in `Real/Core.lean`.
* **The real `rot` is not reconciled.** The pin's `rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]` shares a last name with the port's
  `RepTheory.AntiInvolutionHaar.rot (p q : ℝ) := !![p, q; -q, p]` but **not** its statement. Keep
  the real one at `AutomorphicForm.RealIwasawa.rot`; do **not** promote, rename or import the other
  (topic §4d). Likewise `weylR` is a different statement from the port-`private`
  `CuspForm.FrickeHecke.frickeGL` — re-derive it here, do not promote.
* For each row of §1 declare the public kernel at `AutomorphicForm.RealIwasawa.Engine.<name>` with
  the `Theorems/` wrapper's statement; do **not** declare it at the
  `AutomorphicForm.RealIwasawa.<name>` headline spelling (the manager's façade owns that).
* The pin's local copy of `B2bCKit.pow_mul_norm_fourierIntegral_le_of_coercive` (and
  `gate_degenerate`) is the landed `MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive`:
  import it, do not re-transcribe it.
* Every transcribed declaration carries `-- pin: <name> (S_<stem>.lean:<line>)`.

## 4. Route, mathlib map, and stop conditions

Identical to WORKORDER-I1 §4: statements are the pin's (stop if one must change); the route is
mathlib's `VectorFourier`/`iteratedFDeriv`/`Real.rpow`/`Real.sqrt`/`Complex.exp`/integrability API
with the same `v4.34.0` renames; no new public helper (re-derive `private` and report); no promotion
and no edit to an existing module (stop and report with a `build_ladder.py --edit` price if one is
needed). **Stop and report** if the four kernels cannot be kept free of an import inversion, or if a
real statement needs a definition the pin does not name.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: tier-0 loop until `Core.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Iwasawa.Real.Core`;
then `…Real.Decay`, then `…Real.Continuation`. No bare `lake build`, no dependent, no façade.

**Build-time blow-up protocol.** The named risks are `B2bRUnif.main` (the uniform-in-`g`/`u` decay,
the same `M0' * 2^N + MN' * (2/c)^N + 1` case split as the complex uniform form), the
`norm_iteratedFDeriv_comp_log_rad_le` estimates, and the `Real.rpow`/`Complex.exp` differentiations.
Diagnose at the low cap, fix the inference, report.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `Core.lean`, `Decay.lean`, `Continuation.lean` | exit 0, **0 warnings**, no forbidden token |
| tier-1 builds of the three modules | green; record jobs and wall/user time |
| union parity against `port_advise.py`/`port_plan.py` on the four real nodes | the 92 + 40 shared names present once each; none invented |
| the four `AutomorphicForm.RealIwasawa.Engine.*` kernels | present, public, statements equal to their `Theorems/` wrappers |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring.

## 7. Report shape

As WORKORDER-I1 §7, plus: the `rot`/`weylR` non-promotions confirmed, and the real vocabulary's
public names listed with their `-- pin:` provenance.

## 8. Results as landed

Worker report 2026-10-14; manager review same day.

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `Real/Core.lean` | 819 | 113 | 0 | exit 0, 0 warnings (5.29/9.36/1.99 s) | 3,055 jobs, 5.1 s build (8.09 s wall) |
| `Real/Decay.lean` | 872 | 53 | 0 | exit 0, 0 warnings (17.10/25.91/2.04 s) | 3,062 jobs, 14 s build |
| `Real/Continuation.lean` | 414 | 1 | 40 | exit 0, 0 warnings (4.41/7.07/1.77 s) | 3,079 jobs, 4.0 s build |

The four kernels are public under `AutomorphicForm.RealIwasawa.Engine.*` with the wrapper
statements; the manager re-verified all four as **byte-equal to their `Theorems/` wrappers** with
the checker's own parser (0 diff). **No heartbeat blow-up**: every declaration, including the named
risks `B2bRUnif.main` and the `rpow`/`exp` differentiations, clears the 200,000 cap; the pin's
heartbeat markers are dropped. No statement changed; proof-only adaptations were two `open`s
(`ScalarMajorant`, the pin's `open … HARCHR in`), one added mathlib import
(`…JapaneseBracket`), a dropped `open intervalIntegral` (ambiguity), and one v4.34 rename
(`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`). No helper re-derived; the 40 pin-`private`
`Continuation` helpers stay `private`; no declaration moved; no promotion needed (the `rot`/`weylR`
non-promotions are confirmed). The pin `M4aP3B.FourierDecay` block is imported from
`MeasureTheory.FourierDecay.lean`, not re-transcribed.

**Parity.** The 92-name `kR`/`rot` common block is present exactly once (0 missing, 0 duplicate);
the 42-name two-file `norm` block has 40 names once plus the two imported shared rows. Pin union
206 names; port 207 = 206 + the four kernels − {`gate_degenerate`, `pow_mul_norm_fourierIntegral_le_of_coercive`,
`solution`}; the only port-only names are the four kernels. All 167 public rows carry `-- pin:`
provenance.

The manager's half:

| check | result |
|---|---|
| `Real/Estimates.lean` (tier 1) | 4 public headlines, statement-verified against the wrappers before the engines existed; tier-0 exit 0 / 0 warnings, tier-1 green (3,080 jobs, 3.1 s) |
| checker before I3 | 9660 identical, 0 mismatched, 0 missing, 38 own (9698) |
| checker after the façade | **9664** identical — delta **+4**, exactly the four headlines |
| one-token mutation (`1 < u.re` → `1 ≤ u.re` on `norm_fourierIntegral_cpow_rad_mul_le_polyDecay`) | exactly 1 mismatched (9663), reverted |
| `#print axioms` on all 4 kernels | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep on the three engines | clean |
| `git status` | only the three engine modules + the manager's files; no existing module edited |

Wiring: the four real wrappers then their four `S_` files appended last to `SOURCES`;
`FLTForHuman/AutomorphicForm/Iwasawa/Real/Estimates.lean` appended last to `PORT_FILES`. The three
engines stay tier 3 and are recorded in `spec/UNWIRED-PUBLIC.md`.

**Deviation from the order (recorded).** The order's §2 vocabulary list names `weight`/`weightFun`
among the real proof-local defs; the pin's real half has no such `def`s (only `weight_eq`/
`weightFun_eq`, with the weight spelled inline). Nothing was invented. Also, `spec/UNWIRED-PUBLIC.md`
was regenerated mid-wave rather than at close-out (a worker ran the writer); the manager re-runs it
once I1/I2 have landed so the register reflects the final tree.
