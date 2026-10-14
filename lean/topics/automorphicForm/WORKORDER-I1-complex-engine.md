# WORKORDER-I1 — the complex Iwasawa engine, base layer (wave 1, tier 3)

Read [TOPIC-iwasawa-analytic-core.md](TOPIC-iwasawa-analytic-core.md) first; it carries the
mathematics, the measurement, the definition layer and the port structure this order executes. The
definition layer of §4 is **landed** (`Complex/Basic.lean`, `MeasureTheory/FourierDecay.lean`, both
tier 1, checker 9654 → 9660); this order is the complex engine between it and the manager's
headline façade.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. Scope

Port **once** the shared complex-Iwasawa development that six near-identical self-contained pin `S_`
files carry in full (6,540 raw lines for the nine complex nodes → **3,368 net new** after dedup, 172
declaration groups), into the two tier-3 engine modules of §2. This order covers the **six layer-0
kernels**:

| kernel `AutomorphicForm.ComplexIwasawa.Engine.<name>` | pin `S_` file | own lines |
|---|---|---:|
| `contDiff_and_exists_bound_iteratedFDeriv_kC_apply` | `S_…_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean` | 1,324 |
| `exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact` | `S_…_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean` | 1,754 |
| `kC_mem_specialUnitaryGroup` | `S_…_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean` | 97 |
| `weyl_mul_unipotent_mul_eq_borel_mul_kC` | `S_…_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean` | 109 |
| `exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact` | `S_…_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean` | 234 |
| `norm_fourierIntegral_cpow_radC_mul_le_polyDecay` | `S_…_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean` | 1,955 |

The three complex **successors** (`contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact`,
`exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact`,
`continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`) are **explicitly not this
order** — WORKORDER-I2. Also **not** this order: the manager's façade, the real engine
(WORKORDER-I3), the checker, `spec/UNWIRED-PUBLIC.md`, any other `S_` file, and any existing module.

Each kernel is taken **whole** (playbook §2.3): the engine is the union of the declarations the six
`solution` proofs drag, written once.

## 2. Source and deliverable

The pin's `S_` files are self-contained: each carries the whole prelude it needs under the mangled
chapter `P2MW.S_<stem>.M4aP3C.*`, ending in `theorem solution … := <internal kernel> args` (or an
inline proof). The representative transcription sources are the six files above plus their
`Theorems/Thm_AutomorphicForm_ComplexIwasawa_<name>.lean` wrappers (the **statement authority**).

| module | role | kernels |
|---|---|---|
| `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Core.lean` | the shared complex engine: the `radC`/`kC` prelude and the common decay block, written **once**, plus the compact-factor and decomposition kernels | `Engine.contDiff_and_exists_bound_iteratedFDeriv_kC_apply`, `Engine.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact`, `Engine.kC_mem_specialUnitaryGroup`, `Engine.weyl_mul_unipotent_mul_eq_borel_mul_kC` |
| `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Decay.lean` | the decay engine: the integrability bound and the pointwise Fourier-decay kernel | `Engine.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact`, `Engine.norm_fourierIntegral_cpow_radC_mul_le_polyDecay` |

`Core.lean` imports `FLTForHuman.AutomorphicForm.Iwasawa.Complex.Basic` (the def layer) and
`FLTForHuman.MeasureTheory.FourierDecay` (the shared generic bound);
`Decay.lean` imports `Core.lean`. Neither imports the façade. If the import DAG demands it, a
declaration may move between the two modules — report the move — but `Core` must not depend on
`Decay`.

The shared-block structure is already measured in
`tools/deps/build/ciwasa9_advise.json` (and its `port_plan` output); the worker re-runs
`port_advise.py --nodes "<the nine complex nodes>"` at the end for parity. The blocks to write once:

| block | decls | once-cost | files |
|---|---:|---:|---|
| complex common (the `CplxIwasawa`/`CplxSmooth` decay development) | 65 | 1,155 | the 3 big files |
| complex `radC` prelude | 8 | 102 | 5 files |
| decomposition pair | 6 | 74 | `kC_mem`, `weyl_mul` |

## 3. The transcription rules

### 3.1 Names, namespaces, visibility

* Replace the pin's mangled chapter `P2MW.S_<stem>.M4aP3C` by **`AutomorphicForm.ComplexIwasawa`**,
  keeping the pin's sub-namespaces (`CplxIwasawa`, `CplxSmooth`, `CplxDecay`, …) and every
  declaration name **verbatim**. Drop the outer namespace, the `p2m_*` lines and the per-file
  `solution` wrapper; keep the pin's `open` lines and `noncomputable section`, and add
  `set_option autoImplicit false`.
* **Do not redeclare the definition layer.** `AutomorphicForm.ComplexIwasawa.{botP,botQ,radC,kC}`
  come from `Complex/Basic.lean`; the pin's proof-local copies of those four (inside
  `M4aP3C.CplxIwasawa`) are byte-identical and are **dropped**. The remaining proof-local vocabulary
  (`borelC`, `weylUnipC`, `botNormSqC`, `centerC`, `weylC`, `unipC`, `kCGL`, `borelCGL`, `uQuad`,
  `lamQuad`, `floorK`, `conjCLM`, …) is transcribed once, public at the pin's name.
* A pin-`private` helper stays `private`; a pin-public declaration stays public. Every transcribed
  declaration carries, immediately above it, a provenance comment
  `-- pin: <name> (S_<stem>.lean:<line>)`; `tools/deps/unwired_register.py` reads it.
* **Do not invent a public name.** The pin's prelude names are the register's rows.

### 3.2 The six kernels — the manager's interface

For each row of §1 declare a public kernel at
**`AutomorphicForm.ComplexIwasawa.Engine.<name>`** whose **statement is the `Theorems/` wrapper's**
(playbook §4: the wrapper is the checker's authority; the pin's `solution` already states it). Its
proof is the pin's `solution` proof body — the pin's internal kernel applied, or the inline proof.
Do **not** declare any of the six at its `AutomorphicForm.ComplexIwasawa.<name>` headline spelling;
that name belongs to the manager's façade.

The pin's internal kernels the `solution`s call are, for orientation only (transcribe the
development, not merely these): `CplxIwasawa.contDiff_kC_apply` + `CplxSmooth.exists_bound_iteratedFDeriv_kC`
(first row), `KCUnif.main` (second), `conjTranspose_mul_kC_aux`/`det_kC_aux` (third, inline),
`radC_pos_aux`/`key_aux`/`weylUnip_eq_aux` (fourth, inline), `B2bCL2.main` (fifth),
`CplxDecay.norm_fourierIntegral_cpow_radC_mul_le_polyDecay` (sixth).

**Use the landed shared home.** The pin's local copy of
`B2bCKit.pow_mul_norm_fourierIntegral_le_of_coercive` (and `gate_degenerate`) is now
`MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive`
(`FLTForHuman/MeasureTheory/FourierDecay.lean`, already imported by `Core`); import it, do not
re-transcribe it.

## 4. Route, mathlib map, and stop conditions

* **Statements are the pin's** after the checker's normalisation; only a documented `v4.34.0` drift
  may differ. Proofs adapt freely. **If a proof needs a statement to change, stop and report.**
* The route is mathlib-first: `VectorFourier.fourierIntegral`,
  `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`
  (`Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:636`), `iteratedFDeriv`/`ContDiff`,
  `Real.rpow`/`Complex.cpow`, `Complex.normSq`, `Matrix`/`star`/`conjTranspose`, `MeasureTheory`
  integrability. The pin proves the Iwasawa decomposition itself — mathlib has none, a recorded
  negative, not a gap to route around.
* Likely `v4.34.0` renames: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`; `dif_neg` →
  `dite_eq_right`; `eventually_of_mem` → `Filter.eventually_of_mem`; `Set.range`/`Set.mem_univ`
  qualification; `Submodule.card_bot` → `AddSubgroup.card_bot`; `Real.pi`/`Complex` cpow lemmas moved
  under `Complex.cpow_*`; `Affine.Nonsingular`-style `W.toAffine` moves. Re-derive a monomorphic
  helper by `exact` when `rw`/`simp` will not fire through an unresolved instance.
* **No new public helpers beyond the pin's.** Glue the pin does not have is re-derived `private` in
  the same module and reported. **No promotion and no edit to any existing module.** If you believe a
  promotion is genuinely required, **stop and report** the declaration, host and
  `tools/deps/build_ladder.py --edit` price — the manager decides.
* **Stop and report** if a kernel's statement cannot be matched to its wrapper, if `Core` and
  `Decay` cannot be kept free of an import inversion, or if a block is not self-contained against
  `Complex/Basic` + `MeasureTheory/FourierDecay` + mathlib.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: iterate at the low cap until `Core.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Iwasawa.Complex.Core`;
then the same for `Decay.lean`. Build only these two modules and their dependencies — no bare
`lake build`, no dependent, no consumer, no façade.

**Build-time blow-up protocol.** The named risks are the 139/119/117-line
`exists_*_bound_iteratedFDeriv_*` chains and the `norm_fourierIntegral_*` integration by parts. If
one exceeds the low cap, diagnose with `set_option diagnostics true` /
`trace.Meta.synthInstance true` in a scratch copy (never commit it), fix the inference, re-run, and
report the declaration and the fix.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `Core.lean` then `Decay.lean` | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.AutomorphicForm.Iwasawa.Complex.{Core,Decay}` | both green; record jobs and wall/user time |
| union parity against `port_advise.py`/`port_plan.py` on the nine complex nodes | the 65 + 8 + 6 shared names present once each; none invented |
| the six `AutomorphicForm.ComplexIwasawa.Engine.*` kernels | present, public, statements equal to their `Theorems/` wrappers |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

Do **not** run `spec/check_flt_statements.py` and do **not** edit the register. No wiring for this
order: the engines are tier 3.

## 7. Report shape

1. The two module paths, final line counts, and the pin section → module map as built.
2. Declaration counts per module, public / `private`; confirm the six `Engine.*` kernels.
3. Tier-0 and tier-1 results, with wall/user/sys times and jobs.
4. Every build-time blow-up, the declaration, the diagnosis, and the fix.
5. Any statement that could not be transcribed verbatim, and why (stop condition).
6. Any helper re-derived `private`, any declaration moved between the two modules, and any
   promotion you stopped on.
7. The `unwired_register.py --check` output for the two modules.

## 8. Results as landed

Worker report 2026-10-14; manager review same day.

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `Complex/Core.lean` | 2,189 | 93 | 6 | exit 0, empty log (12.57/86.09/3.42 s) | 3,056 jobs, 12 s |
| `Complex/Decay.lean` | 554 | 11 | 5 | exit 0, empty log (7.49/14.16/1.78 s) | 3,106 jobs, 7.4 s |

The six kernels are public under `AutomorphicForm.ComplexIwasawa.Engine.*`; the manager re-verified
all six against their `Theorems/` wrappers with the checker's own parser. **Five are textually
verbatim; the sixth, `Engine.norm_fourierIntegral_cpow_radC_mul_le_polyDecay`, is stated with `g` as
a section variable** (`variable {g : …}`) rather than the wrapper's inline `{g : Matrix (Fin 2) (Fin 2) ℂ}`,
so its *source text* differs by that one binder while its *elaborated type* is the wrapper's. That is
harmless for a tier-3 engine (the checker never diffs it, and the manager's façade carries the
wrapper spelling — see below), but it is recorded here as a deliberate, reviewed deviation from the
order's "wrapper binders" line.

**No heartbeat blow-up**: the named 139/119/117-line `exists_*_bound_iteratedFDeriv_*` chains and
the `norm_fourierIntegral_*` integration by parts all clear the 200,000 cap; no `diagnostics` /
`trace.Meta.synthInstance` tracing was needed. No statement changed; proof-only adaptations were
seven v4.34 renames/shapes: `Finset.prod_le_prod` → `Finset.prod_le_prod₀` (5 sites), the
deprecated `ContinuousLinearMap.{smul,zero}_apply` → the root names (12 sites), one unreachable
`first | … | ring` branch removed, `set_option linter.unusedSimpArgs false` on one declaration (the
tree's existing convention for v4.34 simp-set drift), and three explicit imports replacing
`import Mathlib` (Decay adds `…Complex.Analytic`, `…ImproperIntegrals`, `…Complex.FiniteDimensional`).
No helper re-derived; the pin-`private` helpers (6 `RhoTwoAux.*_aux`, 5 `CplxDecay.*'`) stay
`private`; no declaration moved between the two modules; no promotion needed; no existing module
edited. Dedup drops: the four def-layer copies → `Complex/Basic.lean`, `B2bCL2`'s ten prelude copies
→ Core, the `M4aP3B.FourierDecay` block → `MeasureTheory/FourierDecay.lean`.

**Parity.** The three measured blocks are satisfied: 65 decls / 1,155 lines once (1,140 in-port),
8 / 102 (96 in-port), 6 / 74 (74 in-port). Direct check: 88 shared last names across the six `S_`
files — 82 present exactly once; `botP`/`botQ`/`radC`/`kC` 0× (homed in `Complex/Basic`); `solution`
0× (dropped); `main` 2× with distinct statements (`KCUnif.main`, `B2bCL2.main`). No invented names
beyond the six kernels, whose names are the wrappers' headlines.

The manager's half:

| check | result |
|---|---|
| `Complex/Estimates.lean` (tier 1) | the six base headlines, statement-verified against the wrappers, tier-0 exit 0 / 0 warnings, tier-1 green (3,107 jobs, 3.1 s) |
| checker before I1's façade | 9664 identical (after I3), 0 mismatched, 0 missing, 38 own (9702) |
| checker after the base façade | **9670** identical — delta **+6**, exactly the six base headlines |
| one-token mutation (`2 < u.re` → `1 < u.re` on the base norm headline) | exactly 1 mismatched (9669), reverted |
| `#print axioms` on all 6 kernels | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep on the two engines | clean |

Wiring: the six complex wrappers then their six `S_` files (the `norm` `S_` file was already listed
for the FourierDecay wire) appended last to `SOURCES`;
`FLTForHuman/AutomorphicForm/Iwasawa/Complex/Estimates.lean` appended last to `PORT_FILES`. The two
engines stay tier 3. The three successors are WORKORDER-I2 and were consolidated into the same
subject-named façade `Complex/Estimates.lean` (nine headlines), not a role-named `Headlines.lean`
(see the topic's naming note).
