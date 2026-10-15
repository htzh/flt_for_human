# WORKORDER-TO2a — `Def_DedekindDomain_IntegralClosure` (W2a)

Wave 2a of the twisted-orbital definition program
([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) §2). This pin module is the home
of `HeightOneSpectrum.Extension` (the places of `L` above a place `v` of `K`), which
`TwistedOrbital.piIntegers` needs and which is absent from mathlib. W1 is landed
([WORKORDER-TO1](WORKORDER-TO1-mathlib-supplements.md) §9): 111 modules / 3,118 public registered,
checker **9790 / 0 / 0 / 38 own**.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Tier 3, wires nothing:
checker delta **0**.

## 1. Scope

The pin node whole (playbook §2.3): `Definitions/Def_DedekindDomain_IntegralClosure.lean`,
**301 lines / 22 declarations**, in the pin's namespaces
(`IsDedekindDomain.HeightOneSpectrum` §`BaseChange`, then `IsDedekindDomain`):

`Extension` (:20), `mk_count_factors_map` (:22), `ramificationIdx_ne_zero` (:69),
`intValuation_comap` (:75), `valuation_comap` (:92), `isTorsionFree` (:103),
`Extension.finite` (:111), `Extension.fintype` (:128), `preimage_comap_finite` (:134),
`preimageComapFinset` (:139), `Ideal.sum_ramification_inertia_extensions` (:145),
`LinearEquivTensorProduct` (:188), `LinearEquivTensorProduct_symm_one_tmul` (:200),
`LinearEquivTensorProduct_symm_tmul` (:208), `linearEquivTensorProductModule` (:217),
`linearEquivTensorProductModuleLeft` (:230), `linearEquivTensorProductModuleLeft_restrictScalars`
(:252), `linearEquivTensorProductModule_symm_tmul` (:257), `linearEquivTensorProductModule_tmul`
(:261), `linearEquivTensorProductModuleLeft_symm_tmul` (:265),
`linearEquivTensorProductModuleLeft_tmul` (:269), `_root_.IsIntegralClosure.isLocalizedModule` (:281).

**Not this wave.** `Def_DedekindDomain_AdicValuation_InlineSpecific` (its residual, if any, is
determined and homed in W2b against `Completion_BaseChange`'s needs) and
`Def_DedekindDomain_Completion_BaseChange` (W2b). No other module.

## 2. Sources and deliverable

Proof and statement authority is the pin `Definitions/` file (a definition module, no `Theorems/`
wrapper): `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DedekindDomain_IntegralClosure.lean`;
the local clone `~/proj/fermats-last-theorem` is the working copy.

**Deliverable:** one new tier-3 module
`FLTForHuman/RingTheory/DedekindDomain/IntegralClosure.lean`, in the pin's namespaces, every
declaration **public at the pin's name**, `-- pin: <name> (Definitions/Def_DedekindDomain_IntegralClosure.lean:<line>)`
above each, and a header naming the subject, the pin and the substitution table. Nothing is wired.

## 3. Substitute first, then transcribe

For **every** declaration check mathlib `v4.34.0` before transcribing: mathlib already has the
`ramificationIdx`/`IsTorsionFree` *concepts* (`RingTheory/DedekindDomain/Different.lean`,
`RingTheory/DedekindDomain/IntegralClosure.lean`), and its `RingTheory/TensorProduct/Maps.lean` has
`algEquivOfLinearEquivTensorProduct`. Where a mathlib declaration has the pin's statement, import
it and do **not** re-declare; where mathlib has the underlying fact under another name, use it;
transcribe only what is genuinely absent, at the pin's name. Known absent so far and therefore to
be transcribed: `Extension`, `Extension.finite`, `Extension.fintype`, `Ideal.sum_ramification_inertia_extensions`,
`IsIntegralClosure.isLocalizedModule`, and the `LinearEquivTensorProduct*` family. **Report the
substitution table** (one row per pin declaration: mathlib name, or `transcribed`).

Replace any bare `import Mathlib` with explicit imports (the pin module may carry one).

## 4. Named risks and stop conditions

`Extension` is `{w : HeightOneSpectrum B // w.under A = v}`; `Extension.finite`/`Extension.fintype`
are the only reason it exists for this program (they feed `TwistedOrbital.piIntegers` and
`isOpen_piIntegers`). `Ideal.sum_ramification_inertia_extensions` and the
`linearEquivTensorProductModule*` family are the heavier proofs; `IsIntegralClosure.isLocalizedModule`
is an instance. Keep the low cap (§5) and fix inference rather than raising it.

**Stop and report** if: a declaration needs a `set_option` (quote it and the pin line); a mathlib
substitute has a different statement than the pin's; or the module cannot compile without editing
an existing one.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock`
> and bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

**Method when a declaration will not fit.** Keep the 200k cap and iterate fast to find the actual
instance. Isolate the declaration in a scratch copy; run `set_option diagnostics true in` /
`set_option trace.Meta.synthInstance true in` on it alone at the low cap; read which search fails
or unfolds a coercion; supply the instance (`letI`/`haveI` with the elaborated type,
`inferInstanceAs`, explicit `@`-application) or restructure so the search is not needed; re-run.
A declaration that will not fit is under-determined, not long. Only a non-fit that survives that
diagnosis is a stop-and-report.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `IntegralClosure.lean` | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) |
| tier-1 build | green; record jobs and wall/user/sys |
| substitution table | one row per pin declaration; every `transcribed` row present **once** at the pin's name |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring.

## 7. Report shape

Path, line count, public/`private` counts, tier-0 and tier-1 times, the substitution table, any
declaration that needed an instance fix (and the fix), any `set_option` you stopped on, and
`git status --porcelain` showing only the one new file.

## 8. The manager's half (not this order)

Register the module; then cut **W2b** (`Def_DedekindDomain_Completion_BaseChange`, the 1,160-line
core) together with whatever residual of `Def_DedekindDomain_AdicValuation_InlineSpecific` the
consumer actually reaches once mathlib substitutes are taken.
