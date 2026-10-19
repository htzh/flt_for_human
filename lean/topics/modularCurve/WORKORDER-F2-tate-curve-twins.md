# WORKORDER-F2 — the `BridgeX` twin/triplet development (tier 3)

**Status: landed 2026-10-13.** Read [TOPIC-tate-curve-twins.md](TOPIC-tate-curve-twins.md) first; it
carries the mathematics, the two equivalence classes, the definition layer and the port structure
this order executes. The six definition modules are landed and wired (the topic's §3); this order
is the shared development between them and the five headlines.

*Results are in §8; the body below is the order as dispatched.*

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. Scope

Port **once** the `ModularCurve.BridgeX` development that five near-identical pin `S_` files carry
in full (4,952 raw lines → 1,338 net new / 75 groups), into the two engine modules of §2, tier 3.
The five public headline façades are **explicitly not this order** — the manager writes
`TateCurve/QPow.lean` afterwards. Also **not** this order: the definition layer (already in),
the checker, `UNWIRED-PUBLIC.md`, any other `S_` file, and any existing module.

Each block is taken **whole** (playbook §2.3).

## 2. Source and deliverable

The representative transcription source is
`P2M/Sol/S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean` (1,343 lines,
pin `aa2d8b3`) — the pair file, which carries both shared blocks. The four other files
(`…_pointY_…_snd` and the triplet `…_curve_X_pow_eq_tateBase`, `…_pointX_C_eq_tateToricPoint_fst`,
`…_pointY_C_eq_tateToricPoint_snd`) are identical up to their namespace stem and final `solution`;
the `Theorems/Thm_ModularCurve_<name>.lean` wrappers are the statement authority for the five
kernels.

| module | pin sections (representative line ranges) | ≈ lines |
|---|---|---:|
| `FLTForHuman/ModularCurve/TateCurve/Bridge.lean` | the common `ModularCurve.BridgeX` blocks, lines **18–751**: `norm_le_norm_X_pow_iff`/`hasSum_of_coeff`/`tsum_eq_of_coeff`; `expand` and its coefficient lemmas; `lambertSeries_mul_one_sub_X`/`X_pow_ne_one`/`term_X_pow_eq_expand`; `coeffSum_X_pow`/`laurentOfInt_mk`/`a₄_X_pow`/`a₆_X_pow`/`curve_X_pow_eq_tateBase`; the `x`-series block (`coeff_one_sub_C_mul_X_mul` … `hasSum_xTerm_toric`); `s₁_X_pow` … `pointX_toric`; the `y`-series block (`ySeries_identity` … `pointY_toric`) | 738 |
| `FLTForHuman/ModularCurve/TateCurve/NonToricSlot.lean` | the non-toric extension, lines **758–1335**: `hasSum_expand_gen`, `expand_X'`, `xfun_single`, `yfun_single`, the `Reindex`/`Reindex2` divisor reorganisations (`sum_sum_divisors_{pos,neg,diag}`), the `Slot` block (`C_mul_X_pow` … `s₁_X_pow'`), `SlotMain` (`hasSum_xTerm_slot`, `hasSum_yTerm_slot`, `sum_split_zero`), and `pointX_slot`/`pointY_slot` | 573 |

`Slot.lean` imports `Bridge.lean`; both import the six definition modules
(`FLTForHuman.Algebra.LaurentSeriesXAdic`, `…TateCurve.QSeries`, `…TateCurve.PointSeries`,
`…ModularForms.KatzLevelOne`, `…ModularCurve.Defs.KatzLevelP`, `…ModularCurve.Defs.KatzLevelPCusps`)
and the already-ported `…ModularCurve.Defs.TateSlots`. They must not import `QPow.lean`.

## 3. The transcription rules

### 3.1 Names, namespaces, visibility

* Keep `namespace ModularCurve` / `namespace BridgeX` and the pin's names **verbatim**, with the
  single exception of §3.2. Drop the outer `P2MW.S_ModularCurve_tateCurve_…` namespace and the
  `p2m_*` lines; keep `set_option autoImplicit false`, `noncomputable section` and the pin's
  `open` lines.
* **`private` stays `private`** for every pin-`private` helper the five kernels do not need; the
  pin's public declarations stay **public**.
* Every transcribed declaration carries, immediately above it (above any `@[...]`), a provenance
  comment `-- pin: <name> (S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean:<line>)`.
  `tools/deps/unwired_register.py` reads it; a missing comment shows as `—` and is a defect.

### 3.2 The five kernels — the manager's interface

Promote each kernel to **public** under `ModularCurve.TateCurve.<kernel>` and state it with the
**`Theorems/` wrapper's binders** (the wrapper is the checker's statement authority, playbook
§7.4). Do **not** declare any of the five at its `ModularCurve.<name>` public wrapper name — that
name belongs to the manager's façade.

| promoted kernel | module | pin kernel (representative line) |
|---|---|---|
| `ModularCurve.TateCurve.curve_X_pow_eq_tateBase` | Bridge | `BridgeX.curve_X_pow_eq_tateBase` (:326) |
| `ModularCurve.TateCurve.pointX_toric` | Bridge | `BridgeX.pointX_toric` (:541) |
| `ModularCurve.TateCurve.pointY_toric` | Bridge | `BridgeX.pointY_toric` (:717) |
| `ModularCurve.TateCurve.pointX_slot` | Slot | `BridgeX.pointX_slot` (:1282) |
| `ModularCurve.TateCurve.pointY_slot` | Slot | `BridgeX.pointY_slot` (:1305) |

The kernels' **statements** are the `Theorems/Thm_ModularCurve_{tateCurve_curve_X_pow_eq_tateBase,
tateCurve_pointX_C_eq_tateToricPoint_fst, tateCurve_pointY_C_eq_tateToricPoint_snd,
tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst, tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd}.lean`
statements; their **proofs** are the pin's bodies (`pointX_toric`'s statement is the `solution`'s
conclusion with `.1`, and so on).

## 4. Route, mathlib map, and stop conditions

* **Statements are the pin's** character-for-character after the checker's normalisation; a
  documented `v4.34.0` drift is the only permitted difference. Proofs are adapted freely. **If a
  proof needs a statement to change, stop and report.**
* Expected drift surface: `PowerSeries`/`HahnSeries` coefficient lemmas, `Finset` divisor sums,
  `tsum`/`HasSum` API, `NormedField`/`Valued` instance names on `LaurentSeries`, and the
  `WeierstrassCurve` `ΨSq`/`Φ`/`preΨ` division-polynomial API (the definition layer's
  `Defs/KatzLevelP.lean` shows the v4.34 import set). Adapt proofs, keep statements.
* **No new helpers beyond the pin's.** If a proof needs glue the pin does not have, re-derive it
  `private` in the same module and report it. **No promotion and no edit to any existing module.**
  If you believe a promotion is genuinely required, **stop and report** the declaration, host and
  `tools/deps/build_ladder.py --edit` price — the manager decides.
* **Stop and report** if a kernel's statement cannot be matched to its wrapper, if `Slot.lean`
  cannot be kept free of a `Bridge.lean` dependency inversion, or if a block is not self-contained
  against the six definition modules + mathlib.
* Do not touch `spec/old_check_stmts.py`, `spec/UNWIRED-PUBLIC.md`, the definition modules, or
  any other existing module. The engine modules stay **tier 3** (not listed in `PORT_FILES`).

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is **low
> on purpose**: a declaration that exceeds it has an instance-inference defect, and the low cap is
> what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: iterate at the low cap until each module is exit 0 with **0 warnings**; then
`flock .lake/flt_build.lock timeout 300 lake build <module>` for that module. Build only these two
modules and their dependencies — no bare `lake build`, no dependent, no consumer.

**Build-time blow-up protocol.** The named risks are `hasSum_expand` (93 lines) and
`sum_sum_divisors_pos`/`_neg` (94 lines each); if one exceeds the low cap, diagnose with
`set_option diagnostics true` / `trace.Meta.synthInstance true` in a scratch copy (never commit
it), fix the inference, and re-run. Report the declaration and the fix.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `Bridge.lean` then `Slot.lean` | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.ModularCurve.TateCurve.{Bridge,Slot}` | both green; record jobs and wall/user time |
| union parity against `port_advise`/`port_plan` on the five files | 46 + 23 = 69 shared names present once each; none invented |
| the five `ModularCurve.TateCurve.*` kernels | present, public, statements equal to their `Theorems/` wrappers |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

Do **not** run `spec/old_check_stmts.py` and do **not** edit the register. No wiring for this
order: the engines are tier 3.

## 7. Report shape

1. The two module paths, final line counts, and the pin section → module map as built.
2. Declaration counts per module, public / `private`; confirm the five `ModularCurve.TateCurve.*`
   kernels are public and match §3.2.
3. Tier-0 and tier-1 results, with wall/user/sys times and jobs.
4. Every build-time blow-up, the declaration, the diagnosis, and the fix.
5. Any statement that could not be transcribed verbatim, and why (stop condition).
6. Any helper re-derived `private`, and any promotion you stopped on.
7. The `unwired_register.py --check` output for the two modules.

## 8. Results as landed (2026-10-13)

| module | lines | public | private | tier-0 | tier-1 (cold) |
|---|---:|---:|---:|---|---|
| `TateCurve/Bridge.lean` | 839 | 50 | 0 | exit 0, 0 warnings | 3,177 jobs, module 5.6 s, wall 7.78 s |
| `TateCurve/NonToricSlot.lean` | 674 | 25 | 0 | exit 0, 0 warnings | 3,179 jobs, module 5.1 s, wall 7.34 s |

`Slot.lean` imports `Bridge.lean` and the already-ported `ModularCurve.TateSlots.SlotCoeff` (the two
slot proofs reach `coeff_slotSubst_tateUnivX/Y` through the tier-3 kernels rather than the pin's
tier-1 wrappers). The five kernels are public under `ModularCurve.TateCurve.*` with the wrapper
binders; their statements are byte-identical to the five `Theorems/` wrappers. **No build-time
blow-up**: the pin's six heartbeat-bump markers were dropped and every declaration clears the
200,000 cap, including the named `hasSum_expand` and `sum_sum_divisors_{pos,neg}`. No statement
changed; proof-only adaptations were the v4.34 deprecation renames, three unused-binder references,
and the `TateSlots.*` qualification. No `private` helper, no promotion; no existing module edited.

**Union parity.** The representative pin block 18–751 holds **47** declarations and 758–1335 holds
**23**; all 47 are in all five files and all 23 in both pair files, so the shared surface is
**70**, each transcribed once, none invented. (`port_plan`'s 69 `in_target` factors omit
`expand_coeff_mul` because it is in no headline's dependency closure; it is transcribed, with its
provenance comment.)

The manager's half:

| check | result |
|---|---|
| `TateCurve/QPow.lean` (tier 1) | 5 public headlines, tier-0 exit 0 / 0 warnings, tier-1 green |
| checker before F2 | 9318 identical, 0 mismatched, 0 missing, 38 own (9356) |
| checker after the six definition modules | **9535** identical — delta **+217**, exactly the def layer |
| checker after the headline façade | **9540** identical, 0 mismatched, 0 missing, 38 own (9578) — delta **+5**, exactly the façade |
| one-token mutation (`(hMut : True)` on `tateCurve_curve_X_pow_eq_tateBase`) | exactly 1 mismatched (9539), reverted |
| `#print axioms` on all 5 headlines | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep | clean |
| `unwired_register.py` | 80 modules / 1,981 public / 1,693 with pin original; Bridge 50/50 and Slot 25/25 rows, none missing a pin original |

Wiring: the five wrappers then their five `S_` files appended last to `SOURCES`;
`FLTForHuman/ModularCurve/TateCurve/QPow.lean` appended last to `PORT_FILES`. The engine stays
tier 3 and is recorded in `spec/UNWIRED-PUBLIC.md`.

**Tool artifact (for the register's owner).** `unwired_register.py` dedups by bare name, first
occurrence first, so the promoted rows show the pin-named `ModularCurve.BridgeX.<kernel>` rather
than the importable `ModularCurve.TateCurve.<kernel>`; a by-line rather than by-bare-name lookup
would fix the dotted column.
