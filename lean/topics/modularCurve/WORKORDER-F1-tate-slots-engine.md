# WORKORDER-F1 — the Tate-slot weight-4 engine (tier 3)

**Status: landed 2026-10-13.** Read [TOPIC-tate-slots-weight-four.md](TOPIC-tate-slots-weight-four.md)
first; it carries the mathematics, the measurement and the port structure this order executes. The
definition layer is already landed (`Defs/TateFormal.lean`, `Defs/TateSlots.lean`); this order is
the shared development between it and the headlines.

*Results are in §9; the body below is the order as dispatched.*

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. Scope

Port **once** the shared development that the fourteen `S_ModularCurve_*` files each carry in full
(23,094 raw lines → 1,671 net new / 134 declaration groups), into the two engine modules of §2,
tier 3. The fourteen **public headline façades are explicitly not this order** — the manager writes
`TateSlots/CoefficientFormulas.lean` afterwards. Also **not** this order: the definition layer, the checker,
`UNWIRED-PUBLIC.md`, any other `S_` file, and any existing module.

Each block is taken **whole** (playbook §2.3): transcribe every declaration of the named sections,
not only the rows the fourteen headlines reach.

## 2. Source and deliverable

The representative transcription source is
`P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean` (1,649 lines, pin `aa2d8b3`). All fourteen
`S_` files are identical up to the namespace stem and the final `solution`; use the representative
file for the text and the `Theorems/Thm_ModularCurve_<name>.lean` wrappers as the statement
authority for the fourteen kernels.

| module | pin sections (representative line ranges) | ≈ lines |
|---|---|---:|
| `FLTForHuman/ModularCurve/TateSlots/Convergence.lean` | `Seam` (286–298), `Kit` (300–378), `Platform` (380–421), `W4B` (430–483), `W4B.B2.GeomPS` (489–525), `W4B.B2.GeomLS` (528–604), `W4B.B2.Lambert` (607–733) | 430 |
| `FLTForHuman/ModularCurve/TateSlots/SlotCoeff.lean` | `BaseFaces` (19–51), `SlotSubstAPI` (53–78), `SpecS0`–`SpecS4` (80–284), `ModularCurve.OfPowerSeriesInt` (744–764, see §3.4), `ToricFaces` (767–781), `ToricCoeffs` (784–889), `W4Bdev.Abstract` (894–942), `W4Bdev` (945–1003), `EngineAux1` (1008–1039), `W4Bdev.Bridge` (1042–1421), `GeomHeads` (1427–1587), `Laurent` (1590–1635) | 1,090 |

Both modules import only `FLTForHuman.ModularCurve.Defs.TateSlots` (and, as the adapted proofs
require, specific mathlib modules — **never** a bare `import Mathlib`). They must not import each
other.

## 3. The transcription rules

### 3.1 Names, namespaces, visibility

* Keep the pin's namespaces `ModularCurve`, `ModularCurve.W4B`, `ModularCurve.W4B.B2`,
  `ModularCurve.W4Bdev` and the pin's names **verbatim**, with the single exception of §3.2.
* Drop the outer `namespace P2MW.S_ModularCurve_tsum_of_coeff_lt_eq_zero`. Drop the `p2m_export` /
  `p2m_open` / `p2m_reactivate` lines: `Defs/TateSlots.lean` already provides the definitions in
  `ModularCurve`. Keep `noncomputable section`, `set_option autoImplicit false` and the pin's
  `open` lines.
* **`private` stays `private`** for every pin-`private` helper the fourteen kernels do not need
  (playbook §4(b)); the pin's public declarations stay **public**.
* Every transcribed declaration carries, immediately above it (above any `@[...]`), a provenance
  comment

  ```lean
  -- pin: <pin name> (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:<line>)
  ```

  `tools/deps/unwired_register.py` reads it for the register's `pin original` column; a missing
  comment shows as `—` and is a defect. A port-only adapter is `-- port-only: <reason>`.

### 3.2 The fourteen kernels — the manager's interface

The pin writes each headline as a public `theorem solution` over a **`private`** kernel. Promote
each kernel to **public** under the uniform port name `ModularCurve.TateSlots.<headline>` and
state it with the **`Theorems/` wrapper's binders** (the wrapper is the checker's statement
authority; take its binder shape, playbook §7.4). Do **not** declare any of the fourteen at its
`ModularCurve.<name>` public wrapper name — that name belongs to the manager's façade.

| promoted kernel `ModularCurve.TateSlots.<name>` | pin kernel (representative `S_` line) | module |
|---|---|---|
| `tsum_of_coeff_lt_eq_zero` | `W4B.tsum_of_coeff_lt_eq_zero` (private, :475) | Convergence |
| `tsum_lambertTerm_eq` | `W4B.B2.tsum_lambertTerm_eq` (private, :666) | Convergence |
| `equation_tateBase_iff` | `ModularCurve.equation_tateBase_iff` (private, :38) | SlotCoeff |
| `slotSubst_gen_injective` | `ModularCurve.slotSubst_gen_injective` (private, :985) | SlotCoeff |
| `coeff_slotSubst_tateUnivX` | `ModularCurve.coeff_slotSubst_tateUnivX` (private, :1383) | SlotCoeff |
| `coeff_slotSubst_tateUnivY` | `ModularCurve.coeff_slotSubst_tateUnivY` (private, :1401) | SlotCoeff |
| `single_div_one_sub_sq` | `ModularCurve.single_div_one_sub_sq` (private, :1613) | SlotCoeff |
| `single_sq_div_one_sub_cube` | `ModularCurve.single_sq_div_one_sub_cube` (private, :1619) | SlotCoeff |
| `toricPoint_fst_coeff_zero` | `ModularCurve.toricPoint_fst_coeff_zero` (private, :771) | SlotCoeff |
| `toricPoint_snd_coeff_zero` | `ModularCurve.toricPoint_snd_coeff_zero` (private, :776) | SlotCoeff |
| `toricPoint_fst_coeff_of_not_dvd` | `ModularCurve.toricPoint_fst_coeff_of_not_dvd` (private, :801) | SlotCoeff |
| `toricPoint_snd_coeff_of_not_dvd` | `ModularCurve.toricPoint_snd_coeff_of_not_dvd` (private, :809) | SlotCoeff |
| `toricPoint_fst_coeff_mul` | `ModularCurve.toricPoint_fst_coeff_mul` (private, :832) | SlotCoeff |
| `toricPoint_snd_coeff_mul_eq_sum_divisors` | `ModularCurve.toricPoint_snd_coeff_mul'` (private, :852) | SlotCoeff |

The kernels' **statements** are the corresponding `Theorems/Thm_ModularCurve_<headline>.lean`
statements; their **proofs** are the pin's bodies. The pin's public `ModularCurve.toricPoint_snd_coeff_mul`
(:842) is a *different* statement and stays in `SlotCoeff` under its own name.

### 3.3 Provenance comments for a promoted kernel

Both names are needed; the register resolves through the pin-`private` dotted fallback:

```lean
-- pin: toricPoint_fst_coeff_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:771)
theorem ModularCurve.TateSlots.toricPoint_fst_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) :
    (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 := …
```

### 3.4 The one dedup inside the source

The pin declares `ofPowerSeries_coeff_neg` / `ofPowerSeries_coeff_int` **twice** — in
`W4B.B2.GeomLS` (:560, :568) and again in `ModularCurve.OfPowerSeriesInt` (:748, :756). The port
writes them **once**, in `Convergence.lean` (`W4B.B2.GeomLS` block), and `SlotCoeff.lean` does not
re-declare them (it does not use them). Nothing else is deduped: the rest of the 112 shared names
are needed exactly once.

## 4. Route, mathlib map, and stop conditions

* **Statements are the pin's** character-for-character after the checker's normalisation; a
  documented `v4.34.0` drift is the only permitted difference. Proofs are adapted freely. **If a
  proof needs a statement to change, stop and report** — do not adapt the statement.
* Expected drift surface: `PowerSeries`/`HahnSeries` coefficient lemmas, `Finset` divisor sums,
  `NormedField`/`Valued` instance names on `LaurentSeries`, `MvPowerSeries.subst`. Adapt proofs,
  keep statements.
* **No new helpers beyond the pin's.** If a proof needs glue the pin does not have, re-derive it
  `private` in the same module and report it. **No promotion and no edit to any existing module.**
  If you believe a promotion is genuinely required, **stop and report** the declaration, host and
  `tools/deps/build_ladder.py --edit` price — the manager decides (§3.5 of the topic note).
* **Stop and report** if a declaration's statement cannot be matched to a wrapper, if the module
  split of §2 forces an import between the two engine modules, or if a block is not self-contained
  against `Defs/TateSlots.lean` + mathlib.
* Do not touch `spec/check_flt_statements.py`, `spec/UNWIRED-PUBLIC.md`, `Defs/*`, or any other
  existing module. The engine modules stay **tier 3** (not listed in `PORT_FILES`).

## 5. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is **low
> on purpose**: a declaration that exceeds it has an instance-inference defect, and the low cap is
> what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely, for this order:

1. iterate with `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
   until exit 0 with **0 warnings**;
2. when a module is done, `flock .lake/flt_build.lock timeout 300 lake build <module>`;
3. build only these two modules (plus their dependencies). No `lake build` with no argument, no
   build of a dependent, no consumer build.

**Build-time blow-up protocol.** The named risks are `boxSum_eq_head_add_doubleSum` (252 lines of
`Finset`/`Nat` arithmetic) and `coeff_slotSubst_tateUnivX`/`_tateUnivY` (long `split_ifs <;> ring`).
If one exceeds the low cap: diagnose with `set_option diagnostics true` /
`set_option trace.Meta.synthInstance true` on that declaration in a scratch copy (never commit it),
fix the inference (explicit `letI`, `inferInstanceAs`, `@`-application, avoid a `def` that blocks
unification), and re-run at the low cap. Report the declaration and the fix. A genuinely long
proof is restructured, not exempted.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on both modules | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularCurve.TateSlots.{Convergence,SlotCoeff}` | both green; record jobs and wall/user time |
| declaration parity against the representative `S_` file | every shared name present once (minus the §3.4 duplicate), none invented |
| the fourteen `ModularCurve.TateSlots.<name>` kernels | present, public, statements equal to their `Theorems/` wrappers |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register; the manager regenerates it) |

Do **not** run `spec/check_flt_statements.py` (the manager wires the façade first) and do **not**
edit the register.

## 7. Wiring

None for this order. The engines are tier 3; the manager's façade module is the tier-1 wire. Any
public declaration of the engines without a consumer is the manager's `UNWIRED-PUBLIC.md` entry.

## 8. Report shape

1. The two module paths, their final line counts, and the pin section → module map as built (flag
   any deviation from §2).
2. The declaration count per module, split public / `private`; confirm the fourteen
   `ModularCurve.TateSlots.*` kernels are public and the interface names match §3.2 exactly.
3. Tier-0 and tier-1 results, with wall/user/sys times per module and the job count.
4. Every build-time blow-up, the declaration, the diagnosis, and the fix.
5. Any statement that could not be transcribed verbatim, and why (stop condition).
6. Any helper re-derived `private`, and any promotion you stopped on.
7. The `unwired_register.py --check` output for the two modules.

## 9. Results as landed (2026-10-13)

| module | lines | public | private | tier-0 | tier-1 (cold) |
|---|---:|---:|---:|---|---|
| `TateSlots/Convergence.lean` | 537 | 38 | 1 (`W4B.B2.dvd_sub_iff_of_le`, pin-private) | exit 0, 0 warnings | 3,155 jobs, module 5.3 s, wall 7.71 s |
| `TateSlots/SlotCoeff.lean` | 1,293 | 81 | 0 | exit 0, 0 warnings | 3,149 jobs, module 8.2 s, wall 10.34 s |

Declaration parity against the representative `S_` file is exact (120 names, none missing, none
invented). The fourteen `ModularCurve.TateSlots.<name>` kernels are public with the §3.2 wrapper
binders; each discharges its `Theorems/Thm_ModularCurve_*` wrapper statement verbatim. **No
build-time blow-up**: the low cap was sufficient throughout and was never raised. The only proof
fixes were four mathlib v4.34 deprecation renames plus a `change` in `slotSubst_gen_eq_zero_iff`.
No private helper was re-derived, no promotion was required, and no existing module was touched.

The manager's half:

| check | result |
|---|---|
| `TateSlots/CoefficientFormulas.lean` (tier 1) | 14 public headlines, tier-0 exit 0 / 0 warnings, tier-1 green (3,157 jobs, 3.1 s) |
| checker before F1 | 9304 identical, 0 mismatched, 0 missing, 38 own (9342) |
| checker after F1 | **9318 identical, 0 mismatched, 0 missing, 38 own (9356)** — delta **+14**, exactly the façade |
| one-token mutation (`(hMut : True)` on `toricPoint_fst_coeff_zero`) | exactly 1 mismatched (9317), reverted |
| `#print axioms` on all 14 headlines | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep | clean |
| `unwired_register.py` | 78 modules / 1,906 public / 1,618 with pin original; 38 + 81 rows for the engines, none missing a pin original |

Wiring: the fourteen wrappers then their fourteen `S_` files appended last to `SOURCES`;
`FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` appended last to `PORT_FILES`. The engine
modules stay tier 3 and are recorded in `spec/UNWIRED-PUBLIC.md`.
