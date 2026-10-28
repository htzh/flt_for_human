# WORKORDER-MC3b — the StarBank's Δ in characteristic `p`

Status: **landed 2026-10-27** (SET [MC-3](SET-MC3.md), order MC-3b). Inserted into
`lean/FLTForHuman/ModularCurve/ModularPolynomialStarBank.lean` (123 → 399 lines) with the one
ordered import and two wires. Manager-verified: `check_port --force` **3 ok / 0 mismatch / 0
missing / 0 own** (the pre-existing `press` verdict unchanged); axioms
`[propext, Classical.choice, Quot.sound]` on `press`, `etaProd_pow_ne`, `delta_pow_ne`; build 8 s
silent; `dedup` 0 clusters (also against `JqCoefficients`' private η-fact); zero warnings, no
options, no `omit`.  Four `private` helpers, each with one consumer: `coeff_one_etaProd`,
`coeff_one_etaC_pow`, `etaC_pow_char`, `etaC_pow_char_pow`.  Dropped as duplicates of existing
homes: `coeff_one_mul` (mathlib), `coeff_one_pow_of_shape` (mathlib `coeff_one_pow`),
`ofPowerSeries_map` (port's `map_ofPowerSeries`), the general `map_intCast_pow_char_pow_eq_qExpand`
(replaced by the private iteration); the pin's four anonymous `Falsifier` examples are dropped as
probes.  `delta_pow_ne` is public at the wrapper's name (the pin keeps it private in the `S_` copy;
it has an outbound pin consumer, so the public form is the right one).  `etaProd_pow_ne` has no
`Them_` wrapper in the pin (it is an `S_`-level lemma), so its verdict against the `S_` copy is the
correct wire.

| node | pin `S_` | lines | frontier | home |
|---|---|---:|---|---|
| `ModularCurve.StarBank.delta_pow_ne` | `P2M/Sol/S_ModularCurve_StarBank_delta_pow_ne.lean` | 254 | ready, silo 254, lev 1 / 1 | insert `ModularPolynomialStarBank.lean` |

Read [SET-MC3.md](SET-MC3.md) (§2, §3). **Pin** `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`; **port** `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

**Insert into** `lean/FLTForHuman/ModularCurve/ModularPolynomialStarBank.lean` (no new module),
which gains **one import**, `FLTForHuman.ModularCurve.Defs.QExpandCharP` (the CL4 node's module;
acyclic, the char-`p` definition does not reach the StarBank), and two `spec-pin:` lines:

```
spec-pin: Theorems/Thm_ModularCurve_StarBank_delta_pow_ne.lean
spec-pin: P2M/Sol/S_ModularCurve_StarBank_delta_pow_ne.lean
```

The statement is the char-`p` `Δ^p ≠ C γ q^p`; the premise `map_intCast_pow_char_eq_qExpand` is the
CL4 node in `Defs/QExpandCharP.lean` — use it, do not restate it.

Rules and gates exactly as MC-2a (no duplication/facades; no options; no linter suppressions;
`check_port --force` `0 mismatch / 0 missing` with the module's existing verdicts unchanged;
axioms clean; silent build; `dedup.py`; zero warnings). The pin's `S_` file sets no option, so no
heartbeat risk.

Report: checker summary + pre-existing verdicts, axioms, build tail, line count, deviations.
