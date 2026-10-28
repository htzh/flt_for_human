# WORKORDER-MC3a — X₁ separability and the canonical divisor

Status: **landed 2026-10-27** (SET [MC-3](SET-MC3.md), order MC-3a). Two insertions:
`X1/FunctionFieldIsAlgClosed.lean` 384 → **772** and the migrated `X1/Structure.lean` 182 → **212**.
Manager-verified: **19 ok / 0 / 0** on the former (its 15 pre-existing `ok`s unchanged; new
`P2MKcSepQ.exists_order_sum_eq`, `T_mem_Gamma1`, `charP_case`, headline), **5 ok / 0 / 0** on the
latter (the **four migrated verdicts unchanged**); axioms clean on both headlines; both modules
build silent under `flock`; `dedup` 0 clusters.  The pin's `main` is not kept separately — its
statement *is* the wrapper's, so the headline carries its proof (keeping both was a facade and an
11-line dedup shape cluster); the three helpers stay public at pin names in
`ModularCurve.P2MKcSepQ`.  **Recorded, not a regression**: this module cannot fit the 200 000-beat
edit loop — the pre-existing `transfer` at :191 already fails there (measured on a probe with the
new block cut out), and the insertion adds :491/:547/:556; `lake build` at the lakefile's
4 000 000 is silent, and no `set_option` was added.  Imports added inside the two modules:
`Mathlib.FieldTheory.PurelyInseparable.PerfectClosure`,
`FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor` (acyclic).

| node | pin `S_` | lines | frontier | home |
|---|---|---:|---|---|
| `ModularCurve.isSeparable_adjoin_qExpFunctionFieldC_gamma1` | `P2M/Sol/S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1.lean` | 363 | ready, silo 363, lev 2 / 4 | insert `X1/FunctionFieldIsAlgClosed.lean` |
| `ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar` | `P2M/Sol/S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar.lean` | 22 | ready, silo 22 | insert **migrated** `X1/Structure.lean` |

Read [SET-MC3.md](SET-MC3.md) (§1, §2, §3). **Pin** `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`; **port** `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

Two insertions, two wires (each module gains its wrapper + `S_` line):

```
# X1/FunctionFieldIsAlgClosed.lean
spec-pin: Theorems/Thm_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1.lean
spec-pin: P2M/Sol/S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1.lean
# X1/Structure.lean  (migrated 2026-10-27: four spec-pin wires, PORT_FILES row deleted, 4 ok / 0 / 0)
spec-pin: Theorems/Thm_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar.lean
spec-pin: P2M/Sol/S_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar.lean
```

Traps: (i) the 363 statement carries the hypothesis `hx : (x : LaurentSeries K) = jqModC K` — keep
it, and use the `FunctionFieldIsAlgClosed` API + the ported `order_jqModC`; (ii) `HasCanonicalDivisor`
is an `AlgebraicCurve` class, and `X1/Structure.lean`'s four declarations are now checker-diffed —
your insertion must leave them `ok`; (iii) do not edit any other module.

Rules and gates exactly as MC-2a (no duplication/facades; no options; no linter suppressions;
`check_port --force` on **both** modules with `0 mismatch / 0 missing` and the four migrated `ok`s
unchanged; axioms clean; both modules' own silent builds; `dedup.py`; zero warnings).

Report: both checker summaries + the pre-existing verdicts, axioms, build tails, line counts,
deviations.
