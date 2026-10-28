# WORKORDER-MC2c — the Γ₁ integral/toric-point theorem and the E₄³/Δ orbit statement

Status: **landed 2026-10-27** (SET [MC-2](SET-MC2.md), order MC-2c). New module
`lean/FLTForHuman/ModularCurve/TateSlots/Invariants.lean`, **938 lines**, both rows. Manager-verified:
`check_port --force` **91 ok / 0 mismatch / 0 missing / 0 own** (both headlines at their `Them_`
wrappers); axioms `[propext, Classical.choice, Quot.sound]` on both; build 15 s silent; `dedup`
0 clusters (one 7-line cross-module cluster on `finset_sum_slash` against a *private* copy in
`WeightOne/Gamma1Basis.lean`, recorded in the header — a private cannot be imported, so the pin's
public declaration is transcribed once here, used twice).  Accounting: the 637 `S_` file's 90
declarations are 85 written, 2 imported (`WPGamma1.T_mem_Gamma1`, `one_mem_strictPeriods`), 1
inlined (`det_mod`), 2 dropped (`main`+`solution`, the pin's own wrapper-over-engine); the 254
file's 15 are 5 written, 6 imported (the `Bridge` section), 1 replaced by the port's
`mem_scale_lattice_iff ∘ mem_lattice`, 2 unnecessary, 1 dropped.  One `private` helper
(`pow_four_six_of_sq`, pin-private).  Heartbeat profile: whole module fits **6 000** hearts (at
5 000 three steps fail), ~30× under the 200 k gate cap — nothing restructured for cost.  Section
layout replaces the pin's `unusedSectionVars` suppression with `section Prelude`/`variable (M)`;
no `omit`, no option, no suppression.

| node | pin `S_` | lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum` | `P2M/Sol/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean` | 637 | 90 | ready, silo 637, lev 2 / 2 |
| `ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq` | `P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean` | 254 | — | ready, silo 254, lev 1 / 2 |

Read [SET-MC2.md](SET-MC2.md) (§0, §1, §3). **Pin** `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`; **port** `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

**New module** `lean/FLTForHuman/ModularCurve/TateSlots/Invariants.lean`, which imports
`FLTForHuman.Elliptic.PeriodPair.InvariantsTorsion` and whatever else the two proofs need
(`X1/Defs.lean`, `Defs/TateSlots.lean`, `Defs/JqCoeff.lean`, `ModularCurve/Defs/HeckeDifferential.lean`).
Wire exactly:

```
spec-pin: Theorems/Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean
spec-pin: Theorems/Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean
```

Traps: (i) 637 is a five-object existential over a 90-declaration `S_` file — most of it should be
in the port's `X1`/`TateSlots` API (`port_advise` first, import what matches, write the rest);
(ii) 254's proof is `PeriodPair.lattice_eq_of_g2_eq_of_g3_eq` (ported) plus the classical
`SL(2,ℤ)` action — watch the `ℍ`/`UpperHalfPlane` coercions; (iii) keep the two rows in the
`ModularCurve` namespace, do not rename the `Elliptic` premise; (iv) the module is new, so it is
cascade-free.

Rules and gates exactly as MC-2a (no duplication/facades; no options; no linter suppressions;
`check_port --force` `0 mismatch / 0 missing`; axioms clean; silent build; `dedup.py` — a new
module's dedup reading must be 0 clusters unless the pin's own wrapper-over-engine pattern is
reproduced, with the reason recorded; zero warnings).

Report: checker summary, axioms, build tail, line count, private declarations and why, the pin
declarations imported vs written, deviations, and the heartbeat profile of `key`-style steps.
