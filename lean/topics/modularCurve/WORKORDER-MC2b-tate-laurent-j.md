# WORKORDER-MC2b — `(tateLaurent K).j = jqModC K`

Status: **landed 2026-10-27** (SET [MC-2](SET-MC2.md), order MC-2b). Inserted into
`lean/FLTForHuman/ModularCurve/Degree/FinrankAdjoinJqNModC.lean` (367 → 531 lines); the headline is
the `Them_` wrapper's statement verbatim (`(K) [CommRing K] : (tateLaurent K).j = jqModC K`).
Manager-verified: `check_port --force` **24 ok / 0 mismatch / 0 missing / 0 own** with the 15
pre-existing verdicts unchanged; axioms `[propext, Classical.choice, Quot.sound]`; build 17 s
silent; `dedup` 0 clusters; zero warnings, no options.  The row needed the pin's tate block, which
the port had nowhere, so **four further pin nodes became ported here** (`c₄_tatePowerSeries`,
`c₆_tatePowerSeries`, `Δ_tatePowerSeries`, `c₄_pow_three_tateLaurent`); the reviewer tested and
then **kept their four `Them_` wrapper wires** (still 24 ok / 0 / 0), so they are source-licensed
rather than only name-covered.  Dropped, documented in the module header:
`eisenstein4_cube_sub_eisenstein6_sq` (already ported as `eisenstein4_cube_sub_mk_sq`),
`jqModC_eq_single_mul_laurentOfInt` (`rfl`), `j_tateLaurent_rat` (a two-rewrite corollary with no
pin consumer), the `S_` file's `private` twins and its `private` `j_map_qExpand_tateLaurent` (a
node of its own, still in the demand), and the re-export `solution`.

| node | pin `S_` | lines | frontier |
|---|---|---:|---|
| `ModularCurve.j_tateLaurent` | `P2M/Sol/S_ModularCurve_j_tateLaurent.lean` | 144 | ready, silo 144, lev 3 / **11** |

Read [SET-MC2.md](SET-MC2.md) (§1, §3). **Pin** `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`; **port** `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

**Insert into** `lean/FLTForHuman/ModularCurve/Degree/FinrankAdjoinJqNModC.lean` (no new module;
its premise module is `X1/IntegralityJqNModC`). Add to its `spec-pin:` block:

```
spec-pin: Theorems/Thm_ModularCurve_j_tateLaurent.lean
spec-pin: P2M/Sol/S_ModularCurve_j_tateLaurent.lean
```

The row is one line over `tateLaurent`/`jqModC` (`Defs/TateSlots.lean`, `Defs/JqCoeff.lean`); its
premise `eisenstein4_cube_sub_mk_sq` lives in `X1/IntegralityJqNModC.lean` — **do not edit that
module or its wire** (MD-001 was just cleaned there).

Rules and gates exactly as MC-2a (no duplication/facades, no options, no linter suppressions,
checker `0/0` with the module's existing verdicts unchanged, axioms clean, silent build, dedup,
zero warnings). Note the 11 project consumers: this is the widest-fan-out row of the set, so a
statement change would be expensive — take the wrapper's binders verbatim.

Report: checker summary + pre-existing verdicts, axioms, build tail, line count, deviations.
