# SET MC-2 — M3, the Tate slots and the tate `j`

**Status: scoped and dispatched (2026-10-27).** The shelf's **MC-2**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1) is story **M3**: `qTwist` on non-toric points,
`(tateLaurent K).j = jqModC K`, the Γ₁ integral q-expansion/toric-point theorem, and the E₄³/Δ
orbit statement. 1,220 silo; the shelf priced it at **1,114 rows-net + 17 gate = 1,131**; this
brief re-reads it after M1 and MC-1 and cuts it as **three modules, two of them new**.

| row (`ModularCurve.` dropped) | silo | prem | lev | home |
|---|---:|---:|---:|---|
| `exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum` | 637 | 2 | 2 / 2 | **new** `TateSlots/Invariants.lean` |
| `exists_smul_eq_of_E4_cube_div_discriminant_eq` | 254 | 1 | 1 / 2 | **new** `TateSlots/Invariants.lean` |
| `qTwist_nonToricPoint_of_pow_eq_one` | 185 | 2 | 1 / 1 | **insert** `TateSlots/CoefficientFormulas.lean` (migrated, §2) |
| `j_tateLaurent` | 144 | 1 | 3 / **11** | **insert** `Degree/FinrankAdjoinJqNModC.lean` |

## 0. The read

All four rows are ready, leaf-free, marker-free and `premises_pruned = 0` on both the instrument's
and the corrected shelf. The 144 row carries 11 project consumers (the widest in the MC block
after the 62 row's 10); the 637 row is the largest of the set and its `S_` file has 90
declarations — read it as a five-object existential (`B`, `D`, `b`, `d` and the Fourier
identities), not as one statement.

## 1. The definition gate, resolved

The shelf's 17-line gate for M3 is `Def_ModularCurve_X1`'s three `JOne.torsionGaloisRep`
declarations, which `X1/Defs.lean`'s header records as **deferred** (they need the ported
`Pic0`/`SemilinearAut` torsion action). **The rows of this set do not use them** — this is the
"17-line check" the shelf asked for, and it is a *check*, not a gate:

- nothing in the four rows' statements mentions `torsionGaloisRep`;
- `X1/Defs.lean` already carries `JOne`/`JOneC`, which is all the 144/185 rows need;
- the two rows that read `qExpFunctionFieldC`/`tateLaurent` live above it.

So the gate is **0**, exactly as `QExpReductionModL` was for M1 — but it must be confirmed per row
by the worker (`grep -n "torsionGaloisRep"` in each `S_` file) before it writes a line. If a row
does need it, **stop and report**: porting the action is a different order (its module is
`AlgebraicCurve/Defs/SemilinearAut.lean`, and the three declarations are 17 lines only if that
layer is already imported).

## 2. The migration this set pays (manager, done)

`TateSlots/CoefficientFormulas.lean` was a legacy module (`PORT_FILES`). It is now **migrated**:
14 `spec-pin:` wires (its `Them_` wrappers and `S_` copies) and the `PORT_FILES` row deleted; the
checker reads **14 ok / 0 mismatch / 0 missing**. The 185 row is inserted into it, so its wire
gains the 185 wrapper + `S_` file. The other half of the shelf's M3 plan — the new
`TateSlots/Invariants.lean` — is a fresh module above
`Elliptic/PeriodPair/InvariantsTorsion.lean`.

## 3. The orders

| order | rows | modules | silo | est. net |
|---|---|---|---:|---:|
| **MC-2a** | 185 | insert `TateSlots/CoefficientFormulas.lean` | 185 | ≈150 |
| **MC-2b** | 144 | insert `Degree/FinrankAdjoinJqNModC.lean` | 144 | ≈100 |
| **MC-2c** | 637, 254 | new `ModularCurve/TateSlots/Invariants.lean` | 891 | ≈880 |

Workorders: [WORKORDER-MC2a-qTwist-nontoric.md](WORKORDER-MC2a-qTwist-nontoric.md),
[WORKORDER-MC2b-tate-laurent-j.md](WORKORDER-MC2b-tate-laurent-j.md),
[WORKORDER-MC2c-tate-slot-invariants.md](WORKORDER-MC2c-tate-slot-invariants.md).  The three
touch disjoint files and can run concurrently.

**Traps.** (i) 185's `qTwist` is the ported `ModularCurve.qTwistFun` (`Defs/Twist.lean`); the
46-suspect list's `twistFun` row is this — check the statement, then use the port's. (ii) 144 is one
line over `tateLaurent`/`jqModC`; its premise `eisenstein4_cube_sub_mk_sq` lives in
`X1/IntegralityJqNModC.lean`, the module MD-001 cleaned — **do not touch that module's wire**.
(iii) 637's `S_` file is 637 lines / 90 declarations; expect most of them in the port already
(`X1`/`TateSlots` API) and price the remainder. (iv) 254's proof is
`PeriodPair.lattice_eq_of_g2_eq_of_g3_eq` (ported) plus the classical `SL(2,ℤ)` action — watch the
`ℍ`/`UpperHalfPlane` coercions. (v) the new module imports
`Elliptic/PeriodPair/InvariantsTorsion.lean`, a top-level `Elliptic` module: keep the
`ModularCurve` namespace of the two rows, do not rename the premise. (vi) no `set_option
maxHeartbeats`, no linter suppressions (SET-MC7's FR-0054).

## 4. Gates

As the recipe §6 and SET-MC7 §6: `check_port --force` on each touched module with `0 mismatch /
0 missing` (the migrated modules' existing verdicts must stay), axioms clean, silent build under
`flock`/`timeout`, `dedup.py`, zero warnings, and the module's `spec-pin:` block gains exactly the
new wrapper + `S_` copy.

## 5. After the landing

Re-read the shelf: the four rows leave (MC shelf 20 → 16 after MC-1's 3), and the 144 row's eleven
consumers are the readiness candidates. Record in the workorders and in
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1.

## 5a. After the landing (measured)

**Measured after the wave (2026-10-27, one read over MC-1 + MC-2 + MC-3).**
Instrument `needed` 1,016 / 402,071 → **1,004 / 398,972**; corrected 1,018 / 402,432 →
**1,006 / 399,333**. Ready 83 / 17,475 → **75 / 15,689**; `ModularCurve` shelf 23 / 5,949 →
**15 / 4,163** (corrected 22 / 5,913 → 14 / 4,127); MC demand 182 / 79,025 → **170 / 75,926**;
frontier +16 nodes / +3,637 lines (the ten cut headlines plus six further pin declarations the
wave made ported — MC-2b's four `tatePowerSeries` nodes among them); leaves 296 / 72,205 →
**294 / 71,671**, because **two rows became ready out of the leaves block**:
`c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` and
`meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` — the readiness delta
this wave produced, and M3's next cut.  Ten rows were cut, nothing was lost, and the only tree
defect found was pre-existing (FR-0055).

## 6. What this set does not do

- **The `JOne.torsionGaloisRep` block** (17 lines) — deferred, not used (§1).
- **The `tateCurve` twins/triplet** (`TateCurve/*`) — a different story, already landed.
- **No promotion.** The migrated module's `private` helpers stay private.
