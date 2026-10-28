# SET MC-3 — M8 + M10, the X₁ field and the StarBank

**Status: scoped and dispatched (2026-10-27).** The shelf's **MC-3**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1) is two small subjects that share the X₁
definition layer: **M8** (separability of `qExpFunctionFieldC` over `K⟮jq⟯`, and the canonical
divisor) and **M10** (the StarBank's Δ and char-`p`). 639 silo; the shelf priced it at
**562 net** and noted "none" as its gate (StarBank gains a 1-line import).

| row (`ModularCurve.` dropped) | silo | prem | lev | home |
|---|---:|---:|---:|---|
| `isSeparable_adjoin_qExpFunctionFieldC_gamma1` | 363 | 2 | 2 / 4 | **insert** `X1/FunctionFieldIsAlgClosed.lean` |
| `hasCanonicalDivisor_x1FunctionFieldBar` | 22 | 3 | 1 / 1 | **insert** `X1/Structure.lean` (migrated, §1) |
| `StarBank.delta_pow_ne` | 254 | 1 | 1 / 1 | **insert** `ModularPolynomialStarBank.lean` + 1 import |

## 0. The read

Three rows, all ready, leaf-free, marker-free, `premises_pruned = 0`. The 22 row is the cheapest
declaration in the entire MC block (22 silo) and the 363 row has four project consumers. The
`--selfcheck` is clean, so the M8 rows' premises are genuinely ported.

## 1. The migrations this set pays (manager, done)

- **`X1/Structure.lean`** was a legacy module (`PORT_FILES`); the 22 row's home. It is now
  **migrated**: four `spec-pin:` wires (its four `Them_` wrappers and `S_` copies), the
  `PORT_FILES` row deleted; the checker reads **4 ok / 0 mismatch / 0 missing**. The 22 row is
  then inserted in the same module, whose wire gains the 22 wrapper + `S_` file.
- **`ModularPolynomialStarBank.lean`** is not legacy; M10 needs exactly one new import,
  `FLTForHuman.ModularCurve.Defs.QExpandCharP` (the CL4 node's module, already in the tree), which
  the shelf verified is acyclic (the char-`p` definition does not reach the StarBank).

## 2. The orders

| order | rows | module | silo | est. net |
|---|---|---|---:|---:|
| **MC-3a** | 363, 22 | insert `X1/FunctionFieldIsAlgClosed.lean` and `X1/Structure.lean` | 385 | ≈340 |
| **MC-3b** | 254 | insert `ModularPolynomialStarBank.lean` (+1 import) | 254 | ≈220 |

Workorders: [WORKORDER-MC3a-x1-separability-and-divisor.md](WORKORDER-MC3a-x1-separability-and-divisor.md),
[WORKORDER-MC3b-starbank-delta-pow.md](WORKORDER-MC3b-starbank-delta-pow.md).  Disjoint files; they
can run concurrently, and MC-3b must be dispatched after MC-3a only if both need
`FunctionFieldIsAlgClosed` (they do not — MC-3b's premises are `AtkinLehnerExchange`/`HeckeDegree`).

**Traps.** (i) 363's hypothesis `hx : (x : LaurentSeries K) = jqModC K` is part of the *statement*:
keep it, and use the `FunctionFieldIsAlgClosed` API plus the ported `order_jqModC`. (ii) 22's
`HasCanonicalDivisor` is an `AlgebraicCurve` class; its home is the migrated `X1/Structure.lean`
(§1) — the insertion must not disturb the four existing verdicts. (iii) M10's `delta_pow_ne` is the
char-`p` statement `Δ^p ≠ C γ q^p`; the premise `map_intCast_pow_char_eq_qExpand` is the CL4 node
in `Defs/QExpandCharP.lean`; the home gains the one-line import. (iv) the 254 `S_` file sets no
`set_option`; no heartbeat risk. (v) no linter suppressions (FR-0054).

## 3. Gates

As the recipe §6 and SET-MC7 §6: `check_port --force` on each touched module with `0 mismatch /
0 missing` and the migrated modules' verdicts unchanged, axioms clean, silent builds under
`flock`/`timeout`, `dedup.py`, zero warnings, and exactly the new wrapper + `S_` wires added.

## 4. After the landing

The three rows leave the shelf (23 → 20 after MC-1, → 17 after MC-2, → 14 after MC-3); the
readiness delta is the next pass's. Record in the workorders and in
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1.

## 4a. After the landing (measured)

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

## 5. What this set does not do

- **No promotion, no new module** — two insertions, one import, two migrations already paid.
- **The `JOne.torsionGaloisRep` block** (the shelf's M3/M8 note): not used by these rows; still
  deferred with `Def_ModularCurve_X1`'s boundary.
