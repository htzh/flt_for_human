# WORKORDER-MC1a — the fibre product over the Vélu quotients at an algebraically closed field

Status: **landed 2026-10-27** (SET [MC-1](SET-MC1.md), order MC-1a). Inserted into
`lean/FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` (377 → **959** lines; **582 insertions,
0 deletions**): the pin's whole `TDescent` block (30 declarations, the pin's last names, its own
`TDescent` namespace) + the headline; the ported transcendental node is called, never re-proved.
Manager-verified: `check_port --force` **33 ok / 0 mismatch / 0 missing / 0 own** — the module's
three public pre-existing verdicts still `ok` (its three `private` helpers are invisible to the
checker, which is why the shelf's "5 ok" was 3); axioms `[propext, Classical.choice, Quot.sound]`
on the headline and on `TDescent.main`; build 14 s silent; edit loop silent; `dedup` 0 clusters.
The pin's three `omit [DecidableEq R] [DecidableEq S] in` lines are kept because they sit inside
the pin's `def mapFun` statement *chunk*, and dropping them is a `MISMATCH` (the checker's chunk
ends at the next declaration keyword) — verified signature-neutral with `#check`.  Two gates were
blocked ~20 minutes by a pre-existing tree collision in `Velu/RestrictAlong.lean` (FR-0055), not by
this order.

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` | `P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean` | 510 | 30 | needed 1, cone 1 / project 1 |

Read [SET-MC1.md](SET-MC1.md) first (§1, §3, §4, §5). **Pin**: `/home/haitao/proj/fermats-last-theorem` at
`aa2d8b3`.  **Port**: `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

## 1. What to write

**Insert into the landed module `lean/FLTForHuman/ModularCurve/ModularPolynomialVelu.lean`** — one
insertion, no new module. The pin's whole `TDescent` block (30 declarations) plus the headline:

| pin section | declarations | note |
|---|---|---|
| `MapPoint` | `nonsingular_map`, `mapFun`, `mapFun_zero`, `mapFun_some`, `mapFun_add`, `mapPoint`, `mapPoint_some`, `mapPoint_injective`, `coordsOrZero_mapPoint`, `addOrderOf_mapPoint`, `oddOrderSummingSet_mapPoint` | `mapPoint` is the group hom; keep the pin's case order in `mapFun_add` |
| `Velu` | `map_veluT`, `map_veluW`, `map_veluTSum`, `map_veluWSum`, `veluQuotient_map` | `hφ : Set.InjOn (Prod.map φ φ) T` |
| descent | `exists_cover`, `fibrePoly_map_ringHom`, `ConclT`, `j_congr` | `ConclT` is the pin's `Prop` packaging — keep it |
| `Transport` | `veluQuotient_oddOrderSummingSet_mapPoint`, `veluQuotient_mapPoint_Δ_ne_zero_iff`, `conclT_map_iff` | |
| `EmbedHahn` | `aleph0_lt_mk_hahn`, `nonempty_ringHom_hahn`, `exists_cover_hahn` | cardinality argument; no `IsAlgClosed` needed for `nonempty_ringHom_hahn` |
| `Assembly` | `transcendental_ringHom_iff`, `aux`, `main` | |
| headline | `solution`'s statement, taken from the `Theorems/` wrapper (30 lines) | one declaration, the wrapper's binders |

The kernel of the proof is the **descent**: `W` is mapped along the embedding
`φ : K →+* HahnSeries ℚ (AlgebraicClosure ℚ)` (whose target is algebraically closed by
`HahnSeries.isAlgClosed_rat`), the `ℓ+1` points are carried along `mapPoint`, the Vélu quotients
commute with `φ` (`veluQuotient_map`), and the **ported transcendental node** finishes:
`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` (same
module, imported line already present). **Do not re-prove the product form** — that is the one
thing this order must not do (SET-MC1 §1).

**Wire**: add exactly

```
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean
```

to the module's leading block; the module's three existing wires and its five existing declarations
must stay as they are. `modularCurve`-level namespace: the pin's declarations are under
`ModularCurve.ModularPolynomialData` / the `TDescent` namespace; keep the pin's last names (the
checker resolves by last name + hash), and keep a `TDescent`-like local namespace if the pin uses one
so that `mapFun` cannot collide with anything.

## 2. Rules (the set's standing ones)

- **No duplicated mathematics, no facades**: the product form is imported, not restated; no
  pin-shaped wrapper around an existing port lemma.
- No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats`; no linter suppressions
  (`linter.style.haveILetI`, `linter.deprecated`, `unusedVariables`) — if a warning appears, fix it
  (FR-0054: `haveI → have`, and `omit` only on a *private* declaration).
- No `sorry`/`admit`/`axiom`/`native_decide`; no edits outside your module (plus an axioms probe in
  `lean/tmp/`); no `git` writes; `lean/tmp` probes are not deliverables.

## 3. Gates

1. edit loop: `timeout 115 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` → silent;
2. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` →
   **0 mismatch, 0 missing**, and the five pre-existing `ok`s still `ok` (an insertion is also a
   test of the old wire);
3. `#print axioms` on the headline and on `main` → `[propext, Classical.choice, Quot.sound]`;
4. `flock /tmp/dsh-lake.lock lake build FLTForHuman.ModularCurve.ModularPolynomialVelu` → builds,
   `.olean` present, no dependents;
5. `python3 ../tools/deps/dedup.py --module FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` → no
   new cluster beyond the module's existing pattern (report it either way);
6. zero warnings at the 200k cap.

## 4. Report back

The checker summary line and the verdict on the five pre-existing declarations, the axioms line,
the build log's last two lines, the final line count, the declarations you kept `private` (with the
reason), and every deviation. If the pin's `TDescent` code has to be split across the module's
existing sections, say how — the module's prose header should gain a line saying where the descent
lives.
