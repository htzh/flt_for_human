# SET-AF59 — the Whittaker ODE: the string linear dependence, and the tower's rpow bound

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF58. The
fifty-ninth set of the column, and its first **`LanglandsTunnell`** set: the two ready rows of the
Whittaker ODE's moderate-growth story, which the AF waves' `AutomorphicForm` block has been feeding.

**2 rows / 690 silo / ≈640 net** in one append and one new module, two orders.

| # | row (`LanglandsTunnell.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **P** | `linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth` | 361 | 1/1 | append `WhittakerODELinearDependence` |
| **Q** | `exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` | 329 | 2/2 | new `WhittakerODETowerBound` |

## 0. The read

| figure | value |
|---|---:|
| `needed [F terminal]` | **673 / 288,239** |
| frontier F | 1,744 / 839,313 |
| ready rows, all namespaces | **32 / 6,634** |
| leaves, all namespaces | **183 / 46,068** |
| `LanglandsTunnell` demand | 23 / 10,609 |

`--selfcheck` unchanged (MD-005's ten + MD-006's one, neither cited here).

## 1. What the set says

- **P** — the complex-parameter Whittaker system's string form of linear dependence: two solutions of
  the same second-order Whittaker ODE with the moderate-growth condition are linearly dependent over
  `ℂ`. Its premise is the module's own
  `linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam`, and its proof is the Wronskian
  argument with the moderate-growth bound.
- **Q** — the `rpow` bound near zero: from the discrete tower of polynomial coefficients
  (`a n m c`, the Laguerre polynomial `p n m c`, the size `s n`) and the ODE of the tower, a
  moderate-growth solution satisfies `|f x| ≤ C x^{-σ}` near `0`. Its premise is
  `linearDependent_of_whittaker_ode_of_moderateGrowth`, which lives in the module P appends to.

The two are the ODE story's next two links: P is the string form of the linear dependence the module
already carries, Q is the near-zero bound the *other* near-zero modules cannot host (they sit below the
linear-dependence row).

### 1.1 What the set does not cut

- The remaining `AutomorphicForm` ready rows: the content/height row (333), the level-one obstruction
  (229), the `Kf`-smooth pair (317 in two rows), `rationalCentreUnipotent` (179), the character-matching
  row (113) and the Siegel-centre covering (30) — six independent subjects.
- `LanglandsTunnell.TateLocal.integral_comp_inv_…` (305) and `dirichletIdeleChar_mul_modulus_det_gen`
  (128), `TateLocal.measureReal_setOf_valued_le_exp` (100): the Tate-local measure rows, a different
  story.
- The other namespaces' ready rows (`GaloisRep` 495, `ModularCurve` 485, `CuspForm` 291, `CohCarrier`
  252, …) and all 183 leaves.

## 2. The price

| figure | SET-AF59 |
|---|---:|
| raw `S_` lines | 690 |
| declaration lines | ≈640 |
| declarations | P: 6 `private` helpers + headline; Q: ≈31 public prelude rows + headline |
| `twin_scan` | `new` for both |

## 3. The homes and the manager's landed layer

| module | rows | lines | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `LanglandsTunnell/WhittakerODELinearDependence.lean` (append) | P | 754 → **869** | +7 | +7 | **3 ok / 0 / 0** |
| `LanglandsTunnell/WhittakerODETowerBound.lean` (new) | Q | **187** | 41 | 30 | **41 ok / 0 / 0** |

Both elaborate at the low cap and build (2,779 / 3,484 jobs, silent); both checker-green before
dispatch. P's pin label namespace `UniqString` is already words and is kept (the pin's `open UniqString in`
prefix above the headline is emitted with it); Q's label token `RS11HW` is rectified to the word
namespace `TowerBound`. No token survives.

**Why Q is a new module rather than an append.** Its premise is
`linearDependent_of_whittaker_ode_of_moderateGrowth`, which lives in `WhittakerODELinearDependence`; the
port's two near-zero modules (`ODENearZeroBounds`, `WhittakerODENearZero`) are **below** that row in the
import graph (neither imports it), so neither can host Q — that is FR-0191's rule, not a preference. Q
sits one import above both, in a module of its own.

## 4. The orders and the gates

Two dispatches, disjoint files: `tmp/af59/WORKORDER-AF59A-string-dependence.md` (P, the append) and
`tmp/af59/WORKORDER-AF59B-tower-bound.md` (Q, the new module). The gates are the recipe's §6 per
module, written into each order: no tree build; the edit loop at `-DmaxHeartbeats=200000`; `lake build
<module>` under `flock`/`timeout`; `check_port` unchanged (**3 ok** and **41 ok**); `#print axioms` on
both headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer;
`dedup`/`move_dead` clean; one consumer zone per order.

## 5. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 670 / 287,672 | **668 / 286,982** | 668 / 286,982 ✓ |
| frontier F | 1,747 / 839,880 | **1,749 / 840,570** | +690 ✓ |
| ready rows | 29 / 6,067 | **27 / 5,377** | — |
| `LanglandsTunnell` demand | 23 / 10,609 | **22 / 9,919** | 22 / 9,919 ✓ |

## 6. The landing record

### 6.1 Order A — the string linear dependence (landed 2026-11-13)

One row, one append, **265 written proof lines** (869 → 1,127), 7 `sorry`s → **0**, no imports and no
`set_option` added, and no statement, import, namespace, `open`, `attribute`, `spec-pin:` line or
docstring touched — every one of the seven bodies is byte-identical to the pin's (verified
programmatically by the worker), and the headline ends at the pin's call to the module's own
`linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `LanglandsTunnell/WhittakerODELinearDependence.lean` | 754 → 869 → **1,127** | +7 | 7 → **0** | 2,779 jobs, 9.5 s, silent | **3 ok / 0 / 0** | clean |

`dedup --within` (all tiers): 0 clusters, 0 removable. `move_dead --dry-run`: 0 declarations, 0 lines —
the six helpers are all reached by the headline. Consumer zone
`spec/LanglandsTunnellSetAF59AConsumer.lean` (180 lines, three executed compositions: the dependence read
in **derivative form**, the vanishing **Wronskian** in the `c₂ ≠ 0` / `c₂ = 0` cases, and the headline
applied to concrete zero data as a non-vacuity check): **0 errors**, silent.

**Heartbeats**: the module passes at 40,000 and fails at 30,000 — and the 30,000 failure is inside the
*pre-existing* `cdecay`, not the appended block, so the new row costs nothing beyond the module's
existing level. Nothing near the 200,000 cap.

Two trivial deviations, both body-mode: two signature lines `… := by` → `… :=` so the pin's term-mode
bodies splice unchanged rather than being wrapped in `exact`; and the pin's own `end UniqString` /
`open UniqString in` lines are not copied into the last helper's body (the module carries its own). The
manager's header said "five `private` helpers" where the pin has six — that inaccuracy is fixed at
review (the docstring now says six).

### 6.2 Order B — the tower's `rpow` bound (landed 2026-11-13)

One row, one module, **180 written proof lines** (187 → 367 as the worker left it, **353** after the
review below), 30 `sorry`s → **0**, no `set_option` added, statements untouched.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `LanglandsTunnell/WhittakerODETowerBound.lean` | 187 → 367 → **353** | 41 public (+1 private) | 30 → **0** | 3,485 jobs, silent | **41 ok / 0 / 0** | clean |

`dedup --within` (all tiers): 0 clusters, 0 removable. `move_dead --dry-run`: 0 declarations, 0 lines.
Consumer zone `spec/LanglandsTunnellSetAF59BConsumer.lean` (74 lines, three executed readings: the bound
at `f := F n m` for arbitrary tower indices returning `δ > 0` and a **nonnegative** `C` read off the
bound at `y = 1/2`, the uniform bound on `(0, 1]` via `Real.rpow_le_one`, and the concrete index
`n = m = 0`): **0 errors**, silent. The whole file also elaborates at 10,000 heartbeats — 20× headroom.

**The review's one change, and the principle behind it.** v4.34's frozen import block did not reach
`Polynomial.hasDerivAt` (`Mathlib/Analysis/Calculus/Deriv/Polynomial.lean`), and the worker — whose
imports were frozen — re-proved it in-file as a 16-line `private theorem polynomial_hasDerivAt`. That is
the right call *for a worker* and the wrong end state *for the port*: the playbook's rule is that a
mathlib lemma is imported, not re-derived, and FR-0181's remedy is the specific import. At review the
import was added, the helper deleted, its three call sites replaced by `(P n m).hasDerivAt` /
`(derivative (P n m)).hasDerivAt`, and the module rebuilt and re-checked (41 ok, unchanged). The file is
**14 lines shorter** for it. This is the manager's half of the "adapters stay private" rule: a private
re-proof that exists only because of a frozen import list is a debt the manager pays at review.

Three further body-level deviations: `RS11HW.hasDerivAt_exp` referenced by its `_root_` name (the frozen
module declares it there); the pin's `convert this using 1` followed by three `rfl`s trimmed to `ring` /
`simp only [Pi.sub_apply]; ring` because v4.34 leaves fewer goals after `convert`; and the headline's
prelude names spelled `TowerBound.x` (the rectified namespace instead of the pin's `RS11HW.x`).

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf15.json
python3 ../tmp/af59/gen.py
cd .. && python3 spec/check_port.py --force FLTForHuman/LanglandsTunnell/WhittakerODELinearDependence.lean
python3 spec/check_port.py --force FLTForHuman/LanglandsTunnell/WhittakerODETowerBound.lean
```
