# SET-AF77 — the box normalization in Fourier form, and the pure-tensor Weyl product

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF76, and cut by the
column's rule: the two rows AF76 readied. Both are continuations of subjects already in the port — the
box normalization (SET-AF76 order B) and the Weyl integrand (the `LocalIntertwining` family).

**2 rows / 255 silo** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` | 185 | 3/9 | new `EisensteinGeneral/Factorization/BoxFourier` |
| **B** | `AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 70 | 4/9 | new `AutomorphicForm/Adelic/WeylIntegrable/PureTensorProd` |

## 0. The read

`needed` **592 / 266,082**, ready **24 / 5,045**, leaves **143 / 37,308** — SET-AF76 §5's post-landing
figures exactly. `--selfcheck` unchanged (the fifteen MD-005 markers, none cited here).

## 1. The rows

- **A** is SET-AF76-B's box normalization with the Fourier integrals put in: `(μ (adelicBox F))⁻¹ *
  fourierIntegral ψ μ (pure tensor) w` equals the discriminant factor times the two one-variable
  transforms. The pin's file is 186 lines: one private countability helper (`countable_heightOneSpectrum`)
  and the private main theorem, with the public surface the headline alone — the module is scaffolded
  with the headline and the worker transcribes the two private declarations above it.
- **B** is the integral of a pure tensor against the product of a finite part of the unramified Weyl
  integrand, a finite Euler product and the `∏'` of the remaining local factors, in the convergence
  half-plane `1/2 < re s`. The whole row is one 70-line `S_` file; the module is that statement alone.

## 2. The price and the home

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `EisensteinGeneral/Factorization/BoxFourier.lean` (new) | A | **47** lines | 1 | **1 ok / 0 / 0** |
| `AutomorphicForm/Adelic/WeylIntegrable/PureTensorProd.lean` (new) | B | **60** | 1 | **1 ok / 0 / 0** |

Both elaborate silently at the edit-loop cap. No `Def_` work: A's vocabulary is
`NumberField.AdelicBox.Normalization` + `NumberField.AdelicFourier` (both new in AF75/AF76), B's is the
`WeylIntegrable` family already in the port. Two manager decisions, both in B's header: the pin's
statement spells `nrComplexPlaces` (so the module opens `NumberField.InfinitePlace`) and its
`∏'`/`∏ᶠ` factors need `open scoped Topology BigOperators`.

## 3. The orders and the gates

| order | row | content | scaffold `sorry`s |
|---|---|---|---:|
| `WORKORDER-AF77A` | A | ≈140 + 2 private decls | 1 |
| `WORKORDER-AF77B` | B | ≈50 | 1 |

Disjoint files, two orders in parallel. Gates: the same six as SET-AF75 §3 (edit loop at 200 k with an
empty `error|warning` grep — a blow-up is diagnosed per playbook §3.5, never bumped; the module's own
`lake build` under `flock`/`timeout`, silent; `check_port --force` at the counts above; axioms clean;
`dedup --within` / `move_dead --dry-run`; one consumer zone).

## 4. The shelf effect

Forecast **measured with `--port`**, jointly with SET-AF78 (the two sets open on the same read, so the
forecast is taken once, with all four of their rows ported):

| figure | §0 | forecast (AF77 + AF78 `--port`ed) |
|---|---:|---:|
| `needed [F terminal]` | 592 / 266,082 | **587 / 265,294** |
| ready rows | 24 / 5,045 | **21 / 5,522** |
| leaves | 143 / 37,308 | 143 / 37,308 |

and it returns **two** rows:

| row readied | silo | lev |
|---|---:|---:|
| `AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow` | 793 | 1/1 |
| `AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion` | 472 | 2/2 |

The ready block shrinks by four and gains two, so this pair of sets trades four small rows for two large
ones (−3 rows, +477 silo): the box-Fourier and Weyl-product subjects are the last missing premise of
791-line-scale rows, which is what the next cut then has to face.

## 5. The landing

Both rows in, 2 `sorry`s → 0, two new modules.

| file | row | lines | `sorry` | checker | axioms |
|---|---|---:|---:|---|---|
| `EisensteinGeneral/Factorization/BoxFourier.lean` | A | 47 → **148** | 1 → 0 | **1 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/WeylIntegrable/PureTensorProd.lean` | B | 60 → **78** | 1 → 0 | **1 ok / 0 / 0** | clean |

Consumers `spec/EisensteinGeneralSetAF77AConsumer.lean` (85 lines) and
`spec/AutomorphicFormSetAF77BConsumer.lean` (134): 0 errors, 0 warnings each. **Heartbeat floors**: A 6 500,
B ≈5 000 — 31–40× under the cap, nothing bumped. A: 4× `haveI`→`have` (FR-0198), and its private engine
kept in the pin's own inner namespace `FiniteAdelicFactorization` because Lean refuses a `private` and a
public declaration of the same name in one namespace (the pin's engine carries the headline's name).
B: one import added — `NumberField.AdelicBox.Normalization`, the home of its premise (the FR-0209
"ported ≠ imported" class); the pin's `letI`/`haveI` walls became `let _`/`have _`.

**Two instrument readings, kept deliberately, both the pin's own pattern.** A's `dedup --within` reports
one `shape` cluster (24 lines) — the private engine against the public headline, whose statement *is* the
engine's: that is the pin's wrapper-over-engine shape (§5 of the recipe) and it stays. Its `move_dead`
reports one declaration / 18 lines — `countable_heightOneSpectrum`, dead *in this file*, which the pin
registers for its sibling rows of the same family; it ships with the module for fidelity, as the pin had it.

### The set's numbers

| figure | before | **after** | forecast (joint with AF78) |
|---|---:|---:|---:|
| `needed [F terminal]` | 592 / 266,082 | **587 / 265,294** | 587 / 265,294 ✓ exact |
| ready rows | 24 / 5,045 | **21 / 5,522** | 21 / 5,522 ✓ exact |
| leaves | 143 / 37,308 | 143 / 37,308 | unchanged ✓ |

Both forecasts were taken once, jointly with SET-AF78 (the two sets opened on the same read), and the joint
figures landed to the row and the line.
