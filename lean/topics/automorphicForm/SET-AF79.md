# SET-AF79 — the Euler product of the Dedekind zeta function

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF78. Three leaves of
one subject (the Euler product `ζ_K(s) = ∏'_𝔭 (1 - |𝔭|^{-s})^{-1}`), and the pin proves a 23-declaration
prelude **three times**, once per consumer — the cleanest "port once" the column has met.

**3 rows / 1,295 silo** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A1** | `NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta` | 338 | 6/26 | new `NumberTheory/LSeries/DedekindZetaEuler` (with the shared prelude) |
| **A2** | `NumberField.dedekindZeta_ne_zero_of_one_lt_re` | 357 | 6/6 | same module |
| **B** | `NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` | 600 | 11/40 | new `NumberTheory/LSeries/DedekindZetaEulerProduct` |

## 0–1. The read, the rows

`needed` **587 / 265,294**, ready **21 / 5,522**, leaves **143 / 37,308** (SET-AF78 §5's figures).

- The **shared prelude** (pin `S_…hasProd…:19–321` ≡ `S_…dedekindZeta_ne_zero…:20–308`, 23 declarations,
  `idealCount`, `dedekindZeta_eq_LSeries`, the `primeSet` construction, `tsum_primeSet_eq_prod`,
  `tendsto_tsum_primeSet_of_summable`, …) is written once, in `DedekindZetaEuler`, publicly.
- **A1** then adds `hasProd_primes`/`primesEquiv` and the Euler product `∏'_𝔭 (1 - |𝔭|^{-s})⁻¹ = ζ_K(s)`.
- **A2** adds the non-vanishing `ζ_K(s) ≠ 0` for `re s > 1`, through the partial products and their limit.
- **B** is the analytic half: the full product is multiplicable, its logarithm's series converges, and the
  product is differentiable with non-zero terms — 24 further declarations, of which four
  (`hasProd_spectrum`, `summable_spectrum`, `two_le_absNorm_spectrum`, …) sit above the prelude.

All three rows are pure mathlib plus the prelude (`S_` imports: `Mathlib` + `P2M.Util` only).

## 2. The price and the homes

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `NumberTheory/LSeries/DedekindZetaEuler.lean` (new) | A1, A2 | **143** lines | 27 | **27 ok / 0 / 0** |
| `NumberTheory/LSeries/DedekindZetaEulerProduct.lean` (new) | B | **153** | 25 | **25 ok / 0 / 0** |

The pin's label namespaces (`EulerZeta`, `ZetaNeZero`) are dropped for the module's
`NumberField.ZetaEuler`; the prelude's 23 declarations are declared **once** here, so the pin's three
copies cost one. No `Def_` work.

## 3–4. The orders and the forecast

| order | rows | content | scaffold `sorry`s |
|---|---|---|---:|
| `WORKORDER-AF79A` | A1, A2 | ≈560 | 27 |
| `WORKORDER-AF79B` | B | ≈500 | 25 |

B imports A's module (its prelude) — the two run in parallel on the statements (FR-0220's lesson: B's
build-side gates close after A lands; it must not edit A's module or hand-make an `.olean`).

Forecast with `--port` on the three rows: `needed` −1,295 silo, ready **18 / 5,522**, leaves
**140 / 36,013**; the joint read with SET-AF80 is taken once, in SET-AF80 §4.

## 5. The landing

All three rows in, 52 `sorry`s → 0, two new modules, **380 lines of proof against 1,295 silo of pin**.

| file | rows | lines | `sorry` | checker | axioms |
|---|---|---:|---:|---|---|
| `NumberTheory/LSeries/DedekindZetaEuler.lean` | A1, A2 | 143 → **388** | 27 → 0 | **27 ok / 0 / 0** | clean |
| `NumberTheory/LSeries/DedekindZetaEulerProduct.lean` | B | 153 → **288** | 25 → 0 | **25 ok / 0 / 0** | clean |

Consumers `spec/NumberTheorySetAF79{A,B}Consumer.lean`: 0 errors, 0 warnings. `dedup --within`: 0
clusters in both; `move_dead`: 0 declarations in both. Imports added: one each
(`EulerProduct.ExpLog` for `Summable.clog_one_sub`, `SpecialFunctions.Log.Summable` for
`Complex.multipliable_of_summable_log`).

**Heartbeat floors**: A 98 000 (the headline's body; probe 1 with the proof `sorry`ed is cheap at 95 000,
so the cost is proof-side), B 100 000 (**in the frozen statement** of `hasProd_spectrum` — a type-level
`isDefEq`; every abort at 95 000 is at that statement). Both are proof/statement costs of the pin's own
shapes, under the 200 k cap, no `set_option` anywhere.

**The set's one accounting point.** The **shared prelude is written once** — 23 declarations the pin
proves twice (`EulerZeta` in one file, `ZetaNeZero` in the other) — which is why the pair costs 245 lines
and B needs only the 24 declarations above it. Two smaller decisions: AF79A refused to add the pin's
`scoped instance finite_fiber` (a 28th public declaration would move the checker off `27 ok`) and
reproduced the fact locally as `have : Finite {I // |I| = n}`; and the port keeps the scaffold's
**explicit `K`** in B's last fifteen declarations rather than the pin's mid-file `variable {K}` (same
statement text, so the wire is unmoved; flipping fifteen signatures buys only the pin's call shape).

### The set's numbers

| figure | before | **after** | forecast (joint with AF80) |
|---|---:|---:|---:|
| `needed [F terminal]` | 587 / 265,294 | **582 / 262,734** | 582 / 262,734 (the pair's joint figure) |
| ready rows | 21 / 5,522 | **21 / 4,877** | 21 / 4,877 |
| leaves | 143 / 37,308 | **140 / 36,013** | 140 / 36,013 |
