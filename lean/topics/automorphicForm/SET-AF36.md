# SET-AF36 — the Whittaker-equation engine: linear dependence at moderate growth, and the near-zero bound

**Status: scoped 2026-11-08, two orders in parallel** — §5 is the forecast, §6 the landing record (to be
appended). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). It is the
thirty-sixth set of the column, and the first cut on the **leaves** shelf that is not an
`AutomorphicForm` row.

**3 rows / 1,955 silo / 1,768 net priced, ≈1,312 written** (the `(ν²).im = 0` row is *derived* from the
general complex-parameter row: both are premise-free pin leaves, neither cites the other).

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A** | `LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam` | 711 | **1/14** | two polynomially-growing solutions of the Whittaker equation `y²f'' + (1/4 − ν² + 2πky − 4π²y²)f = 0` are linearly dependent |
| **A′** | `LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth` | 643 | 2/2 | the same with `(ν²).im = 0` — **derived** from A |
| **B** | `LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing` | 601 | 1/1 | for a forcing term bounded by `A·y^σ` on `(0,1]`, a solution is bounded by `C·y^(min (1/2 − |Re ν|) σ − ε)` |

**Why the leaves shelf, and why now.** The recipe's cheap-leaf signal: A is 711 lines with **14 project
consumers** and A′ 643 with 2, both premise-free (needed = 1), and B 601 with 1 — 1,955 silo and *no*
unported premise between them. The ready shelf's own head is a 1,187 AF row (SET-AF35, cut in the same
wave); the leaves block is where the rest of this subject lives, and these three are its engine: the
linear-dependence lemma is what makes the local Whittaker functional one-dimensional under moderate
growth, and B is the indicial-root growth bound at the cusp. Together they are the analytic input of the
weight-one lifting's local theory.

## 0. The read

The read SET-AF34's landing left: `needed` **759 / 317,413**, frontier 1,657 / 809,963, ready
59 / 13,881, leaves **203 / 52,512** (`LanglandsTunnell`: 18 / 5,597), `LanglandsTunnell` demand
37 / 16,932. The three rows are in the leaves block at 711 / 643 / 601 — the top three `LanglandsTunnell`
leaves, and 0-premise rows, so there is no premise audit to run for them: **the definition gate is empty
too**, and for a structural reason: the pin files import **mathlib only** (`Analysis.SpecialFunctions.Pow.Real`,
`Calculus.Deriv.{Basic,MeanValue,Prod}`, `Analysis.ODE.{Gronwall,ExistUnique}`,
`SpecialFunctions.{ExpDeriv,Log.Basic}`, `Complex.RealDeriv`, `Pow.Asymptotics`,
`Topology.Order.MonotoneConvergence`) plus `P2M.Util` — no `Definitions/Def_*` module at all. `port_advise
--with-defs` confirms it: the def closure is empty. This set is pure analysis.

**The relation between A and A′ was checked, not assumed** (the recipe's §2 warning about sibling
inversion): A′ carries the extra hypothesis `(ν²).im = 0` and states the *same* conclusion, so A
(general, no such hypothesis) implies A′; and neither pin file cites the other (their `Theorems/`
import lists are empty — they are leaves). So A is ported and A′ is derived, which also removes the two
files' duplicated 132-line prelude from the written total.

## 1. The cut

| order | module | content | silo | written |
|---|---|---|---:|---:|
| **36A** | `LanglandsTunnell/WhittakerODELinearDependence.lean` | A (711) + A′ (derived, ~10 lines) | 1,354 | ~720 |
| **36B** | `LanglandsTunnell/WhittakerODEGrowth.lean` | B (601) | 601 | ~600 |
| | **2 modules** | | **1,955** | **≈1,320** |

Both are new modules with no in-tree importers and **no importers of each other**: the two orders are
disjoint and run in parallel.

## 2. The price

`port_advise` + `port_plan` on the three:

| figure | value |
|---|---:|
| raw `S_` lines | 1,955 |
| declaration lines | 1,900 |
| — duplicate copies | 132 (A and A′ share their prelude; A′ is derived, so this vanishes) |
| — boilerplate | 55 |
| distinct declaration groups | 53 |
| already in the port | **0** |
| **net new math lines (priced)** | **1,768** |
| **written** | **≈1,320** |

1 suspect substitution (`Efun → ModularCurve.clamp01`): a type-only `def` match; A/A′ define their own
`Efun`/`eA`-style exponential helper and must not be rewritten to the port's unrelated `clamp01`.

## 3. Homes

Both are `LanglandsTunnell/` modules: the pin keeps the `LanglandsTunnell` namespace, and the port's
`LanglandsTunnell/` directory is the home of that route's number-theoretic modules
(`StandardLocalConstantsAt`, `TateLocalConstantsAt`, `TateLocalZeta`, `ArchParam`). The ODE rows are the
route's *analysis* half and get their own modules rather than being appended to a constants module.

## 4. Orders and gates

`lean/tmp/WORKORDER-AF36A-whittaker-ode-dependence.md`,
`…-AF36B-whittaker-ode-growth.md`. The standard gates: `check_port --force` at 0 mismatch / 0 missing
(A: 2 ok incl. the derived A′), axioms clean, the module's own build under `flock`/`timeout` and
silence, `dedup`/`move_dead`, and a `spec/` consumer zone. Both scaffolds are already checker-green
(2 ok / 1 ok).

## 5. Forecast

SET-AF35 is cut in the same wave, so each set's delta is quoted from the read it starts on, and the
wave's total at the end.

| figure | start | after AF36 | after both sets |
|---|---:|---:|---:|
| `needed [F terminal]` | 759 / 317,413 | 756 / 315,458 | **753 / 313,678** |
| `needed [literal]` | 771 / 320,878 | 768 / 318,923 | **765 / 317,143** |
| frontier F | 1,657 / 809,963 | 1,660 / 811,918 | **1,663 / 813,698** |
| ready rows | 59 / 13,881 | 59 / 13,881 | **57 / 12,226** (AF35's two) |
| leaves | 203 / 52,512 | **200 / 50,557** | **200 / 50,557** |
| `LanglandsTunnell` demand | 37 / 16,932 | **34 / 14,977** | **33 / 13,790** |
| `AutomorphicForm` demand | 269 / 117,257 | 269 / 117,257 | **267 / 116,664** |

## 6. The landing (2026-11-08)

Two orders, two modules, all gates green.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **36A** | `LanglandsTunnell/WhittakerODELinearDependence.lean` | 754 | 8 (1 public headline, 6 `private` helpers, the derived companion) | **2 ok** | 2,779 jobs, silent | clean, both |
| **36B** | `LanglandsTunnell/WhittakerODEGrowth.lean` | 604 | 43 (42 `private` + the headline) | **1 ok** | 2,238 jobs, silent | clean |

**What the set consumed**: 3 rows / 1,955 silo in **1,358 written lines** — the derivation of A′ is the
whole saving (its pin file is 643 lines and its port is 18; A alone is 754 lines of module including the
header for a 711-line pin file). Consumers: `spec/LanglandsTunnellSetAF36AConsumer.lean` (163, 4 zones)
and `…AF36BConsumer.lean` (142, 3 zones), both **0 errors**, both real compositions (the `f = c·g`
normalisation of the dependence; the seminorm/homogeneity/`|Re ν|` properties of the growth bound). No
new module beyond the two, no promotion, no migration, no definition layer, no tree build. `dedup
--within` is 0 clusters on each; `move_dead` finds nothing dead; the set-level axiom probe
(`lean/tmp/af3536-axioms.lean`) is clean on all three headlines, the derived one included.

### 6.1 Deviations held for review

1. **A′ derived** (§1) — the general file's 711 lines went through the port **verbatim**: a `diff` of
   pin `:21–711` against the port's spliced range has exactly two hunks, the theorem name and a trailing
   blank line. The companion's hypothesis `hν` is referenced by a single `have _ := hν` (the general
   statement does not need it), which keeps the wrapper's binder name — the checker compares binder text,
   so `_hν` was rejected as a deviation.
2. **B: five `convert` drifts, one mechanism** — at v4.34 `convert … using 1` leaves strictly fewer
   subgoals than at the pin, so five sites' `rfl` paddings became "No goals to be solved" (pin `:67-70`,
   `:85-88`, `:137-141`, `:307-311`, `:358-361`; −14 lines). No `Real.rpow`/`Finset`/`HasDerivAt.scomp`
   rename was needed anywhere.
3. **B keeps `Gf` and `Ff` as two declarations** with the same body (the pin has both, both are used):
   `dedup --within` reports it as the module's one duplicate cluster and the port keeps it, since merging
   would un-port a pin declaration.
4. **`Efun` is the pin's own object**, not `ModularCurve.clamp01` — the advice tool's type-only `def`
   match was refused, as the order required.

### 6.2 A note on the orders, not the port

The work orders' *suggested consumer compositions* were wrong twice and the agents were right to refuse
them: at `ν = 1/2, k = 0` the Whittaker equation reads `w'' = 4π²w`, whose solutions have no moderate
growth (so the `sin`/`cos` pair of the 36A order does not fit), and
`AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` — offered to 36B as a
composition target — is a **shelf row readied by SET-AF34**, not a ported declaration, so the interfaces do
not meet. Both were replaced by better zones (the dependence normalisation; the growth bound's seminorm
and `|Re ν|` invariance). The lesson for the recipe: a consumer suggestion in an order must name a
declaration that exists in the port *now*, and an illustration of an ODE must be checked against the
equation, not recalled.

### 6.3 The re-read

Taken with SET-AF35 in one wave and with the next wave's scaffolds un-ported (FR-0157); the full table is
[SET-AF35.md](SET-AF35.md) §6.2. This set's own delta, from the shelf diff:

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 759 / 317,413 | **756 / 315,458** (the wave lands at 753 / 313,678) |
| leaves | 203 / 52,512 | **200 / 50,557** (all three rows were leaves) |
| `LanglandsTunnell` demand | 37 / 16,932 | **34 / 14,977** |

**Rows this set readied: two**, and they are the answer to "what does the ODE engine unblock" —

| row | silo | why it is ready |
|---|---:|---|
| `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth` | 361 | cites the general linear-dependence headline |
| `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` | 329 | cites the growth bound |

690 silo of new ready work for 1,358 written lines — the best unblocking-per-line figure the column has
recorded since SET 3's leaf tail.

## 7. What this set does not do

- The **moderate-growth hypothesis** stays a hypothesis: A says two *polynomially growing* solutions are
  dependent, and B bounds a solution *near zero*; neither produces the moderate-growth hypothesis from an
  automorphic input. That bridge (the cusp's growth at `∞` from the adèlic side) is a later row.
- The **other ODE leaves** (`norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` 443,
  `exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half` 427,
  `norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori` 420,
  `norm_le_mul_rpow_near_zero_of_first_order_system_of_diag` 240) — the rest of the ODE family, left for
  the next leaves cut.
- **No definition layer, no promotion, no migration, no legacy touch, no tree build.**
