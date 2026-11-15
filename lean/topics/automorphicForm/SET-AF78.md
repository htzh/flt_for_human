# SET-AF78 — local Haar inversion and the ball volume

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF76. The
`LanglandsTunnell.TateLocal` ready rows — the local Haar measure's behaviour under inversion and the
measure of a valued ball — are one subject (the local Haar machinery the local zeta integral is built
from), and two of them are cut here.

**2 rows / 405 silo** in **two new modules**, two orders. **One row deferred on a definition gate.**

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | new `LanglandsTunnell/TateLocal/HaarInvariance` |
| **B** | `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` | 100 | 1/13 | new `LanglandsTunnell/TateLocal/BallVolume` |
| — | `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` | 128 | 2/2 | **deferred**: its statement needs `DirichletCharacter.dirichletIdeleChar`, which lives in the pin's `Definitions/Def_DirichletCharacter_DirichletIdeleChar.lean` and is **not** ported — a definition gate the port has not opened. Recorded, not cut. |

## 0. The read

`needed` **592 / 266,082**, ready **24 / 5,045**, leaves **143 / 37,308** (SET-AF76 §5's figures).
`--selfcheck` unchanged (MD-005 markers, none cited here).

## 1. The rows

- **A** — inversion on a nonarchimedean local field: `∫ x, f x⁻¹ ∂μ = ∫ u, ((modulus u : ℝ)²)⁻¹ • f u ∂μ`
  for an additive Haar measure `μ`. The pin's nine declarations are the engine: `modulus` on the unit
  group and its inverse law, the scaling of `μ` by a unit (`measure_smul_units`), the same for
  `lintegral`s (`lintegral_comp_smul_units`), the density `dens x = (modulus x)⁻¹`, and the invariance of
  `μ.withDensity dens` under a unit (`rho_smul`), then the integral identity.
- **B** — the real measure of the ball `{x | Valued.v x ≤ WithZero.exp k}` is `|𝔭|ᵏ` times the measure of
  the integer ring. The pin's file is 101 lines with four private declarations
  (`valued_uniformizerUnit_zpow`, `ball_eq_smul_integers`, `main_of_distribHaarChar_uniformizer`,
  `distribHaarChar_uniformizerUnit`) and the public headline; the module is scaffolded with the headline,
  the worker transcribes the four private declarations.

## 2. The price and the home

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `LanglandsTunnell/TateLocal/HaarInvariance.lean` (new) | A | **61** lines | 7 | **8 ok / 0 / 0** |
| `LanglandsTunnell/TateLocal/BallVolume.lean` (new) | B | **28** | 1 | **1 ok / 0 / 0** |

Both elaborate at the edit-loop cap. No `Def_` work for either row (A's `modulus` is the port's
`LanglandsTunnell.TateLocal.modulus`, B's `Valued`/`adicCompletionIntegers` are mathlib + `AdelicHaar`).

**One warning is expected and is the frozen statement's, not the worker's:** `integral_comp_inv` carries
the pin's `[μ.IsAddHaarMeasure] [μ.Regular]` telescope, and v4.34's `linter.instances` reports
"Overlapping instance parameters" on it. The binder list cannot change (it is the checker's hash), so the
honest fix is a **documented, scoped** silencer on that one declaration, with the reason in the header —
this is the FR-0214 shape and the one place in this set where a silencer is the answer.

## 3. The orders and the gates

| order | row | content | scaffold `sorry`s |
|---|---|---|---:|
| `WORKORDER-AF78A` | A | ≈250 | 7 |
| `WORKORDER-AF78B` | B | ≈80 + 4 private decls | 1 |

Disjoint files, two orders in parallel. Gates: the same six as SET-AF75 §3.

## 4. The shelf effect

Forecast **measured with `--port`**, jointly with SET-AF77 (the two sets open on the same read):

| figure | §0 | forecast (AF77 + AF78 `--port`ed) |
|---|---:|---:|
| `needed [F terminal]` | 592 / 266,082 | **587 / 265,294** |
| ready rows | 24 / 5,045 | **21 / 5,522** |
| leaves | 143 / 37,308 | 143 / 37,308 |

| row readied | silo | lev |
|---|---:|---:|
| `AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow` | 793 | 1/1 |
| `AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion` | 472 | 2/2 |

No row is readied by this set's two rows *alone* on the evidence available — the 793-line row is the
`adelicHeight`/`weyl_unipotent` estimate whose premises are the local Haar/ball rows, and it needs the
whole set (A and B together) plus nothing else; the second is AF77-B's consumer. Both are measured, not
argued: the joint read returns them.

## 5. The landing

Both rows in (the third stayed deferred on its definition gate), 8 `sorry`s → 0, two new modules.

| file | row | lines | `sorry` | checker | axioms |
|---|---|---:|---:|---|---|
| `LanglandsTunnell/TateLocal/HaarInvariance.lean` | A | 61 → **328** | 7 → 0 | **9 ok / 0 / 0** | clean |
| `LanglandsTunnell/TateLocal/BallVolume.lean` | B | 28 → **99** | 1 → 0 | **1 ok / 0 / 0** | clean |

Consumers `spec/LanglandsTunnellSetAF78AConsumer.lean` (84) and `…B…` (113): 0 errors, 0 warnings.
**Heartbeat floors**: A 12 000 (10 400 before the row statement's import widened the instance set —
the cost is `integral_comp_inv`'s own instance search, not the new proof), B 4 400 — 17×/45× margins.

### The one silencer in the two sets, and why it is right

`integral_comp_inv` carries the pin's `[μ.IsAddHaarMeasure] [μ.Regular]` telescope. Both give
`IsFiniteMeasureOnCompacts μ`, so v4.34 reports the overlap; the binders are the checker's wire (FR-0214),
so the declaration cannot change. The worker probed it — deleting the silencer reproduces **exactly one**
warning, there — and wrote `set_option linter.overlappingInstances false in` scoped to that declaration,
with the reason in the header. (The order guessed `linter.instances`; the printed name is
`linter.overlappingInstances`.) Nothing else in either module is silenced and no `omit` was used.

### BallVolume's v4.34 problem, solved without touching the statement

v4.34's `distribHaarChar_mul` now demands `[μ.Regular]`, which the row's frozen headline does not carry.
Rather than adding a hypothesis (impossible — the statement is the wire) the worker derives it locally in
the private engine (`Measure.regular_of_isAddLeftInvariant` at `v.adicCompletionIntegers`, σ-finiteness
from `IsAddHaarMeasure.sigmaFinite` + `SigmaCompactSpace`) as a plain `have hreg : μ.Regular`, which
instance search finds. That is the shape to reach for whenever the pin's proof needs an instance the row's
statement does not bind.

### The row the scaffold lost, and the instrument that found it

Order A's first landing ported the pin's *general* theorem and stopped there: the checker was `8 ok / 0 / 0`
and the mathematics was in, but the post-landing read came out **588 / 265,599 against a forecast of
587 / 265,294** — the graph's name tier credits a node by the port declaration's **last name**, and the
port had `integral_comp_inv` where the row is `integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`
(the pin's `solution` at `:269–304`, the specialization to `v.adicCompletion F`). The manager added the
row's statement (byte-identical, so in the checker's wire) and the module's worker proved it from the
general theorem with `hmod`/`h0` discharged — `hmod` from the port's
`modulus_adicCompletion_eq_nnnorm`, `h0` by the pin's uniformizer argument. The module is now 328 lines /
**9 ok**, one import richer (`TateGlobal.NormIntegrable`), and the read credits the row. Recorded as
**FR-0221**, the inverse of SET-AF75's A3 omission: a scaffold must carry the *row's* statement, not only
its engine's.

### The set's numbers

| figure | before | **after** | forecast (joint with AF77) |
|---|---:|---:|---:|
| `needed [F terminal]` | 592 / 266,082 | **587 / 265,294** | 587 / 265,294 ✓ exact |
| ready rows | 24 / 5,045 | **21 / 5,522** | 21 / 5,522 ✓ exact |
| leaves | 143 / 37,308 | 143 / 37,308 | unchanged ✓ exact |

The two readied rows are the pair the joint forecast named
(`AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow`,
793, and `AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion`,
472), and the ready block now trades four small rows for two large ones — the next cut faces a 793-line
row whose premises are the Haar/ball estimates this set closed.
