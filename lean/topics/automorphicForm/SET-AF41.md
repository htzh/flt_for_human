# SET-AF41 — the near-zero growth bound at the cusp: the unforced Whittaker pair and the three ODE bounds

**Status: LANDED 2026-11-12** — §0 the read, §1–2 the rows and the price, §3 the manager's layer,
§5 the forecast, §6 the landing record and the re-read. Read off the D–S shelf
with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). Forty-first set
of the column, and its return to the `LanglandsTunnell` leaves after the AF34–AF40 detour through the
definition layer, the Satake bound and the idèle product measure.

**5 rows / 1,658 silo / 970 net (`port_plan`) in ≈940 written lines and 50 declaration groups**, of which
**190 declaration lines are already in the port** and **299 are one prelude the pin copies into two
files**. Two new modules, three headlines, no definition gate, no promotion of new mathematics (one
*visibility* promotion, §3), no legacy module, no migration.

| # | row (`LanglandsTunnell.` dropped) | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` | 443 | 1/2 | a solution of `y²f'' + (¼ − ν² + 2πky − 4π²y²)f = 0` on `(0,1]` is `O(y^(½−|Re ν|))`, and `O(y^(½−|Re ν|−ε))` for every `ε > 0` |
| **A2** | `exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half` | 427 | 2/2 | for `|Re ν| < ½` there is **some** `δ > 0` with `‖f y‖ ≤ C y^δ` |
| **B1** | `norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori` | 420 | 2/2 | the Bessel-type equation `y²f'' + (¼ − ν² − 4π²y²)f = h`, with `‖h‖ ≤ A y^σ` and an a-priori `‖f‖ ≤ B y^r`, gives `‖y f' − (½ − ν) f‖ = O(y^(min(min(½+Re ν,σ),r+2) − ε))`, and `‖f‖, ‖y f'‖` at `min(½+Re ν,σ)` once `r > ½ − Re ν` |
| **B2** | `norm_le_mul_rpow_near_zero_of_first_order_system_of_diag` | 240 | 1/1 | a first-order system `y F' = A F + B F` with `Re a_i ≥ r₀` and an off-diagonal part of order `y^τ` has `‖F i y‖ = O(y^(r₀−ε))` |
| **B3** | `norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing` | 128 | 1/1 | a first-order equation `y f' = b f + h` with `‖h‖ ≤ A y^σ` has `‖f y‖ = O(y^(min(Re b,σ) − ε))` |

## 0. The read

`frontier.py --ds --ready --include-leaves --rank-by silo --top 0`:

| figure | value |
|---|---|
| `needed [F terminal]` | **742 / 309,646** |
| `needed [literal]` | 754 / 313,111 |
| frontier F | 1,674 / 817,730 |
| ready rows | 50 / 9,171 |
| leaves | 200 / 50,557 |
| `AutomorphicForm` demand | 260 / 113,790 |
| `LanglandsTunnell` demand | 33 / 13,790 |
| withheld (`premises_pruned`) | 4 rows |

**The corrected read, and what it corrects.** `--selfcheck` fails one line: five `ModularCurve` `SOURCES`
`Thm_` markers (`ModularPolynomialData.evalSymm_of_irreducible`,
`ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion`, `PhiGen.evalSymm_of_coeff_evalAtJ_eq`,
`PhiGen.evalSymm_of_splits`, `PhiGen.splits_of_coeff_evalAtJ_eq`) resolve to no port declaration — the
phi-refactor workstream's markers, not this column's. Corrected (`--unport` × 10: those five plus this
set's five in-flight rows of §3): `needed` **742 / 309,646** (unchanged — none of the five is in `F`),
literal **758 / 315,065**, frontier 1,669 / 814,882, ready **50 / 9,171**, leaves **200 / 50,557**,
AF 260 / 113,790, `LanglandsTunnell` **33 / 13,790**. So the corrected read confirms the instrument's
`needed` and moves only the literal column (the five markers are real pin nodes with no port declaration).

**The post-landing read is already taken, by accident, and it is the forecast's source.** A read taken once
§3's scaffolds existed but with only the phi markers unported reads `needed` **737 / 307,988**, ready
**53 / 10,555**, leaves **195 / 48,899** — the scaffolds' `spec-pin:` wires, not their proofs, do that,
which is exactly FR-0114's mid-dispatch trap ("a wire on a skeleton marks the pin file ported"). For a
brief it is a measurement: it is the state the landing produces, and §5 quotes it as such.

**The withheld block**, quoted as the recipe requires: `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH`,
`ModularCurve.moduleFinite_padicInt_tateModule_jOne`,
`AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`,
`AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` — the first two are the phi markers'
neighbours, the last two the prunable subject's residue (§0 of the recipe). None is cut here.

**The premise audit is empty**, and for a structural reason: all five rows are pin **leaves** with
`premises = 0` — their `S_` files cite nothing. The **definition gate is empty** too: the five wrappers
import `Mathlib.{Analysis.Calculus.Deriv.Basic, Analysis.Complex.Basic, Analysis.SpecialFunctions.Pow.Real,
Data.Matrix.Basic}` and `P2M.Util` — no `Definitions/Def_*` line at all (FR-0049's check, run by hand).
This is the AF36 shape: pure analysis, no definition layer.

## 1. The rows, and why these five

AF36 §7 named this cut: "the rest of the ODE family
(`norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` 443,
`exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half` 427,
`norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori` 420,
`norm_le_mul_rpow_near_zero_of_first_order_system_of_diag` 240) — left for the next leaves cut", and 128
(the Euler row) is the fifth. All five are premise-free leaves; the recipe's §1 cheap-leaf signal gives
**1,658 silo for 1,384 silo of readiness** (below), the best return the column has measured since AF36.

**A2 is derived from A1, and this was checked, not assumed.** A2's hypotheses are A1's plus
`|ν.re| < 1/2`, and its conclusion is the existence of *some* exponent below `1/2`; A1's second conjunct
gives it at `ε := (½ − |Re ν|)/2`, `δ := (½ − |ν.re|)/2 > 0`. Neither pin file cites the other (both are
leaves), so the inversion is available — unlike SET-AF15's case. What is *not* derived is A1's sharp
`ε = 0` conjunct, which the pin proves by a separate `ν = 0` / `ν ≠ 0` split; that whole file is
transcribed.

**The pin duplicates 327 lines across A1 and A2** — `diff` of the two `S_` files shows exactly two hunks,
`engine`'s conclusion and the headline; everything before line 328 is byte-identical modulo the namespace
label. So the port writes that prelude **once**, and A2 costs about ten lines.

## 2. The price

`port_advise --with-defs` + `port_plan` over the five:

| figure | value |
|---|---:|
| raw `S_` lines | 1,658 |
| declaration lines | 1,574 |
| — duplicate copies (A2's prelude) | 414 |
| — boilerplate | 84 |
| distinct declaration groups | 50 |
| once-cost after dedup | 1,160 |
| already in the port | **190** |
| **net new math lines** | **970** |
| written (two orders) | ≈940 forecast → **828 measured** (§6) |

`port_advise`'s *substitute* block is the set's decisive measurement: **48 target declarations are
byte-identical to `private` declarations in
`FLTForHuman/LanglandsTunnell/WhittakerODEGrowth.lean`** (AF36's forced-equation development), i.e. 24
names × the two files. Four further names (`vp_hasDerivAt`, `vm_hasDerivAt` and their two copies) exist
there under a *different* statement: the port's copies carry the forcing summand `+ Ff h t`. Those two are
written in the new module (11 lines each, the pin's own text).

Two `port_advise` false positives are refused: `Efun` is matched to `ModularCurve.clamp01` and `rate` to
`LanglandsTunnell.mfun` — both type-only `def` matches. `Efun` is the energy of the Liouville transform
and keeps the pin's name.

## 3. The manager's layer, landed (do not redo it)

1. **The prelude is promoted, and the promotion is checker-measured.** 33 declarations of the
   `WhittakerODEGrowth.lean` prelude are now **public**, at the pin's names: `eA`, `eB`, `eA_pos`,
   `eB_pos`, `eA_le_one`, `eA_zero`, `eB_sq`, `eA_mul_eB_sq`, `eA_hasDerivAt`, `eB_hasDerivAt`, `Gf`,
   `Hf`, `vp`, `vm`, `sfun`, `vp_sub_vm`, `Gf_hasDerivAt`, `Hf_hasDerivAt`, `nsq`, `nsq_eq`,
   `nsq_hasDerivAt`, `cross_le`, `cross_decomp`, `rate_bound`, `Efun`, `Efun_nonneg`, `mfun`,
   `norm_sfun_le`, `rate`, `Phi`, `Phi_hasDerivAt`, `Phi_zero`, `Phi_le`. The module's `spec-pin:` wire was
   widened by two pin files, and `check_port --force` reads **34 ok / 0 mismatch / 0 missing** where it read
   **1 ok** before; the module builds silent in 19 s. This is the recipe's §5 surface gate run in the
   forward direction: the pin copies this prelude into *three* files, so the port owns it once, publicly.
   The forced half (`Ff`, the forced `vp`/`vm` derivative rows, `rate_bound_forced`, `sq_assemble`,
   `Phi_ge`, `engine`, `Efun_hasDerivAt_le`, `Efun_le`, and the headline) stays `private`.
2. **Two skeletons exist, elaborate and are checker-green.** `…/LanglandsTunnell/WhittakerODENearZero.lean`
   (105 lines: the five declarations A1/A2 need beyond the promoted prelude, and two headlines) reads
   **2 ok / 0 mismatch / 0 missing**; `…/LanglandsTunnell/ODENearZeroBounds.lean` (156 lines: the seven
   pin-public helpers and three headlines) reads **10 ok / 0 mismatch / 0 missing**. Both elaborate with
   exactly their `sorry` warnings and nothing else, which is the statement probe.
3. **The homes are the subjects'.** A1/A2 are the *unforced* half of the same equation
   `WhittakerODEGrowth.lean` treats forced, so they are their own module above it, and they import the
   promoted prelude rather than copying 327 lines. B1/B2/B3 are three different equations with one method
   (an a-priori bound and a bootstrap), and they are one module because their consumers are one block
   (`exists_norm_le_mul_rpow_of_torus_system_*`); the three pin namespaces `Gap41`, `OdeEAux`, `OdeCAux`
   are kept verbatim, because the pin's `main` occurs in two of them with two statements.
4. **No `own:` row is needed**: every declaration in both modules is transcribed at its pin name and
   spelling. No `set_option` beyond `autoImplicit false`; no linter suppression.
5. **Imports are the mathematics':** `WhittakerODENearZero` imports `WhittakerODEGrowth`, nothing else;
   `ODENearZeroBounds` imports six mathlib analysis modules and `Data.Matrix.Basic` (the pin's union,
   minus its `import Mathlib`), and no port module.

## 4. Orders and gates

`tmp/af41/WORKORDER-AF41A-whittaker-near-zero.md` and `tmp/af41/WORKORDER-AF41B-ode-bounds.md`. The two
modules are disjoint, share no declaration and neither imports the other, so both orders run in parallel.
The standard gates: `check_port --force` at 0 mismatch / 0 missing with the counts above, axioms clean on
all five headlines, each module's own `lake build` under `flock`/`timeout` with no tree build, silence and
zero warnings, `dedup`/`move_dead`, and one `spec/` consumer zone per order with a real composition.

## 5. Forecast

The post-landing column is the read taken after §3's scaffolds appeared (they wire exactly these five pin
files), so this table is measured except for the two cells the reader must add, marked ·.

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 742 / 309,646 | **737 / 307,988** |
| `needed [literal]` | 758 / 315,065 | **753 / 313,407** |
| frontier F | 1,669 / 814,882 | **1,674 / 816,540** |
| ready rows | 50 / 9,171 | **53 / 10,555** |
| leaves | 200 / 50,557 | **195 / 48,899** |
| `AutomorphicForm` demand | 260 / 113,790 | 260 / 113,790 |
| `LanglandsTunnell` demand | 33 / 13,790 | **28 / 12,132** |
| withheld | 4 rows | 4 rows |

**The return: three rows / 1,384 silo**, measured by `af24-return.py` —
`exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded` (508),
`exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos` (499) and
`norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq` (377). The torus-system block is therefore
AF42, and it is a *composition* set in the AF9 sense: its three rows reuse the very bounds this set
writes, and 139 (`casimir_pos_or_discrete_or_zero_of_weightSet`) is its CuspidalConstituent edge.

## 6. The landing (2026-11-12)

Two orders, two new modules, all gates green; the manager then deduped one row of the second.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **41A** | `LanglandsTunnell/WhittakerODENearZero.lean` | 105 → **294** (189 written) | 7 (5 `private` + 2 public) | **2 ok / 0 / 0** | 7.8 s, silent | 2/2 clean |
| **41B** | `LanglandsTunnell/ODENearZeroBounds.lean` | 156 → 795 → **694** | 10 (7 pin-public helpers + 3 headlines) | **10 ok / 0 / 0** | 5.9 s, silent | 3/3 clean |
| | **2 modules** | **988 lines** | 17 (12 public, 5 `private`) | **12 ok, 0 mismatch, 0 missing, 0 own** | | 5/5 |

**What the set consumed**: 5 rows / 1,658 silo in **828 written lines** (189 + 639 body lines), against
`port_plan`'s 970 net forecast — the difference is exactly the two economies the set was cut for: 327
pipeline lines of preamble imported instead of retyped (41A) and 102 of the pin's own duplicated proof
merged away (41B, below). Net module text in the tree: **988 lines for 1,658 silo**, 0.60 lines per silo
line — the column's cheapest set per silo line since AF36.

**The prelude promotion paid off exactly as measured, and needed nothing else.** 41A's six transcribed
bodies compiled **first try** against the promoted prelude with **zero** local re-statements, zero added
imports and zero `set_option`s; the only declarations re-declared rather than imported are the two
unforced derivative rows (whose forced twins carry `+ Ff h t`) and the three sharp rows the forced module
keeps `private`. So the promotion's 33 public declarations are the whole interface, and the set adds no
duplicate of them.

### 6.1 Deviations held for review

1. **A2 is derived, not transcribed** (11 lines against a 427-line pin file). `δ := (½ − |ν.re|)/2 > 0`,
   `ε := δ` into A1's second conjunct, `C' := max C 0` — and because the resulting exponent is *equal* to
   `δ`, no `rpow` monotonicity is needed. Consequence: the pin's 427-file `engine` and its 327-line copy
   of the prelude are not in the port at all; the node is ported through its headline.
2. **`Gap41.odeC` is merged, not transcribed** (the manager's edit after the worker's report): the pin's
   first-order argument `y f' = b f + h` is stated **identically** in `OdeCAux.main` (euler file `:19`)
   and `Gap41.odeC` (bessel file `:16`), so the port proves it once and keeps the second pin name as a
   one-line application. `dedup`'s removable count went 106 → 8 (the residual is the pin's own duplicated
   *statement*, kept on purpose) and the checked surface stayed 10 `ok`. Recorded as FR-0165, with the
   rule: for a `shape` cluster, compare the statements before accepting a keep.
3. **One mathlib import added**: `Mathlib.Algebra.Order.Chebyshev`, for `sq_sum_le_card_mul_sum_sq` in
   `OdeEAux.main` (pin diag `:148`), which the pin obtained from its own file's import — the scaffold's
   union had dropped it. `P2M.Util` turned out to be tooling only (127 lines of elab commands, no lemmas),
   so nothing had to be ported from it.
4. **`open Real Set Filter` + `open scoped Topology` inside `Gap41`** (the pin's `open Real Set Filter
   Topology`): at v4.34 `Tendsto`/`tendsto_id` are not root-exported and `𝓝` is `scoped[Topology]`.
   Proof-level only; `gapC` is the one consumer.
5. **Four `convert … <;> try with_reducible_and_instances rfl` sites** became `refine h.congr_deriv ?_`
   plus the coefficient identity, because v4.34's `unnecessarySeqFocus`/`unusedTactic` fire on the pin's
   form and gate 1 forbids warnings. The `congr_deriv` orientation is the *reverse* of the pin's
   `convert`, so the two `hGd` coefficients carry the opposite sign. FR-0163.
6. **The Bessel headline's unused `(hν : 0 ≤ ν.re)`** is referenced by one `have hν₀ : 0 ≤ ν.re := hν`
   rather than renamed (a statement change the checker sees) or suppressed (forbidden). FR-0164.
7. **No `own:` row, no marker, no linter suppression, no `sorry`** in either module; both consumers are
   `spec/` probes with three real zones each at **0 errors**, no `#check`.

### 6.2 The re-read, exact on all seven cells

Both readings taken with the two modules landed; the corrected one unports the five `ModularCurve` phi
markers of §0 (the instrument read is quoted too, because the two differ on the literal column).

| figure | before (corrected) | forecast | **actual (corrected)** | instrument |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 742 / 309,646 | 737 / 307,988 | **737 / 307,988** ✓ | 737 / 307,988 |
| `needed [literal]` | 758 / 315,065 | 753 / 313,407 | **753 / 313,407** ✓ | 749 / 311,453 |
| frontier F | 1,669 / 814,882 | 1,674 / 816,540 | **1,674 / 816,540** ✓ | 1,679 / 819,388 |
| ready rows | 50 / 9,171 | 53 / 10,555 | **53 / 10,555** ✓ | 53 / 10,555 |
| leaves | 200 / 50,557 | 195 / 48,899 | **195 / 48,899** ✓ | 195 / 48,899 |
| `AutomorphicForm` demand | 260 / 113,790 | unchanged | **260 / 113,790** ✓ | 260 / 113,790 |
| `LanglandsTunnell` demand | 33 / 13,790 | 28 / 12,132 | **28 / 12,132** ✓ | 28 / 12,132 |

**Rows this set readied: three, and exactly the three the return column priced** —
`exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded` (**508**),
`exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos` (**499**) and
`norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq` (**377**), 1,384 silo in all. This is the rare
set whose forecast was exact including the return: the three rows' *only* missing premises were the five
of §1, which is why the brief could name them before dispatch. A one-row-per-order removal accounts for
the node column exactly (−5), so AF24's arithmetic rule needed no correction here.

## 7. What this set does not do

- **The two system rows AF36 readied** stay: `linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth`
  (361, ready, cites AF36's complex-parameter engine) and
  `exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` (329, ready). They are
  the *system* versions of A1/A2 and belong with the torus-system block, not with the scalar bounds.
- **`casimir_pos_or_discrete_or_zero_of_weightSet`** (139, leaf, 2/2) — readies two `CuspidalConstituent`
  rows; deferred to AF42 by name.
- **The other `LanglandsTunnell` rows** on the shelf, named so the next pass starts from the figure:
  ready `TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` (305, 1/7),
  `dirichletIdeleChar_mul_modulus_det_gen` (128, 2/2), `TateLocal.measureReal_setOf_valued_le_exp` (100,
  1/13); leaves `isBoundedOnSiegelWindows_weightOneLift` (501), `exists_heckeCosetSystem_productionPinsCompact_of_not_dvd`
  (446), `RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one` (231),
  `TateLocal.realZeta_eq_localZeta` / `complexZeta_eq_localZeta` (166 + 166),
  `TateLocal.tateFourier_indicator_setOf_valued_sub_le` (149), `eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow`
  (104), `TateLocal.psiLocal_eq_one_of_mem_integers` (45), `TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel`
  (37).
- **The AF shelf's own head** is untouched: the cuspidal unfolding row (635) and the level-one Hecke coset
  obstruction (229) that SET-AF40 §5 named (measured return 266 for a 1,400-silo cut), the adèlic Fourier
  block (`NumberField.AdelicFourier.*`, 1,234 silo of leaves, measured return 0), and the isotypic cuspidal
  constituent cluster (1,446 silo, measured return 637).
