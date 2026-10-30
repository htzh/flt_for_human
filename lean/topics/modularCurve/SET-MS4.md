# SET MS-4 — the Siegel unit: its integral q-expansion, its peaked exponent, its product law

**Status: landed (2026-10-28), fourth order of ready shelf 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U2**, §1, §2, §3, §4; brief
[WORKORDER-MS4-siegel-unit.md](WORKORDER-MS4-siegel-unit.md). Three rows: one new module, two
insertions, no manager lane.

| row | silo | file | checker | promotion (§9.1) |
|---|---:|---|---:|---|
| `SiegelUnit.exists_isIntegral_hasSum_siegelFun` | 1,057 | **new** `SiegelUnit/Integrality.lean` (1,090 lines) | 1 ok | → **115 ok** |
| `SiegelUnit.exists_peaked_exponent` | 373 | insert `SiegelUnit/BernoulliWeight.lean` (+388) | 67 → **68** | → **79 ok** |
| `SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul` | 191 | insert `SiegelUnit/Basic.lean` (+189) | 9 → **10** | → **59 ok** |

| figure | priced | measured |
|---|---:|---:|
| rows / silo | 3 / 1,621 | 3 / 1,621 |
| net new math lines | ≈1,557 | 1,557 (declaration lines 1,567 − in-port 0, minus the 10 duplicate copies) |
| declarations | 117 + 12 + 13 pin | **1 + 117** (new), **+12** / **+13** private (insertions) |
| imports | 2 port modules | + **8 mathlib modules** the brief did not name (see §2) |

## 0. What landed

- **`SiegelUnit/Integrality.lean`** — the 1,057-line analytic engine, transcribed name-for-name
  (117 declarations diffed against the pin's `S_` body, identical), with the headline verbatim:
  `∃ c`, every `c n` integral, the exact `c 0` (`1` or `1 - exp(2πi s/N)`), the integrality of
  `N · (c 0)⁻¹`, the `HasSum` at every `τ`, and the `Tendsto` at `i∞`. The engine is the pin's own
  split — `EulerProdFam.Formal` (`fac`/`pp`/`Pabs`/`Mfam`/the domination bound),
  `EulerProdFam.Topological` (`multipliable_eval`/`tprod_eval_ne_zero`/`hasSum_coeff_W`),
  `EulerProdFam.Analytic` (`zet`a, `qN`, the `CoeffInt` structure), then `ArchSkel` and the
  headline.
- **`SiegelUnit/BernoulliWeight.lean`** — the pin's `Peak` section appended (11 private) plus the
  public `exists_peaked_exponent`: the arithmetic `m`/`Ord` with `Ord 1 0` minimal.
- **`SiegelUnit/Basic.lean`** — the pin's `SiegelTransport` section appended (13 private) plus the
  public double-product law, for **every** exponent function `e`, with the `Γ₁(N)` clause under
  `e r (s + r) = e r s`.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | 1 / 10 / 68 ok, each `0 mismatch / 0 missing / 0 own` |
| `#print axioms` | all three `[propext, Classical.choice, Quot.sound]` |
| builds (workspace lock) | `BernoulliWeight` 3,930 jobs; `Basic` 3,939; `Integrality` 3,955 — all `exit=0` |
| edit loop (200k cap) | silent, zero warnings, all three |
| `dedup.py --module … --within --tier shape` | `Basic` 0 clusters; `Integrality` 1 (10 lines, the **pin's own** duplicate `isIntegral_zeta`/`isIntegral_exp_of_pow`, both present at pin :446 and :529); `BernoulliWeight` 1 (20 lines, the wrapper-over-engine `private solution` / public headline pair) |
| `set_option` | only the project-universal `autoImplicit false`; **no heartbeat cap** |

## 2. Deviations (all forced by v4.34, all recorded in the modules' headers)

1. **Eight mathlib imports the brief did not name**: `Algebra.Polynomial.Expand`,
   `Analysis.SpecialFunctions.Complex.Log`, `Analysis.SpecialFunctions.Log.Summable`,
   `RingTheory.IntegralClosure.IsIntegral.{Basic,Defs}`, `RingTheory.PowerSeries.{Order,PiTopology}`,
   `Topology.Algebra.InfiniteSum.NatInt`. The needmods scan covers *port* modules, not the mathlib
   surface a proof adds — the same lesson as U9's three (SET-MS3 §3.1).
2. **`haveI` and the linter.** The pin's tactic `haveI : NeZero N := ⟨hN.ne'⟩` trips
   `linter.style.haveILetI`, and suppression is barred: `siegel_streams` opens with the term-mode
   `refine (haveI : NeZero N := ⟨hN.ne'⟩; ?_)`; in `tprod_Pc_eval` the same instance is *unused* in
   v4.34, so the line is dropped and the binder written `(_hN : 0 < N)` (positionally unchanged).
3. **The 373 wrapper.** The pin's body needs a tactic `haveI : Fact (1 < N)`, so `solution` is kept
   as `private Peak.solution` taking `[Fact (1 < N)]`, with a 20-line public wrapper supplying it
   (`@solution N _ ⟨by omega⟩ hN`) — the one BernoulliWeight dedup cluster.
4. **191's section variables.** The pin's `variable (N) [NeZero N]` is replaced by explicit
   `(N : ℕ)` (with `[NeZero N]` only where the proof needs it) to avoid
   `linter.unusedSectionVars`; `intCast_zmod_val` needs it because v4.34's `ZMod.val_intCast`
   requires it.
5. **Drift**: 16 deprecated `if_pos`/`if_neg`/`if_true` → `ite_eq_left`/`ite_eq_right`/`ite_true`;
   six unused simp args dropped; the pin's `_root_.…SEXP1.tprod_Pc_eval` alias loses its `_root_`
   prefix (it existed only to escape the pin's `P2MW.S_` wrapper).
6. **Cosmetic, tooling.** `check_port` prints the new headline as
   `ModularCurve.exists_isIntegral_hasSum_siegelFun` — `statement_db` mis-tracks the pin's
   anonymous `section`/bare `end` in that `S_` file; the real name (via `#check`, and
   `#print axioms`) is `ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun`, and the
   verdict is `ok`.

## 3. What this story unlocks

- 1,057's consumer `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow` (364), and from there
  the Siegel-product chain to
  `exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral` (1,267).
- 191's consumers: that same 1,267 row, `isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_…`
  (469), `FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit`
  (330).
- 373's consumer: `exists_gamma1_peaked_auxiliary_form_twelve_dvd` (252), the peaked-form chain.
