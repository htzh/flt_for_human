# WORKORDER-LS1 — Landau's theorem for L-series (the `P2M_Landau` cut)

The `frontier.py --include-leaves` shelf showed the leaf
`LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball` at a 3,140-line silo. This order records the
scoping of that silo, the cut, and the landed module. Manager's work (playbook §3.4, §4); no
subagent.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. What the leaf is, and its defs dependencies

`LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball` is **Landau's theorem** for Dirichlet
series with non-negative coefficients, in the ball/contrapositive form: if the series agrees with
a function holomorphic on `ball (x:ℂ) r` on the right of `x`, then `abscissaOfAbsConv a < x`. It is
a citation-graph **leaf** (cites 0) and sits on the Gate-1 path (→
`abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq` → the Rankin–Selberg second
moment → the weight-one bound).

**Defs dependencies: none.** The pin `S_` file imports only `Mathlib.*` (mostly
`NumberTheory/LSeries/*`) plus `P2M.Util` (which is `import Lean`); `fltdata.stmt_defs` and
`proof_defs` are both empty. Its definitional prerequisites are mathlib's
`LSeries.abscissaOfAbsConv : EReal` (`NumberTheory/LSeries/Convergence.lean`) and the Landau
ingredients `LSeries.positive` / `iteratedDeriv_alternating` (`…/Positivity.lean`). So no
definition layer was owed (playbook §4(a)).

## 2. The silo is mostly an unrelated, unconsumed Landau–Siegel development

The file is 3,140 lines / **186 public declarations** / 2 private, with **17 local `def`s**
(`summatory`, `mellinSummatory`, `localSeries`, `siegelCoeff`, `productChar`, `zeta0`, `siegelG`,
`chi4`, `bFactor`, `zeroTerm`, …). Only one 180-line section — `P2M_Landau`, pin lines 1659–1838,
four declarations (`re_term_logMul_pow`, `abscissaOfAbsConv_lt_of_differentiableOn_ball'`, and the
two contrapositive corollaries) — stands behind the headline; the remaining ≈2,960 lines
(`P2M_CharacterSum` … `P2M_Siegel`, `P2M_ZeroFactorization` … `P2M_Page`) are a Siegel-zero
development. The `P2M_Landau` section references **none** of the 17 local definitions (the only
local name it touches is its own `re_term_logMul_pow`).

**Nothing consumes the Siegel silo** — pin or port:

* only `Theorems/Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean` imports the `S_`
  file; no other file in `P2M/`, `Theorems/`, `Definitions/` does;
* the distinctive names (`siegelG`, `siegelCoeff`, `siegelGConst`, `Estermann`, `zeroTerm`,
  `productChar`, `zeta0Bound`) occur nowhere else in the pin;
* of the silo's whole vocabulary, the pin's citation graph has **2** nodes — the headline and its
  `Landau`-form sibling — and `explore.py` cannot resolve its declarations (`LandauSiegel.siegelG`,
  `norm_LFunction_one_le`, `localSeries_mul`) as theorems at all;
* the port had nothing matching `abscissaOfAbsConv`/`LSeries`/`LandauSiegel`.

This is the §2.3 exclusion exactly: content with no consumer anywhere. It is **dropped**, not
deferred — there is no consumer to defer to.

## 3. The cut and the port

One new module, `FLTForHuman/NumberTheory/LSeries/Landau.lean` (new area; the port had no `LSeries`
modules), keeping the pin's `LSeries` namespace and names:

| declaration | pin source |
|---|---|
| `LSeries.re_term_logMul_pow` | `S_…:1670` |
| `LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball'` | `S_…:1687` |
| `LSeries.not_exists_extension_of_abscissaOfAbsConv_eq` | `S_…:1821` |
| `LSeries.not_differentiableOn_ball_abscissaOfAbsConv` | `S_…:1830` |
| `LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball` | `Theorems/Thm_…` wrapper |

The first four are the `P2M_Landau` section, transcribed; the fifth is the wrapper statement,
proved by the engine. The ≈2,960-line Siegel silo is not transcribed.

Adaptations (proof-level, statements unchanged):

* the pin's `p2m_open` listed a project-local `Set.Finset` namespace — dropped;
* mathlib imports for the proof's `Real`/`Complex` power-log lemmas:
  `Analysis/SpecialFunctions/Pow/Real`, `…/Complex/Log`, `Analysis/Complex/Basic`;
* the pin's `all_goals first | rfl | skip` after the `hexp` `convert` is dead in `v4.34.0` (the
  `convert` closes the goal) and removed; the one after the `hrow` `convert` is **kept** — it
  closes the `LSeries = ∑' term` goal;
* `abscissaOfAbsConv_lt_of_differentiableOn_ball` is declared outside the `variable {a : ℕ → ℂ}`
  section with an explicit `{a : ℕ → ℂ}` binder, because the wrapper spells it inline and the
  checker's diff is textual (the four `S_`-file declarations stay under the section variable, as
  the pin's are).

## 4. Results as landed

| check | result |
|---|---|
| tier-0 loop on `Landau.lean` | exit 0, **0 warnings** (≈4.8 s) |
| tier-1 build | green, 2,815 jobs, 3.0 s |
| checker | 9690 → **9695** identical — delta **+5**, exactly the five declarations; 0 mismatched, 0 missing |
| `#print axioms` on all five | `[propext, Classical.choice, Quot.sound]` |
| `unwired_register.py --check` | current (the module is listed; nothing added to the register) |
| forbidden-token sweep | none |

Wiring: the wrapper and the `S_` file appended last to `SOURCES`; `NumberTheory/LSeries/Landau.lean`
appended last to `PORT_FILES`. Files changed: `FLTForHuman/NumberTheory/LSeries/Landau.lean` (new),
`spec/old_check_stmts.py`.
