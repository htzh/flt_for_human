# WORKORDER-LP3b — coefficient growth of an algebraic power series

**Status (closed 2026-10-19): landed and reviewed green.** One set, one module, one
public headline and 23 public lemmas, **all 24 statement-checked**. Measured:
`FLTForHuman/Analysis/PowerSeries/EisensteinAlgSeries.lean`, 491 lines,
`spec/check_port.py` **24 ok / 0 mismatch / 0 missing**; tier-1 build 3,097 jobs,
**0 warnings**; axioms `[propext, Classical.choice, Quot.sound]`; frozen checker
unchanged at **10473**. Four proof-body adaptations: `aeval_algebraMap_apply` →
`aeval_algebraMap_apply_eq_algebraMap_eval`, the deprecated
`natDegree_eq_zero_of_derivative_eq_zero` → `Polynomial.derivative_eq_zero`,
`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (8 sites), and one added mathlib import
(`RingTheory.PowerSeries.NoZeroDivisors`) for the `NoZeroDivisors`/`IsReduced`
instances. This is the analytic leaf the third `localParam` leaf
(WORKORDER-LP4) needs: it supplies the majorant that makes a `LaurentSeries`
coefficient bound out of an algebraic equation.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the new per-module protocol (`spec-pin:` header, `spec/check_port.py`).
Read [WORKORDER-LP3a-laurent-and-generator-transfers.md](WORKORDER-LP3a-laurent-and-generator-transfers.md)
for the house style of the companion set (same protocol, same build discipline).

## 1. Scope

Port the pin `S_` file **whole** (playbook §2.3 — it is a graph leaf with no premises
of its own):

`P2M/Sol/S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean`,
455 lines, 24 declarations, **all public**, namespace
`PowerSeries.EisensteinAlgSeries`.

The mathematics: an algebraic complex power series has geometric coefficient growth.
`pn N x f` is the majorant `∑_{n<N} ‖f_n‖ xⁿ`; the development proves it is subadditive
and multiplicative (`pn_add_le`, `pn_mul_le`, `pn_pow_le`, `pn_succ_X_mul`), bounds a
polynomial's coefficients by `pabs`, builds a **majorant** from an algebraic equation,
finds an annihilator of `φ` of minimal degree whose derivative does not vanish
(`exists_annihilator_derivative_ne_zero`, via the Taylor shift
`aeval_taylor_powerSeries` and `X_pow_dvd_aeval_sub`), prepares the tail
(`exists_prepared_tail`) and concludes `‖coeff n φ‖ ≤ C * R ^ n`.

**Not this set:** LP3a, LP4, any edit to an existing module.

Measured: **0 substitutions, 0 residue** (`port_advise`, shape tier) — every
declaration is new. Net new = 455 pin lines / 24 declarations, all statement-checked.

## 2. Pre-round: none is owed

The file imports **mathlib only** (`import Mathlib` at the top, nothing else). There
is no definition layer, no port reuse, and no name collision: the port has nothing in
`PowerSeries.EisensteinAlgSeries` and no `pn`/`pabs`/`majorant` anywhere. The leaf has
no premises.

**Layering.** Home it outside `AlgebraicCurve` — it is complex analysis of power
series, consumed by the curve layer but not part of it.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement: `Theorems/Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean`
* proof: `P2M/Sol/S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean`

Rendered:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean>.

## 4. Deliverable

**4.1 Home.** `FLTForHuman/Analysis/PowerSeries/EisensteinAlgSeries.lean` (new
`Analysis/` directory; the module is the only thing in it for now). Keep the pin's
namespace `PowerSeries.EisensteinAlgSeries` — the statements do not mention it, but
the names are FLT's and the pin's consumers will expect them.

**4.2 The headline**, exactly as the wrapper (verbatim; keep the `-- pin:` marker):

```lean
-- pin: PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex (Theorems/Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean:5)
theorem PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex
    (φ : PowerSeries ℂ) (hφ : IsAlgebraic (Polynomial ℂ) φ) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n φ‖ ≤ C * R ^ n
```

**4.3 The 24 declarations.** Transcribe them in the pin's order and at the pin's
names, all public:
`pn`, `pn_nonneg`, `pn_zero` (`@[scoped simp]`), `pn_succ`, `pn_add_le`, `pn_sum_le`,
`pn_mono`, `norm_coeff_mul_pow_le_pn`, `pn_mul_le`, `pn_one_le`, `pn_pow_le`,
`pn_succ_X_mul`, `pn_succ_C`, `pabs`, `pabs_nonneg`, `pn_coe_le_pabs`,
`pabs_le_pabs_one`, `majorant`, `exists_annihilator_derivative_ne_zero`,
`aeval_taylor_powerSeries`, `coe_aeval_eq`, `X_pow_dvd_aeval_sub`,
`exists_prepared_tail`, and the headline. Keep the `noncomputable def`s and the
`@[scoped simp]` attribute exactly where the pin has them.

**4.4 Module header.**

```lean
/-
  … one paragraph: the pin node, that it is a graph leaf with mathlib as its only
  import, and what it feeds (the majorant behind the Laurent expansion of LP3a/LP4).

  spec-pin: Theorems/Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean
  spec-pin: P2M/Sol/S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean
-/
```

## 5. Route

Transcribe; adapt only what mathlib `v4.34.0` forces. Expected drift points (the AC
friction log, [../../logs/ac-port.md](../../logs/ac-port.md) §11.2): `Polynomial`
`aeval`/`taylor` API names, `PowerSeries.coeff` vs `Polynomial.coeff` coercions, and
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` (deprecated — use
`ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`, as LP2 did for 0 warnings).
`simp`/`gcongr`/`positivity` are the workhorses; if a proof needs a heartbeat bump,
that is an instance-inference defect — diagnose it, do not raise the cap.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`.
> Never raise `maxHeartbeats`, never a module-level `set_option maxHeartbeats`.
> `flock .lake/flt_build.lock timeout 300 lake build <module>` per finished file.
> Never a bare whole-tree `lake build`. Every tool call within 2 minutes, no loops.

## 7. Hub prohibition

One new module, no existing file edited, no `PORT_FILES`/`SOURCES` entry, no commit,
no promotion. Stop and report anything that seems to need one.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/Analysis/PowerSeries/EisensteinAlgSeries.lean   # 24 ok
python3 spec/check_port.py --changed                                                    # none failing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.Analysis.PowerSeries.EisensteinAlgSeries
```

plus `#print axioms PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex`
(`[propext, Classical.choice, Quot.sound]`), the grep sweep, 0 warnings, `git status`
showing only the new module, and the frozen checker unchanged at 10473.

## 9. Report shape

Module path, lines, declaration count and the fact that all 24 are statement-checked;
the `check_port` output with the pin line each declaration matched; build result and
warnings; the axioms line; the grep sweep; `git status`; every deviation (the
statement must not change — if the checker reports a MISMATCH, fix the port's text).
