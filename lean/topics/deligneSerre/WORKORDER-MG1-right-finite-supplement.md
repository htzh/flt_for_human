# WORKORDER-MG1 — the right-finite pair: polynomial approximation on `U(2)` and `O(2)`

**Status (closed 2026-10-20): landed and reviewed green.** One set, **three modules, zero host
edits**, one coding session. Measured: 68 / 816 / 760 lines, **96 statement-checked declarations**
(1 prelude + 49 `U(2)` + 46 `O(2)`), checker **1942 → 2038 ok**, 0 mismatched / 0 missing over 56
modules; tier-1 builds 2,051 / 2,639 / 2,639 jobs (2.8 / 6.2 / 5.9 s), **0 warnings**; axioms
`[propext, Classical.choice, Quot.sound]`; 7/7 `haveILetI` suggestions taken verbatim and 0
suppressions. Record: [logs/matrixgroup-rightfinite.md](../../logs/matrixgroup-rightfinite.md).
The topic is [TOPIC-matrixgroup-rightfinite.md](TOPIC-matrixgroup-rightfinite.md).

The rows are the D-S leaf shelf's ranks #2 and #5 of 442
(`frontier.py --ds --include-leaves --rank-by silo`):

| node | pin `S_` lines | `used_by` cone/project |
|---|---:|---|
| `Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite` | 802 | 2 / 5 |
| `Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite` | 748 | 1 / 1 |

They are one set because they are one development: mathlib defines
`abbrev orthogonalGroup n R := unitaryGroup n R`, so the two statements are the same statement with
the base field substituted, and the two pin files are **≈80 % identical at the base field** (170
changed lines, 37 hunks). They are **ported together, faithfully, not strengthened** — the generic
`[RCLike 𝕜]` and general-`n` routes were considered and declined (topic §7).

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

## 1. Scope

> If `Φ : U(2) → ℂ` is continuous and its right translates span a finite-dimensional space, then on
> `U(2)` it agrees with a polynomial in the real coordinates of the entries — an element of
> `Submodule.span ℂ {F | ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (· m)).prod}`.

Proof shape (both files, block for block):

| block | pin lines (U / O) | the mathematics |
|---|---|---|
| `TensorSplit.exists_eval_combination` | 16–46 / 15–45 | every functional on a finite-dimensional space of functions is a finite combination of evaluations |
| group + Haar | 61–122 / 58–114 | `abbrev U2`/`O2`, `polyFun`, `isCompact_unitaryGroup`/`isCompact_orthogonalGroup` (closed + entry-bounded), the six `scoped` instances, `K0`, `haarU2`/`haarO2`, `haar*_univ`, `integral_translate(_real)`, `integrable_of_continuous`, `integral_pos_of_continuous` |
| Fejér kernel | 124–229 / 116–203 | `qker`, `continuous_qker`, the entry bounds, `qker_nonneg`/`_le_one`/`_one`/`_eq_one_iff`, `exists_lt_one_bound` |
| convolution | 231–481 / 205–455 | `fejerNorm`, `fejerNorm_pos`, `fejerConv`, `integrable_conv_kernel`, `fejerConv_sub`, `private aux_ratio`, `fejerConv_tendsto`, `fejerConv_mem_span` |
| polynomial algebra | 483–597 / 457–566 | `entryCLM`(+`_apply`), `conjEntryCLM`(+`_apply`, ℂ only), `coordFns`, `monom`, `Pdeg`, `scoped instance finite_expIndex`, `finiteDimensional_Pdeg`, `one_mem_polyFun`, `polyFun_mul_mem`, `Pdeg_le_polyFun`, `Pdeg_mul_mem`, `pow_mem_Pdeg`, `coordFn_mem_Pdeg_one`, `const_mem_Pdeg_one` |
| assemble | 599–750 / 568–696 | `aker`, `aker_coe`, `continuous_aker`, `akerC_mem_Pdeg_one`, `restrictU2`/`restrictO2`, `exists_polyFun_fejerConv`, `exists_polyFun_eq_of_continuous_of_rightFinite` |
| `solution` | 788 / 734 | the pin's `S_`-level wrapper — **not ported**; the headline is restated at the `Theorems/` name (§3) |

**Not this set:** the consumers of §6; any generic `[RCLike 𝕜]` or general-`n` restatement; any edit
to an existing module (there is none to make — see §4); any promotion or `spec/decl_markers.tsv` entry.

## 2. Measurement

`tools/deps/port_advise.py --target … --target … --json build/u2o2_advise.json`,
`port_plan.py --json build/u2o2_advise.json`:

| quantity | value |
|---|---:|
| raw `S_` lines (both files) | 1,550 |
| declaration lines | 1,521 |
| of which duplicate copies (removable) | 87 |
| boilerplate (imports/attrs/`p2m`) | 29 |
| distinct declaration groups | 91 |
| already in the port (vetted) | **0** |
| substitutions | **0 trusted / 2 suspect** |
| **net new math lines** | **1,434** |
| named declarations | 99 (51 + 48): 1 prelude + 95 silo + 2 `private aux_ratio` + 1 `solution` + 1 `solution` |

The 2 suspect rows are both the parser's type-only `def` match
`fejerNorm ↔ AutomorphicForm.RealIwasawa.Engine.towerD`: **false**, the two share only `ℕ → ℝ`
(`fejerNorm n = ∫ h, qker h ^ n`; `towerD n = n ! * max 1 ratio`). Recorded, nothing to do.

## 3. Deliverables

Three new modules, all **listed** (each carries `spec-pin:` lines; every public declaration in them
is a pin statement, so the checker diffs the whole surface). **No engine/façade split**: a façade
exists only when a module's public surface is the port's own rather than the pin's.

**(a) `FLTForHuman/LinearAlgebra/Dual/EvalSpan.lean`** — the shared prelude, 1 public declaration:

```lean
variable {G : Type*}

theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l)
```

namespace `Submodule`, pin name kept, body transcribed from either pin file (byte-identical). Keep the
**`variable {G : Type*}` line**: the checker's statement diff is textual, and inlining the binder
changes the hash.

```lean
spec-pin: P2M/Sol/S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
spec-pin: P2M/Sol/S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
```

**(b) `FLTForHuman/Analysis/MatrixGroup/UnitaryRightFinite.lean`** — the `U(2)` development,
namespace **`Matrix.UnitaryGroup`** (the pin's `P2MW.S_….M4aP3C.SU2Finite` is pin bookkeeping; the
pin's short names are what the statement diff sees, so `abbrev U2`, `polyFun`, `qker`, `Pdeg`, … keep
their names and their written binders). 49 public declarations = the 48 silo declarations of the pin
plus the headline at the wrapper's name; 1 `private aux_ratio`.

```lean
spec-pin: Theorems/Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
spec-pin: P2M/Sol/S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
```

**Wrapper first** — a listed `S_` file shadows its own `Theorems/` wrapper for last-name matching
otherwise (column note §9).

The headline is the pin's silo theorem at the pin's silo name, plus the wrapper's statement:

```lean
theorem exists_polyFun_eq_of_continuous_of_rightFinite
    (Φ : U2) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (U2 → ℂ), ∀ k : U2, (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (U2 → ℂ))) :
    ∃ F ∈ polyFun, ∀ k : U2, Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) := …   -- the whole proof

theorem Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  exists_polyFun_eq_of_continuous_of_rightFinite Φ hc hfin
```

— the second takes its statement verbatim from
`Theorems/Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean:5–13`; that
text, not the `S_` file's, is what the checker diffs.

**(c) `FLTForHuman/Analysis/MatrixGroup/OrthogonalRightFinite.lean`** — the `O(2)` twin, namespace
**`Matrix.OrthogonalGroup`**, 46 public declarations + 1 `private aux_ratio`, same two `spec-pin:`
lines with `Orthogonal` for `Unitary`. Write it **from the `U(2)` module**, not from scratch: the
37 hunks of the base-field diff are the whole job (§5 step 3).

## 4. Route, and what must *not* be invented

* **There is no definition gate.** Both pin `S_` files import mathlib + `P2M.Util` (the pin's
  `p2m_*` tactic macros) and nothing else. No `Definitions/Def_*.lean` is reached.
* **The imports are targeted, not `import Mathlib`.** The pin's own `import Mathlib` line is not
  copied. Needed API (all in `v4.34.0`, source module in brackets):
  `Matrix.unitaryGroup`/`mem_unitaryGroup_iff`/`orthogonalGroup` [`Mathlib.LinearAlgebra.UnitaryGroup`],
  `Matrix.entry_norm_bound_of_unitary` [`Mathlib.Analysis.CStarAlgebra.Matrix`],
  `isClosed_unitary` [`Mathlib.Topology.Algebra.Star.Unitary`],
  `Matrix.normedAddCommGroup`/`normedSpace` [`Mathlib.Analysis.Matrix.Normed`],
  `Matrix.trace`/`trace_fin_two`/`eta_fin_two`/`one_fin_two`, `FiniteDimensional.proper`,
  `Submodule.closed_of_finiteDimensional`, `Submodule.finiteDimensional_of_le`
  [`Mathlib.Topology.Algebra.Module.FiniteDimension`],
  `Metric.isCompact_of_isClosed_isBounded` [`Mathlib.Topology.MetricSpace.Bounded`],
  `Measure.haarMeasure`/`haarMeasure_self`/`isHaarMeasure_haarMeasure`
  [`Mathlib.MeasureTheory.Measure.Haar.Basic`], `integral_mul_left_eq_self`
  [`Mathlib.MeasureTheory.Group.Integral`], `integral_ofReal`,
  `Subspace.dualCoannihilator_dualAnnihilator_eq` [`Mathlib.LinearAlgebra.Dual.Lemmas`],
  `borel`. Add what is missing; never widen to `Mathlib`.
* **The four-line `integrable_of_continuous` stays local.** The port's
  `Q09.integrable_of_continuous` (`RepTheory/TypeReproducer.lean`, tier 3) is the same lemma up to
  binder spelling, but importing it would make an `Analysis/` module depend on a `RepTheory` engine
  for four lines and invert the import graph (playbook §2.4). Recorded negative.
* **`solution` is not ported** (either file): it is the pin's `S_`-level wrapper, and the port's
  headline is the same statement at the `Theorems/` name. Do **not** carry two copies.
* **`p2m_reactivate` / `p2m_export` lines are dropped**, and `p2m_exact_reverting` never appears.
* **`scoped` is kept exactly where the pin has it**, including `scoped instance : CompactSpace U2`,
  `… MeasurableSpace`, `… BorelSpace`, `… MeasurableMul`, `… Measure.IsHaarMeasure haarU2`,
  `… IsProbabilityMeasure haarU2` and `scoped instance finite_expIndex`. The anonymous instances stay
  anonymous (the checker flags them `anon` on both sides).
* **`private aux_ratio` stays `private`** in each module, as at the pin; it needs no marker (the
  checker only requires public declarations to be accounted for).
* **No `-- pin:`/`-- own:` markers and no `spec/decl_markers.tsv` entry**: both modules are listed
  and every public declaration is the pin's own statement, so the name/hash tiers match.

## 5. The route

1. **Scout baseline is already established — do not re-derive it.** The pin's two files, minus
   `import P2M.Util`/`p2m_*`/`#print axioms solution`, compile **verbatim** on `v4.34.0`:
   a git-ignored scratch copy of each `S_` file under `lean/tmp/` (pin text minus `import P2M.Util`,
   the `p2m_reactivate` lines and the `solution` wrapper), both exit 0 under
   `-DautoImplicit=false -DmaxHeartbeats=200000`, axioms `[propext, Classical.choice, Quot.sound]`,
   **no proof drift**, 8 warnings each. Use the two scouts as the transcription source (they are the
   pin text with the pin's bookkeeping lines already removed) and keep them for the diff.
2. **Module (a)**, then the `U(2)` module (b): transcribe the scout body, replace the namespace, the
   imports and the docstring, and append the two declarations of §3(b)'s headline pair (`solution`
   dropped). Build, then `check_port.py --force`.
3. **Module (c)** is the `U(2)` module copied and adapted. Every hunk is mechanical and comes from
   the pin's own `O(2)` file:
   * `ℂ → ℝ` in the matrix type; `trace` is real, so `(Matrix.trace …).re` becomes `Matrix.trace …`
     and `Complex.add_re`/`Complex.continuous_re` disappear (`continuous_qker`, `qker`, `qker_nonneg`,
     `qker_le_one`, `qker_eq_one_iff`, `aker`, `continuous_aker`, `akerC_mem_Pdeg_one`);
   * the entry bounds are `entry_abs_le` (`|x| ≤ 1`, via `Real.norm_eq_abs`) and `entry_le`, not
     `entry_re_le`/`entry_abs_re_le`; `Complex.normSq` and its zero lemma become `mul_self_eq_zero`;
     the unitary relation is `star_trivial`;
   * `integral_translate_real` does not exist in the `O(2)` file;
   * `conjEntryCLM`(+`_apply`) does not exist; `entryCLM` composes `Complex.ofRealCLM`, so
     `entryCLM_apply` reads `entryCLM i j m = ((m i j : ℝ) : ℂ)`; `coordFns` is `Fin 4` and every
     `Fin 8` becomes `Fin 4` (`monom`, `Pdeg`, `finite_expIndex`, `pow_mem_Pdeg`, `Pdeg_mul_mem`,
     `coordFn_mem_Pdeg_one`);
   * `aker`'s real-linearity step is the `O(2)` file's own (`8`-fold sum with `(1/2 : ℂ)` and no
     conjugate half), `restrictO2` replaces `restrictU2`.
   Do not "improve" the `ℝ` proof into the `ℂ` shape: the checker diffs each file against its own
   `S_` source, and the two statements are different (different base ring).
4. **Clear the warnings** — the tier-1 build must be 0-warning. Both scouts print exactly 8:
   * 7 × `linter.style.haveILetI`: the three `letI`/`haveI` of `isCompact_unitaryGroup`/
     `isCompact_orthogonalGroup` (`NormedAddCommGroup`, `NormedSpace`, `ProperSpace`) and the four
     `haveI : FiniteDimensional ℂ (…)` (`fejerConv_mem_span`, `exists_polyFun_fejerConv` ×2,
     `exists_polyFun_eq_of_continuous_of_rightFinite`). Take Lean's own suggestion (`letI → let`,
     `haveI → have`) **if it compiles**; the instances are globally reachable for a `Matrix` (the Pi
     norm instances are found up to defeq), which is why the linter fires. Where a suggestion does
     not compile, suppress **narrowly** on that declaration
     (`set_option linter.style.haveILetI false in`) — never file-wide — and report which.
   * 1 × `Set.mem_setOf_eq` deprecation (U2 306 / O2 280): `simp only [hVdef, Set.mem_setOf_eq,
     qker_one]` → `Set.mem_ofPred_eq`.
5. **Verify and report** (§7).

## 6. Successors this landing unblocks

`frontier.py --ds --include-leaves` loses the two leaves (1,362 → 1,360 nodes, −1,550 raw `S_`
lines) and moves:

| consumer | silo lines | needed before | after |
|---|---:|---:|---:|
| `AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary` | 3,747 | 13 | 11 |
| `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` | 5,407 | 3 | 2 |

Outside the cone: the `bigCell_eq_sum_pureTensor_of_flat_family_of_{restrict_eq,type_parity}` twins
and `AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex`.

## 7. Verification (record the numbers on the tree you leave)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/LinearAlgebra/Dual/EvalSpan.lean       # expect 1 ok
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/UnitaryRightFinite.lean   # 49 ok
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/OrthogonalRightFinite.lean # 46 ok
python3 spec/check_port.py --changed          # then --all: expect 1942 + 96 = 2038 ok, 0 mismatch, 0 missing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.Analysis.MatrixGroup.UnitaryRightFinite
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.Analysis.MatrixGroup.OrthogonalRightFinite
```

plus `#print axioms` on the two headlines (`[propext, Classical.choice, Quot.sound]`), a `rg` sweep
of the three modules for `sorry|admit|^axiom|native_decide|import Mathlib|maxHeartbeats`, `git status`
showing only the three new files, and **0 warnings** from both module builds.

## 8. Report shape

Per module: lines, public/private count, checker verdict, build jobs/time, axioms. Then: the warning
cleanup (how many `have`/`let` suggestions taken verbatim, how many narrow suppressions and why), any
API drift found beyond §5.1 (expected none), the diff between the two group modules (line count and
hunk count) as the twin's measured cost, and the two `check_port.py --all` totals (before/after).
Stop-and-report items of §9 separately.

## 9. Hub prohibition and stop conditions

No subagent edits an existing module, appends to `spec/old_check_stmts.py`, or touches
`spec/decl_markers.tsv`. If you believe a promotion, a host edit, a marker entry or a
`set_option` beyond the narrow linter suppression of §5.4 is genuinely required, **stop and report**
with the declaration, the host and (for an edit) `build_ladder.py --edit` price. The manager decides.
Stop and report if a pin statement cannot be reproduced verbatim (a `MISMATCH` you cannot fix by
spelling the binder as the pin wrote it), or if a proof step needs more than the column's 200,000
heartbeat cap.
