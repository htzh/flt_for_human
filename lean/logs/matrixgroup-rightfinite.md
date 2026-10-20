# The matrix-group right-finite supplement — `U(2)`/`O(2)`, landed

**Status: landed 2026-10-20.** One set, **three modules, zero host edits, nothing registered** (all
three are listed and fully diffed). Checker **1942 → 2038 ok** (+96), 0 mismatched / 0 missing over
56 modules; tier-1 builds 2,051 / 2,639 / 2,639 jobs at 2.8 / 6.2 / 5.9 s, **0 warnings**; axioms
`[propext, Classical.choice, Quot.sound]`. Topic:
[topics/deligneSerre/TOPIC-matrixgroup-rightfinite.md](../topics/deligneSerre/TOPIC-matrixgroup-rightfinite.md);
order: [topics/deligneSerre/WORKORDER-MG1-right-finite-supplement.md](../topics/deligneSerre/WORKORDER-MG1-right-finite-supplement.md).

| module | lines | public | private | checker | build |
|---|---:|---:|---:|---|---|
| `LinearAlgebra/Dual/EvalSpan.lean` | 68 | 1 | 0 | 1 ok | 2,051 jobs, 2.8 s |
| `Analysis/MatrixGroup/UnitaryRightFinite.lean` | 816 | 49 (+7 anon) | 1 | 49 ok | 2,639 jobs, 6.2 s |
| `Analysis/MatrixGroup/OrthogonalRightFinite.lean` | 760 | 46 (+7 anon) | 1 | 46 ok | 2,639 jobs, 5.9 s |

The two pin leaves are the D-S leaf shelf's ranks #2 and #5 of 442 (802 + 748 pin lines). The
landing removes **2 nodes / 1,550 raw `S_` lines** from the demand (1,362 → 1,360) and moves its two
cone consumers: `AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`
needs 13 → 11, `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` 3 → 2.

## 1. What was landed, and why it is a supplement

The theorem — a continuous `Φ` on `U(2)` whose right translates span a finite-dimensional space
agrees on the group with a polynomial in the real coordinates of the entries — is a Fejér-kernel
argument over a compact matrix group. It names only mathlib objects (`Matrix.unitaryGroup`,
`Matrix.orthogonalGroup`, `→L[ℝ] ℂ`, `Submodule.span`), its two pin files import mathlib plus
`P2M.Util` (the pin's `p2m_*` macros) and **nothing else**, and mathlib `v4.34.0` has neither the
compactness of `U(2)`/`O(2)` nor a Haar instance on it nor any right-finite ⟹ polynomial statement.
So it is homed as a mathlib supplement at the paths mathlib would use, not under the pin's
consumers.

The pair is one development written twice by the pin: at the base field the two files are ≈80 %
identical (170 changed lines, 37 hunks), because `Matrix.orthogonalGroup n R` *is* mathlib's
`abbrev` for `unitaryGroup n R` and the `ℝ` proof text is the `ℂ` one without conjugation. It was
ported faithfully anyway — **not** strengthened to a generic `[RCLike 𝕜]` or general-`n` statement —
so that all 96 pin statements are diffed rather than 2. The declined routes are recorded in the
topic §7 with the reason each was declined.

## 2. The one dedup

`M4aP3C.TensorSplit.exists_eval_combination` is byte-identical in both pin files (every functional
on a finite-dimensional space of functions is a finite combination of evaluations). It is homed once
at `LinearAlgebra/Dual/EvalSpan.lean` (namespace `Submodule`, pin name and the pin's
`variable {G : Type*}` line kept — the checker's diff is textual), and both group modules import it.
mathlib has the ingredient (`Subspace.dualCoannihilator_dualAnnihilator_eq`) but not the statement.

The four-line `integrable_of_continuous` was **not** imported from
`RepTheory/TypeReproducer.lean`'s `Q09.integrable_of_continuous`: sharing it would make an
`Analysis/` module depend on a `RepTheory` engine for four lines and invert the import graph
(playbook §2.4). Recorded negative.

## 3. The scout made the set risk-free

Before dispatching, the pin's two files were compiled unchanged against `v4.34.0`
(a git-ignored scratch copy of each pin `S_` file under `lean/tmp/`, with `import P2M.Util`, the
`p2m_reactivate` lines and the `solution` wrapper removed and nothing else touched), under the
column's cap:

```
timeout 900 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 lean/tmp/Scout.lean
```

Both exited **0** with `[propext, Classical.choice, Quot.sound]` and **no proof drift**: the pin's
terms elaborate as written in `v4.34.0` (`FiniteDimensional.proper`,
`Matrix.normedAddCommGroup`/`normedSpace`, `Complex.normSq`, `Complex.ofRealCLM` all still resolve).
Each file produced exactly 8 warnings, all mechanical.

Because the scout had isolated the proof text, the set's actual diff against the pin is exactly the
eight warning fixes plus two prelude-reference renames
(`M4aP3C.TensorSplit.exists_eval_combination → Submodule.exists_eval_combination`); body line counts
are identical to the scouts (717 / 666). No statement drift, no proof drift.

## 4. The warning cleanup

**7/7 `have`/`let` suggestions taken verbatim, 0 suppressions** — no
`set_option linter.style.haveILetI` in any of the three modules; the only `set_option` is
`autoImplicit false`.

* `isCompact_unitaryGroup` / `isCompact_orthogonalGroup`: `letI NormedAddCommGroup → let`,
  `letI NormedSpace → let`, `haveI ProperSpace → have` (U2:82–84, O2:77–79). These compiled because
  the Pi norm instances are reachable up to defeq for `Matrix`, which is why the linter fired.
* `fejerConv_mem_span` (U2:445, O2:417), `exists_polyFun_fejerConv` (U2:710, O2:654),
  `exists_polyFun_eq_of_continuous_of_rightFinite` (U2:781, 790; O2:725, 734):
  `haveI FiniteDimensional → have`.
* one deprecation: `Set.mem_setOf_eq → Set.mem_ofPred_eq` (U2:322, O2:294).

## 5. The twin's measured cost

`diff -u UnitaryRightFinite.lean OrthogonalRightFinite.lean`: 986 diff-output lines, 20 hunks,
309 −/257 + whole-file (the prose headers merge hunks); **body-only from `abbrev U2`/`O2`: 898 diff
lines in 33 hunks**. Every hunk is a base-field adaptation (`.re`, `Complex.normSq`, `starRingEnd`,
`Fin 8` vs `Fin 4` coordinates, `Complex.ofRealCLM` in `entryCLM`, the ℂ-only `conjEntryCLM`), and
no `ℝ` proof was re-shaped into the `ℂ` one. That duplication is the pin's, kept deliberately; a
generic rewrite would be a revision.

## 6. Verification, as the manager re-ran it

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/LinearAlgebra/Dual/EvalSpan.lean
#   1 ok, 0 mismatch, 0 missing, 0 own, 0 kw        (matched S_…:16)
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/UnitaryRightFinite.lean
#   49 ok …   (headline matched Theorems/Thm_…:7 — the wrapper's text)
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/OrthogonalRightFinite.lean
#   46 ok …   (headline matched Theorems/Thm_…:5)
python3 spec/check_port.py --all
#   2038 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 56 module(s)
```

plus `#print axioms` on the two headlines, the two silo headlines and the prelude
(`[propext, Classical.choice, Quot.sound]`), an `rg` sweep of the three modules (no `sorry`/`admit`/
`axiom`/`native_decide`, no bare `import Mathlib`, no heartbeat override, no linter suppression),
and `git status` showing only the three new modules.

## 7. Friction recorded

* `integral_ofReal` is not reachable from `Mathlib.MeasureTheory.Integral.Bochner.{Basic,Set}`; it
  lives in `…Bochner.ContinuousLinearMap`. Targeted import added (first-round error U2:271/O2:243).
* `ℂ` notation alone needs `Mathlib.Analysis.Complex.Basic` in the prelude module.
* The order's API map mis-homed `FiniteDimensional.proper`: in `v4.34.0` it is in
  `Mathlib.Analysis.Normed.Module.FiniteDimension`, while `Submodule.closed_of_finiteDimensional`
  stays in `Mathlib.Topology.Algebra.Module.FiniteDimension`. Both imported, no impact.
* `Mathlib.LinearAlgebra.Dual.Lemmas` was trimmed from both group modules (only the prelude needs
  it; it arrives transitively).

## 8. Residuals

* The two group modules remain 80 % parallel (above). The generic `[RCLike 𝕜]` statement — which
  after normalization is *one* sentence, since `orthogonalGroup` is `unitaryGroup` — is the natural
  revision when a later column wants the general form; it would leave ≈45 declarations in the
  tier-3 register and was declined here for risk and coverage (topic §7).
* `Matrix.orthogonalGroup`'s `ℝ`-side `Pdeg` uses `Fin 4` coordinates and the `ℂ`-side `Fin 8`;
  the two `Pdeg` submodules differ by design, not by port artifact.
* The supplement's consumers are still unported; the next cut of the family is priced in
  [topics/deligneSerre/TOPIC-matrix-family-in-cone.md](../topics/deligneSerre/TOPIC-matrix-family-in-cone.md).
