# The matrix-group right-finite supplement — polynomial approximation on U(2) and O(2)

This is the topic record for the landing of the two pin leaves

* `Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite` (802 pin lines)
* `Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite` (748)

— the D-S leaf shelf's ranks #2 and #5 of 442 (`--ds --include-leaves`) — as one
mathlib supplement in three modules. The order is
[WORKORDER-MG1-right-finite-supplement.md](WORKORDER-MG1-right-finite-supplement.md);
the landing record is [logs/matrixgroup-rightfinite.md](../../logs/matrixgroup-rightfinite.md).

**Status: landed 2026-10-20.** Three modules (68 / 816 / 760 lines), **96 statement-checked
declarations** (1 + 49 + 46), checker **1942 → 2038 ok**, 0 mismatched / 0 missing over 56 modules;
tier-1 builds 2,051 / 2,639 / 2,639 jobs, **0 warnings**; axioms
`[propext, Classical.choice, Quot.sound]`; zero host edits, nothing registered. The scout's
no-drift prediction (§5) held exactly: the set's diff against the pin is the eight warning fixes
plus the two prelude-reference renames.

## 1. The subject

> If `Φ` is continuous on `U(2)` and its right translates span a finite-dimensional
> space, then on `U(2)` it agrees with a polynomial in the real coordinates of the matrix
> entries.

and the same with `O(2)` over `ℝ`. Here "polynomial" is the pin's explicit set: the
`ℂ`-span of products of *real*-linear functionals on the ambient matrix space
`Matrix (Fin 2) (Fin 2) 𝕜`, i.e. the symmetric algebra on the real dual. The statements
name only mathlib objects.

The proof is a Fejér-kernel argument, and it is self-contained:

1. `qker k = (2 + tr k)/4` is a positive approximate identity on the group —
   `qker_nonneg`, `qker_le_one`, `qker_one`, and `qker_eq_one_iff` (`qker k = 1 ↔ k = 1`),
   which with compactness gives `exists_lt_one_bound`: off any neighbourhood of `1` the
   kernel is bounded by some `δ < 1`;
2. the normalized convolutions `fejerConv n Φ k = Z_n⁻¹ ∫ h, Φ (k h) qker h ^ n`
   converge to `Φ` (`fejerConv_tendsto`, the estimate `fejerConv_sub` + `aux_ratio`);
3. each `fejerConv n Φ` lies in the right-translate span (`fejerConv_mem_span`, via the
   finite basis and the evaluation-combination lemma of §4) **and** is the restriction of
   a polynomial of degree `n`: `aker h M = qker (M * h)` is affine in the entries and their
   conjugates (`akerC_mem_Pdeg_one`), its `n`-th power lies in `Pdeg n` (`pow_mem_Pdeg`),
   and expanding in a basis of `Pdeg n` gives `exists_polyFun_fejerConv`;
4. `V ⊓ R` (right-translate span meet restricted polynomials) is finite-dimensional hence
   closed, so the limit `Φ` lies in it (`exists_polyFun_eq_of_continuous_of_rightFinite`
   for `Submodule.closed_of_finiteDimensional.mem_of_tendsto`).

## 2. The pair is one theorem, and the pin writes it twice

mathlib defines `abbrev orthogonalGroup n R := unitaryGroup n R`, so for `𝕜 = ℝ` the two
statements are the *same* statement with the base field substituted: both conclude about
`∃ F ∈ Submodule.span ℂ {F : Matrix (Fin 2) (Fin 2) 𝕜 → ℂ | ∃ l : List (Matrix (Fin 2) (Fin 2) 𝕜 →L[ℝ] ℂ), …}`.
The pin proves it twice because the `ℝ` proof text simplifies (no conjugation, `Fin 4`
coordinates instead of `Fin 8`, `trace` real rather than `.re`). Measured at the base
field, the pair is **≈80 % shared: 170 changed lines in 37 hunks**, every hunk a `ℝ`/`ℂ`
adaptation:

| | U(2) | O(2) |
|---|---:|---:|
| pin lines | 802 | 748 |
| named declarations | 51 | 48 |
| of which `private` | 1 (`aux_ratio`) | 1 (`aux_ratio`) |
| of which the shared prelude | 1 (`exists_eval_combination`, 32/31 lines) | 1 (same, byte-identical) |

`port_advise` reads the shared blocks as 8 declarations / 89 removable lines — an
under-count, because the tool compares statements and the remaining 60-odd declarations
differ in the *base field*, not in the mathematics. That is the same situation as the
`tateCurve` twins, one level down: not an exact twin, a transcription difference.

## 3. Why it is a mathlib supplement, and where it is homed

Both pin `S_` files import **mathlib plus `P2M.Util` only** (`P2M.Util` is the pin's
`p2m_*` tactic macros), so there is **no definition gate**: no `Definitions/Def_*.lean`
is reached and nothing has to be homed before the statements can be written. That is
unusual for this column and it is what makes the pair a single set.

mathlib `v4.34.0` supplies the analytic ingredients (`isClosed_unitary`, the
`[RCLike 𝕜]`-generic `Matrix.entry_norm_bound_of_unitary`, `Measure.haarMeasure`,
`integral_mul_left_eq_self`, `Submodule.closed_of_finiteDimensional`,
`Subspace.dualCoannihilator_dualAnnihilator_eq`), but it has **no compactness of
`U(2)`/`O(2)`, no Haar instance on it, and no right-finite ⟹ polynomial statement**.
Hence the home mirrors mathlib rather than the pin's consumers:

| module | role |
|---|---|
| `FLTForHuman/LinearAlgebra/Dual/EvalSpan.lean` | the shared prelude: every functional on a finite-dimensional space of functions is a finite combination of evaluations |
| `FLTForHuman/Analysis/MatrixGroup/UnitaryRightFinite.lean` | the `U(2)` development (`namespace Matrix.UnitaryGroup`) |
| `FLTForHuman/Analysis/MatrixGroup/OrthogonalRightFinite.lean` | the `O(2)` twin (`namespace Matrix.OrthogonalGroup`) |

All three are **listed** — they carry `spec-pin:` headers and every public declaration in
them is a pin statement, so the checker diffs the whole surface (expected **+96**: 1 + 49
+ 46). There is no engine/façade split: a façade exists only when a module's public
surface is *ours* rather than the pin's, and here it is the pin's.

## 4. The one dedup

`M4aP3C.TensorSplit.exists_eval_combination` is written byte-identically in both files:

```lean
theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l)
```

— every functional on a finite-dimensional space of functions is a finite combination of
point evaluations. It has no matrix or analytic content, so it is homed once at
`LinearAlgebra/Dual/EvalSpan.lean` (namespace `Submodule`, pin name kept) and imported by
both group modules. mathlib has the ingredient
(`Submodule.dualCoannihilator_dualAnnihilator_eq`) but not the statement: a recorded
negative from a search of `Mathlib/LinearAlgebra/Dual/`.

Nothing else is shared: the two group developments are transcribed as the pin wrote them.
In particular the port does **not** re-prove the four-line `integrable_of_continuous`
from the port's `Q09.integrable_of_continuous` (`RepTheory/TypeReproducer.lean`): sharing
it would make an `Analysis/` module import a `RepTheory` engine for four lines and invert
the import graph (playbook §2.4).

## 5. The scout: zero drift

The pin is `v4.33.1`/mathlib `db584cd6`, the port `v4.34.0`. The pair was checked before
dispatching by compiling the pin's text unchanged: a git-ignored scratch copy of each `S_` file
under `lean/tmp/`, with `import P2M.Util`, the `p2m_reactivate` lines, `#print axioms solution`
and `solution` itself removed and nothing else touched, under the column's own cap:

```
timeout 900 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 lean/tmp/Scout.lean
```

Both files exit **0** with `#print axioms` = `[propext, Classical.choice, Quot.sound]` and
**no proof drift at all** — the pin's terms elaborate as written (`FiniteDimensional.proper`,
`Matrix.normedAddCommGroup`/`normedSpace`, `Complex.normSq`, `Complex.ofRealCLM`,
`Set.mem_setOf_eq` all still resolve). Each file produces exactly 8 warnings, all
mechanical: 7 `linter.style.haveILetI` suggestions and 1 deprecation
(`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`). The port's tier-1 build must be warning-free,
so the order carries the cleanup as an explicit step.

## 6. Where it sits, and what it buys

`frontier.py --ds --include-leaves --rank-by silo` lists the pair at 802 and 748 silo
lines with `needed 1`: both are graph leaves of the demand, `used_by` 2/5 and 1/1
(cone/project). Landing them removes **2 nodes / 1,550 raw `S_` lines** from the demand
(1,362 → 1,360 nodes) and moves their cone consumers up:

| consumer | silo lines | needed before | after |
|---|---:|---:|---:|
| `AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary` | 3,747 | 13 | 11 |
| `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` | 5,407 | 3 | 2 |

Three further citers are outside the D-S cone and become cheaper without being scheduled:
the `bigCell_eq_sum_pureTensor_of_flat_family_of_{restrict_eq,type_parity}` twins and
`AutomorphicForm.exists_mvPolynomial_apply_eq_mul_bottomRow_of_rightTranslatesSpanFinite_of_isComplex`
(the `mvPolynomial` successor of the same idea).

## 7. Routes considered and declined

* **One generic `[RCLike 𝕜]` engine + a two-headline façade.** Attractive: after the
  base-field normalization the two statements *are* one sentence, `Matrix.orthogonalGroup`
  is mathlib's `abbrev` for `unitaryGroup`, and every `RCLike` lemma the `ℂ` branch uses
  exists (`RCLike.add_conj`, `normSq_apply`, `ext_iff`, `mul_conj`, `abs_re_le_norm`,
  `normSq_eq_zero`). It would halve the writing (≈810 lines instead of 1,434) and leave
  ≈45 declarations in the tier-3 register with `own` statements. Declined by the manager:
  it is a *strengthening* of the pin's two statements, its risk is concentrated in the
  generic `qker_eq_one_iff` and the `algebraMap 𝕜 ℂ`-valued coordinate set, and it would
  leave 94 pin statements undiffed where the faithful route verifies all 96. Recorded so
  a later column can take it up as a deliberate rewrite if it wants the general statement.
* **Generalizing `n` as well** (`U(n)`/`O(n)`, `2n²` coordinates): the true mathlib
  strength, but a redesign of the coordinate machinery (`Fin 8` → `Fin (2 * n * n)`), and
  the pin's own statements would no longer be reproduced. Declined for the same reason.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/LinearAlgebra/Dual/EvalSpan.lean
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/UnitaryRightFinite.lean
python3 spec/check_port.py --force FLTForHuman/Analysis/MatrixGroup/OrthogonalRightFinite.lean
python3 spec/check_port.py --changed
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.Analysis.MatrixGroup.UnitaryRightFinite
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.Analysis.MatrixGroup.OrthogonalRightFinite
```

plus `#print axioms` on the two headlines and the `sorry`/`axiom`/`native_decide`/
`import Mathlib`/heartbeat-override sweep.

## 9. Residuals

* The two group modules are 80 % parallel by construction. That is the pin's text, kept
  deliberately (§7); a future generic rewrite is a *revision* and must be priced as one.
* The `ℂ`-side entry functionals are the `Fin 8` set (entries and conjugates); the `ℝ`-side
  ones are `Fin 4`. The pin's choice, not a port artifact — the two `Pdeg` definitions are
  therefore different submodules, and the statements stay per-file.
* `Auxiliary`: both files carry `private aux_ratio` (5 lines). Left `private`, as at the pin.
