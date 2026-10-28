# WORKORDER WR1 — the Weil reciprocity theorem on ℙ¹ and the Weil pairing's laws

Scope: **one insertion** into `FLTForHuman/AlgebraicCurve/P1/Dictionary.lean`, **one insertion** into
`FLTForHuman/AlgebraicCurve/Defs/WeilDatum.lean`, and **one new module**
`FLTForHuman/AlgebraicCurve/Pic0/WeilPairing.lean`. Nothing else may be edited (no hub, no spec/,
no `spec/decl_markers.tsv`). Part of SET 6, [SET-6.md](SET-6.md) §1 (WR) and §5.

## Nodes

| node | pin stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.RationalFunctionField.weilReciprocity` | `S_AlgebraicCurve_RationalFunctionField_weilReciprocity` | 1,273 | append to `P1/Dictionary.lean` |
| `AlgebraicCurve.WeilDatum.addLeft_pairing` | `S_AlgebraicCurve_WeilDatum_addLeft_pairing` | 80 | append to `Defs/WeilDatum.lean` |
| `AlgebraicCurve.WeilDatum.pairing_ne_zero` | `S_AlgebraicCurve_WeilDatum_pairing_ne_zero` | 65 | append to `Defs/WeilDatum.lean` |
| `AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub` | `S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub` | 439 | **new** `Pic0/WeilPairing.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. Read every `S_` file **and** its
`Theorems/` wrapper (the statement is the wrapper's, the proof the `S_` file's):
`P2M/Sol/S_AlgebraicCurve_<stem>.lean`, `Theorems/Thm_AlgebraicCurve_<stem>.lean`, e.g.
<https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean>.

## What the ground prep already gives you (do not rewrite it)

- `P1/Dictionary.lean` was migrated by the manager: it now carries a 26-line `spec-pin:` wire and
  checks **69 ok / 0 mismatch / 0 missing**. The `weilReciprocity` row is the **last declaration of
  the pin's own duplicated file**: the pin ships the same 1,260-line dictionary twice
  (`S_…_weilReciprocity.lean` 1,273 ln and `S_…_ord_placeOfPoint_algebraMap.lean` 1,263 ln, one
  `p2m_export` line and the tail different), and the port transcribed the second one here. So the
  row is **one theorem**; every other declaration of its `S_` file is already in this module, in
  `PrincipalDivisors/RatFuncDegree.lean`, or private here. Do not re-transcribe any of them.
- `Defs/WeilDatum.lean` carries the **support block** the two small laws need, publicly, at the
  pin's `Def_`-file names: `ord_f₁_eq_zero_of_mem_support`, `ord_f₂_eq_zero_of_mem_support`,
  `rational_of_mem_support_left`, `rational_of_mem_support_right`, `evalAt_f₁_ne_zero`,
  `evalAt_f₂_ne_zero`, `evalFun_f₁_ne_zero`, `evalFun_f₂_ne_zero` (plus `symm_pairing`). The
  `'`-suffixed copies in the two `S_` files and the `_i`-suffixed copies in
  `pairing_eq_of_isPrincipal_sub` are the **same statements**: import and use the block, do not
  restate any of them.
- `Defs/PlaceEvaluationAlgebra.lean` has `evalFun_mul`, `evalFun_add`, `evalFun_zsmul`,
  `evalFun_zpow_left`, `evalFun_ne_zero`; `Defs/PushPull.lean` has `mem_of_ord_nonneg`,
  `Place.ord_nonneg_of_mem`; `Defs/PlaceEvaluation.lean` has `Place.evalAt_algebraMap`,
  `evalAt_ne_zero`, `isRational_iff_deg_eq_one`; `Pic0/Torsion.lean` has
  `Pic0.torsion.exists_forall_ord_eq_mul`. Import them; `Pic0/Torsion.lean` is **not** edited by
  this order.

## What to write

### 1. `P1/Dictionary.lean` — `weilReciprocity`

Append, inside the module's `AlgebraicCurve.RationalFunctionField` namespace, the wrapper's exact
statement:

```
theorem AlgebraicCurve.RationalFunctionField.weilReciprocity (K : Type*) [Field K] [IsAlgClosed K] :
    WeilReciprocity K (RatFunc K)
```

`WeilReciprocity` is the `def … : Prop` in `Defs/PlaceEvaluation.lean` (already imported). The
proof is the `S_` file's `solution` (lines 1262–1273, 9 lines): `Finsupp.ext` the two divisor
hypotheses into `principalDivisor`, then the two cases of `hdisj (placeInfty K)` through
`reciprocity_of_ord_placeInfty_eq_zero … Finset.card_erase_le`. Drop the pin's enormous `open` line
and its `p2m_` scaffolding. The wire already lists this row's wrapper and `S_` file, so
`check_port` should go from 69 to **70 ok**.

### 2. `Defs/WeilDatum.lean` — the two small laws

Append, in `namespace AlgebraicCurve.WeilDatum`, the wrappers' statements verbatim:

```
theorem addLeft_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing

theorem pairing_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (d : WeilDatum K F n) : d.pairing ≠ 0
```

Their proofs are the `S_` files' `solution` bodies (16 and 2 lines) with the `'`-suffixed prelude
replaced by the support block: `addLeft_pairing` unfolds `pairing`, uses `evalFun_mul` on `D₂`
and `evalFun_add` on `D₁ + D₂` and the block's `evalAt_…_ne_zero`; `pairing_ne_zero` is
`div_ne_zero d.evalFun_f₁_ne_zero d.evalFun_f₂_ne_zero`. Add the two `S_` files' and two wrappers'
`spec-pin:` lines to this module's wire (after the `Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`
line the manager added), and **no imports** — the manager added `Defs.PlaceEvaluationAlgebra`
already; `Defs.PushPull` comes through `Defs.PlaceEvaluation`.

### 3. `Pic0/WeilPairing.lean` — the pairing is a class invariant

New module, header `/- … -/` with prose and the two `spec-pin:` lines (wrapper + `S_` file), then:

```
import FLTForHuman.AlgebraicCurve.Defs.WeilDatum
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Pic0.Torsion
```
(adjust only if a name genuinely needs more; never `import Mathlib`).

Transcribe the `S_` file's declarations in its order, at the pin's names (keep the `_i` suffixes —
they are the pin's own names and the checker matches by statement anyway), **minus** the four
`_i`-suffixed support copies it repeats (`ord_f₁_…_i`, `ord_f₂_…_i`, `rational_of_mem_support_left_i`,
`rational_of_mem_support_right_i`), which are the manager's block. So:

- private: `support_zsmul_subset_i` 7, `isPrincipal_neg_i` 6, `isPrincipal_add_i` 7,
  `isPrincipal_sub_of_mk_eq_i` 14, `evalFun_algebraMap_of_degree_eq_zero_i` 24,
  `isPrincipal_smul_left_i` 5, `isPrincipal_smul_right_i` 5, `degree_eq_zero_of_isPrincipal_i` 7,
  `degree_D₁_eq_zero_i` 7, `degree_D₂_eq_zero_i` 9, `degZeroLeft_i` 5, `degZeroRight_i` 4,
  `evalAt_f₂_ne_zero_i` 7;
- public: `coe_degZeroLeft_i` 3, `coe_degZeroRight_i` 4, `mk_mem_torsion_i` 18, `classLeft_i` 4,
  `classRight_i` 6, `evalAt_f₁_ne_zero_i` 5, `pairing_eq_of_addPrincipalLeft_i` 67,
  `pairing_eq_of_isPrincipal_sub_left_i` 55, `pairing_eq_of_isPrincipal_sub_right_i` 23, and the
  headline `solution` 88 — stated as the wrapper's
  `WeilDatum.pairing_eq_of_isPrincipal_sub` (drop the `solution` name, use the node name).

The statement is the wrapper's, exactly (it takes `hrec : WeilReciprocity K F`, `hconst` and
`hmove` as hypotheses; `WeilReciprocity` is imported from `Defs/PlaceEvaluation`).

## Rules

- Statements are the `Theorems/` wrappers', character for character; proofs are the `S_` files',
  adapted to mathlib `v4.34.0` and to the port's names. If a proof needs a declaration that is
  `private` in the port or below the home, **stop and report** — do not promote, do not restate,
  do not edit a hub.
- Imports stay specific (`import Mathlib` is forbidden in a library module); `set_option
  autoImplicit false`, `noncomputable section`; no `set_option maxHeartbeats`; no `sorry`/`admit`/`axiom`.
- Edit loop from `lean/`: `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
  FLTForHuman/…/X.lean`. Finished modules: `flock .lake/flt_build.lock timeout 110 lake build
  FLTForHuman.AlgebraicCurve.…X`. **No tree build, no dependents**; every command under two
  minutes, its own `timeout`; logs under `lean/tmp/wr1-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module;
  `#print axioms` on the four headlines → `[propext, Classical.choice, Quot.sound]`; 0 warnings
  (run the edit loop and read the output — `lake build` alone hides linter warnings); no commit.
- After the final build, run `python3 tools/deps/dedup.py --module <module> --within` on the new
  module and report its clusters (do not refactor them; the wrapper-over-engine pairs are the
  pin's own shape).

## Report (one message)

Per module: the build line and any warnings, the `check_port` summary line, the axioms lines.
For `Pic0/WeilPairing.lean`: its line count and the count of public/private declarations.
Any deviation from the pin's statements, any blocker, and anything the next order should know.
