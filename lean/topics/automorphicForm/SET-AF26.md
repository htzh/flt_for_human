# SET-AF26 — the local `L²` bound of an `LsXi` function

**Status: DISPATCHED 2026-11-07** — one order, one new module; §5 is the forecast, §6 records the
landing at review. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF25 left. It is the **twenty-sixth** `AutomorphicForm`-serving set and the first half of the
compact-operator chain SET-AF25 §8 named.

**2 rows / 1,808 silo / 1,665 net new math lines (`port_plan`) / 120 declaration groups**, of which 79
lines are already in the port. **Both rows are on the ready block**, and between them they share
**zero declarations** — two independent transcribing jobs: one 1,361-line file of thin lemmas (78
declarations) and one 447-line file that is two `private def`s and a single long proof.

| row (`AutomorphicForm.` dropped) | silo | prem | block | what it says |
|---|---|---:|---|---|
| `exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre` | 1,361 | 2 | ready | for a finite union of translates of a centre-cut Siegel set that covers `GL₂(𝔸_K)` modulo the centre, a compact `R` has `∫⁻_R ‖φ‖² ≤ N · ∫⁻_{⋃ x ∈ T, (·*x)''centreCutSiegelSet} ‖φ‖²` for every continuous `LsXi` function `φ` |
| `…_of_isFundamentalDomain` | 447 | 5 | ready | the same bound against a **fundamental domain** `Φ₀` of the determinant-norm slab `α ≤ ‖det g‖ ≤ β` |

## 0. The read (SET-AF25's post-landing read)

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af25-post.json
python3 build/af-return.py build/shelf-af25-post.json AutomorphicForm. 100
```

| figure | value |
|---|---|
| `needed [F terminal]` | **786 nodes / 332,109 lines** |
| `needed [literal]` | 798 / 335,574 |
| frontier F | 1,630 / 795,267 |
| ready block | **71 / 24,001** — 43 `AutomorphicForm` / 17,862 |
| leaves block | **210 / 54,362** — 45 `AutomorphicForm` / 9,242 |
| `AutomorphicForm` demand | 295 / 131,814 |
| withheld | 4 (the prunable complex-analytic premises) |
| `--unport` corrections | none (`--selfcheck` PASS) |

## 1. Why this cut

After AF25 the return column is thin (best: `exists_sum_prod_mul_of_rightTranslatesSpanFinite` 576 →
552; the carrier hub is gone), so this cut is made on **completeness and subject**: the two rows are
the only pair on the ready block whose closures are *complete* (every premise ported, closure = the
rows themselves) and whose subject is one statement in two shapes — the local `L²` bound that turns
the Siegel covering theorem into an estimate.

They are also the first half of the chain SET-AF25 §8 named: the compact-operator gateway
`isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285, off-shelf) needs seven unported premises,
of which these two are the largest (`…_of_isFundamentalDomain` 447 is one of them; the other,
`…_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain` 1,165, is not). So the chain is
AF26 → (the 1,165 row) → the 285 gateway → the 114/43 compact-operator rows — and this set is the
part of it that is *ready now*.

**What it readies: nothing directly** (`build/af24-return.py` over the pair: 0 rows), but it moves
`exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain`
(209) to **one premise short**, that premise being the 78-line leaf
`norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` — which is the natural AF27 head (§6).

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 1,808 |
| declaration lines | 1,744 |
| — duplicate copies | **0** (the two files share no declaration) |
| — boilerplate | 64 |
| distinct declaration groups | 120 |
| already in the port (vetted) | 79 |
| **net new math lines** | **1,665** |

11 trusted substitutions and one suspect (`ratCentre → WindowedSiegel.rowIsometrySubgroup`, the
parser's type-only `def` false positive — read the body before believing it). No definition gate:
`gate_scan` over `Def_AutomorphicForm_SiegelCovering`, `_AdelicLsXi`, `_FnTwist`,
`Def_NumberField_AdelicVolume`, `_TateGlobalZeta` reads **0 missing**. `twin_scan`: `new` twice.

## 3. Home

**One new module, `Adelic/LsXiBound.lean`**, beside `Adelic/LsXi.lean` (the predicate it is about) and
above `Adelic/Siegel/Covering.lean` + `Adelic/WindowedSiegel/CentreCutSet.lean` (the covering
vocabulary). No insertion, no legacy module, cascade-free.

## 4. The cut and the gates

One order, against the checker-green scaffold
(**2 ok / 0 mismatch / 0 missing**), which already carries the pin's three
`attribute [local instance]` lines — without them `MeasurableSpace (AdelicGL2 (𝓞 K) K)` does not
resolve, the same deviation AF25 recorded.

## 5. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 786 / 332,109 | **784 / 330,301** |
| `needed [literal]` | 798 / 335,574 | **796 / 333,766** |
| frontier F | 1,630 / 795,267 | **1,632 / 797,075** |
| ready block | 71 / 24,001 | **69 / 22,193** (2 out: 1,808; 0 in) |
| leaves block | 210 / 54,362 | **210 / 54,362** (untouched) |
| `AutomorphicForm` demand | 295 / 131,814 | **293 / 130,006** |
| rows readied | — | **0** (one row moved to one premise short) |

## 6. What this set does not do, and what is named next

- **The `Lp` continuity block** — `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` (78, a
  ready **leaf**), `exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain`
  (209, one premise behind it after this set), `adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain`
  (119) and `exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le` (139):
  ≈545 silo, the cheap rest of the compact-operator chain's left side. That is the natural **AF27**.
- **The 1,165-row** `exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain`
  — the middle of the chain, on neither block (`needed = 2` before this set), behind this set's 447
  row and the 1,165-row's own Lp sibling.
- **The compact-operator rows** (285 gateway, then 114 and 43) — blocked until the 1,165 row lands.
- **The Weyl intertwining integrand** (≈4,482 silo) and the `isCuspConstituent` cluster remain the two
  large open subjects, as SET-AF25 §8 lists them.
