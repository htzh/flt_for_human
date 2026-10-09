# WORKORDER-W4 — the good-reduction definition wave (story C)

**Status: stage 1 landed; stages 2–4 paused and handed off (2026-10-08).** This is the
definition layer story C is gated on ([TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md)
§3 and §5, W4). It is **not** a subagent set: it is new definition modules plus one hub append,
and the playbook puts the definition layer with the manager. **A new session resumes at §1a.**
Pin `aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`), port `v4.34.0`; checker at hand-off
**7246 identical, 0 mismatched, 0 missing, 37 own (7283 checked)**.

Two story-C headlines are gated on it:
`WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero` (185 `S_` lines) and
`WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map` (601).

## 0. The budget is measured, not the file sizes

The four pin definition modules are 253 + 1,233 + 489 + 1,103 = **3,078 raw lines**, but the
rule is to home the *used block*. Taking the two `S_` files, collecting every pool declaration
name they mention, and closing transitively over the pool's own declaration bodies (all
components of every dotted reference, since `W.formalCoordinates.eq_zero_of_nsmul_eq_zero`
hides `formalCoordinates` behind its last token):

| pin module | used / total decls | used raw lines |
|---|---:|---:|
| `Def_WeierstrassCurve_ReductionMap.lean` | 14 / 26 | 158 |
| `Def_WeierstrassCurve_TorsionIntegral.lean` | 34 / 40 | 1,148 |
| `Def_WeierstrassCurve_ReduceHom.lean` | 18 / 22 | 497 |
| `Def_WeierstrassCurve_ZeroComponentReduction.lean` | 22 / 57 | 278 |
| **used block** | **88 / 145** | **2,081** |

So the wave is ≈2,081 raw pin lines (≈1,400–1,600 written after the scaffolding is dropped) —
about one set's worth, not the 3,000+ the topic first guessed. The unused remainder is
recorded in §5 and stays unported: `Def_ZeroComponentReduction`'s smooth-locus half
(`reducePointSmooth*`, `SmoothLocusReductionData`, `zeroComponentSubgroup`, `reduceHom₀`, …),
`Def_TorsionIntegral`'s six unused leaf lemmas, `Def_ReduceHom`'s four, and
`Def_ReductionMap`'s twelve.

## 1. Four stages, in import order

Each stage is a new leaf module under a new `WeierstrassCurve/Reduction/` theory directory
(playbook §3.2), except where noted. Build and checker-check each before the next.

| stage | module | pin source (used block) | decls | raw |
|---|---|---|---|---:|---:|
| 1 | `FLTForHuman/WeierstrassCurve/Reduction/Point.lean` **+ an append to `NumberTheory/ValuationAtPlace.lean`** | `Def_ReductionMap` lines 84–197 | 10 + 4 | 158 |
| 2 | `FLTForHuman/WeierstrassCurve/Reduction/TorsionIntegral.lean` | `Def_TorsionIntegral` | 34 | 1,148 |
| 3 | `FLTForHuman/WeierstrassCurve/Reduction/ReduceHom.lean` | `Def_ReduceHom` | 18 | 497 |
| 4 | `FLTForHuman/WeierstrassCurve/Reduction/ZeroComponent.lean` | `Def_ZeroComponentReduction` | 22 | 278 |

### 1a. Resume here (handed off to a new session, 2026-10-08)

**State.** Stage 1 is **landed and verified** (§6). Stages 2–4 are **not started**. Checker at
hand-off: **7246 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7283
checked)**; the wave build at hand-off was green (9,353 jobs). Nothing is committed — the whole
worktree, including the new modules and the checker wiring, is uncommitted.

**Why it paused.** The wave is bigger than first estimated: **88 of 145 declarations / 2,081 raw
pin lines** (stage 1 took 158 of them). The remaining **1,923 raw lines** are real transcription
with mathlib `v4.33.1 → v4.34.0` drift, and none of it is new mathematics.

**The whole wave hangs off 17 entry points.** These are the declarations the two `S_` files name
*directly*; everything else in the used block is their transitive closure. They are where a
re-cut should cut, and stage 1 has already consumed `Def_ReductionMap`'s ten:

| pin module | entry points (pin line) | closure |
|---|---|---:|
| `Def_ReductionMap` — **done** | `mul_mem_nonunits` 84, `one_notMem_nonunits` 92, `some_congr` 101, `Affine.Y_mem_of_X_mem` 108, `map_residue_Δ_ne_zero_iff` 138, `reducePoint` 157, `reducePoint_some_of_mem` 173, `reducePoint_some_of_notMem` 181, `smul_mem_of_mem_decompositionSubgroup` 209, `residue_smul_eq_of_mem_inertiaSubgroup` 216 | 14 |
| `Def_TorsionIntegral` | `inv_mem_of_notMem_nonunits` 214, `inv_mem_nonunits_of_notMem` 219 | 34 |
| `Def_ReduceHom` | `residue_eq_of_coe_eq` 20, `reduceHom` 481 | 18 |
| `Def_ZeroComponentReduction` | `natCast_mem` 17, `X_mem_of_nsmul_eq_zero_of_formalCoordinates` 254, `zero_mem` 651 | 22 |

Note how lopsided stage 2 is: **two** entry points (both one-line valuation lemmas) close over 34
declarations and 1,148 lines, because the pin's `X_mem_of_nsmul_eq_zero_of_formalCoordinates`
route runs through the whole formal-parameter estimate chain. The largest used declarations, by
captured span (**an upper bound** — unused declarations may sit inside a span):
`slope_div_intercept_estimate` 299 lines (pin :545), `add_formal_param_estimate` 173 (:868),
`slope_mem_residue_of_not_inverse` 164 (`ReduceHom`:116), `formal_param_nsmul` 112
(`TorsionIntegral`:1040), `reducePoint_add_of_mem` 88 (`ReduceHom`:279).

**Suggested re-cut for a fresh session, in import order.** Split stage 2 into
**2a** the small membership/integrality block (`TorsionIntegral` pin 11–278: `add_notMem`,
`mul_notMem`, `div_notMem`, `coe_mem_nonunits_iff_residue_eq_zero`, `sub_mul_sub_negY`,
`notMem_nonunits_of_sub_negY_mem_nonunits`, `slope_notMem_of_sub_mem_nonunits`,
`addX_notMem_of_sub_mem_nonunits`, the `*_nonunits` inversion family,
`natCast_mem_nonunits_iff_residue_eq_zero`, `cubic_inv_notMem_nonunits`, `rhs_eq_cubic_mul`,
`Y_ne_zero_of_X_notMem`, `X_div_Y_mem_nonunits`, `Y_notMem_of_X_notMem`,
`X_cubed_div_Y_sq_notMem_nonunits`, `inv_Y_div_mem_nonunits`, `inv_X_mul_div_mem_nonunits`) and
**2b** the formal-parameter estimate tail (pin 404–1148: `neg_formal_param_add`,
`neg_formal_param_estimate`, `sub_eq_slope_mul_sub`, `vieta_addX`, `secant_slope_identity`,
`slope_div_intercept_estimate`, `collinear_prod_sum`, `add_formal_param_estimate`,
`formal_param_nsmul`). 2a is the foundation the reduction map's additivity needs; 2b is the
formal-group estimate that `ZeroComponentReduction`'s `eq_zero_of_nsmul_eq_zero` consumes. The
same treatment applies to stage 3 (`reduceHom` is a definition plus three case lemmas) and
stage 4.

**First commands for the new session.**

```bash
cd lean
timeout 400 python3 spec/check_flt_statements.py    # expect 7246 / 0 / 0 / 37 own
git status --porcelain                              # everything uncommitted, by design
```

Then stage 2a as a new leaf module under `WeierstrassCurve/Reduction/`, appended last to
`PORT_FILES` (the pin `SOURCES` row for `Def_TorsionIntegral.lean` must be **added** — unlike
stage 1's pin file, it is not yet in `SOURCES`), and checker-checked **before** building: the
checker is text-only and catches statement drift while the proofs are still red.

**Stage 1 is landed — see §6.** The hub append is the four `ValuationSubring` rows of the same
pin file (`mul_mem_nonunits`, `one_notMem_nonunits`, and the two inertia rows
`smul_mem_of_mem_decompositionSubgroup`, `residue_smul_eq_of_mem_inertiaSubgroup`): they are
generic valuation lemmas, so their natural home is the module that already carries the pin's
*other* `ValuationSubring` block from the same file, `NumberTheory/ValuationAtPlace.lean`.
Appending there is a hub edit — price it with `build_ladder.py --edit` and do it in the same
wave as the stage's new module, not separately.

## 2. Faithfulness rules for a definition wave

* **Statements are law**, and the pin's `Definitions/Def_*.lean` declarations are *public*
  there, so every homed declaration is a public port declaration the checker will diff against
  `SOURCES`. Transcribe each statement verbatim; run the checker after each stage. The
  expected delta is **+ the stage's declaration count** (the used block's 88 + any row that
  matches a `kw_`-stripped pin-private name).
* **Declarations only, in the pin's own names and namespaces** — this is not the place for a
  role-based rename. Where the pin splits a block across two namespaces (`ValuationSubring`
  and `WeierstrassCurve`), keep the split.
* A pin `private` helper the proofs need stays `private` in the homed module; only the pin's
  public declarations become public.
* **Transcribe the pin's `linter.*` suppressions, never `maxHeartbeats`.** None of the four
  files sets either, so write neither unless a real warning appears (fix the warning).
* The pin's `attribute [-instance]`/`[-simp]` scaffolding is not transcribed; the pin's
  `import Mathlib` becomes specific imports.

## 3. Route and risks

* **Everything is new files except the stage-1 append**, so there is no cascade until the
  hub append; a stage-1..2..3..4 sequence can therefore be built stage by stage.
* The proof bodies are valuation/`linear_combination` heavy (`slope_mem_residue_of_not_inverse`
  is 164 lines, `Affine.addX_notMem_of_sub_mem_nonunits` 86, `reducePoint_add_of_mem` 88). None
  of this is new mathematics — it is the reduction map and the formal-group estimates — so the
  route is transcription with mathlib v4.34.0 drift, not invention.
* **The mathlib line differs** (pin v4.33.1, port v4.34.0): expect `if_neg` → `ite_eq_right`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `dif_neg`/`dif_pos` → `dite_eq_*`, and
  self-base-change not being definitional. See `porting-playbook.md` §7.
* **`reducePoint` uses `open Classical in` + `if hx : x ∈ A`**, and the pin's
  `reducePoint_some_of_mem`/`_of_notMem` are `dif_pos`/`dif_neg` — transcribe the `open
  Classical in` and the `@[simp]` on `reducePoint_zero` exactly.
* The `ValuationSubring` block's two inertia rows mention `A.decompositionSubgroup` and
  `A.inertiaSubgroup`; check the port's `NumberTheory/ValuationAtPlace.lean` /
  `GaloisRep/Defs/Ramification.lean` spellings before writing them, and keep the pin's
  `_root_.ValuationSubring.` prefix where the pin has it.

## 4. Wiring

Per stage, in `lean/spec/check_flt_statements.py`, appending **last**: the pin
`Definitions/Def_<…>.lean` to `SOURCES` (stage 1's `Def_WeierstrassCurve_ReductionMap.lean` is
**already** in `SOURCES` from the earlier `ValuationSubring` promotion — do not duplicate it),
and the new module to `PORT_FILES`. Definition modules get coverage by name against the pin's
`Definitions/` files (playbook §4.1).

## 5. Deliberately not ported (counted)

* `Def_ZeroComponentReduction`: the smooth-locus/zero-component half — `reducePointSmooth`,
  its seven lemmas, `SmoothLocusReductionData` and its four fields' users, `zeroComponentSubgroup`,
  `reduceHom₀`, `mem_zeroComponentSubgroup_iff`, `nonempty_smoothLocusReductionData`,
  `nonIntegralLocus_le*` (35 of 57 declarations). Trigger: a consumer of the smooth-locus
  reduction rather than the formal-coordinate one.
* `Def_TorsionIntegral`: `X_mem_of_nsmul_eq_zero'`, `X_mem_of_nsmul_eq_zero''`, the `addAux_*`
  family, `addX_notMem_*`/`addY_*`/`residue_addX_*`/`residue_addY_*`, `tangent_*`,
  `some_eq_of_mem_inertia_of_nsmul_eq_zero'`, `fixed_of_mem_inertia_of_nsmul_eq_zero`,
  `charP_residueField_of_liesOverPrime_def`, `exists_liesOverPrime`, `liesOverPrime_iff`,
  `mem_inertiaSubgroupIn`, `natCast_mem'`, `natCast_mem_maximalIdeal_of_liesOverPrime` — the
  last five are the *other* `ValuationSubring` block, and `charP_residueField_…`/`liesOverPrime_iff`/
  `natCast_mem_maximalIdeal_…`/`natCast_mem'` are already public in
  `NumberTheory/ValuationAtPlace.lean` (they are in `SOURCES` for `Def_ReductionMap`); the
  duplicate names appear here because both pin files declare them.
* `Def_ReduceHom`: `additive`, `reducePointSmooth_eq_reducePoint`, and the residue lemmas the
  smooth-locus route would need.
* `Def_ReductionMap`: the twelve not in the used block, including
  `Affine.Y_mem_of_X_mem`'s sibling statements and the first `ValuationSubring` block already
  homed.

## 6. Outcome

*(filled in stage by stage below.)*

### Stage 1 — landed 2026-10-08

Two pieces, one wave (the hub append's cascade is 10 modules / 2,342 lines ≈ 31 s; the wave
build was **9,353 jobs / 51.8 s wall / CPU 88.5 + 31.8**).

| piece | decls public / private | tier 1 |
|---|---:|---:|
| `NumberTheory/ValuationAtPlace.lean` (append) | 4 / 0 | 4.0 s (hub) |
| `WeierstrassCurve/Reduction/Point.lean` (new, 160 lines) | 9 / 1 | 3.1 s |

**Checker 7233 → 7246 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own
(7283 checked)** — +13, exactly the four `ValuationSubring` rows plus the nine public
declarations of the new module (the pin's `private some_congr` stays private and is invisible).
Warning-free on both pieces. This closes the pin `Def_WeierstrassCurve_ReductionMap.lean` used
block entirely: its 14 used declarations are now all public in the port.

*The hub append is the four `ValuationSubring` rows* (`mul_mem_nonunits`, `one_notMem_nonunits`,
`smul_mem_of_mem_decompositionSubgroup`, `residue_smul_eq_of_mem_inertiaSubgroup`) in
`NumberTheory/ValuationAtPlace.lean`, beside the pin's first `ValuationSubring` block, with a
section note naming the pin lines (80–95, 205–228) and the `open IsLocalRing` /
`open scoped Pointwise` they need. The pin's `_root_.ValuationSubring.` prefixes are spelled by
the enclosing namespace, which does not affect the checker (it matches by last name and
statement).

*Proof adaptations to mathlib `v4.34.0` (statements untouched):* the pin's `dif_pos`/`dif_neg`
in `reducePoint_some_of_mem`/`_of_notMem` are the non-deprecated `dite_eq_left`/`dite_eq_right`
(the pin's spellings still elaborate but emit deprecation warnings, and the review gate is
warning-free); `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` is the specific import
for the affine point API (the pin's `import Mathlib` is not transcribed, and
`…EllipticCurve.Affine` itself has no olean in this checkout). Nothing else moved: the block
compiled from its first transcription.

*Residual for stages 2–4:* `reducePoint_some_apply_of_mem_inertia` (pin line 228) is in the
not-used set and stays unported with the rest of §5.
