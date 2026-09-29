# SET W2 — rewire the level family onto the shared homes

**Status: done (2026-09) — all six modules rewired; the width family deferred to W4.** Third
set of the [WeightOne rectification](TOPIC-weightone-rectify.md). SET-W1 created the
level-family homes (`Defs/PeriodPair`, `QExpansionCoeff`, `DiscPow`, `Defs/PTorsion`,
`Fricke`); this set makes the six level-family modules **import them and delete their private
copies**. It is the one set that edits the big modules, and it edits each of them **once**,
so the rebuild wave happens once.

## Execution record

| # | module | before → after | status |
|---|---|---|---|
| 1 | `Basic.lean` | 1,863 → 1,579 | **done** — imports `ModularForms.DiscPow`; the lifted `UpperHalfPlaneAux` prelude (lines 1278–1563) deleted |
| 2 | `WeierstrassPTorsion.lean` | 1,317 → 1,160 | **done** — 31 statement-identical private copies deleted |
| 3 | `LevelOneHauptmodul.lean` | 2,803 → 2,570 | **done** — 36 deleted |
| 4 | `FrickeFunction.lean` | 3,702 → 3,304 | **done** — 65 deleted |
| 5 | `LevelFraction.lean` | 3,874 → 3,606 | **done** — 38 deleted |
| 6 | `LevelN.lean` | 3,386 → 3,112 | **done** — 39 deleted |

Verified after the wave: `timeout 500 lake build` **green, 4,648 jobs** (6:19 wall — the
level-family recompile); checker **1653 identical / 0 mismatched / 0 missing** (unchanged);
`WeightOneConsumer.lean` exit 0; `port_graph.py --blocks` **7,242 → 5,737** removable lines
(−1,505, ≈21 %).

### The namespace policy that made it work

The wave is one coordinated change, not a batch of file edits (the first attempt failed — see
below). What fixed it:

- **`open` the homes at the top of every consumer**: `open WLight`,
  `open UpperHalfPlaneAux`. All the lifted names are then reachable unqualified, exactly as
  each consumer's own private copy was.
- **Delete in the same pass, in every consumer.** The `Ambiguous term` on
  `periodPairOfTau`/`periodPair_eq_of_ω` (top-level `PeriodPair` names vs a not-yet-rewired
  consumer's private copy) only clears when all six drop their copies together.
- **Do not touch the `qExpansion_coeff_width` family in this wave.** Each file namespaces it
  differently (`WLight.ModularFormClass...`, `WLightR2.ModularFormClass...`) and the call
  sites pick among `qExpansion_coeff_width`/`_fn`; deleting them produced `Application type
  mismatch` where the resolved variant's binder order differed. They are excluded and left to
  W4, where they will be **generalised** to one lemma rather than relinked.
- **The statement-identity gate is the safety net.** A copy is deleted only when the
  checker's normalized statement equals the home's, so a same-name-different-lemma is never
  silently replaced.

### The first attempt (kept as the record of what not to do)

The reverted attempt deleted the width family too and rewrote qualified references with a
global string replace, which renamed a *declaration site*
(`private theorem _root_.WLight.ModularFormClass.qExpansion_coeff_width` →
`_root_.UpperHalfPlaneAux...`), colliding with the home. It had failed in three ways: exported
top-level names colliding with consumer copies (`Ambiguous term` at `LevelN:1241`);
qualified references dangling; and `Application type mismatch` from namespace-version
differences. The corrected plan below is what landed.

## 0. Scope

Rewire, in this order (bottom-up within the level family):

| # | module | homes it consumes |
|---|---|---|
| 1 | `ModularForms/WeightOne/Basic.lean` | `Defs/PeriodPair`, `QExpansionCoeff`, `DiscPow`, `Defs/Pole`, `Fricke`, `LevelField` (whichever it references) |
| 2 | `ModularForms/WeightOne/WeierstrassPTorsion.lean` | `Defs/PeriodPair`, `Fricke` |
| 3 | `ModularForms/WeightOne/LevelOneHauptmodul.lean` | `Defs/PeriodPair`, `DiscPow`, `Defs/Pole` |
| 4 | `ModularForms/WeightOne/FrickeFunction.lean` | `Defs/PeriodPair`, `DiscPow`, `Defs/Pole`, `Fricke` |
| 5 | `ModularForms/WeightOne/LevelFraction.lean` | `Defs/PeriodPair`, `QExpansionCoeff`, `DiscPow`, `Defs/Pole`, `Fricke`, `LevelField` |
| 6 | `ModularForms/WeightOne/LevelN.lean` | `Defs/PeriodPair`, `QExpansionCoeff`, `DiscPow`, `Defs/Pole`, `Fricke`, `LevelField` |

**Not authorized:** the Γ-modules (SET-W3), the near-duplicate generalisations and adapter
demotions (SET-W4), the capstone, the FFG/T-side modules, commits.

## 1. Method, per module

1. Add the home imports (specific; no `import Mathlib`).
2. Delete the now-duplicated `private` copies of the lifted declarations.
3. Resolve references: either qualify (`DiscPow.ratCoeff_mul`) or `open` the home's
   namespace at the top of a `section`, whichever keeps the diff smallest and the reading
   order clearest. A name that was `WLight`-nested in the pin keeps its meaning; only its
   home changes.
4. `timeout 90 lake build <module>` after each module — **not** after the whole set.
5. If a reference turns out to be to a helper that was *not* lifted (a consumer-only
   private helper), leave it private in that consumer and note it; do not silently drop it.

## 2. Definition of done

- All six modules import the homes; their duplicated private copies are gone.
- Public surface unchanged: every headline keeps its name, binders and statement, and the
  `PORT_FILES` entries are unchanged.
- `timeout 180 lake build` green, 0 warnings, no `sorry`.
- `python3 spec/check_flt_statements.py`: **0 mismatched, 0 missing**, and the `identical`
  count unchanged from the W1 review (no public declaration moved out of a checked module).
- `timeout 120 lake env lean spec/WeightOneConsumer.lean` exit 0.
- `python3 ../tools/deps/port_graph.py --blocks 5` in the tool dir: the level-family block
  is gone from the report (only the Γ block remains over threshold).

## 3. What to report back

1. Per module: imports added, private copies deleted (count and lines), build time.
2. Any helper that stayed private because it was not shared, and why.
3. Any reference that could not be resolved by import (a genuine cycle) — stop and report.
4. The `--blocks` before/after figure.
5. Any build that hit its bound: the declaration, the CPU reading, the outcome.

## Appendix — the per-consumer deletion checklist (generated)

Regenerate with `python3 ../tools/deps/port_graph.py --duplicates 400`. The count is
the number of *distinctive private* declarations that module defines which also appear
in at least one other level-family module; the executor confirms the home assignment
and that the statements are identical before deleting.

### `Basic` — 26 duplicated private declarations

`ratCoeff_pow` (20L, in 5), `mul_discPow_mono` (20L, in 5), `qExpansion_coeff_width` (17L, in 6), `isIntegral_subring_iff` (17L, in 2), `ratCoeff_discriminant` (16L, in 6), `periodic_discPow_comp_ofComplex` (16L, in 5), `qExpansion_discPow_coeff_mem` (12L, in 5), `discPowForm_coe` (12L, in 5), `ratCoeff_mul` (11L, in 6), `ratCoeff_E` (11L, in 6), `qExpansion_one_discPowForm` (11L, in 5), `discriminant_eq_smul_eCubeSubESq` (9L, in 6), `ratCoeff_sub` (8L, in 6), `qParam_one_eq_pow` (8L, in 6), `isBoundedAtImInfty_discPow` (8L, in 5), `eCubeSubESq_qExpansion` (8L, in 6), `analyticAt_cuspFunction_zero_of` (6L, in 5), `KPoleAt` (5L, in 5), `mem_of_rat` (4L, in 5), `mdiff_mul_discPow` (4L, in 5),
… and 6 more.

### `WeierstrassPTorsion` — 55 duplicated private declarations

`norm_wpTail_le` (37L, in 2), `qExpansion_coeff_width` (27L, in 6), `qExpansion_frickeH_coeff_mem_kN` (23L, in 2), `wpMonCoeff_mem_kN` (18L, in 2), `ratCoeff_discriminant` (16L, in 6), `ratQExp_one` (15L, in 2), `wpTorsionSeries` (14L, in 3), `periodic_wpNorm` (13L, in 2), `ratCoeff_sub` (12L, in 6), `periodPairOfTau` (12L, in 5), `mdifferentiable_wpTorsion` (12L, in 2), `ratCoeff_mul` (11L, in 6), `ratCoeff_E` (11L, in 6), `periodic_frickeH` (10L, in 2), `discriminant_eq_smul_eCubeSubESq` (9L, in 6), `wpMonCoeff` (8L, in 2), `qParam_one_eq_pow` (8L, in 6), `norm_qN_le_of_le_im` (8L, in 2), `eCubeSubESq_qExpansion` (8L, in 6), `cexp_two_pi_I_mul_torsionPt` (8L, in 2),
… and 35 more.

### `LevelOneHauptmodul` — 73 duplicated private declarations

`j_surjective` (110L, in 3), `isZeroAtImInfty_mul_disc_of_coeff_le` (43L, in 2), `norm_wpTail_le` (37L, in 2), `kPole_algebraMap` (34L, in 4), `norm_le_of_monicRel` (32L, in 2), `qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc` (30L, in 2), `powerSeries_coeff_mem_of_mul_eq` (30L, in 2), `isBigO_qParam_pow_of_qExpansion_coeff_eq_zero` (27L, in 2), `qExpansion_coeff_width` (26L, in 6), `powerSeries_coeff_mem_of_mul_eq'` (26L, in 2), `kPole_invariant_eq_polynomial_j_mem` (24L, in 2), `isBoundedAtImInfty_of_monicRel` (21L, in 2), `levelOne_holFn_eq_polynomial_j` (19L, in 2), `ratCoeff_discriminant` (16L, in 6), `periodic_discPow_comp_ofComplex` (16L, in 5), `qExpansion_discPow_coeff_eq_zero_of_lt` (15L, in 2), `weierstrassP_smulPeriodPair` (14L, in 2), `mdifferentiable_wpTorsion` (14L, in 2), `ratCoeff_sub` (12L, in 6), `ratCoeff_pow` (12L, in 5),
… and 53 more.

### `FrickeFunction` — 111 duplicated private declarations

`bounded_orbitCoeff_prod` (66L, in 2), `orbit_integral_over_j` (40L, in 2), `kPole_jf` (37L, in 3), `frickeF_eq_imp` (35L, in 3), `kPole_algebraMap` (34L, in 4), `exists_fixed_div_of_fixed` (34L, in 3), `qExpansion_frickeH_coeff_mem_kN` (28L, in 2), `mem_Gamma_or_neg_mem_of_vecMulSL` (27L, in 3), `ratCoeff_discriminant` (24L, in 6), `mdiff_orbitCoeff_prod` (21L, in 2), `frickeF_integral_over_j` (21L, in 3), `poleBounded_j` (20L, in 3), `exists_poly_j_orbitCoeff` (20L, in 2), `denomZ_ne_zero` (20L, in 3), `wpMonCoeff_mem_kN` (18L, in 2), `weierstrassP_smulPeriodPair` (18L, in 2), `smul_j` (18L, in 3), `mdifferentiable_frickeF` (18L, in 3), `frickeF_faithful` (18L, in 3), `eq_polynomial_j_of_invariant_of_mem_adjoin` (18L, in 3),
… and 91 more.

### `LevelFraction` — 168 duplicated private declarations

`bounded_orbitCoeff_prod` (66L, in 2), `kPole_jf` (45L, in 3), `isZeroAtImInfty_mul_disc_of_coeff_le` (43L, in 2), `orbit_integral_over_j` (41L, in 2), `qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc` (36L, in 2), `qExpansion_coeff_width` (34L, in 6), `norm_le_of_monicRel` (34L, in 2), `kPole_algebraMap` (34L, in 4), `r4a_package` (32L, in 2), `powerSeries_coeff_mem_of_mul_eq` (30L, in 2), `mem_Gamma_or_neg_mem_of_vecMulSL` (28L, in 3), `mem_levelFixer_iff_frickeF` (27L, in 2), `isBigO_qParam_pow_of_qExpansion_coeff_eq_zero` (27L, in 2), `powerSeries_coeff_mem_of_mul_eq'` (26L, in 2), `fixedPoints_levelField_eq_adjoin_j` (26L, in 2), `exists_fixed_div_of_fixed` (26L, in 3), `exists_poly_j_orbitCoeff` (25L, in 2), `ratCoeff_discriminant` (24L, in 6), `mdiff_orbitCoeff_prod` (22L, in 2), `eq_zero_or_eq_zero_of_mul_eq_zero` (22L, in 2),
… and 148 more.

### `LevelN` — 148 duplicated private declarations

`kPole_jf` (45L, in 3), `toField` (34L, in 2), `qExpansion_coeff_width` (34L, in 6), `kPole_algebraMap` (34L, in 4), `r4a_package` (32L, in 2), `kPole_aeval` (31L, in 2), `mem_Gamma_or_neg_mem_of_vecMulSL` (28L, in 3), `mem_levelFixer_iff_frickeF` (27L, in 2), `fixedPoints_levelField_eq_adjoin_j` (26L, in 2), `exists_fixed_div_of_fixed` (26L, in 3), `ratCoeff_discriminant` (24L, in 6), `eq_zero_or_eq_zero_of_mul_eq_zero` (22L, in 2), `mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero` (21L, in 3), `denomZ_ne_zero` (20L, in 3), `polyJEquiv` (18L, in 2), `frickeF_faithful` (18L, in 3), `eq_polynomial_j_of_invariant_of_mem_adjoin` (18L, in 3), `r4b_package` (17L, in 2), `frickeF_integral_over_j` (17L, in 3), `smul_eq_self_of_pm` (16L, in 2),
… and 128 more.

