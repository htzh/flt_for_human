# SET-AF43 — the `Γ₁` level-lowering separation, the cusp-space structure, and the diamond divisor sums

**Status: LANDED 2026-11-12** — §1–3 the rows, price and manager's layer, §5 the forecast, §6 the landing record and the re-read. Read off the D–S shelf
with the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md),
on the read SET-AF41's landing left. Forty-third set of the column, and the first cut in the `ModularForms`
(`Γ₁`) layer since SET-AF38.

**7 rows / 1,203 silo / 1,070 net (`port_plan`) in three modules**, of which 3 declaration lines are
already in the port. It is the **best-returning set on the shelf**: `af24-return.py` measures **776 silo
readied in two rows** (485 + 291), the highest return-per-silo figure the column has recorded since AF41.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq` | 570 | 1/1 | a `Γ₁(N)`-invariant sum `∑_{p ∣ N} F p` of `Γ₁(N)`-cusp forms splits: there are `G p` at level `Γ₁(N/p)` with the same sum and each `G p` stable under the `S · T^{N/p} · S⁻¹` conjugate |
| **A2** | `CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne` | 218 | 1/3 | the degeneracy lifts `G i d τ = g i (d • τ)` of eigenforms whose `q`-coefficients separate outside `N` are linearly independent |
| **B1** | `CuspForm.heckeULinH_comm` | 74 | 2/3 | the `U_ℓ` operators commute: `U_q (U_{q'} f) = U_{q'} (U_q f)` |
| **B2** | `CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div` | 69 | 1/1 | a primitive form's `q`-coefficient at `q` vanishes once `q ∣ M` and `q ∣ M/q` |
| **B3** | `CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast` | 19 | 1/3 | the `Γ₁` cusp space has a basis whose two recorded `q`-coefficients are integral |
| **B4** | `CuspForm.finiteDimensional_Gamma1` | 16 | 1/2 | the `Γ₁(M)` cusp space is finite-dimensional over `ℂ` |
| **C** | `ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq` | 237 | 1/2 | for each `c ∈ (ZMod M)ˣ` there is a weight-4 `Γ₁(M)` form with an integral `q`-expansion of partial divisor sums, moving by the diamond action under `Γ₀(M)` |

## 0. The read

The read SET-AF41's landing left: `needed` **737 / 307,988**, literal 753 / 313,407, frontier
1,674 / 816,540, ready **53 / 10,555**, leaves 195 / 48,899, `CuspForm` demand 40 / 12,464, `ModularForm`
12 / 3,280. All seven rows are on the ready block; none is a leaf.

**The definition gate is closed at the module level**: the seven pin files import six pin `Def_` modules —
`Def_CohCarrier_Level`, `Def_CuspForm_HeckeOperatorFormsGammaH`, `Def_CuspForm_PrimitiveFormGamma1`,
`Def_FLTPrelim_Modularity`, `Def_ModularCurve_X1`, `Def_ModularForm_HeckeOperator` — and every one has a
port home (`ModularForms/Defs/CohCarrierLevel`, `…/Defs/GammaH`, `…/Defs/PrimitiveFormGamma1`,
`…/HeckeQCoeff`, `…/WeightOne/Gamma1Basis`, `…/Defs/FormalHeckeOperators`). `port_advise --with-defs`
finds **178 of their declarations already substituted** in the port. **One recorded hazard** (FR-0161's
class): the A2 pin file opens with `attribute [-simp] FreyPackage.ModMCarrier.…`, and
`Def_FreyPackage_ModMCarrier_Rescale` is *not* ported; the attribute is a pin-local simp shim, so it is
**dropped** in the port, as AF7's order did for all `attribute [-…]` lines.

**The premise audit**: the seven rows cite eleven `Theorems/Thm_*` premises between them, among them
SET-AF38's two landed headlines (`exists_degeneracy_gamma1_hasNebentypus`,
`exists_gamma1_div_coe_eq_heckeU_of_dvd_div`). All are in the port at their last names; the worker who
finds one missing reports it (the FR-0156 shadow class is the risk here, not a size risk).

## 1. The rows, grouped into three stories

- **A: level lowering / multiplicity one** (788 silo) — A1 splits a `Γ₁(N)`-invariant divisor sum into
  the smaller levels, A2 makes the degeneracy lifts of separated eigenforms independent. These are the
  two halves of the multiplicity-one step of the level-lowering argument.
- **B: the `Γ₁` cusp space's structure** (178 silo) — commuting `U_ℓ`, the primitive-form vanishing
  criterion, an integral basis and finite dimension. These are the finiteness facts the level-lowering
  argument reads a `Γ₁(N)` form against.
- **C: the diamond divisor sums** (237 silo) — the weight-4 Eisenstein witness that the diamond action is
  non-trivial; it is what makes `IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` (485) true.

**Returns, measured separately**: A readies **none** but makes
`exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero` (868) one premise away; B readies
`CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291); C readies
`ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` (485). So the cheap 415 silo of B+C
carries the set's whole return, and A is the cone movement — the brief states both numbers rather than
letting the 776 hide a 788-silo row with no return.

## 2. The price

| figure | value |
|---|---:|
| raw `S_` lines | 1,203 |
| declaration lines | 1,087 |
| — duplicate copies | 14 |
| — boilerplate | 116 |
| distinct declaration groups | 75 |
| once-cost after dedup | 1,073 |
| already in the port | 3 |
| **net new math lines** | **1,070** |
| written (two orders) | ≈1,000 |

Eight `port_advise` *substitute* hits are type-only `def` matches (`IsEigenformWith → HasNebentypus`,
`JOne → Place.ResidueField`, `IsPrimitiveForm → HasNebentypus`, …) and are refused: none of them is the
statement being ported.

## 3. The manager's layer, landed (do not redo it)

1. **Three modules exist, elaborate and are checker-green**, each with its own `spec-pin:` wire:

| module | scaffold | declarations | unproved | `check_port` |
|---|---|---:|---:|---|
| `ModularForms/NebentypusSeparation.lean` | 428 lines | 62 | 54 | **55 ok / 0 mismatch / 0 missing** |
| `ModularForms/Gamma1CuspStructure.lean` | 124 lines | 12 | 12 | **12 ok / 0 / 0** |
| `ModularForms/CohCarrier/DiamondDivisorSum.lean` | 66 lines | 2 | 2 | **1 ok / 0 / 0** |

   Every public statement of the seven pin files is verified verbatim; the eight data definitions the pin
   states outright are transcribed, the rest wait on proofs. All three build (`lake build`, silent except
   the `sorry` warnings).
2. **The pin's structure is kept**: `DS575Sol`'s four sections (`Action`, `Average`, `Group`,
   `Induction`) in `NebentypusSeparation`, `CuspForm.M4aIndep`'s two (`Separation`, `QCoeff`) in the same
   module, `FracLemma` in `DiamondDivisorSum`, and the pin's `variable`/`include` blocks. The headlines
   sit at their wrapper names in `CuspForm` / `ModularForm`.
3. **Two pin shims are dropped, not ported**: `attribute [-simp] FreyPackage.ModMCarrier.…` (A2, its
   names are unported — FR-0161) and the pin's `set_option maxHeartbeats 3200000` (A1) — the order must
   fit the default 200,000 budget or measure and report the cost (as AF33/AF36 did).
4. **No `own:` row, no marker, no linter suppression**; `autoImplicit false` is the only `set_option`.
5. **Nothing else in the tree is touched**: no insertion, no migration, no promotion.

**The scaffold's import closure was too narrow, in four places, and the workers raised each as a
report rather than adding silently** — the rule is that a module's imports are the mathematics'. Each of
the four is the port home of a pin `Theorems/` premise that only the *proof* consumes (so the
statement-only closure the scaffolder computed does not contain it, and `check_port`, which matches
statements, cannot see the difference):

| order | import added | the pin premise it is the port home of |
|---|---|---|
| 43A | `NumberTheory/ModularForms/CongruenceSubgroupLattice` | `CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers` (pin `:491`) |
| 43A | `ModularForms/Level/DegeneracyString` | `CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul` (pin `:146`) |
| 43BC | `ModularForms/Eisenstein/ResidueSumQExpansion` | `EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow` |
| 43BC | `ModularForms/WeightOne/Gamma1IntegralBasis` | `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` and `ModularForm.finiteDimensional_of_isArithmetic` |

One premise is **not** imported but re-stated: `CuspForm.StableU`, whose port sits in
`ModularCurve/Period/HeckeStability.lean` behind `EichlerShimura/PeriodOf` and five other modules. The
trade was made explicitly (manager's call): a heavy closure imported into every future consumer of this
module, against a ~one-screen private proof from in-closure facts (`heckeU_eq_sum_zmod`,
`heckeMatrix_mul_of_dvd`). The private route was chosen; the report carries the line count and the
declaration it would have used.

## 4. Orders and gates

`tmp/af43/WORKORDER-AF43A-nebentypus-separation.md` (A, 788 silo) and
`tmp/af43/WORKORDER-AF43BC-gamma1-structure.md` (B + C, 415 silo). The two orders touch disjoint files
and neither module imports the other, so they run in parallel; A is the big one (54 proofs, one of them
570 pin lines) and B+C is the small one (14 proofs, two of them one-liners). Standard gates:
`check_port --force` at the counts above, axioms clean on all seven headlines, each module's own
`lake build` under `flock`/`timeout` with no tree build, silence and zero warnings,
`dedup --within --module <Name>` / `move_dead` per module, and one `spec/` consumer zone per order.

## 5. Forecast

| figure | before | after AF43 | after AF42 + AF43 |
|---|---:|---:|---:|
| `needed [F terminal]` | 737 / 307,988 | **730 / 306,785** | **726 / 305,262** |
| `needed [literal]` | 753 / 313,407 | **746 / 312,204** | **742 / 310,681** |
| frontier F | 1,674 / 816,540 | **1,681 / 817,743** | **1,685 / 819,266** |
| ready rows | 53 / 10,555 | **48 / 10,128** | **45 / 8,744** |
| leaves | 195 / 48,899 | 195 / 48,899 | **194 / 48,760** |
| `CuspForm` demand | 40 / 12,464 | **33 / 11,261** | 33 / 11,261 |
| `ModularForm` demand | 12 / 3,280 | **11 / 3,043** | 11 / 3,043 |
| `LanglandsTunnell` demand | 28 / 12,132 | 28 / 12,132 | **24 / 10,609** |

**Rows readied: two** — `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` (485, from
C) and `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291, from B) — plus, one premise away,
`CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero` (868, from A).

## 6. The landing (2026-11-12)

Two orders, three modules, all gates green; nothing left undone and no statement drifted.

| order | module | lines | proofs | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **43A** | `ModularForms/NebentypusSeparation.lean` | 427 → **815** | 54 | **55 ok / 0 / 0** | 6.5 s cold / 2.6 s warm, silent | 2/2 clean |
| **43BC** | `ModularForms/Gamma1CuspStructure.lean` | 123 → **250** | 12 | **12 ok / 0 / 0** | 4.1 s, silent | 4/4 clean |
| **43BC** | `ModularForms/CohCarrier/DiamondDivisorSum.lean` | 65 → **260** | 2 | **1 ok / 0 / 0** | 4.5 s, silent | 1/1 clean |
| | **3 modules** | **1,325 lines** | 68 | **68 ok, 0 mismatch, 0 missing, 0 own** | | 7/7 |

**What the set consumed**: 7 rows / 1,203 silo in **1,057 written proof lines** over three verified
scaffolds of 261 lines — 1,325 module lines for 1,203 silo. `dedup` reports **0 clusters** on B and on C
and **1** on A (the pin's own `M4aIndep.main`/headline double statement, both `spec-pin:`-mandated, kept);
`move_dead` reports **0 dead** on all three.

**The return landed as measured**: `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem`
(**485**) and `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (**291**) are on the ready block — the two rows
`af24-return.py` priced before dispatch.

### 6.1 Deviations held for review

1. **The four approved imports** (§3) are the set's only header deviations, each the port home of a pin
   `Theorems/` premise: closure 37 (A), 62 (B), 56 (C) modules, **zero `ModularCurve.Period` entries** and
   twelve definition-layer `ModularCurve.Defs.*` in both of the latter. Fresh-build costs measured:
   `ResidueSumQExpansion` 31 s, `WeightOne/Gamma1IntegralBasis` 17 s.
2. **`CuspForm.StableU` is re-proved inline, not imported**: the pin used it at
   `S_CuspForm_heckeULinH_comm.lean:60`, whose port is `CuspForm.stableU` in
   `ModularCurve/Period/HeckeStability.lean:94` (16-module closure behind `EichlerShimura/PeriodOf`). The
   port re-proves it as a **62-line `have`** inside `qCoeff_heckeULinH` from in-closure facts
   (`heckeU_eq_sum_zmod` + `heckeMatrix_mul_of_eq`, with `CuspForm.dvd_numerator` for the permutation
   identification), so **no declaration is added** and the checker surface is unchanged. That is the
   manager's recorded trade (§3), now with its cost: 62 lines against a `EichlerShimura`-bearing closure.
3. **The pin's 3,200,000-heartbeat override is gone and the margin is measured.** 43A probed it by
   lowering the gate's own budget: silent at 40,000 / 20,000 / 10,000, three declarations failing at
   5,000, and 101 failing at 1,000 — so the worst proof is in **[5k, 10k]**, a 20×–40× margin under
   200,000, and nothing was restructured for heartbeats. Recorded as a reusable instrument (FR-0168).
4. **One genuinely v4.34-only elaborator failure, not a budget one**: the pin's `FracLemma` summability
   one-liner `(summable_pow_mul_geometric_of_norm_lt_one 4 …).mul_left 2` `whnf`s into a deterministic
   timeout in v4.34 — measured to persist at 2,000,000 heartbeats — so it is written as a fixed-ring `h0`
   plus `.mul_left 2`, with the `gcongr` step expanded to an explicit `calc`. Same mathematics, same
   constants; the rest of the `eisensteinG` assembling route is the pin's verbatim.
5. **The rest is v4.34 proof text**: `FunLike.coe_zero/coe_add/coe_sub/coe_smul` for the `CuspForm.*`
   aliases, `ite_eq_left`/`ite_eq_right` for `if_pos`/`if_neg`, `haveI` → `have` (`haveILetI`), two unused
   `simp` args trimmed (`linter.unusedSimpArgs`), and 43A's `dvd_ordCompl` consuming its `[NeZero N]` by
   the `N = 0` case split instead of `omit` — the same device as AF42's `hκ` and AF41B's `hν`.
6. **One consumer suggestion was replaced, with the reason in the file**: at `L 0 = M` the only divisor is
   `1`, so "every coefficient of a single degeneracy lift" is not the statement's shape; the zone reads
   `c 0 1 = 0` for the single lift and the per-`d` form appears in the `n = 2` zone.

### 6.2 The re-read

Both sets of the wave landed (AF42 + AF43); the corrected reading, i.e. with the five `ModularCurve` phi
markers of §0 unported:

| figure | before the wave | forecast (§5) | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 737 / 307,988 | 726 / 305,262 | **726 / 305,262** ✓ |
| `needed [literal]` | 753 / 313,407 | 742 / 310,681 | **742 / 310,681** ✓ |
| frontier F | 1,674 / 816,540 | 1,685 / 819,266 | **1,685 / 819,266** ✓ |
| ready rows | 53 / 10,555 | 45 / 8,744 | **45 / 8,744** ✓ |
| leaves | 195 / 48,899 | 194 / 48,760 | **194 / 48,760** ✓ |
| `CuspForm` demand | 40 / 12,464 | 33 / 11,261 | **34 / 11,498** ✗ |
| `ModularForm` demand | 12 / 3,280 | 11 / 3,043 | **11 / 3,043** ✓ |
| `LanglandsTunnell` demand | 28 / 12,132 | 24 / 10,609 | **24 / 10,609** ✓ |
| `AutomorphicForm` demand | 260 / 113,790 | unchanged | **260 / 113,790** ✓ |

**One wrong cell, and it is bookkeeping**: the seventh row of §1 is namespaced `ModularForm.`, so the
forecast should have taken six rows (966 silo) out of the `CuspForm` column and one (237) out of
`ModularForm`. Subtracting all seven from `CuspForm` undercounted it by exactly that row — the `ModularForm`
cell was right, `CuspForm` is 34 / 11,498, and the totals (which do not depend on the split) were exact.

**The wave's totals**: `needed` **737 / 307,988 → 726 / 305,262** (−11 nodes / −2,726 lines, matching the
two sets' silo to the line), and **two rows readied / 776 silo** — both from this set, as measured.

## 7. What this set does not do

- **The 868-line `exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`** is not cut: it is
  one premise (this set's A1) plus `qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero`,
  which the port does not hold. That row is AF44's head by measurement.
- **The other `CuspForm` shelf rows** are left, named with their sizes: `HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash`
  (582, leaf), `exists_finset_dirichlet_sum_eq_and_independent_of_gammaH` (340), `exists_gamma1_qCoeff_eq_ite_coprime`
  (339), `peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff` (249), `HasNebentypus.sum_filter_eq_of_sum_eq`
  (185), `exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` (168), `exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj`
  (126), `exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` (69), `exists_gammaH_coe_eq_of_hasNebentypus`
  (68), `exists_gamma1_coe_eq_of_gammaH` (51) — 2,177 silo of the same layer, a later set.
- **`CohCarrier`'s own surface** and the `ModularCurve` diamond-pullback rows are untouched.
