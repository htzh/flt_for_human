# SET-AF4 — the norm side of the adèle ring: the idèle norm's values, the height, and the norm product

**Status: landed 2026-11-02**, ported by the manager in one session (§1.5 records the landing, §8 the
measured re-read). This is the fourth `AutomorphicForm`-serving set and the first one whose shelf rows
are **not** in the `AutomorphicForm` namespace: the column's next move was not another AF proof module
but the small definition-and-norm layer that six large AF rows were one premise short of.

The set is **four declarations of definition ground and five shelf rows** —
`finitePartUnits`, `unitIdeles` + `mem_unitIdeles_iff`, `uniformizerIdele` (≈23 pin lines) and

- 49 `ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles` (ready),
- 39 `ideleNorm_uniformizerIdele` (ready),
- 115 `ideleNorm_det_eq_prod_archDetNorm_pow_mult` (ready),
- 146 `continuous_adelicHeight` (leaf),
- 179 `tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top` (leaf),

which together are **528 raw `S_` lines → 109 net new math lines** (323 lines are already in the
port: 80 statement-diffed and 243 tier-3 engine), and whose landing makes **eight rows ready
(9,350 silo)** — including the D–S cone's largest single row, `bigCell_eq_sum_pureTensor_of_flat_family`
(5,407 silo), which is waiting on exactly the 49-line one.

§0 the read and the instrument that chose the cut; §1 the cut and its pricing; §2 what the rows say;
§3 homes; §4 ground prep; §5 traps; §6 gates; §7 calls (including the three AF families this defers);
§8 reproduce and the forecast; §9 what it does not do. **Appendix A** lists all 56 ready rows with
each one's readiness return; **Appendix B** all 253 leaves.

## 0. The read

### 0.1 The canonical read, and the corrected one

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af4.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af4-corr.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS** — 1,345 `Thm_` sources, 1,510 declared names, 1,510 / 755,896 raw `S_` lines.

| figure | instrument's read | **corrected read** | SET-AF3 §8 (corrected) |
|---|---:|---:|---:|
| `needed [F terminal]` | 905 / 371,470 | **906 / 371,498** | 906 / 371,498 |
| `needed [literal]` | 918 / 374,945 | **919 / 374,973** | 919 / 374,973 |
| frontier F (union) | 1,510 / 755,896 | **1,509 / 755,868** | 1,509 / 755,868 |
| … of F, inside the cone | 1,185 / 607,228 | **1,184 / 607,200** | — |
| port cone / avoided R | 2,103 / 982,173 · 140 / 74,620 | same | same |
| ready rows, all namespaces | 55 / 10,943 | **56 / 10,971** | 56 / 10,971 |
| leaves, all namespaces | 252 / 62,934 | **253 / 62,962** | 253 / 62,962 |
| `AutomorphicForm` ready rows | 27 / 6,248 | **25 / 5,487** | 25 / 5,487 |
| `AutomorphicForm` leaves | 81 / 16,570 | **82 / 16,598** | 82 / 16,598 |
| `AutomorphicForm` demand | 402 / 169,277 | **402 / 169,277** | 402 / 169,277 |
| withheld by the FR-0044 guard | 4 / 831 | **4 / 831** | 4 / 831 |

**This read is SET-AF3's own post-landing re-read**, so the brief opens on a measured delta and not on
a stale absolute: §8 of that brief quotes exactly these corrected figures, and the raw column is the
AF2 shadow again (§0.2). The withheld block is unchanged: the two Tate-module rows (327 + 283), the
`Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` row (126) and the `Pic0` torsion
finiteness (95) — the prunable complex-analytic subject, not this column's.

### 0.2 The correction

The instrument's read differs from the corrected one by exactly the AF2 shadow:
`AutomorphicForm.continuous_unipotentGL2` (28 silo) is a pin node shadowed by SET-AF2's
`private continuous_unipotentGL2`, so the raw read reports 905 / 371,470 and puts the two AF2 shadow
rows (471, 290) on the ready shelf; `--unport AutomorphicForm.continuous_unipotentGL2` restores
906 / 371,498 and 25 / 5,487. **SET-AF3's landing added no shadow** (its §8 checked its own private
names against the unported last names), so the correction is one node, unchanged since AF2.

### 0.3 The instrument that chose the cut: readiness return

The recipe ranks by silo and leverage. On this shelf both are the wrong key. The shelf's rows are
mostly *premises* of large unported rows, and the quantity that matters is:

> **return(r)** = the silo of the unported rows of the D–S cone whose **unported premise set is
> exactly `{r}`** — i.e. the rows that become ready the moment `r` lands.

It is computed from the same graph: for every unported node of the cone, take its premises that are
still unported; a row with a single such premise is waiting on exactly that shelf row. The top of the
result (Appendix A has all 56):

| shelf row | silo | return | the row(s) it would ready |
|---|---:|---:|---|
| `NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles` | **49** | **5,407** | `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` |
| `NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top` (leaf) | 179 | 2,640 | `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` 1,349 + `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_…` 1,291 |
| `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` (leaf) | 21 | 2,884 | the two `archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` (1,246, 1,248) + 390 |
| `NumberField.AdelicHeight.continuous_adelicHeight` (leaf) | 146 | 2,423 | 1,043 + 624 + 431 + 325 |
| `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` (leaf) | 123 | 2,113 | six rows, 635 … 277 |
| `AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective` (leaf) | 70 | 1,445 | 1,175 + 190 + 80 |
| `AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex` (leaf) | 401 | 1,443 | 1,227 + three Casimir rows |
| `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | 32 | 1,161 | five rightConv rows, incl. `continuous_rightConv_of_continuous_of_hasCompactSupport` |
| `AutomorphicForm.exists_mem_adelicBorel_mul_eq` | 372 | 1,014 | seven rows, 245 … |
| `AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 990 | `adjoint_rightConv_weightedPairing_…` 661 + 217 + 112 |

**Return per silo is the ranking, and it is not silo's order.** The 49-line row buys 5,407 lines; the
1,745-line arch-derivative family buys 1,443. This is the recipe's §7 metric (`which rows became ready
because of the set`) read *before* the set instead of after it.

### 0.4 The declaration-level gate, and the one it hides

`spec/gate_scan.py` over the five rows' `Def_` closures:

| row | gate module | used-and-missing | pin lines |
|---|---|---|---:|
| 49 | `NumberField_IdeleBox` | `finitePartUnits` | 2 |
| 49 | `IsDedekindDomain_FiniteUnitIdeles` (**not imported by the row**) | `unitIdeles`, `mem_unitIdeles_iff` | 19 |
| 39 | `AutomorphicForm_HeckeEigenfunction` | `uniformizerIdele` | 6 |
| 115 | — | none (0 missing) | 0 |
| 146 | — | none (`AdelicHeight` is ported, 6/27 used) | 0 |
| 179 | — | none (a mathlib-asymptotics proof) | 0 |

**The second line is the one that matters.** The 49-row's *statement* says
`finitePartUnits … ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles`, but its wrapper imports only
`Def_NumberField_TateGlobalZeta` and `Def_NumberField_IdeleBox`; `unitIdeles`/`mem_unitIdeles_iff` are
transcribed in the port-absent `Def_IsDedekindDomain_FiniteUnitIdeles` and reach the row through
*that module's own imports*. Neither `gate_scan` (which reads only the named `Def_` module) nor
`port_advise --with-defs` (which closes only over the wrappers' direct `Definitions/` imports) sees
it; the hand read of the statement did. Recorded as FR-0099.

The gate of the whole set is therefore **four declarations / ≈27 pin lines in three pin modules**, and
nothing else: `twin_scan` says all five rows are `new`, and every other declaration they use is in
the port (68 trusted substitutions, 3 suspect).

### 0.5 What the five rows are waiting on, and what their consumers are

All five rows are **ready** (`needed = 1` for the three ready ones, leaves for the other two):
premises 1, 1, 1, 0, 0. Their consumers are not all gate-free, and the brief must say which:

| consumer | silo | remaining gate after this set |
|---|---:|---|
| `bigCell_eq_sum_pureTensor_of_flat_family` | 5,407 | **none** |
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1,349 | **none** |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1,291 | **none** |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | **none** — `uniformizerIdele` is the *whole* of the `HeckeEigenfunction` gate (FR-0093 check: `gate_scan` reports 1/8 used, that one missing) |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | **none** |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | **none** |
| `ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 63 | **none** |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | **none** |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1,043 | `UnramifiedWhittaker_HeckeRecursion.placeEmbed` (8 pin lines) |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | **none** (`WeylSelectors` is 29/39 used, **0 missing**) |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | `FnTwist.isSmoothVector_rightTranslationFn_mul` (22 pin lines) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | `RationalCentreUnipotentQuotient` (13 pin lines: `rationalCentre`, `rationalCentreUnipotent`, `rationalCentreUnipotentHaar`) |

**This table was wrong when the brief was cut, and the landing paid for it.** Three of the four rows
were priced from the *module-level* import census instead of `gate_scan` — the very over-report FR-0096
names: `WeylSelectors` turned out to have 0 missing declarations (624 is gate-free), and the two real
gates are larger than claimed (22 and 13 pin lines, not 4 and 5). The cut, the pricing and the
forecast are unaffected; the *writability* of three rows is (FR-0100).

## 1. The cut

### 1.1 The story

The idèle norm `ideleNorm` is the product of the normalized absolute values, and the adelic height
`adelicHeight` is built from the same local factors. This set is that object's **evaluation and
continuity layer**:

1. on the units of the finite adèles — `finitePartUnits u ∈ unitIdeles` forces every finite
   component to have norm `1`, so the norm is the archimedean product, and with trivial archimedean
   part it is `1` (49);
2. on the uniformizer idèle — `|uniformizerIdele v| = |absNorm v|⁻¹` (39);
3. on a determinant — for `X` with integral finite part,
   `|det X| = ∏_w archDetNorm w X ^ w.mult` (115);
4. the height is **continuous** (146);
5. and the finite-support norm product `k ↦ ∏_v absNorm(v)^{k v}` is summable for `t > 1` (179) —
   the geometric series that every Euler-product bound in the column consumes.

That is one chapter — the norm's values and the norm's bounds — and it is the last piece of
vocabulary the flat-family and Weil-integrand rows need before their own proofs can start.

### 1.2 The steps

| step | node | namespace | silo | net | gate | order |
|---|---|---|---:|---:|---|---|
| **G1** | `finitePartUnits` (IdeleBox) | `NumberField.AdeleRing` | 2 | ~3 | — | manager |
| **G2** | `unitIdeles`, `mem_unitIdeles_iff` (FiniteUnitIdeles) | `IsDedekindDomain.FiniteAdeleRing` | 19 | ~19 | — | manager |
| **G3** | `uniformizerIdele` (HeckeEigenfunction) | `AutomorphicForm` | 2 | ~2 | — | manager |
| **N1** | `ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles` | `NumberField.TateGlobal` | 49 | 29 | G1, G2 | worker |
| **N2** | `ideleNorm_uniformizerIdele` | `NumberField.TateGlobal` | 39 | 27 | G3 | worker |
| **N3** | `ideleNorm_det_eq_prod_archDetNorm_pow_mult` | `NumberField.TateGlobal` | 115 | 0 | — | worker |
| **N4** | `continuous_adelicHeight` | `NumberField.AdelicHeight` | 146 | 49 | — | worker |
| **N5** | `tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top` | `NumberField` | 179 | 8 | — | worker |
| | **8 steps** | | **528 + 23** | **≈133** | | |

The per-row nets are the single-node `port_plan` readings and they sum to 113, against the set's 109
(its own dedup removes the shared prelude): N1 29, N2 27, N3 **0** (`port_advise` finds the whole proof
already in the port as tier-3 declarations — 93 of 115 lines), N4 49 (74 of 146 in port), N5 **8**
(150 of 179 in port). N3 and N5 are pure assembly rows.

### 1.3 Pricing

```bash
python3 port_advise.py --with-defs --nodes <the five> --json build/af4-norm-advise.json
python3 port_plan.py --json build/af4-norm-advise.json
```

**528 raw `S_` lines − 87 boilerplate = 441 declaration lines − 9 duplicate copies = 432 once-cost −
323 already in the port = 109 net new math lines.** The 323 is 80 statement-diffed + **243 tier-3**
lines: the port already has the norm-composition and height-estimate lemmas, unchecked but built, and
this set is mostly the assembly of them into the five statements. 68 substitutions are trusted, 3
suspect; the *port once* block is empty (no name is proved in two of the five files). The
`--with-defs` closure is four modules, and the manager's part is the 4 declarations §0.4 prices.

**This is the cheapest big-return set on the shelf.** For comparison, the three families SET-AF2 §9
predicted as the column's next sets cost 1,190 / 1,393 / 1,406 net lines for returns of 1,443 /
~0 / ~0 (§7).

### 1.4 The lanes

| order | who | steps | file | why |
|---|---|---|---|---|
| **1** | manager | G1, G2, G3 | `TateGlobal/Defs.lean` (2 defs), new `FiniteIdeles.lean` (2) | the rows cannot be *stated* before them; the 468-row's gate closes with G3 |
| **2** | worker | N1, N2, N3 | new `TateGlobal/IdeleNormValues.lean` | one subject: the norm's values on the three kinds of idèle |
| **3** | worker | N4, N5 | insertions: `AdelicHeight.lean`, `TateGlobal/PlaceSum.lean` | the height and the norm product are already modules of their own |

Orders 2 and 3 are disjoint files; only the manager's defs are shared, and they land first.

### 1.5 The landing — the manager ported the whole set

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| G1, G2 | `NumberTheory/NumberField/FiniteIdeles.lean` (**+65**; `unitIdeles`, `mem_unitIdeles_iff`, `finitePartUnits`) | **3 ok** / 0 / 0 | silent, 3.0 s | clean |
| G3 | `TateGlobal/Defs.lean` (**+20**; `uniformizerIdele`) | **16 ok** / 0 / 0 | silent | clean |
| N1, N2 | `TateGlobal/IdeleNormValues.lean` (**+98**; 2 public + 3 private) | **2 ok** / 0 / 0 | silent, 3.1 s | clean ×2 |
| N3 | `AutomorphicForm/Adelic/IdeleNormDetGlue.lean` (**+138**; 5 promoted helpers + headline) | **6 ok** / 0 / 0 | silent, 3.6 s | clean |
| N4 | `NumberTheory/AdelicHeight.lean` (**+143**; 11 public) | **39 ok** / 0 / 0 | silent | clean |
| N5 | `AutomorphicForm/Adelic/WeylIntegrable/NormProdSum.lean` (**+39**; 1 public) | **1 ok** / 0 / 0 | silent, 2.9 s | clean |
| — | consumer probe `spec/SetAF4NormConsumer.lean` (**+65**, 4 examples, 2 zones) | — | 0 errors | — |

**What the set consumed**: 528 silo of rows (109 net priced) + 23 pin lines of ground — **340 new
source lines** in four new modules and 163 inserted lines in two, against the 133 net priced; the
extra is the pinned glue block of N3, which the port moved rather than imported (§1.5's dedup note).
`dedup --within` **0 clusters** in all six; `dedup --cross` 0 involving the set; `move_dead --dry-run`
**0 declarations / 0 lines** in all six. No marker, no migration, no tree build.

**Deviations from the plan, all forced by the tree:**

- **N3's home is `AutomorphicForm/Adelic/IdeleNormDetGlue.lean`, not the `NumberField` tree.** The
  statement's hypothesis is `AdelicGL2 (𝓞 F) F`, whose home is `AutomorphicForm/Adelic/Basic`; a
  `NumberField` module cannot import it (`AutomorphicForm → NumberTheory`, never back). The pin puts
  its copy on the same side.
- **N3 was a duplicate before it was a row.** `AutomorphicForm/Adelic/Siegel/SlabCovering.lean`
  carried the whole six-declaration block `private`, and the pin's `_pow` helper is
  statement-identical to its `_pow_mult` headline. The port now has **one** copy: the glue module
  holds the five helpers public and the headline at the wrapper's name, `SlabCovering` imports it
  (its own private block deleted, −91 lines, its ℚ specialisation now uses the public headline), and
  `SlabCoveringTheorems` rebuilt green. `dedup` cannot see a private copy, so this was a hand find
(FR-0101).
- **N5's home is `AutomorphicForm/Adelic/WeylIntegrable/NormProdSum.lean`, not `PlaceSum.lean`.** The
  engine (`normProd`, `idealOf`, `idealCount`, `zetaTerm`, `tsum_normProd_rpow_neg_lt_top`) is already
  transcribed in `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean`; `PlaceSum.lean` is on
  the `NumberField` side and could not import it. The one-declaration module states the pin's leaf and
  applies the engine.
- **`finitePartUnits` is homed with `unitIdeles`** (`FiniteIdeles.lean`) rather than in `Defs.lean`:
  it is the projection onto `(FiniteAdeleRing R K)ˣ`, which is the subgroup `unitIdeles` describes.
  `Defs.lean` still needed a pin wire for `uniformizerIdele` only.
- **`uniformizerIdele` keeps the pin's explicit `F`** (`variable (F : Type)` in a `section Defs`), as
  the wrapper's statement spells it `uniformizerIdele F v`; with the `{F}` binding the statement is
  right but the application sites are not.
- **N4**: the pin's `P6B.RFCSol` proof-search namespace is dropped; the deprecated
  `mul_lt_one_of_nonneg_of_lt_one_left` is replaced by `mul_lt_mul_of_pos_right` + `linarith`; the
  `_impl` helper is folded into the headline (its statement equals the wrapper's, and two copies would
  be a dedup cluster).

**`Siegel/SlabCovering.lean` was brought up to standards in the same touch** (it is touched by N3's
refactor and `instructions.md` requires it): **60 per-declaration `-- pin:` markers removed, six
`spec-pin:` wires in** (the three wrappers + their three `S_` files), checker **3 ok / 0 / 0** (its 52
private declarations are not diffed), silent rebuild and silent dependent, register 113 → **112**
modules (it leaves it: tier 1 now). It had two **pre-existing dead private declarations**, both
unreachable from its public API and neither carrying mathematics the public statement does not: the ℚ
specialisation `ideleNorm_det_eq_archDetNorm_rat` (a one-line corollary of the now-public general
theorem) and the one-line inclusion `openShell_subset_shellIdeles` — both **deleted** (a shelf move
would preserve content that is derivable in a line; the `Reserve/` shelf is for dead code that *is*
mathematics). `move_dead --select dead` now reports **0 declarations / 0 lines**. Its one dedup cluster
(`exists_finset_central_covering_of_point_of_stable_of_decomposition` 57 lines vs its `centreCut`
sibling 25) is the pin's own two-statement pattern and stays, per the recipe.

## 2. What the rows say

**N1 (49).** For `u ∈ (𝔸_F)ˣ` with trivial archimedean component and finite part in `unitIdeles`,
`ideleNorm F u = 1`. The proof unfolds `ideleNorm` as
`distribHaarChar = ∏_w ‖·_w‖^{w.mult} · ∏'_v ‖·_v‖` (already in the port), kills the archimedean
product by `harch`, and gets `‖u_v‖ = 1` at every finite `v` from the two integrality halves of
`mem_unitIdeles_iff` plus `mul_le_mul_of_nonneg_left`. Three private helpers, 49 lines.

**N2 (39).** `ideleNorm F (uniformizerIdele F v) = (absNorm v.asIdeal : ℝ)⁻¹`: the uniformizer idèle
is `localUnit v (uniformizerUnit v)` at `v` and `1` elsewhere, so the product collapses to the single
factor, which is `‖ϖ_v‖` and equals the inverse absolute norm. Needs G3.

**N3 (115).** For `X : GL₂(𝔸_F)` with integral finite part,
`ideleNorm F (det X) = ∏_w archDetNorm w X ^ w.mult`. The proof compares the two sides componentwise:
`norm_eq_zpow_of_valued`, `valued_det_le_one` (the finite part is integral, so `‖det‖ ≤ 1` and
`‖det⁻¹‖ ≤ 1`), `det_snd_apply`, `det_fst_apply`. `port_advise` prices it at **0 net new lines**: the
`IdeleNormDetGlue` development is in the port already, and the row is its assembly.

**N4 (146).** `Continuous (adelicHeight F)`. The pin's `P6B.RFCSol` block: `gl_coe_mul`,
`rowMaxNorm_mul_le`, `rowMaxNorm_mul_integral`, `norm_det_eq_one_of_integral`,
`finLocalHeight_mul_integral`, `finHeight_mul_integral`, and the limit argument. `twin_scan` finds
4/12 of the file's declarations already in the port.

**N5 (179).** `∑' k : HeightOneSpectrum →₀ ℕ, (∏_v absNorm(v)^{k v} : ℝ≥0∞)^{-t} < ⊤` for `t > 1`. The
pin proves it in a local `AutomorphicForm.WeylIntegrable` block: `normProd`, `idealOf`
(`k ↦ ∏ v.asIdeal^{k v}`), `absNorm_idealOf`, `countable_ideal`, the ideal-count `idealCount`/
`zetaTerm`, `summable_zetaTerm` from the p-series, `tendsto_sum_idealCount_div` and the fibre identity
`tsum_fibre_card_mul`. 16 of its 17 declarations are already ported (`prelude 16/17`); the row is the
last one.

## 3. Homes

| # | module | holds | kind |
|---|---|---|---|
| 1 | `NumberTheory/NumberField/FiniteIdeles.lean` (new) | `unitIdeles`, `mem_unitIdeles_iff`, `finitePartUnits` | new |
| 2 | `NumberTheory/NumberField/TateGlobal/Defs.lean` | `uniformizerIdele` | insertion |
| 3 | `NumberTheory/NumberField/TateGlobal/IdeleNormValues.lean` (new) | N1, N2 | new |
| 4 | `AutomorphicForm/Adelic/IdeleNormDetGlue.lean` (new) | N3 + the five shared helpers | new |
| 5 | `NumberTheory/AdelicHeight.lean` | N4 | insertion |
| 6 | `AutomorphicForm/Adelic/WeylIntegrable/NormProdSum.lean` (new) | N5 | new |

**Why these homes.** `FiniteIdeles.lean` is "the finite units of the idèle group", and
`finitePartUnits` is the projection onto exactly that group, so the three declarations belong together
even though they come from two pin modules. `Defs.lean` already defines `ideleNorm`, `zetaIntegral`,
`localChar`, `archUnitHom` — it *is* the idèle-norm definitional ground, and `uniformizerIdele` keeps
the pin's `AutomorphicForm` namespace there (namespace ≠ module: the `NumberField` tree must not
import `AutomorphicForm`). `IdeleNormValues.lean` is the "values of the norm" story. N3 goes on the
`AutomorphicForm` side because its hypothesis is about `AdelicGL2`, and it *replaces*
`SlabCovering`'s private copy of the same block (§1.5). N4 belongs to the height module (all its
premises are there); N5 belongs beside its engine in `WeylIntegrable/`.

**Import direction.** Every destination sits above its premises: `Defs.lean` already imports
`AdelicLevel/HeckeGen` (for `localUnit`/`uniformizerUnit`); `FiniteIdeles.lean` imports mathlib's
`NumberField.AdeleRing` + `AdicValuation` (for `FiniteAdeleRing`/`adicCompletionIntegers`);
`IdeleNormValues.lean` imports `FiniteIdeles`, `Defs` and `AdelicModulus`; `IdeleNormDetGlue.lean`
imports `AutomorphicForm/Adelic/Basic` (for `AdelicGL2`) plus the four `NumberTheory` modules it uses;
`NormProdSum.lean` imports `LatticeEstimates`. No cycle: the two `AutomorphicForm`-side new modules are
leaves of the import graph.

**No legacy module, no migration.** `AdelicHeight.lean` and `Defs.lean` are wired by their own
`spec-pin:` headers (part of the 2026-11-02 sweep), so both insertions are ordinary tier-1 edits. The
one *promotion* is the pinned glue block of N3 (five pin-private helpers made public at the pin's
names, checker `ok` through the pin-private fallback) — it is a promotion by the checker's own
reading, and it deleted a private duplicate in the same touch.

## 4. Ground prep (the manager's)

### 4.1 The four definitions (this set's `Def_*` work)

| declaration | pin | lines | note |
|---|---|---:|---|
| `NumberField.AdeleRing.finitePartUnits R K : (AdeleRing R K)ˣ →* (FiniteAdeleRing R K)ˣ` | `Def_NumberField_IdeleBox.lean:96` | 2 | `Units.map (RingHom.snd …)`; the ℚ twin `finPart` is in `RatIdele/Normalizer.lean` (FR-0093: do not re-derive, do not rename) |
| `IsDedekindDomain.FiniteAdeleRing.unitIdeles R K : Subgroup (FiniteAdeleRing R K)ˣ` | `Def_IsDedekindDomain_FiniteUnitIdeles.lean:9` | 13 | integral element **and** integral inverse at every finite place |
| `…mem_unitIdeles_iff` | `…:24` | 6 | `Iff.rfl` |
| `AutomorphicForm.uniformizerIdele F v` | `Def_AutomorphicForm_HeckeEigenfunction.lean:31` | 2 | `Units.map (finIncl) (localUnit v (uniformizerUnit v))` |

`unitIdeles`'s `@[simp]`-free `Iff.rfl` lemma is the one the rows rewrite with; keep the pin's name
and statement. The pin's other `IdeleBox` declarations (`unitsComponent`, `finiteUnitsComponent`,
`infiniteUnitsComponent`, `ideleBox`, …) are **not** in this set: the declaration-level gate is what
the rows name, and `ideleBox` has no consumer on the shelf yet.

### 4.2 Wires

- `FiniteIdeles.lean` gains `spec-pin: Definitions/Def_IsDedekindDomain_FiniteUnitIdeles.lean` and
  `spec-pin: Definitions/Def_NumberField_IdeleBox.lean` (it holds declarations of both).
- `Defs.lean` gains `spec-pin: Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean` (its existing
  `Def_NumberField_TateGlobalZeta` line stays).
- Each row's module gains its two lines (wrapper + `S_` `-- comparable copy`), as in SET-AF2/AF3 —
  twelve wire lines in all (6 for the defs, 2 per row for N1/N2, 2 for N3, 2 for N4, 2 for N5).
- **As built**: 14 wire lines — `AdelicHeight.lean` also carries N4's, and `IdeleNormDetGlue.lean`'s
  two cover the promoted helpers as well.
- No marker is expected anywhere: every declaration is at the pin's name and namespace. If the
  `AutomorphicForm`-namespaced `uniformizerIdele` in a `NumberField` module trips the checker's
  namespace tracker, the fix is a `spec-pin:` line and nothing else (the checker matches by last name
  and statement hash, not by module).

### 4.3 The consumer zone (after the landing)

`spec/SetAF4NormConsumer.lean` (a `spec/` probe, not a library module), two zones:
- **A** — the three norm values composed: `N1` applied to a unit idèle, `N2` at a uniformizer, and
  `N3` at a determinant with integral finite part, all rewritten into one `ideleNorm` expression;
- **B** — the height and the norm product: `N4`'s continuity read on a concrete sequence against the
  summability bound of `N5`, at a fixed `t > 1`.
The zone's error count is the metric; deleting any of the modules must break it.

### 4.4 After the landing

`dedup.py --within` on each module, `dedup.py --cross` over the five and the engines they import,
`move_dead.py --source … --target lean/Reserve/AF4/… --select dead --dry-run` on each (expect
`0 declarations, 0 lines`), `unwired_register.py --check`, the §8 re-read (twice: instrument and
`--unport`), and the FR-0095 shadow diff of the new modules' `private` names against the unported
last names.

## 5. Traps

**N1 (49).** The statement's hypothesis is `finitePartUnits … ∈ unitIdeles`, not the bare integrality
conjunctions — use `mem_unitIdeles_iff` to get them, and both halves (the element *and* its inverse).
`ideleNorm` is `distribHaarChar`, and the product identity is
`distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` (in the port); `harch : (u : AdeleRing …).1 = 1`
kills the archimedean factors by `Finset.prod_eq_one`. The three private helpers are the pin's
(`norm_le_one_of_mem` from `Valued.toNormedField.norm_le_one_iff`).

**N2 (39).** The uniformizer idèle is `1` at every place but `v`; the `Finsupp`/`finprod` collapse is
the whole proof. `norm_coe_uniformizerUnit` is the pin's private helper. Do **not** re-derive
`uniformizerIdele` (G3).

**N3 (115).** `port_advise` prices this at 0 net: the `IdeleNormDetGlue` block is in the port as
tier-3 declarations. Find them by last name (`norm_eq_zpow_of_valued`, `valued_det_le_one`,
`det_snd_apply`, `det_fst_apply`) before writing anything; a re-derivation here would be the set's one
easy duplication. The hypothesis `glFin X ∈ finiteIntegralGL2` is what gives `‖det‖ ≤ 1` at the
finite places, and `‖det X · det X⁻¹‖ = 1` closes the other side.

**N4 (146).** The pin's `P6B.RFCSol` namespace is a proof-search label: drop it, keep the names. The
row's content is the submultiplicativity `finHeight (g * k) ≤ finHeight g * finHeight k` on the
integral part and the limit along the neighbourhood filter of `1`; the port has 4 of the 12
declarations and the `finHeight` API. `Continuous (adelicHeight F)` is stated for the product topology
on `AdelicGL2` — do not restate it on the `AdeleRing` product.

**N5 (179).** The pin proves it inside `AutomorphicForm.WeylIntegrable`; the statement is
`NumberField.` — keep the statement's namespace and drop the proof namespace. `idealOf k = ∏ v.asIdeal^{k v}`
and `absNorm_idealOf` are the dictionary to the ideal-count function; `summable_absNorm_rpow_neg`
(`PlaceSum.lean`) is the p-series input, and the fibre identity `tsum_fibre_card_mul` is what turns
the ideal count into the exponent sum. `t > 1` is used only through `Real.summable_one_div_nat_rpow`.

## 6. The gates

1. `check_port --force` on the two new modules and the two edited ones: **0 mismatch, 0 missing**;
   the manager's defs land **first** and must be `ok` before the rows are written (the four rows' own
   counts: 1 each).
2. `#print axioms` on the five headlines → `[propext, Classical.choice, Quot.sound]`.
3. Each module's own `lake build` under `flock`/`timeout 110`, silent, zero warnings; the two
   insertions rebuild `AdelicHeight`/`PlaceSum` and nothing else.
4. `dedup.py --within` and `--cross`; `move_dead.py --dry-run` (0 declared dead).
5. No `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats` (nothing here needs one).
6. The consumer zone of §4.3 at 0 errors, load-bearing.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **the norm/height five: 528 silo / 109 net / ≈27 pin lines of ground**, readying nine rows / 9,350 silo | the alternative cuts are the three AF families (see below); this one is 10× cheaper per line of readiness and includes the 5,407-line `bigCell` row |
| 2. **the shelf's own AF families** | **defer all three to the sets after this one** — they are the column's *proof* work, this is its last cheap ground | arch-derivative chain: 10 rows / 2,212 silo / ≈1,190 net / **return 1,443**; `LocalIntertwining`: 8 / 1,578 / 1,393 net / return 729; `CuspidalConstituent`: 9 / 1,593 / 1,406 net / return 28 |
| 3. **the three definition gates** | **a later manager order**: `placeEmbed` 8, `RationalCentreUnipotentQuotient` 13, `FnTwist.isSmoothVector_rightTranslationFn_mul` 22 | each closes one consumer of this set (1,043 / 179 / 325); 43 pin lines, and the middle one is a `Def_` module with five declarations |
| 4. **`WeylSelectors`** | **no action**: the landing's `gate_scan` shows 29/39 used and **0 missing**, so 624 was never gated | nothing to port |
| 5. **the homes** | **one new def module, one new proof module, three insertions** | the defs cannot go in `AutomorphicForm` (import direction) and the rows' subjects are already modules |
| 6. **the dispatch** | **manager defs, then two worker lanes** (values; height+product) | the lanes are disjoint files and only share the defs |

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af4.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af4-corr.json
python3 frontier.py --selfcheck
python3 port_advise.py --with-defs --nodes <the five> --json build/af4-norm-advise.json
python3 port_plan.py --json build/af4-norm-advise.json                        # 109 net
python3 twin_scan.py --node <each of the five>                                 # new × 5
# the readiness return (§0.3) is a graph query, not a tool flag:
#   for each unported node of the cone, take its unported premises; keep rows with exactly one.
# from lean/, the declaration gates:
python3 spec/gate_scan.py --pin Definitions/Def_NumberField_IdeleBox.lean \
    --rows S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean \
    --rows S_NumberField_TateGlobal_ideleNorm_uniformizerIdele
```

**What the set consumed**: 528 silo of rows (109 net priced) + 23 pin lines of ground — **340 new
source lines** in four new modules and 163 inserted, 12 wire lines, one promotion (the N3 glue block)
that deleted a private duplicate, no migration, no marker, no tree build (§1.5).

**Measured after the landing — twice**, as §4.4 requires:

| figure | before | forecast | measured (raw) | **measured (corrected)** |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 906 / 371,498 | 901 / 370,970 | 900 / 370,942 | **901 / 370,970** ✓ |
| `needed [literal]` | 919 / 374,973 | 914 / 374,445 | 913 / 374,417 | **914 / 374,445** ✓ |
| frontier F | 1,509 / 755,868 | — | 1,515 / 756,424 | **1,514 / 756,396** |
| ready rows, all namespaces | 56 / 10,971 | 61 / 20,118 | 66 / 22,656 | **66 / 22,656** |
| leaves, all namespaces | 253 / 62,962 | 251 / 62,637 | 251 / 62,637 | **251 / 62,637** ✓ |
| `AutomorphicForm` ready rows | 25 / 5,487 | 32 / 14,774 | 37 / 17,312 | **37 / 17,312** |
| `AutomorphicForm` leaves | 82 / 16,598 | 82 / 16,598 | 82 / 16,598 | **82 / 16,598** ✓ |
| `--selfcheck` | PASS | — | PASS (1,350 `Thm_` / 1,515 names) | PASS |

`needed` and the leaf figures are exact. The **ready** figures are larger than forecast for two
reasons, both of them the shelf's, not the set's: a thirteenth row
(`SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_…`, 367 silo) was waiting on the
determinant row too and was missed by the §0.3 instrument (it had no *single* unported premise — it had
several, all inside the set); and the three rows §0.5 called gated (1,043 / 325 / 179) are **on the
shelf regardless**, because the frontier's ready test is premise-based and cannot see a definition
gate (FR-0049). Writable among the thirteen: **ten** (the eight of the table below plus 624 and 367);
gated: 1,043 (`placeEmbed` 8), 325 (`isSmoothVector_rightTranslationFn_mul` 22), 179 (RationalCentre
13).

**The rows this set readies** — thirteen on the shelf, 11,888 silo, of which ten (10,341 silo) are
gate-free:

| row | silo |
|---|---:|
| `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` | 5,407 |
| `AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1,349 |
| `AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1,291 |
| `AutomorphicForm.a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 |
| `AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 |
| `AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 |
| `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 63 |
| `AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 |
| `AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` (gate-free, §0.5 corrected) | 624 |
| `AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` (the missed one) | 367 |
| `AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (gated: `placeEmbed` 8) | 1,043 |
| `AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection` (gated: 22) | 325 |
| `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` (gated: 13) | 179 |
| **total (13 rows)** | **11,888** |

and the 384-line leaf `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing`
becomes **writable** (its `HeckeEigenfunction` gate is G3, the same declaration).

## 9. What this set does not do

- **The three AF families.** The arch-derivative chain (return 1,443), `LocalIntertwining` (729) and
  `CuspidalConstituent` (28) are measured in §7 call 2 and stay the column's next three sets — in that
  order. This set is ground and norm evaluation; those are the proofs, and per line of readiness the
  chain is the only one of the three that pays.
- **The 5,407-line `bigCell` row it readies.** Ready is not landed: it is a row of its own, with its
  own set (and it is the cone's largest single row — its brief must price it alone).
- **The three remaining definition gates** (§0.5, corrected at landing): `placeEmbed` 8,
  `RationalCentreUnipotentQuotient` 13, `FnTwist.isSmoothVector_rightTranslationFn_mul` 22. They are a
  **definition sweep** of 43 pin lines, to be bundled with whatever set first needs them; this one
  closed only `HeckeEigenfunction` (and `IdeleBox` + `FiniteUnitIdeles`).
- **`ideleBox`/`unitsComponent`/`infiniteUnitsComponent`**, the rest of the two `Def_` modules: no
  shelf row names them.
- **The 384-line Peterson leaf and the HeckeEigenfunction row**: writable, not written.
- **Anything behind the prunable complex-analytic subject**: the withheld 4 / 831. No new `Def_`
  module beyond §4.1, no promotion, no migration, no tree build.

## Appendix A — the 56 ready rows, with each one's readiness return (**before** the landing)

The set consumed the three `ideleNorm` rows from this table; the shelf now reads 66 / 22,656 (§8).

`return` = the unported rows of the D–S cone whose **only** missing premise is this row — the
metric that chose the cut; `lev` is `leverage / leverage_project`. **◀** marks the set's rows.

| ready row | silo | prem | lev | return |
|---|---:|---:|---|---:|
| `NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles` **◀** | 49 | 1 | 3/55 | 5407 |
| `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | 32 | 1 | 22/217 | 1161 |
| `AutomorphicForm.exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | 1014 |
| `AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | 990 |
| `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` | 252 | 1 | 1/1 | 697 |
| `NumberField.TateGlobal.ideleNorm_uniformizerIdele` **◀** | 39 | 1 | 5/49 | 647 |
| `ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq` | 237 | 2 | 1/2 | 485 |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1 | 1/7 | 472 |
| `NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult` **◀** | 115 | 1 | 14/71 | 404 |
| `CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast` | 19 | 1 | 1/3 | 291 |
| `CuspForm.exists_degeneracy_gamma1_hasNebentypus` | 218 | 1 | 9/12 | 218 |
| `NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod` | 215 | 1 | 3/5 | 201 |
| `NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap` | 122 | 2 | 1/11 | 104 |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 2 | 1/3 | 80 |
| `CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div` | 348 | 3 | 1/2 | 69 |
| `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | 56 |
| `AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | 28 |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | 23 |
| `NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul` | 580 | 1 | 1/2 | 0 |
| `CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq` | 570 | 1 | 1/1 | 0 |
| `AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | 0 |
| `AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | 0 |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 3 | 1/1 | 0 |
| `AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | 0 |
| `CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero` | 351 | 1 | 1/1 | 0 |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | 0 |
| `AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | 0 |
| `AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | 0 |
| `AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | 0 |
| `CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd` | 241 | 3 | 3/4 | 0 |
| `AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | 0 |
| `AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | 0 |
| `AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | 0 |
| `AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4/12 | 0 |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1 | 1/1 | 0 |
| `AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | 0 |
| `AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | 0 |
| `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | 0 |
| `AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1/2 | 0 |
| `AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | 0 |
| `NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` | 129 | 1 | 1/2 | 0 |
| `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` | 128 | 1 | 2/2 | 0 |
| `NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero` | 128 | 2 | 1/1 | 0 |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 2 | 1/2 | 0 |
| `NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero` | 119 | 2 | 1/1 | 0 |
| `NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero` | 105 | 1 | 6/18 | 0 |
| `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` | 100 | 1 | 1/13 | 0 |
| `CuspForm.heckeULinH_comm` | 74 | 2 | 2/3 | 0 |
| `AutomorphicForm.isKfSmooth_rightConv` | 70 | 1 | 7/21 | 0 |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1 | 1/3 | 0 |
| `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | 0 |
| `CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus` | 51 | 3 | 1/3 | 0 |
| `AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | 0 |
| `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | 0 |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1 | 1/6 | 0 |
| `CuspForm.finiteDimensional_Gamma1` | 16 | 1 | 1/2 | 0 |

total 56 rows / 10971 silo

## Appendix B — the 253 leaves, 62,962 silo (corrected read, **before** the landing)

The set consumed `continuous_adelicHeight` and `tsum_prod_absNorm_…`; the shelf now reads 251 / 62,637
(§8).

All leaves, grouped by namespace; the set's leaf is marked **◀**. `return` as in Appendix A.

**AutomorphicForm** — 82 row(s), 16598 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | 21 | 17/48 | 2884 |
| `AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | 1445 |
| `AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | 8/9 | 1443 |
| `AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | 465 |
| `AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | 264 |
| `AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | 169 |
| `AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | 133 |
| `AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | 113 |
| `AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | 108 |
| `AutomorphicForm.whittakerCoefficient_unipotentGL2_mul` | 123 | 17/54 | 84 |
| `AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | 25 |
| `AutomorphicForm.constantTerm_add` | 13 | 1/2 | 14 |
| `AutomorphicForm.constantTerm_smul` | 11 | 1/1 | 11 |
| `AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 2/2 | 0 |
| `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | 0 |
| `AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | 0 |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | 0 |
| `AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | 0 |
| `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | 0 |
| `AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | 0 |
| `AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | 0 |
| `AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 2/2 | 0 |
| `AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | 0 |
| `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | 0 |
| `AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | 0 |
| `AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 1/1 | 0 |
| `AutomorphicForm.not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | 0 |
| `AutomorphicForm.isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | 0 |
| `AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | 0 |
| `AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | 0 |
| `AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | 0 |
| `AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 2/3 | 0 |
| `AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | 0 |
| `AutomorphicForm.archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | 2/2 | 0 |
| `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | 0 |
| `AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | 0 |
| `AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt` | 208 | 1/4 | 0 |
| `AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | 0 |
| `AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | 0 |
| `AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | 0 |
| `AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | 8/14 | 0 |
| `AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | 0 |
| `AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 1/1 | 0 |
| `AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | 0 |
| `AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 1/1 | 0 |
| `AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | 0 |
| `AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | 0 |
| `AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | 0 |
| `AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | 0 |
| `AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | 0 |
| `AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | 0 |
| `AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 1/1 | 0 |
| `AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | 0 |
| `AutomorphicForm.RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 1/1 | 0 |
| `AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | 0 |
| `AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | 2/3 | 0 |
| `AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | 0 |
| `AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | 2/2 | 0 |
| `AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | 0 |
| `AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | 2/3 | 0 |
| `AutomorphicForm.continuous_whittakerCoefficient` | 108 | 3/14 | 0 |
| `AutomorphicForm.existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | 0 |
| `AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | 2/3 | 0 |
| `AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | 0 |
| `AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous` | 86 | 10/17 | 0 |
| `AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 1/2 | 0 |
| `AutomorphicForm.norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | 0 |
| `AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | 0 |
| `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | 0 |
| `AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | 0 |
| `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | 0 |
| `AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | 0 |
| `AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | 0 |
| `AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | 0 |
| `AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | 0 |
| `AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | 0 |
| `AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | 0 |
| `AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | 0 |
| `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | 0 |
| `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | 0 |
| `AutomorphicForm.continuous_unipotentGL2` | 28 | 8/122 | 0 |
| `AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | 0 |

**M4aTorus** — 1 row(s), 12126 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `M4aTorus.completedRayL_fe` | 12126 | 1/2 | 102 |

**NumberField** — 48 row(s), 8933 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top` **◀** | 179 | 2/5 | 2640 |
| `NumberField.AdelicHeight.continuous_adelicHeight` | 146 | 5/73 | 2423 |
| `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` | 123 | 14/41 | 2113 |
| `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | 93 | 25/74 | 489 |
| `NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` | 118 | 1/4 | 483 |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | 440 |
| `NumberField.Units.exists_forall_abs_sub_mult_mul_log_le` | 98 | 2/2 | 214 |
| `NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` | 600 | 11/40 | 199 |
| `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | 1/1 | 154 |
| `NumberField.mixedEmbedding.trace_mixedEmbedding` | 17 | 6/8 | 118 |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | 1/2 | 0 |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | 0 |
| `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 3/4 | 0 |
| `NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum` | 381 | 1/4 | 0 |
| `NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral` | 370 | 1/6 | 0 |
| `NumberField.AdelicFourier.fourierIntegral_pureTensor_eq` | 359 | 4/8 | 0 |
| `NumberField.dedekindZeta_ne_zero_of_one_lt_re` | 357 | 6/6 | 0 |
| `NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta` | 338 | 6/26 | 0 |
| `NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` | 237 | 2/11 | 0 |
| `NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat` | 236 | 2/3 | 0 |
| `NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat` | 235 | 5/20 | 0 |
| `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one` | 233 | 1/2 | 0 |
| `NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles` | 229 | 1/2 | 0 |
| `NumberField.AdelicFourier.fourierIntegral_comp_mul_left` | 215 | 3/10 | 0 |
| `NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half` | 207 | 4/4 | 0 |
| `NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one` | 201 | 1/3 | 0 |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | 0 |
| `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | 3/3 | 0 |
| `NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero` | 161 | 1/22 | 0 |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing` | 140 | 1/2 | 0 |
| `NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` | 109 | 2/2 | 0 |
| `NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat` | 101 | 1/7 | 0 |
| `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` | 94 | 1/2 | 0 |
| `NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact` | 93 | 1/1 | 0 |
| `NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet` | 84 | 1/1 | 0 |
| `NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq` | 73 | 1/1 | 0 |
| `NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le` | 71 | 1/1 | 0 |
| `NumberField.AdelicBox.exists_denom_of_hasCompactSupport` | 70 | 1/1 | 0 |
| `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` | 69 | 7/41 | 0 |
| `NumberField.StandardAddChar.psiLocal_rat_eq_psiV` | 69 | 1/38 | 0 |
| `NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate` | 67 | 1/1 | 0 |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal` | 62 | 3/6 | 0 |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex` | 61 | 2/2 | 0 |
| `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | 1/4 | 0 |
| `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | 2/3 | 0 |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | 1/3 | 0 |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | 0 |
| `NumberField.StandardAddChar.isGlobalAddChar_stdAddChar` | 10 | 17/59 | 0 |

**LanglandsTunnell** — 18 row(s), 5597 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag` | 240 | 1/1 | 377 |
| `LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam` | 711 | 1/14 | 361 |
| `LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth` | 643 | 2/2 | 329 |
| `LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing` | 601 | 1/1 | 0 |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | 0 |
| `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | 0 |
| `LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` | 443 | 1/2 | 0 |
| `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half` | 427 | 2/2 | 0 |
| `LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori` | 420 | 2/2 | 0 |
| `LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one` | 231 | 1/1 | 0 |
| `LanglandsTunnell.TateLocal.realZeta_eq_localZeta` | 166 | 1/13 | 0 |
| `LanglandsTunnell.TateLocal.complexZeta_eq_localZeta` | 166 | 1/7 | 0 |
| `LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le` | 149 | 1/21 | 0 |
| `LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet` | 139 | 2/2 | 0 |
| `LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing` | 128 | 1/1 | 0 |
| `LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow` | 104 | 1/1 | 0 |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 45 | 4/116 | 0 |
| `LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel` | 37 | 3/100 | 0 |

**ValuationSubring** — 16 row(s), 3652 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `ValuationSubring.exists_forall_mem_and_sub_mem_nonunits` | 317 | 7/10 | 1710 |
| `ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` | 83 | 2/21 | 1105 |
| `ValuationSubring.natDegree_map_eq_card_roots_of_splits` | 174 | 1/1 | 604 |
| `ValuationSubring.tensorProduct_exists_primitive_factor` | 78 | 1/1 | 300 |
| `ValuationSubring.exists_smul_mem_of_transcendental_residue` | 262 | 1/1 | 221 |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_aeval_inv_div` | 672 | 1/1 | 138 |
| `ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin` | 259 | 3/36 | 98 |
| `ValuationSubring.mem_of_forall_mem_iff_of_subset` | 126 | 1/1 | 91 |
| `ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg` | 269 | 1/3 | 75 |
| `ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` | 57 | 1/3 | 42 |
| `ValuationSubring.exists_root_mem_of_monic` | 23 | 1/2 | 30 |
| `ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul` | 705 | 1/1 | 0 |
| `ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem` | 310 | 1/3 | 0 |
| `ValuationSubring.exists_le_forall_mem_iff_apply_mem` | 168 | 2/2 | 0 |
| `ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin` | 112 | 3/5 | 0 |
| `ValuationSubring.charP_residueField_of_liesOverPrime` | 37 | 1/27 | 0 |

**WeierstrassCurve** — 18 row(s), 2860 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | 599 |
| `WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three` | 213 | 1/1 | 572 |
| `WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j` | 496 | 1/3 | 0 |
| `WeierstrassCurve.finite_stabilizer_variableChange` | 285 | 1/10 | 0 |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three` | 256 | 1/7 | 0 |
| `WeierstrassCurve.stepCurve_stepSubgroup_two_eq` | 231 | 1/5 | 0 |
| `WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo` | 215 | 1/3 | 0 |
| `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` | 194 | 1/2 | 0 |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728` | 187 | 1/8 | 0 |
| `WeierstrassCurve.transcendental_j_perturb` | 156 | 1/2 | 0 |
| `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` | 100 | 2/41 | 0 |
| `WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero` | 70 | 1/2 | 0 |
| `WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one` | 40 | 1/3 | 0 |
| `WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model` | 34 | 1/3 | 0 |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 | 2/44 | 0 |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 | 2/51 | 0 |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one` | 26 | 1/6 | 0 |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one` | 26 | 1/6 | 0 |

**CuspForm** — 11 row(s), 2319 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` | 126 | 3/8 | 177 |
| `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` | 582 | 1/1 | 0 |
| `CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH` | 340 | 1/1 | 0 |
| `CuspForm.exists_gamma1_qCoeff_eq_ite_coprime` | 339 | 2/4 | 0 |
| `CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff` | 249 | 2/2 | 0 |
| `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` | 185 | 3/3 | 0 |
| `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` | 168 | 1/1 | 0 |
| `CuspForm.peterssonOn_add_smul_conj` | 142 | 2/2 | 0 |
| `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` | 69 | 2/3 | 0 |
| `CuspForm.exists_gammaH_coe_eq_of_hasNebentypus` | 68 | 1/2 | 0 |
| `CuspForm.exists_gamma1_coe_eq_of_gammaH` | 51 | 1/3 | 0 |

**MeasureTheory** — 14 row(s), 1962 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` | 99 | 3/6 | 431 |
| `MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` | 90 | 3/4 | 78 |
| `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` | 148 | 1/1 | 74 |
| `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | 0 |
| `MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` | 222 | 1/2 | 0 |
| `MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le` | 139 | 1/1 | 0 |
| `MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex` | 104 | 1/1 | 0 |
| `MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives` | 99 | 3/13 | 0 |
| `MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` | 98 | 2/3 | 0 |
| `MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real` | 95 | 1/1 | 0 |
| `MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` | 84 | 1/1 | 0 |
| `MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives` | 77 | 3/18 | 0 |
| `MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` | 63 | 1/1 | 0 |
| `MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top` | 18 | 1/1 | 0 |

**ContinuousLinearMap** — 7 row(s), 1539 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq` | 385 | 1/2 | 0 |
| `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | 276 | 1/1 | 0 |
| `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` | 275 | 2/4 | 0 |
| `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute` | 275 | 1/1 | 0 |
| `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | 0 |
| `ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` | 108 | 2/2 | 0 |
| `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute` | 40 | 1/2 | 0 |

**HaarQuotient** — 3 row(s), 1406 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out` | 620 | 2/7 | 302 |
| `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` | 616 | 2/48 | 0 |
| `HaarQuotient.lintegral_density_mul_eq_one` | 170 | 2/39 | 0 |

**EisensteinGeneral** — 5 row(s), 1378 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `EisensteinGeneral.Arch.exists_norm_archIntegral_le` | 233 | 2/2 | 1794 |
| `EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq` | 125 | 4/6 | 138 |
| `EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable` | 165 | 1/1 | 122 |
| `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | 0 |
| `EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero` | 189 | 2/2 | 0 |

**TateCurve** — 9 row(s), 1038 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `TateCurve.point_mul_eq_add_of_norm_eq_one` | 247 | 1/1 | 704 |
| `TateCurve.hasSum_xfun` | 17 | 3/3 | 101 |
| `TateCurve.pointX_q_mul` | 19 | 2/9 | 22 |
| `TateCurve.pointY_q_mul` | 19 | 2/7 | 22 |
| `TateCurve.nodal_xfun_yfun` | 22 | 1/1 | 13 |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | 1/1 | 0 |
| `TateCurve.tsum_succ_prod_eq_tsum_divisors` | 157 | 2/2 | 0 |
| `TateCurve.exists_zpow_mul_mem_annulus` | 69 | 1/6 | 0 |
| `TateCurve.hasSum_yfun` | 17 | 2/2 | 0 |

**ModularForm** — 6 row(s), 935 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` | 94 | 5/8 | 2352 |
| `ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 406 | 1/3 | 0 |
| `ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le` | 195 | 1/1 | 0 |
| `ModularForm.exists_levelOne_coe_eq_sum_slash` | 156 | 1/1 | 0 |
| `ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one` | 62 | 1/1 | 0 |
| `ModularForm.exists_coe_eq_of_levelOne` | 22 | 1/4 | 0 |

**UnramifiedWhittaker** — 3 row(s), 792 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor` | 380 | 3/7 | 1264 |
| `UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval` | 207 | 1/2 | 0 |
| `UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow` | 205 | 1/2 | 0 |

**IsDedekindDomain** — 5 row(s), 753 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers` | 342 | 1/5 | 1179 |
| `IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers` | 228 | 1/5 | 397 |
| `IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact` | 52 | 3/14 | 266 |
| `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` | 111 | 1/12 | 0 |
| `IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat` | 20 | 2/9 | 0 |

**LocalNewvector** — 2 row(s), 647 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` | 589 | 1/1 | 0 |
| `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization` | 58 | 1/2 | 0 |

**CohCarrier** — 5 row(s), 427 silo

| leaf | silo | lev | return |
|---|---:|---|---:|
| `CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0` | 49 | 1/11 | 587 |
| `CohCarrier.charInvolution_comp_opFamily` | 247 | 1/3 | 0 |
| `CohCarrier.H1_moduleFinite` | 74 | 1/70 | 0 |
| `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` | 32 | 1/22 | 0 |
| `CohCarrier.exists_gamma0_lift_dvd` | 25 | 1/10 | 0 |

total 253 leaves / 62962 silo
