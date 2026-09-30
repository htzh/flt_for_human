# Work order — H: the shared prelude homes, then the promotion / clash pass

**Status: ready to dispatch once phase D closes (2026-09-29).** This is the real
work order for the phase after the definitions layer. It supersedes
`TOPIC-definitions-and-homes.md` §2–§3, which named the largest blocks but not the
declaration-level work, and whose promotion list disagrees with the tool output
(see §2a). Every number and declaration below is reproduced from
`tools/deps/build/groupA_advise.json` (`port_advise.py`, 54 nodes); the raw tables
are also in `tools/deps/build/homes_tables.md`.

Regenerate the advice against the current tree before dispatch:

```bash
cd tools/deps
python3 port_advise.py --nodes "$(paste -sd, build/groupA_nodes.txt)" --json build/groupA_advise.json
```

## 0. The decided order

After the definitions layer (D):

| step | what | why here |
|---|---|---|
| **H1** | the four new prelude homes | new files, so no build cascade; the theorem sets import them instead of re-proving |
| **H2** | the 7 promotions + the 22 clash reconciliations | the only cascade; one pass, then the touched files are closed |
| **T** | the theorem sets, in this order: **S1, S2, S3, S4, S5, S7, S6, S8** | importees first; S3 needs S1+S2; S6's Galois node needs S7; S8 last |

S7 precedes S6 only because
`GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`
consumes `FrobeniusDensity.statement`; S4 and S5 are independent of everything but
S8 and could be moved earlier at no cost. Each theorem set gets its **own** work
order, written after the previous set's review (playbook §0.2) — **not** the
T0–T9 level table in `TOPIC-theorem-order.md`.

H comes before T because the pin repeats its private preludes in every `S_` file:
78 blocks are shared inside the 54 targets, **585 removable lines** by the tool's
greedy count and far more by raw span (`one_mem_strictPeriods`, 24 copies;
`T_mem_Gamma1`, 18; `det_eq`, 7). Write each once, before the theorem sets.

## 1. H1 — the four homes

Against the live tree (mid-D) the 78 shared blocks divide into **44 written once
here**, **25 already reachable in the port** (reuse/verify — includes the
definitions layer's `sum_eq` and `sum_slash_mapGL`, and the pre-existing
`one_mem_strictPeriods`, `restrictMF`, `conj_mem_Gamma1`), and **9 names / 22
declaration rows that clash** and are reconciled in H2. The four home files and
their blocks follow; the tables **are** the scope.

**Namespace, decided before writing.** Each home must export its names under the
namespace the theorem sets will use:
`Cotangent.lean` → `EisensteinSeries` (beside the D0
`ModularForms/Eisenstein/WeierstrassZeta.lean`); `FrobeniusDensity/Basic.lean` →
`FrobeniusDensity`; `GaloisRep/Prelude.lean` → `GaloisRep`;
`ModularForms/HeckePrelude.lean` → `CuspForm` / `ModularForm` (one section each),
importing `ModularForms/Level/Diamond.lean`,
`ModularForms/Defs/HeckeRepresentatives.lean`, `ModularForms/HeckeAnalytic.lean`,
`ModularForms/HeckeQCoeff.lean` and `ModularForms/Eisenstein/WeierstrassZeta.lean`
so the “in port” and “D provides” names are reachable through the home. Keep
imports specific — never `import Mathlib`.

**Take the union of the pin copies, not one copy.** The copies differ in binders
and helper sub-blocks; read every copy listed and port the union, including a
sub-block absent from any single copy (playbook §2.4). The pin copy is the
statement authority: write the block at the pin's exact name and statement
(namespace prefix allowed).

**The tables are proofs, so scan for shared *definitions* too.** The 78-block list
comes from the tool's proof dedup and omits repeated `def`/`abbrev`/`structure`
declarations. Before writing each home, scan that home's pin copies for any
repeated definition the table does not list and home it as well; one that occurs in
only a single pin file stays in that file. Known Eisenstein cases: `om` (all four
`S_EisensteinSeries_*` files) and `ser` (the `weierstrassZeta_add_one…` and
`isBoundedAtImInfty…` files) belong in `ModularForms/Eisenstein/Cotangent.lean`.

**Skip what the port already reaches.** Before writing a block, grep the post-D
tree (`grep -rn '\b<name>\b' FLTForHuman --include=*.lean`). If a public
declaration of that name is reachable through the home's imports, do **not**
re-declare it — importing the home's dependency is enough. If it is present but
`private`, or present with a *different* statement, that is **H2**, not H1: do not
duplicate it in the home (redeclaring an imported name is a hard error). The
`status (live)` column below is the grep result on the mid-D tree; recompute it
after D closes, and treat every `live in port` row as a *verify the statement*
task, not a write. A name-based test is an upper bound (§2.1 of the playbook): a
renamed port copy will still need the block.

**Checker wiring.** For each home module: append its path to `PORT_FILES` (before
the `]` at line 1607 of `spec/check_flt_statements.py`), and append the pin `S_`
files named in its table to `SOURCES` (before the `]` at line 1248) so the
promoted pin-`private` blocks verify through the checker's dotted fallback. Append
new entries last. Then run the checker from `lean/`; it must stay **0 mismatched /
0 missing**.

## 2. H2 — promotions and reconciliations (the cascade)

Do this only after all four homes build green. One pass, then one full build, then
the touched files are **closed**.

### 2a. Promotions — the seven port-`private` copies, plus the four `_11` refinements

These pin statements already exist in the port but are `private`, so no other
module can import them. Promote each **at its existing port location** (drop
`private`, keep the pin name); the checker verifies a promotion through its dotted
name fallback.

The D friction log adds a promotion cluster the advice tool cannot see:
`ModularForms/Defs/HeckeRepresentatives.lean` carries the pin's **three-conjunct**
`heckeMatrix_mul_of_eq` / `…_of_eq'` / `heckeDiagMatrix_mul_of_eq` / `…_of_eq'` as
the `private …_11` refinements, while the public names carry the weaker
two-conjunct `S_`-file statements. Resolve each in one move: promote the `_11`
refinement to the pin's public name, and rename (or `private`-ise) the two-conjunct
copy, keeping a local alias for its consumers — see 2b.

> The `TOPIC-definitions-and-homes.md` list is wrong: it names
> `heckeU_eq_sum_zmod` and `redMatrix` (both already **public** in the port,
> `port_public_count = 1`) and omits `T_zpow_mem_Gamma1` and `adjoinRoot'`. Use the
> table below plus the four `_11` refinements.

### 2b. Reconciliations — the 22 name clashes

The port already declares these names with a *different* statement, so the pin's
statement is not yet in the proof tree. Resolution, by shape:

- **binder-only (5: `coef`, `det_mod` ×2, `isUnit_wt`, `rep`)** — take the pin copy's
  binders. Where the port copy adds a hypothesis (`isUnit_wt`'s `hp : p.Prime`),
  prove the pin statement without it, using the pin's own proof as the template,
  and update the call sites.
- **naming-only (textual, e.g. `T_mem_Gamma1`'s `N` vs `M`, `mapGL_apply`'s
  `Matrix.SpecialLinearGroup.mapGL`, `qCoeffLin`'s `Gamma1` vs `Γ₁ℝ`, `det_mod`'s
  `Gamma0` vs `CongruenceSubgroup.Gamma0`) — restate with the pin's exact
  spelling/head.**
- **dropped conjunct (`heckeDiagMatrix_mul_of_eq`, `heckeDiagMatrix_mul_of_eq'`,
  `heckeMatrix_mul_of_eq`, `heckeMatrix_mul_of_eq'`)** — the port copy silently
  dropped a conjunct (`g' 1 1 = …`). **Strengthen** to the pin statement; the
  proofs and the Hecke consumers are the gate.
- **specialised vs general (`periodic_smul`, `T_pow_mem_Gamma1`)** — the port copy
  is more general (`Periodic … c`, ℤ-indexed) and the pin's is the special case.
  Declare the pin statement under the pin name (deriving it from the general one)
  and keep the general lemma under a distinct name with local aliases.
- **genuine content difference (`heckeRep_mul` `Gamma1` + the extra `wt` factor,
  `mdifferentiable_heckeU` binder explicitness, `coe_smul_eq` `denomC`,
  `qCoeffLin`)** — reconcile to the pin's statement, generalising or specialising
  once and updating consumers.
- **unrelated collision (`coef`, `rep`)** — the port's declaration is a different
  object that happens to share the name. Give the pin declaration its home at the
  pin name; rename the unrelated port declaration (`private` if it has no other
  consumer), keeping a local alias for its consumers.
- **D friction-log additions the advice table misses** (`lean/logs/deligne-serre-friction.md`
  is the authoritative phase-D share): `isZeroAt_heckeU` (`HeckeCusps.lean` — the
  port's public copy drops the pin's `hp : p ≠ 0` and is therefore more general)
  and `sum_range_eq_sum_zmod` (`HeckeRepresentatives.lean` — binder-only,
  `{M} (F : …)` against the pin's `{A} (G : …)`). The D worker deliberately did
  not port or shadow the `Def_CuspForm_Gamma1HeckeOperators` copies of the seven
  declarations `mdifferentiable_heckeU`, `isZeroAt_heckeU`, the four `…_mul_of_eq`,
  `sum_range_eq_sum_zmod`; reconcile them here.
- `coe_smul_eq` lives in `Reserve/` and is **not** diffed; fix it there or move the
  pin copy into its home — do not leave a `Reserve/` declaration shadowing a home.

After each declaration: `grep -rn '\b<name>\b' FLTForHuman --include=*.lean` to find
consumers, and let `lake build` find what the textual change broke.

## 3. Closing a step

- `timeout 120 lake build <module>` is green, with no `sorry`/`admit`;
- the statement checker is 0 mismatched / 0 missing;
- `#print axioms` on the step's headlines is `[propext, Classical.choice, Quot.sound]`;
- the friction log (`lean/logs/deligne-serre-friction.md`) has an entry for
  anything resolved locally;
- H2 ends with **one** full `lake build` (serialised with `flock`, bounded), after
  which the touched files are closed.

## 4. Out of scope

The theorem sets (phase T); any edit to the definitions-layer modules beyond the
promotions in §2a. Do not re-plan the route; if a block cannot be placed without a
plan change, stop at the home boundary and report.

---

## Appendix — the tool-generated scope tables

Regenerated against the **post-D tree** (2026-09-29). `live file` is the first

grep hit in `FLTForHuman/`; a name-based test is an upper bound, so a renamed

port copy still needs the block (§2.1 of the playbook).

#### EIS — `FLTForHuman/ModularForms/Eisenstein/Cotangent.lean`

| block | copies | span | status (post-D) | live file | pin copies (file:line) |
|---|---:|---:|---|---|---|
| `norm_pi_cot_add_le` | 3 | 22 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:313`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:40`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:118` |
| `pi_cot_add_eq` | 3 | 12 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:301`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:28`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:106` |
| `norm_pi_cot_sub_le` | 3 | 9 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:335`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:62`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:140` |
| `om_injective` | 2 | 18 | **write once (H1)** | — | `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:151`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:94` |
| `norm_cexp_two_pi_I` | 3 | 5 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:296`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:23`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:101` |
| `add_intCast_mul` | 2 | 9 | **write once (H1)** | — | `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:102`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:197` |
| `NotLat` | 3 | 4 | **write once (H1)** | — | `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:92`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:92`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:187` |
| `add_intCast` | 2 | 6 | **write once (H1)** | — | `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:96`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:191` |
| `cot_neg` | 3 | 3 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:127`; `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:20`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:84` |
| `om_smul` | 2 | 6 | **write once (H1)** | — | `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:21`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:28` |
| `hasSum_ser` | 2 | 3 | **write once (H1)** | — | `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:131`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:211` |
| `zterm` | 2 | 3 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:20`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:23` |
| `pval` | 2 | 2 | **write once (H1)** | — | `S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean:126`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:209` |
| `weierstrassZeta_eq` | 2 | 2 | **write once (H1)** | — | `S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean:23`; `S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean:26` |

#### FD — `FLTForHuman/NumberTheory/FrobeniusDensity/Basic.lean`

| block | copies | span | status (post-D) | live file | pin copies (file:line) |
|---|---:|---:|---|---|---|
| `sum_moebius_mem_zpowers` | 2 | 39 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:52`; `S_FrobeniusDensity_weight_eq.lean:51` |
| `mem_zpowers_pow_div_iff` | 2 | 30 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:22`; `S_FrobeniusDensity_weight_eq.lean:21` |
| `tsum_normFiber` | 2 | 22 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:89`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:90` |
| `isBigO_sum_of_tendsto_div` | 2 | 20 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:38`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:39` |
| `exists_pow_coprime_eq_of_orderOf_eq` | 2 | 19 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:91`; `S_FrobeniusDensity_weight_eq.lean:90` |
| `ncard_conj_mem_eq_card_mul_ncard` | 2 | 16 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:118`; `S_FrobeniusDensity_weight_eq.lean:117` |
| `tendsto_sum_idealCount_div` | 2 | 15 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:23`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:24` |
| `card_le_of_forall_pow_eq` | 2 | 12 | **write once (H1)** | — | `S_FrobeniusDensity_ncard_degreeOne_primesOver_under.lean:87`; `S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.lean:21` |
| `ncard_eq_sum_indicator` | 2 | 14 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:134`; `S_FrobeniusDensity_weight_eq.lean:133` |
| `primeSum_le_idealSum` | 3 | 7 | **write once (H1)** | — | `S_FrobeniusDensity_degOneSum_add_log_isBigO.lean:26`; `S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:240`; `S_FrobeniusDensity_summable_degOne_term.lean:18` |
| `toReal_term` | 2 | 7 | **write once (H1)** | — | `S_FrobeniusDensity_degOneSum_add_log_isBigO.lean:221`; `S_FrobeniusDensity_summable_degOne_term.lean:33` |
| `term_eq_ofReal_zetaTerm` | 2 | 9 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:64`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:65` |
| `degOneSum_ne_top` | 2 | 7 | **write once (H1)** | — | `S_FrobeniusDensity_degOneSum_add_log_isBigO.lean:36`; `S_FrobeniusDensity_summable_degOne_term.lean:25` |
| `idealSum_eq_tsum_zetaTerm` | 2 | 8 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:116`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:117` |
| `orderOf_pow_orderOf_div` | 2 | 8 | **write once (H1)** | — | `S_FrobeniusDensity_sum_moebius_mul_pos.lean:110`; `S_FrobeniusDensity_weight_eq.lean:109` |
| `normFiberEquiv` | 2 | 7 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:82`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:83` |
| `LSeriesSummable_idealCount` | 2 | 6 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:58`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:59` |
| `summable_zetaTerm` | 2 | 6 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:73`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:74` |
| `zetaTerm_nonneg` | 2 | 6 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:17`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:18` |
| `tsum_equiv'` | 2 | 5 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:111`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:112` |
| `NormFiber` | 2 | 3 | **write once (H1)** | — | `S_FrobeniusDensity_idealSum_ne_top.lean:79`; `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:80` |
| `mono` | 7 | 7 | live in port → reuse/verify | ModularForms/Analytic/StarConvexPrimitive.lean | `S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:84`; `S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean:57`; `S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean:57`; `S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean:23`; `S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean:36`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.lean:38`; `S_WLight_frickeFunction_intBaseChange.lean:651` |

#### GR — `FLTForHuman/GaloisRep/Prelude.lean`

| block | copies | span | status (post-D) | live file | pin copies (file:line) |
|---|---:|---:|---|---|---|
| `finite_range_of_factorsThroughFiniteLevel` | 2 | 28 | **write once (H1)** | — | `S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean:21`; `S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean:18` |

#### HK — `FLTForHuman/ModularForms/HeckePrelude.lean`

| block | copies | span | status (post-D) | live file | pin copies (file:line) |
|---|---:|---:|---|---|---|
| `periodic_of_slash_T` | 3 | 22 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:43`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:114`; `S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean:36` |
| `heckeDiagMatrix_mul_T` | 2 | 12 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:31`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:102` |
| `cusp_bdd` | 2 | 6 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:116`; `S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean:73` |
| `slash_heckeDiagMatrix_slash_T` | 2 | 6 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:65`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:136` |
| `isBoundedAtImInfty_slash_heckeDiagMatrix` | 2 | 4 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:75`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:146` |
| `isBoundedAtImInfty_slash_heckeMatrix` | 2 | 4 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:71`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:142` |
| `cusp_holo` | 2 | 2 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:114`; `S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean:70` |
| `cusp_periodic` | 2 | 3 | **write once (H1)** | — | `S_CuspForm_qCoeff_heckeTLinOne.lean:111`; `S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean:67` |
| `mdifferentiable_heckeU` | 5 | 10 | clash → H2 | ModularForms/HeckeQCoeff.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:13`; `S_CuspForm_qCoeff_heckeTLinOne.lean:88`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:159`; `S_ModularForm_mdifferentiable_heckeU.lean:45`; `Thm_ModularForm_mdifferentiable_heckeU.lean:7` |
| `det_eq` | 7 | 9 | live in port → reuse/verify | ModularForms/WeightOne/IntegralStructure.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:88`; `S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:38`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:29`; `S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean:47`; `S_Ihara_amalgamToGamma0Away_surjective.lean:115`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:23`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:25` |
| `periodic_smul` | 7 | 9 | clash → H2 | ModularForms/WeightOne/Gamma1Basis.lean | `S_CuspForm_qCoeff_heckeTLinOne.lean:98`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:183`; `S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean:76`; `S_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean:91`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean:168`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean:182`; `S_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean:76` |
| `isBoundedAtImInfty_heckeU` | 4 | 9 | live in port → reuse/verify | ModularForms/HeckeQCoeff.lean | `S_CuspForm_qCoeff_heckeTLinOne.lean:79`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:150`; `S_ModularForm_mdifferentiable_heckeU.lean:52`; `Thm_ModularForm_isBoundedAtImInfty_heckeU.lean:7` |
| `det_mod` | 4 | 8 | clash → H2 | ModularForms/Level/Diamond.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:231`; `S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:42`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:33`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:294` |
| `T_pow_mem_Gamma1` | 9 | 4 | clash → H2 | ModularForms/WeightOne/Gamma0Integral.lean | `S_CuspForm_qCoeff_heckeTLinOne.lean:23`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:95`; `S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean:32`; `S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean:83`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_comp_mul_smul_coeff_eq_apply_of_gamma1_mul.lean:202`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean:454`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean:468`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean:489`; `S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.lean:490` |
| `T_mem_Gamma1` | 18 | 3 | clash → H2 | ModularForms/WeightOne/Gamma0Rationality.lean | `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:92`; `S_ModularCurve_JOne_degeneracyPullbackInputs.lean:146`; `S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.lean:549`; `S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean:32`; `S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean:29`; `S_ModularCurve_exists_algHom_igusaFunctionFieldX1C_apply_eq_jqNModC_and_apply_eq_jqModC.lean:243`; `S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean:22`; `S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean:87`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.lean:85`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean:94`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean:458`; `S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean:306`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean:472`; `S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean:79`; `S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd.lean:282`; `S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.lean:220`; `S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1.lean:224`; `S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean:626` |
| `one_mem_strictPeriods` | 24 | 3 | live in port → reuse/verify | ModularForms/WeightOne/Gamma1IntegralBasis.lean | `S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean:65`; `S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean:24`; `S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean:598`; `S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.lean:92`; `S_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.lean:22`; `S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean:320`; `S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.lean:414`; `S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.lean:322`; `S_ModularCurve_exists_algHom_igusaFunctionFieldX1C_apply_eq_jqNModC_and_apply_eq_jqModC.lean:168`; `S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash.lean:35`; `S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.lean:37`; `S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.lean:39`; `S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion.lean:70`; `S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.lean:79`; `S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean:25`; `S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean:90`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.lean:88`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean:97`; `S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean:309`; `S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean:82`; `S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd.lean:207`; `S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div.lean:37`; `S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean:65`; `S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean:598` |
| `sum_slash_mapGL` | 2 | 11 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:417`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:312` |
| `map_eq` | 5 | 7 | live in port → reuse/verify | ModularForms/WeightOne/Gamma0Rationality.lean | `S_Ihara_amalgamToGamma0Away_surjective.lean:74`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean:386`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean:400`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean:421`; `S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.lean:422` |
| `conj_mem_Gamma1` | 8 | 12 | live in port → reuse/verify | ModularForms/WeightOne/Gamma1IntegralBasis.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:492`; `S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean:70`; `S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean:37`; `S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean:159`; `S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean:897`; `S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean:461`; `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean:475`; `S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean:86` |
| `heckeU_eq_sum_zmod` | 3 | 11 | live in port → reuse/verify | ModularForms/HeckeInvariance.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:175`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:109`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:111` |
| `redMatrix` | 3 | 11 | live in port → reuse/verify | ModularForms/PhiGenDescends.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:254`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:136`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:207` |
| `heckeDiagMatrix_mul_of_eq'` | 3 | 21 | clash → H2 | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:145`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:80`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:82` |
| `restrictMF` | 5 | 9 | live in port → reuse/verify | ModularForms/Level/Degeneracy.lean | `S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean:46`; `S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.lean:107`; `S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean:106`; `S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean:100`; `S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean:278` |
| `heckeDiagMatrix_mul_of_eq` | 3 | 16 | clash → H2 | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:129`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:64`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:66` |
| `heckeMatrix_mul_of_eq` | 3 | 16 | clash → H2 | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:97`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:32`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:34` |
| `heckeMatrix_mul_of_eq'` | 3 | 16 | clash → H2 | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:113`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:48`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:50` |
| `mem_Gamma1_of_d_eq_one` | 2 | 15 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:239`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:302` |
| `redMatrix_apply_one_one` | 3 | 4 | live in port → reuse/verify | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:277`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:159`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:230` |
| `T_zpow_mem_Gamma1` | 5 | 4 | live in port → reuse/verify | ModularForms/WeightOne/Gamma1Basis.lean | `S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:87`; `S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean:385`; `S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.lean:233`; `S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1.lean:237`; `S_ModularForm_exists_gamma1_frickeRational_sigmaTransport.lean:385` |
| `sum_eq` | 2 | 11 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:360`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:277` |
| `heckeT_eq_sum_onePoint` | 2 | 9 | live in port → reuse/verify | ModularForms/Defs/HeckeRepresentatives.lean | `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:127`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:198` |
| `sum_range_eq_sum_zmod` | 3 | 9 | live in port → reuse/verify | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:166`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:101`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:103` |
| `d_mul` | 2 | 6 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:225`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:288` |
| `heckeRep` | 3 | 3 | live in port → reuse/verify | ModularForms/PhiGenDescends.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:186`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:120`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:191` |
| `lift_apply_one_one` | 2 | 6 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:219`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:271` |
| `lift_mem` | 2 | 6 | live in port → reuse/verify | ModularForms/Defs/Gamma1HeckeOperators.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:213`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:265` |
| `exists_rep` | 3 | 14 | live in port → reuse/verify | ModularForms/WeightOne/Gamma1Basis.lean | `S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:252`; `S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean:816`; `S_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean:816` |
| `heckeRep_infty` | 3 | 2 | live in port → reuse/verify | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:189`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:123`; `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:194` |
| `lift` | 4 | 2 | live in port → reuse/verify | ModularForms/QExpansionPrinciple.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:207`; `S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one.lean:422`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:259`; `S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean:492` |
| `lift_infty` | 2 | 2 | live in port → reuse/verify | ModularForms/Level/Diamond.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:209`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:261` |
| `wt_infty` | 2 | 2 | live in port → reuse/verify | ModularForms/Defs/HeckeRepresentatives.lean | `Def_CuspForm_Gamma1HeckeOperators.lean:195`; `S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:169` |

#### H2 promotions — the seven port-`private` copies to promote

| declaration | kind | port file | pin file:line |
|---|---|---|---|
| `T_zpow_mem_Gamma1` | theorem | `FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean` | `P2M/Sol/S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:87` |
| `adjoinRoot'` | def | `FLTForHuman/ModularForms/WeightOne/Gamma0Rationality.lean` | `P2M/Sol/S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean:469` |
| `heckeDiagMatrix_mul_of_eq` | theorem | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:64` |
| `heckeDiagMatrix_mul_of_eq'` | theorem | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:80` |
| `heckeMatrix_mul_of_eq` | theorem | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:32` |
| `heckeMatrix_mul_of_eq'` | theorem | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean:48` |
| `locKer` | def | `FLTForHuman/ModularForms/WeightOne/Gamma0Rationality.lean` | `P2M/Sol/S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean:149` |

Plus the four `private …_11` refinements in `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` (2a).

#### H2 clashes — the 22 tool rows plus the 2 phase-D friction rows

| name | kind | binder-only | port file | pin statement | port statement |
|---|---|---|---|---|---|
| `T_mem_Gamma1` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean` | `(N : ℕ) : ModularGroup.T ∈ Gamma1 N` | `(M : ℕ) : ModularGroup.T ∈ Gamma1 M` |
| `T_pow_mem_Gamma1` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Defs/GammaRational.lean` | `(N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N` | `(t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N` |
| `T_pow_mem_Gamma1` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Defs/GammaRational.lean` | `(N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N` | `(t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N` |
| `T_pow_mem_Gamma1` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Defs/GammaRational.lean` | `(M n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 M` | `(t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N` |
| `coe_smul_eq` | lemma | no | `Reserve/ModularCurve/Analytic/LevelTauBridge.lean` | `(γ : SL(2, ℤ)) : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / denom γ τ` | `(γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = (((γ.val 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ.val 0 1 : ℤ) : ℂ)) / denomC γ (τ : ℂ)` |
| `coef` | def | yes | `FLTForHuman/ModularForms/WeightOne/Gamma0Rationality.lean` | `(z : ℂ) (n : ℕ) : ℂ` | `(i : Idx) : ℂ` |
| `det_mod` | theorem | yes | `FLTForHuman/ModularForms/Level/Diamond.lean` | `{N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1` | `(γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1` |
| `det_mod` | theorem | yes | `FLTForHuman/ModularForms/Level/Diamond.lean` | `{N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1` | `(γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1` |
| `heckeDiagMatrix_mul_of_eq` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (j' : ℕ) (e : ℤ) (he : g 1 1 = g 1 0 * j' + p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = e ∧ heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j'` | `(g : SL(2, ℤ)) (j' : ℕ) (e : ℤ) (he : g 1 1 = g 1 0 * j' + p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j'` |
| `heckeDiagMatrix_mul_of_eq'` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = e ∧ g' 1 1 = g 1 1 ∧ heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p` | `(g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = e ∧ heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p` |
| `heckeMatrix_mul_of_eq` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ) (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧ heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j'` | `(g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ) (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j'` |
| `heckeMatrix_mul_of_eq'` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (j : ℕ) (e : ℤ) (he : g 0 0 + j * g 1 0 = p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = p * g 1 1 ∧ heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p` | `(g : SL(2, ℤ)) (j : ℕ) (e : ℤ) (he : g 0 0 + j * g 1 0 = p * e) : ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p` |
| `heckeRep_mul` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `{N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N) (x : OnePoint (ZMod p)) : ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧ ((g' 1 1 : ℤ) : ZMod N) * wt N p x = wt N p (redMatrix p g • x) ∧ heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)` | `{N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (x : OnePoint (ZMod p)) : ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧ ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧ heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)` |
| `isUnit_wt` | theorem | yes | `FLTForHuman/ModularForms/Level/Diamond.lean` | `{N : ℕ} (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) : IsUnit (wt N p x)` | `{N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) : IsUnit (wt N p x)` |
| `mapGL_apply` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (i j : Fin 2) : (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ)` | `(g : SL(2, ℤ)) (i j : Fin 2) : (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ)` |
| `mapGL_apply` | theorem | no | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `(g : SL(2, ℤ)) (i j : Fin 2) : (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ)` | `(g : SL(2, ℤ)) (i j : Fin 2) : (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ)` |
| `mdifferentiable_heckeU` | theorem | no | `FLTForHuman/ModularForms/HeckeAnalytic.lean` | `{F : ℍ → ℂ} (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p F)` | `{f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f)` |
| `mdifferentiable_heckeU` | theorem | no | `FLTForHuman/ModularForms/HeckeAnalytic.lean` | `{F : ℍ → ℂ} (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p F)` | `{f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f)` |
| `periodic_smul` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Defs/RatAt.lean` | `{G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((c • G) ∘ ofComplex) 1` | `{g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) : Periodic ((a • g) ∘ ofComplex) c` |
| `periodic_smul` | theorem | no | `FLTForHuman/ModularForms/WeightOne/Defs/RatAt.lean` | `{G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) : Periodic ((c • G) ∘ ofComplex) 1` | `{g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) : Periodic ((a • g) ∘ ofComplex) c` |
| `qCoeffLin` | def | no | `FLTForHuman/ModularForms/WeightOne/Gamma1IntegralBasis.lean` | `(N : ℕ) (k : ℤ) (n : ℕ) : CuspForm (Gamma1 N) k →ₗ[ℂ] ℂ` | `(N : ℕ) (k : ℤ) (m : ℕ) : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ` |
| `rep` | def | yes | `FLTForHuman/ModularCurve/Analytic/Gamma0Cosets.lean` | `(hpM : ¬ p ∣ M) (q : 𝒬) : SL(2, ℤ)` | `(ℓ : ℕ) (i : Fin (ℓ + 1)) : SL(2, ℤ)` |
| `isZeroAt_heckeU` | theorem | no | `FLTForHuman/ModularForms/HeckeCusps.lean` | `… (hp : p ≠ 0) … : c.IsZeroAt …` (pin, phase-D friction log) | port copy omits `hp : p ≠ 0` (more general) |
| `sum_range_eq_sum_zmod` | theorem | yes | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | `{A} (G : ℕ → A)` | `{M} (F : ℕ → M)` |
