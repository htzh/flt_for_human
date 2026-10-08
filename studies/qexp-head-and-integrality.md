# The qexp function-field head and the integrality effort — the intersection, and what the C′ shortcut leaves

**Status: measured 2026-10-08** against the pin `aa2d8b3`, with `tools/deps`
(`fltdata.FltData` docs-site graph closure; raw `S_`-file lines) and the port at
`6520 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own-proof
(6556 checked)`. Companion to
[../lean/topics/functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](../lean/topics/functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md)
(the head), [route-c-prime-scout.md](route-c-prime-scout.md) (the shortcut),
[eichler-shimura-scout.md](eichler-shimura-scout.md) §0 (the terminology), and
[../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md](../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md)
(the delivered work order).

**The question.** The qexp head is the five `ModularCurve.*` targets of the ready
shelf. Our integrality effort took the **C′ shortcut** — the trace lemma of
[route-c-prime-scout.md](route-c-prime-scout.md) §2 — and therefore did **not** port
**route A**, the pin's own *integral-structure* route
(`CuspForm.hasIntegralStructure_of_two_le`, 657 nodes). Do the two efforts meet?
And if route A is pruned (its proof supplied by C′), what is the gap?

**Answer in one line.** They are *complementary, not competing*: the Γ₀-rationality
pair (targets 1 and 3) stands on exactly the layer the C′ port landed (their whole
16- and 20-node premise sets lie in C′'s 53-node cone, which is 53/53 ported), no
target of the head touches route A's criterion or its Eichler–Shimura layer, and
pruning route A's proof costs exactly **4 nodes / 800 lines** with **zero rewire
obligations**. The gap that remains is not the head: it is route A's *unported*
cone — **283 nodes / 68,094 lines**, of which the relaxed packaging route removes
only 32 / 10,193, leaving **251 nodes / 57,901 lines** as the eventual need.

## 0. Terminology (borrowed from [eichler-shimura-scout.md](eichler-shimura-scout.md) §0)

| object | what it is in this note | measure |
|---|---|---|
| **route A** | the pin's proof of `CuspForm.hasIntegralStructure_of_two_le` (the integral-structure route) | cone **657 nodes / 263,720** `S_` lines |
| **the E-S cohomological layer** | `HeckeEis.*` + `ModPForms.*`, the object side of the Eichler–Shimura isomorphism | footprint **195 / 59,600** in the port |
| **C′** | the trace lemma + the integral Γ₁-basis theorem; the shortcut that *replaces route A's proof* | cone **53 nodes / 33,719**, 53/53 ported |
| **the qexp head** | the five targets of `TOPIC-qexp-rationality-degree-head.md` §1 | 578 public declarations, 249 ported |

The metric is graph closure and raw `S_`-file lines throughout, the convention
that reproduces route A's 263,720.

## 1. The five targets stand on two different landed bases

Every target is **node-ready**: `frontier.needed(target)` is the target alone, so
each premise of each target is already in the port. What differs is *which* base
it stands on — and hence which effort paid for it.

| target | premises | ported | base the premises lie in | in C′ cone | in route-A cone |
|---|---:|---:|---|---:|---:|
| 1 `exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd` | 16 | 16 | `WLight.*` fricke / level-`N` package + `IsIntegral.*` | **16 / 16** | 0 |
| 2 `le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd` | 1 | 1 | SET-H-C `qCoeff_comp_heckeDiagMatrix_smul` | 0 | 0 |
| 3 `exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion` | 20 | 20 | the same `WLight.*` layer plus 4 nodes | **20 / 20** | 0 |
| 4 `finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index` | 112 | 111 | `ModularCurve.PhiGen.*` / `modularFunctionField` / place theory | 2 / 112 | **111 / 112** |
| 5 `exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField` | 6 | 6 | `JOneES` + `qExpansion_discriminant` | 2 / 6 | 3 / 6 |

Two things are worth reading off the table.

1. **Targets 1 and 3 are entirely inside the C′ cone's base.** Their premise sets
   (16 and 20 nodes) are subsets of C′'s 53 nodes — the `WLight.frickeFunction_*` /
   `levelOne_hauptmodul_package` / `levelN_structure_package` /
   `ModularForm.weierstrassP_torsion_qExpansion_package` / `IsIntegral.mem_span_*`
   layer, plus (for target 3) `WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient`,
   `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient`,
   `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem` and
   `ModularCurve.surjective_specialLinearGroup_map_zmod`. Nothing else.
2. **Target 5 straddles both bases** — 2 of its 6 premises are in the C′ cone
   (`qExpansion_discriminant_*`) and 3 in route A's — but it too needs no route-A
   proof.
3. **Target 4 is the one that reaches into route A's cone** — 111 of its 112
   premises — but *not* into route A's proof: the route-A criterion
   `CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent` is not in
   any of the five cones, nor is `hasIntegralStructure_of_two_le` itself. Target 4's
   base is the endgame modular-curve/`PhiGen` geometry that route A's cone happens
   to contain, not the integral-structure argument.

## 2. The C′ cone is 53/53 ported — the shortcut *is* the port's weight-one base

`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`'s 53-node cone is
**fully in the ported frontier** (53/53, 33,719 lines), i.e. the 48 nodes
[TOPIC-route-c-prime-integral-structure.md](../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md)
§2 listed as new have all landed. The declaration-level counterpart is the head's
§3 reuse table: target 1 draws on `ModularForms/WeightOne/Defs/GammaRational.lean`
(69 rows), `Defs/RatAt.lean` (12) and `Gamma0Rationality.lean` (6); target 3 on the
same `GammaRational`/`RatAt` pair plus `Gamma1Basis.lean` (15). The last two modules
are the C′ work order's own; the first two are the weight-one rectification
definitions that C′ (and now the head) sits on. So the head's reused surface is
literally the C′ development plus its `Defs/` layer.

So the intersection is real and one-directional at the theorem level: **the
rationality pair is the first new headlines written over the base the integrality
shortcut landed** — but it does not consume C′'s own Γ₀-rationality nodes. In
particular neither target 1 nor 3 has
`ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0` (or its `slash`
sibling) in its cone: the pin proves the `_of_dvd` generalisation directly from the
`WLight` package, not by specialising the ported node. The two are *siblings over
the same base*, and §6 records the dedup that follows.

## 3. `prune.py` on the route-A shortcut

The faithful model of "route A's proof is supplied by C′" is to delete the four
nodes that leave the endgame when route A's proof edge is dropped
([route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum) and to mark the
statement itself as supplied:

```bash
cd tools/deps
python3 prune.py --scenario none --top 20 \
  --also CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent \
  --also CuspForm.linearIndependent_complex_of_linearIndependent_int_of_periodPackage \
  --also CuspForm.conjForm_heckeTLin_heckeULin_comm \
  --also HeckeEis.span_range_coeffH1par_map_int_complex_eq_top \
  --replaced CuspForm.hasIntegralStructure_of_two_le
```

```
removed set R                           4 nodes /       800 lines
prunable(R)  [the saving]               4 nodes /       800 lines
  of which ES-ish                       1 nodes /        54 lines
rewiring frontier                       1 nodes /       515 lines
  replaced (exempt)                     1 nodes /       515 lines
  obligations                           0 nodes /         0 lines
```

This reproduces the scout's closure-accurate figure exactly: **4 nodes / 800
lines**, one of them E-S-ish (`HeckeEis.span_range_coeffH1par_map_int_complex_eq_top`,
54 lines). The rewire frontier is the supplied theorem itself
(`hasIntegralStructure_of_two_le`, 515 lines) and **zero obligations** — no *other*
retained proof cites any of the four pruned nodes, because the supplied theorem was
their only consumer. The "eventually needs" of the shortcut is therefore not a
rewiring problem at all.

The complementary model — remove the *statement vertex*, i.e. "the port never
carries route A" — gives 5 nodes / 1,315 lines prunable and a 13-node frontier: the
direct consumers of `hasIntegralStructure_of_two_le` that must then be re-proved
against C′'s statement.

| direct consumer of `hasIntegralStructure_of_two_le` | in root | ported today |
|---|---:|---:|
| `CuspForm.moduleFinite_heckeAlgebra` | yes | **yes** |
| `WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two` (interface 4) | yes | no |
| `CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd` (interface 5) | yes | no |
| `CuspForm.heckeAlgebra.exists_mem_modPCusp_isModPEigen_of_ringHom` | yes | no |
| `CuspForm.exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt` | yes | no |
| `CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd` | yes | no |
| `CuspForm.heckeLocal.exists_patchingDatum_…_of_eq_three_…_of_level_not_cube_dvd` | yes | no |
| `CuspForm.heckeLocal.exists_patchingDatum_…_of_level_not_sq_dvd_…_of_level_not_cube_dvd` | yes | no |
| `CuspForm.heckeLocal.unitRoot_sq_ne_one_of_point` | yes | no |
| `GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two` | yes | no |
| `ModPForms.dimFormulaCusp_le_finrank_modPCusp` | yes | no |
| `WeierstrassCurve.exists_ideal_heckeAlgebra_two_or_succ_…_of_inertia_moves_torsion_of_katz_of_eq_three` | yes | no |
| `WeierstrassCurve.exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two` | yes | no |

Only one of the thirteen is ported. The list is exactly the Hecke/patching front
of the endgame; two of its entries are the headline nodes of interfaces 4 and 5,
and a third interface headline (6) has `hasIntegralStructure_of_two_le` in its cone.
That is the correct reading of the shortcut: it leaves a **statement obligation at
13 proofs**, all of them already in the endgame's future work, and no new
mathematics.

**The C′ cone itself is load-bearing.** Pruning the whole 53-node cone instead
(`python3 prune.py --also <every C′ cone node>`) gives 53 nodes / 33,719 lines
prunable — and a **220-node** rewire frontier, headed by `Ihara.mennickeCSP_of_prime`
and the `ModularCurve.FullLevel.*` cluster. Nothing below the cone is exclusive to
it, but 220 retained proofs cite into it. C′ is not a throwaway branch.

## 4. The gap: route A's *unported* cone

The shortcut did not spare the port route A's cone — it spared it route A's
*proof*. Measured on the current port:

| | nodes | `S_` lines |
|---|---:|---:|
| route A cone `closure(hasIntegralStructure_of_two_le)` | 657 | 263,720 |
| of which ported | 374 | 195,626 |
| **of which unported** | **283** | **68,094** |

By namespace the 283 unported nodes are `ModularCurve.` 121, `WeierstrassCurve.` 47,
`AlgebraicCurve.` 40, `HeckeEis.` 37, `HahnSeries.` 8, `ModularForm.` 6, `CuspForm.`
5, and a tail of mathlib-namespace nodes — i.e. the endgame modular-curve /
Eichler–Shimura geometry, exactly the layer the scout flagged as surviving
regardless of the integral-structure route.

Applying the **relaxed** scenario (drop the E-S packaging `eichlerShimuraMap` /
`coeffH1par` plus the 12-node analytic core) to that unported remainder:

```bash
python3 prune.py --scenario relaxed --per-interface --top 18
```

```
prunable(R)  [the saving]              63 nodes /    18391 lines
  of which ES-ish                      56 nodes /    16298 lines
rewiring frontier                       3 nodes /     1458 lines
  obligations                           2 nodes /      943 lines
```

- **40 of route A's 657 cone nodes / 10,781 lines** are in the prunable set; of the
  *unported* 283, only **32 nodes / 10,193 lines** fall.
- **The eventual need is 251 nodes / 57,901 lines** of route A's cone under the
  relaxed route.
- The E-S interface as a namespace: `HeckeEis.` + `ModPForms.` is 195 nodes /
  59,600 lines in the port; the relaxed prune removes 56 / 16,298 and leaves
  **139 nodes / 43,302 lines**.

This is the honest "gap" number for the integrality effort: the shortcut's own
saving is 4/800, and the thing it does *not* save is the ~43k-line interface that
the endgame continues to owe.

## 5. The qexp head's own gap — and its insulation from the pruning

At theorem-graph level the head's gap is one node per target:

| target | `needed` | literal `closure \ ported` |
|---|---:|---|
| 1, 3, 5 | 1 (itself) | 1 |
| 2 | 1 (itself) | 1 |
| 4 | 1 (itself) | 2 — adds `ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` |

The target-4 extra is the **terminal-reading subtlety**: `hasSum_cosetPoly_coeff`
is reachable from target 4 only through an already-ported intermediate, so the
port's obligation is discharged by the statement that intermediate supplies;
`needed` stops there while a bare closure difference still counts it. It is one
declaration, not a development.

Declaration-level (the budget the topic uses) the head is **329 new declarations /
≈4,114 raw lines** after the once-only dedup, against 249 ported of 578 public —
[TOPIC-qexp-rationality-degree-head.md](../lean/topics/functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md)
§2.

And the insulation: **the relaxed removal set intersects none of the five cones,
and `needed(target, avoided = R_relaxed)` is still 1 for every target.** The
qexp head neither needs the E-S packaging nor route A; it is a consumer of the
already-landed base.

## 6. A reverse saving the head's topic does not claim

Target 1 *specialises* to the ported C′ node. At `ℓ = 1`, target 1's extra
hypotheses collapse — `Γ₁ M ⊓ Γ₀ (M * 1) = Γ₁ M`, `(1 : ℤ) ∣ γ 1 1` is trivial,
and `qExpansion 1` is the C′ conclusion — so *mathematically* target 1 at
`ℓ = 1` **is** the C′ statement
`ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0` for `N = M`
(the Lean application is schematic and not compiled here; the point is the
statement relation, not a checked proof). `prune.py` prices the consequence:
removing that C′ node and supplying it from target 1 is **1 node / 1,267 lines**
prunable with exactly **one** rewire obligation,
`ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0` (597 lines, ported,
its only consumer).

```
remove ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0:
prunable: 1 / 1267
frontier (target 1 exempt):
   ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 -> [the removed node]
```

Today this is a *dedup*, not a budget line: the C′ node is already ported, so
porting target 1 adds work rather than removing it. It becomes real if the port
ever has to re-derive or maintain `Gamma0Rationality.lean` — and it is the kind of
row [porting-playbook.md](../lean/porting-playbook.md) wants recorded rather than
silently duplicated. The topic's §9 can carry it as the one place the head and the
integrality effort overlap *in the saving direction*.

## 7. Consequences

1. **No re-opening of route A.** The head's Γ₀-rationality pair proves rationality
   where C′ proves integrality; neither needs route A's criterion, and no target of
   the head has route A's proof or the E-S layer in its cone. The topic's §9 "what
   this is not" list can add: not a re-opening of route A.
2. **Budget target 4 as a rider on the endgame geometry, not as new theory.** Its
   111-node base is the `ModularCurve.PhiGen` / `modularFunctionField` / place layer
   that route A's cone also contains and that the endgame owes anyway; the 1,045
   new lines of the residue-field model (target 5) and the 1,204 of the relrank
   (target 2) are the genuinely new ones.
3. **The gap to track is the interface, not the head.** After the relaxed route the
   surviving `HeckeEis`/`ModPForms` layer is 139 nodes / 43,302 lines, and route A's
   unported cone is 251 nodes / 57,901 lines. Neither number moves when the head
   lands; both should be carried in the E-S column's ledger.
4. **The C′ shortcut is confirmed minimal and safe.** 4 nodes / 800 lines saved,
   zero rewire obligations, one supplied statement, 13 consumers all in the
   endgame's future work. `prune.py --verify-known` still reproduces every anchor
   figure, so none of the above disturbs the recorded payout accounting.

## 8. Regenerate

```bash
cd tools/deps
python3 prune.py --selftest
python3 prune.py --verify-known
python3 prune.py --scenario relaxed --per-interface --top 18
python3 prune.py --scenario none --top 20 \
  --also CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent \
  --also CuspForm.linearIndependent_complex_of_linearIndependent_int_of_periodPackage \
  --also CuspForm.conjForm_heckeTLin_heckeULin_comm \
  --also HeckeEis.span_range_coeffH1par_map_int_complex_eq_top \
  --replaced CuspForm.hasIntegralStructure_of_two_le
python3 frontier.py --target ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd --ready
python3 frontier.py --target ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index --ready
```

The cone/overlap tables of §1 and §4 are `FltData` closure queries; the
`FltPayoff`/`Frontier` classes in `tools/deps` expose them directly
(`pay.closure`, `pay.total_lines`, `frontier.needed`).

Pin sources, pinned at `aa2d8b3`:

- `CuspForm.hasIntegralStructure_of_two_le` —
  [S_CuspForm_hasIntegralStructure_of_two_le.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_CuspForm_hasIntegralStructure_of_two_le.lean)
- the C′ basis theorem —
  [S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean)
- the ported C′ Γ₀ node —
  [S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean)
- target 1 —
  [S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean)
