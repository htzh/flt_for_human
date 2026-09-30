# Mathlib-first substitution audit — the Riemann–Roch definition layer (phase D)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first).
Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Source of truth for the inventory is
[`tools/deps/build/rr_defs_inventory.txt`](../../../tools/deps/build/rr_defs_inventory.txt)
(the tool omits `class`, so the three classes are added by hand). Scratch evidence
was `lean/Scratch.lean` (gitignored; **removed at the phase-2 closeout**, so the
classifications below are the retained record), compiled from `lean/` with
`timeout 90 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false Scratch.lean`
(4 s, exit 0). The D-layer modules have since been transcribed under
`FLTForHuman/AlgebraicCurve/Defs/`; the examples below therefore elaborate against
the real port statements, not paraphrases.

**Class convention.** SUBSTITUTE = the port can import the mathlib object/lemma
instead of proving it: either the pin's definition body *is* the mathlib constant
(an `rfl`-equal alias, which playbook §2.2 explicitly legalises), or the pin's
conclusion, after unfolding the pin's own wrappers, is the mathlib statement.
PROOF-INGREDIENT = the statement is bespoke (must be written) but the proof is
assembled from named mathlib lemmas (the pin's definitions are the only new
vocabulary). BESPOKE = a definition/structure/class/`Prop` object with no mathlib
analogue; here these are "recorded negatives" and are exactly the phase's work.

Sources, in pin order:
[`Def_ModularCurve_CanonicalDivisor.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CanonicalDivisor.lean),
[`Def_AlgebraicCurve_CanonicalDivisor.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean),
[`Def_AlgebraicCurve_Repartitions.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean),
[`Def_AlgebraicCurve_AdelicIndex.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean),
[`Def_AlgebraicCurve_IsCurveOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean),
[`Def_AlgebraicCurve_RiemannRochRows.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean),
[`Def_AlgebraicCurve_PoleDivisorPackage.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean); the shared prelude is
[`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean) (the sibling
`..._finiteDimensional_lSpace_zero_of_constantsAreBase.lean` is the same file under a
different `P2MW` namespace: 2,545 lines, only the namespace strings differ).

## 1. Summary — class counts per module

| pin module | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| `Def_ModularCurve_CanonicalDivisor` | 0 | 11 | 5 | 16 |
| `Def_AlgebraicCurve_CanonicalDivisor` | 0 | 1 | 4 | 5 |
| `Def_AlgebraicCurve_Repartitions` | 0 | 13 | 6 | 19 |
| `Def_AlgebraicCurve_AdelicIndex` | 5 | 42 | 21 | 68 |
| `Def_AlgebraicCurve_IsCurveOver` | 0 | 9 | 1 | 10 |
| `Def_AlgebraicCurve_RiemannRochRows` | 0 | 2 | 6 | 8 |
| `Def_AlgebraicCurve_PoleDivisorPackage` | 0 | 0 | 10 | 10 |
| **pin total** | **5** | **78** | **53** | **136** |
| shared `S_…` prelude (named lemmas + generic helpers) | 0 | 15 | 0 | 15 |

The row count 136 = 133 inventory rows + `Place.DCoordGenerates`, `HasCanonicalDivisor`,
`IsCurveOver` (the three `class`es the inventory tool drops). No declaration in the
seven modules is a *statement-identical* import except through a definitional alias:
the phase's objects (`LSpace`, `ell`, `adeleBdd`, `omegaSpace`, `genus`, the six RR
predicates, the Stichtenoth structures) are all absent from mathlib. The reuse is
proof-level plus five aliases.

## 2. Per-module tables

### 2.1 `Def_ModularCurve_CanonicalDivisor.lean` (16 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `Place.uniformizer` | BESPOKE | `IsDiscreteValuationRing.exists_irreducible` | def = `Classical.choose` of the mathlib existence; the *chosen* object is pin-only |
| `Place.ord_uniformizer` | PROOF-INGREDIENT | `Place.ord_coe_irreducible` (port) | `choose_spec` + port lemma |
| `Place.uniformizer_ne_zero` | PROOF-INGREDIENT | `Place.ord_zero` (port) | contradiction from `ord 0 = 0` |
| `Place.dCoord` | BESPOKE | `KaehlerDifferential.D` | def = `D K F v.uniformizer` |
| `Place.dCoord_ne_zero` | PROOF-INGREDIENT | `Submodule.span_zero_singleton`, `Submodule.mem_bot` | span of `0` is `⊥` |
| `Place.differentialCoeff` | BESPOKE | — | `Classical.propDecidable` choice; no mathlib declaration states this |
| `Place.exists_eq_smul_dCoord` | PROOF-INGREDIENT | `Submodule.span_singleton_eq_top_iff` / `Submodule.mem_span_singleton` | Scratch: proved from `DCoordGenerates.span_eq_top` |
| `Place.differentialCoeff_smul_dCoord` | PROOF-INGREDIENT | `dif_pos`, `Classical.choose_spec` | |
| `Place.differentialCoeff_unique` | PROOF-INGREDIENT | `smul_eq_zero`, `sub_eq_zero` | equivalently `smul_left_injective` |
| `Place.differentialCoeff_dCoord` | PROOF-INGREDIENT | `one_smul` | |
| `Place.differentialCoeff_zero` | PROOF-INGREDIENT | `zero_smul` | |
| `Place.differentialCoeff_smul` | PROOF-INGREDIENT | `mul_smul` | |
| `Place.ordDifferential` | BESPOKE | — | def = `v.ord (v.differentialCoeff ω)` |
| `Place.gate_ordDifferential_dCoord` | PROOF-INGREDIENT | `Place.ord_one` (port) | |
| `Place.ordDifferential_smul` | PROOF-INGREDIENT | `Place.ord_mul` (port) | |
| `Place.DCoordGenerates` | BESPOKE | `finrank_eq_one_iff_of_nonzero` | the class is pin; its content is `span {dCoord} = ⊤`, mathlib-equivalent to `finrank = 1` |

### 2.2 `Def_AlgebraicCurve_CanonicalDivisor.lean` (5 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `HasCanonicalDivisor` | BESPOKE | — | class asserting a divisor with `D v = v.ordDifferential ω`; no mathlib analogue |
| `canonicalDivisorOf` | BESPOKE | `Classical.choose` | choice from the class field |
| `canonicalDivisorOf_apply` | PROOF-INGREDIENT | `Classical.choose_spec` | |
| `canonicalClass` | BESPOKE | `QuotientAddGroup.mk`, `Classical.propDecidable` | the `propDecidable` branch must be kept (work order §3) |
| `genus` | BESPOKE | — | `(deg K + 2).toNat / 2`; mathlib has **no** `genus` at all (see §5) |

### 2.3 `Def_AlgebraicCurve_Repartitions.lean` (19 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `Place.adicValuation_le_one_of_mem` | PROOF-INGREDIENT | `HeightOneSpectrum.intValuation_le_one` | via port's `adicValuation_coe` |
| `Place.adicValuation_algebraMap_le_one` | PROOF-INGREDIENT | port `Place.algebraMap_mem'` | |
| `Place.adicValuation_eq_exp_neg_ord` | PROOF-INGREDIENT | `WithZero.exp_log` | |
| `Place.adicValuation_le_exp_iff` | PROOF-INGREDIENT | `WithZero.exp_le_exp`, `neg_le` | |
| `Place.adicValuation_le_one_iff` | PROOF-INGREDIENT | `WithZero.exp_zero` | corollary of the above at `n = 0` |
| `Place.not_adicValuation_le_one_iff` | PROOF-INGREDIENT | `not_or`, `not_le` | |
| `repartitions` | BESPOKE | `Algebra.adjoin`; route: `RestrictedProduct` | def is pin; see §4 route R3 |
| `mem_repartitions_of_finite` | PROOF-INGREDIENT | `Algebra.subset_adjoin` | |
| `mem_repartitions_of_finite_ord` | PROOF-INGREDIENT | `Set.ext`, `not_adicValuation_le_one_iff` | |
| `mem_repartitions_of_forall_le_exp` | PROOF-INGREDIENT | `Finsupp.support`, `Finset.finite_toSet`, `Finsupp.mem_support_iff` | |
| `repartitionsOf` | BESPOKE | `Valuation.map_add`/`map_mul` (closure) | `Submodule` of bounded repartitions |
| `mem_repartitionsOf_iff` | PROOF-INGREDIENT | `forall_congr'`, `adicValuation_le_exp_iff` | |
| `repartitionsOf_mono` | PROOF-INGREDIENT | `WithZero.exp_le_exp`, `Finsupp.le_def` | |
| `riemannRochSpace` | BESPOKE | `Valuation.map_add`/`map_mul` (closure) | no mathlib `LSpace` |
| `mem_riemannRochSpace_iff` | PROOF-INGREDIENT | `forall_congr'` | |
| `principalRepartitions` | BESPOKE | `LinearMap.range`, `Submodule.restrictScalars` | body is mathlib terms on the pin's `Algebra.linearMap` |
| `mem_principalRepartitions_iff` | PROOF-INGREDIENT | `LinearMap.mem_range`, `Submodule.restrictScalars_mem` | |
| `H1` | BESPOKE | — | quotient, pin-only |
| `genusFF` | BESPOKE | — | `finrank K (H1 0)`, pin-only |

### 2.4 `Def_AlgebraicCurve_AdelicIndex.lean` (68 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `LSpace` | BESPOKE | — | alias of `riemannRochSpace`; statement-checker needs the name |
| `ell` | BESPOKE | `Module.finrank` | |
| `mem_lSpace_iff` | PROOF-INGREDIENT | `Iff.rfl` | |
| `mem_lSpace_iff_ord` | PROOF-INGREDIENT | `WithZero.exp_le_exp`, `WithZero.exp_log` | |
| `lSpace_mono` | PROOF-INGREDIENT | `WithZero.exp_le_exp.mpr` | |
| `algebraMap_mem_lSpace_zero` | PROOF-INGREDIENT | `Place.adicValuation_algebraMap_le_one` | |
| `one_mem_lSpace_zero` | PROOF-INGREDIENT | `Algebra.linearMap` | |
| `ConstantsAreBase` | BESPOKE | — | `Prop`, pin-only |
| `ell_zero_eq_one_of_constantsAreBase` | PROOF-INGREDIENT | `LinearMap.finrank_range_of_inj`, `Module.finrank_self` | |
| `adeleBdd` | BESPOKE | — | bounded adeles `Submodule`, pin-only |
| `mem_adeleBdd` | PROOF-INGREDIENT | `Iff.rfl` | |
| `adeleBdd_mono` | PROOF-INGREDIENT | `WithZero.exp_le_exp.mpr` | |
| `diagonalHom` | BESPOKE | `LinearMap` | pin-only diagonal map |
| `diagonalHom_apply` | PROOF-INGREDIENT | `rfl` | |
| `diagonalHom_injective` | PROOF-INGREDIENT | `congrFun`, `Classical.arbitrary` | |
| `diagonal_mem_adeleBdd_iff` | PROOF-INGREDIENT | `Submodule.mem_inf`-style simp | |
| `adeleSpace` | BESPOKE | `iSup` | colimit of `adeleBdd`, pin-only |
| `adeleBdd_le_adeleSpace` | **SUBSTITUTE** | `le_iSup` | Scratch: `example … := le_iSup adeleBdd D` |
| `diagonal_mem_adeleSpace` | PROOF-INGREDIENT | port `HasPrincipalDivisors.exists_divisor`, `WithZero.exp_log` | |
| `globalSub` | BESPOKE | `LinearMap.range` | range of the diagonal, pin-only |
| `diagonal_mem_globalSub` | **SUBSTITUTE** | `LinearMap.mem_range_self` | Scratch: `example … := LinearMap.mem_range_self _ f` |
| `map_diagonal_lSpace` | PROOF-INGREDIENT | `Submodule.mem_map`, `Submodule.mem_inf`, `LinearMap.mem_range` | |
| `lSpaceEquivAdeleBddInfGlobal` | PROOF-INGREDIENT | `Submodule.equivMapOfInjective`, `LinearEquiv.ofEq` | |
| `finrank_adeleBdd_inf_global_eq_ell` | PROOF-INGREDIENT | `LinearEquiv.finrank_eq` | Scratch: exact proof |
| `indexOfSpecialty` | BESPOKE | `Module.finrank` of a quotient | the pin's adelic index; keep it (work order §3) |
| `adeleBdd_directed` | PROOF-INGREDIENT | `Directed`, `sup` | |
| `mem_adeleSpace_iff` | PROOF-INGREDIENT | `Submodule.mem_iSup_of_directed` | Scratch: exact proof |
| `adeleBddPrincipal` | BESPOKE | `Submodule.comap`, `⊔` | |
| `indexOfSpecialty_eq` | PROOF-INGREDIENT | `rfl` | |
| `omegaSpace` | **SUBSTITUTE** | `Submodule.dualAnnihilator` | Scratch: `example … := rfl` against `(adeleBddPrincipal …).dualAnnihilator` |
| `omegaSpace_vanishBdd` | PROOF-INGREDIENT | `Submodule.mem_dualAnnihilator`, `Submodule.mem_sup_left` | |
| `omegaSpace_vanishGlobal` | PROOF-INGREDIENT | `Submodule.mem_dualAnnihilator`, `Submodule.mem_sup_right` | |
| `omegaSpace_antitone` | PROOF-INGREDIENT | `Submodule.dualAnnihilator_anti`, `Submodule.comap_mono` | |
| `omegaSpaceEquivIndexDual` | **SUBSTITUTE** | `Submodule.dualQuotEquivDualAnnihilator` | Scratch: `example … := rfl` (up to `.symm`) |
| `finrank_omegaSpace_eq_indexOfSpecialty` | PROOF-INGREDIENT | `Subspace.dual_finrank_eq` | Scratch: exact proof |
| `weilDifferentialModule` | BESPOKE | `iSup` | |
| `omegaSpace_le_weilDifferentialModule` | **SUBSTITUTE** | `le_iSup` | Scratch: `example … := le_iSup omegaSpace D` |
| `omegaSpace_directed` | PROOF-INGREDIENT | `omegaSpace_antitone` | |
| `mem_weilDifferentialModule_iff` | PROOF-INGREDIENT | `Submodule.mem_iSup_of_directed` | |
| `mulAdele` | BESPOKE | `LinearMap` | |
| `mulAdele_apply` | PROOF-INGREDIENT | `rfl` | |
| `mulAdele_one` | PROOF-INGREDIENT | `LinearMap.ext`, `one_mul` | |
| `mulAdele_mul` | PROOF-INGREDIENT | `mul_assoc` | |
| `mulAdele_mem_adeleBdd_sub` | PROOF-INGREDIENT | `Valuation.map_mul`, `WithZero.exp_log`, `WithZero.exp_add` | |
| `mulAdele_globalSub_le` | PROOF-INGREDIENT | `Submodule.map_le_iff_le_comap` | |
| `mulAdele_mem_adeleSpace` | PROOF-INGREDIENT | `mem_adeleSpace_iff`, port `HasPrincipalDivisors.exists_divisor` | |
| `adeleSpaceMul` | BESPOKE | `LinearMap.restrict` | |
| `adeleSpaceMul_coe` | PROOF-INGREDIENT | `rfl` | |
| `weilSmul` | BESPOKE | `LinearMap.dualMap` | |
| `weilSmul_apply` | PROOF-INGREDIENT | `rfl` | |
| `adeleSpaceMul_one` | PROOF-INGREDIENT | `LinearMap.ext`, `mulAdele_one` | |
| `adeleSpaceMul_mul` | PROOF-INGREDIENT | `mulAdele_mul` | |
| `weilSmul_one` | PROOF-INGREDIENT | `adeleSpaceMul_one` | |
| `weilSmul_mul` | PROOF-INGREDIENT | `LinearMap.dualMap_comp_dualMap` | |
| `weilSmul_injective` | PROOF-INGREDIENT | `Function.LeftInverse.injective`, `mul_inv_cancel₀` | |
| `weilSmul_mem_omegaSpace_add` | PROOF-INGREDIENT | `Submodule.mem_dualAnnihilator`, `Submodule.mem_sup` | bespoke statement, mathlib body |
| `weilSmul_mem_omegaSpace_of_mem_lSpace` | PROOF-INGREDIENT | `omegaSpace_antitone`, port `HasPrincipalDivisors.exists_divisor` | |
| `residuePairing` | BESPOKE | `LinearMap` | the pin's pairing; must be written |
| `residuePairing_apply_coe` | PROOF-INGREDIENT | `rfl` | |
| `residuePairing_injective` | PROOF-INGREDIENT | `LinearMap.ext`, `weilSmul_injective`, `sub_eq_zero` | no mathlib statement of this |
| `ell_sub_le_indexOfSpecialty` | PROOF-INGREDIENT | `LinearMap.finrank_le_finrank_of_injective` | Scratch: exact proof |
| `WeilDifferentialRankOne` | BESPOKE | — | `Prop`, pin-only |
| `HasWeilCanonicalDivisor` | BESPOKE | — | `Prop`, pin-only |
| `RiemannGenusReachedAt` | BESPOKE | — | structure, pin-only |
| `RiemannGenusReached` | BESPOKE | — | `Prop`, pin-only |
| `StichtenothGenusExists` | BESPOKE | — | `Prop`, pin-only |
| `RiemannGenusBounded` | BESPOKE | — | `Prop`, pin-only |
| `IndexOfSpecialtyFinite` | BESPOKE | — | `Prop`, pin-only |

### 2.5 `Def_AlgebraicCurve_IsCurveOver.lean` (10 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `IsCurveOver` | BESPOKE | — | class extending the port's `HasPrincipalDivisors`; pin-only |
| `IsCurveOver.hasPrincipalDivisors` | PROOF-INGREDIENT | structure projection `h.toHasPrincipalDivisors` | |
| `IsCurveOver.finite_residueField` | PROOF-INGREDIENT | class projection | |
| `IsCurveOver.instFiniteResidue` | PROOF-INGREDIENT | `FiniteResidue.mk` | |
| `IsCurveOver.instFreeKaehler` | PROOF-INGREDIENT | projection `.1` | |
| `IsCurveOver.finrank_kaehler` | PROOF-INGREDIENT | projection `.2` | |
| `IsCurveOver.instNontrivialKaehler` | PROOF-INGREDIENT | `Module.nontrivial_of_finrank_eq_succ` | Scratch: exact proof |
| `Place.deg_eq_one_of_isAlgClosed_of_finite` | PROOF-INGREDIENT | `IsAlgClosed.algebraMap_bijective_of_isIntegral` + `Module.finrank_of_bijective_algebraMap` (or `AlgEquiv.ofBijective` + `Module.finrank_self`) | Scratch proves the generic residue-field statement in one line |
| `IsCurveOver.deg_eq_one_of_isAlgClosed` | PROOF-INGREDIENT | previous lemma | |
| `IsCurveOver.forall_deg_eq_one_of_isAlgClosed` | PROOF-INGREDIENT | previous lemma | |

### 2.6 `Def_AlgebraicCurve_RiemannRochRows.lean` (8 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `RiemannInequality` | BESPOKE | — | `Prop`; `port_advise`'s "already present" match is the known false positive (`PLAN-P1.md` §1) |
| `RiemannIndexFormula` | BESPOKE | — | same |
| `WeilDualityAdelic` | BESPOKE | — | same |
| `WeilDuality` | BESPOKE | — | same |
| `WeilOmegaEllAgrees` | BESPOKE | — | same |
| `FunctionFieldRiemannRoch` | BESPOKE | — | same; mathlib has no `RiemannRoch` |
| `functionFieldRiemannRoch_of_riemann_and_duality` | PROOF-INGREDIENT | `linarith` | statement pin-only, proof pure arithmetic |
| `weilDuality_of_riemannIndex_of_adelic` | PROOF-INGREDIENT | `linarith` | same |

### 2.7 `Def_AlgebraicCurve_PoleDivisorPackage.lean` (10 rows)

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `PoleDivisorPackage` | BESPOKE | — | structure over `LSpace`/`LinearIndependent`; pin-only |
| `HasPoleDivisorPackage` | BESPOKE | — | `Nonempty`, pin-only |
| `TranscendenceTower` | BESPOKE | — | structure, pin-only |
| `TranscendenceTower.xF` | BESPOKE | `algebraMap` | |
| `TranscendenceTower.poleDivisor` | BESPOKE | `Divisor.pullback` (port) | |
| `TranscendenceTower.RegularOutside` | BESPOKE | — | `Prop`, pin-only |
| `IntegralBasisInLSpace` | BESPOKE | — | structure, pin-only |
| `HasIntegralBasisInLSpace` | BESPOKE | — | `Prop`, pin-only |
| `HasIntegralBasisRegularOutside` | BESPOKE | — | `Prop`, pin-only |
| `HasRegularFractionSubring` | BESPOKE | — | `Prop`, pin-only |

### 2.8 Shared `S_…` prelude — the load-bearing lemmas

Two names on the brief's load-bearing list — `residuePairing_injective` and
`ell_sub_le_indexOfSpecialty` — are defined in the pin's `Def_AlgebraicCurve_AdelicIndex.lean`
(not in the `S_` prelude) and are audited in §2.4; the table below covers the
declarations that live in the shared prelude itself.

| decl | class | mathlib name | evidence/note |
|---|---|---|---|
| `ell_le_ell_sub_single_add_deg` | PROOF-INGREDIENT | `LinearMap.quotKerEquivRange`, `Submodule.finrank_le`, `Submodule.finrank_quotient_add_finrank`, `Submodule.comapSubtypeEquivOfLe`, `IsLocalRing.residue_eq_zero_iff`, `IsDiscreteValuationRing.exists_irreducible` | statement has no mathlib analogue; every move is a mathlib lemma on the residue-field reduction |
| `ell_le_degree_add_ellZero` | PROOF-INGREDIENT | `Nat.strong_induction_on`, `Finsupp.support_nonempty_iff`, `Finsupp.mem_support_iff`, `Divisor.degree_single` | classical weak-RR induction |
| `lSpaceShiftEquiv` | PROOF-INGREDIENT | `Units.mulLeftLinearEquiv`/`LinearMap.mulLeft` (route), `mul_inv_cancel₀` | see route R2 |
| `adeleBddQuotSingleEquivResidueField` | PROOF-INGREDIENT | `LinearMap.quotKerEquivOfSurjective`, `Submodule.Quotient.equiv`, `IsLocalRing.residue_surjective`, `IsLocalRing.residue_eq_zero_iff` | statement pin-only |
| `finrank_adeleBdd_quotient` | PROOF-INGREDIENT | `Submodule.finrank_quotient_chain` (own helper), `Submodule.finrank_quotient_add_finrank`, `Submodule.quotientQuotientEquivQuotient` | no mathlib function-field-adeles statement |
| `lSpaceQuotientToAdeleBddQuotient` | PROOF-INGREDIENT | `Submodule.mapQ` | |
| `lSpaceQuotientToAdeleBddQuotient_injective` | PROOF-INGREDIENT | `Submodule.Quotient.mk_eq_zero`, `Submodule.Quotient.mk_surjective` | mathlib has no `Submodule.mapQ_injective` |
| `ell_sub_ell_le_degree_sub_degree` | PROOF-INGREDIENT | `Submodule.finrank_quotient_add_finrank`, `LinearMap.finrank_le_finrank_of_injective` | |
| `range_lSpaceQuotientToAdeleBddQuotient` | PROOF-INGREDIENT | `Submodule.mem_map`, `Submodule.mem_comap`, `Submodule.mem_sup` | |
| `finrank_adeleBddSup_quotient` | PROOF-INGREDIENT | `LinearMap.quotientInfEquivSupQuotient`, `Submodule.quotientQuotientEquivQuotient`, `Submodule.finrank_quotient_add_finrank` | |
| `finiteDimensional_lSpace` | PROOF-INGREDIENT | `Module.Finite.of_injective`, `Module.Finite.of_submodule_quotient`, `Module.Finite.equiv`, `Submodule.comapSubtypeEquivOfLe` | |
| `finiteDimensional_lSpace_zero_of_constantsAreBase` | PROOF-INGREDIENT | `LinearMap.finiteDimensional_range` | one line once `ConstantsAreBase` rewrites |
| `Submodule.nestedComapMapMkQEquiv` | PROOF-INGREDIENT | `Submodule.Quotient.equiv`, `LinearMap.quotKerEquivRange`, `Submodule.map_comap_subtype` | bespoke statement, mathlib body |
| `Submodule.finrank_quotient_chain` / `_chain'` | PROOF-INGREDIENT | `Submodule.quotientQuotientEquivQuotient`, `Submodule.finrank_quotient_add_finrank` | not in mathlib (negative N6) |
| `Submodule.finrank_quotient_chain_top`, `Submodule.comap_subtype_sup_of_le_of_le` | PROOF-INGREDIENT | `Submodule.map_comap_subtype`, `Submodule.map_injective_of_injective`, `Submodule.map_sup`, `Submodule.quotientQuotientEquivQuotient` | not in mathlib (negatives N6, N7) |

## 3. Reuse wins — the SUBSTITUTE rows and their evidence

All five compile in `Scratch.lean` (run is clean, exit 0):

1. **`AlgebraicCurve.omegaSpace D` = `Submodule.dualAnnihilator (adeleBddPrincipal K F D)`.**
   `def omegaSpace` is *literally* mathlib's annihilator; the port keeps the pin name
   as a one-line alias and owes no proof.
   ```lean
   example (D : Divisor K F) : omegaSpace D = (adeleBddPrincipal K F D).dualAnnihilator := rfl
   ```
2. **`omegaSpaceEquivIndexDual D` = `(Submodule.dualQuotEquivDualAnnihilator …).symm`.**
   ```lean
   example (D : Divisor K F) :
       omegaSpaceEquivIndexDual D
         = (Submodule.dualQuotEquivDualAnnihilator (adeleBddPrincipal K F D)).symm := rfl
   ```
3. **`adeleBdd_le_adeleSpace` is `le_iSup`.**
   ```lean
   example (D : Divisor K F) : adeleBdd D ≤ adeleSpace K F := le_iSup adeleBdd D
   ```
4. **`omegaSpace_le_weilDifferentialModule` is `le_iSup`.**
   ```lean
   example (D : Divisor K F) : omegaSpace D ≤ weilDifferentialModule K F := le_iSup omegaSpace D
   ```
5. **`diagonal_mem_globalSub` is `LinearMap.mem_range_self`** (`globalSub` is a `def`
   equal to `LinearMap.range (diagonalHom K F)`).
   ```lean
   example (f : F) : diagonalHom K F f ∈ globalSub K F := LinearMap.mem_range_self _ f
   ```

Two more rows are one-mathlib-call restatements worth banking even though the pin's
statement mentions the pin's own `dCoord`/`indexOfSpecialty` (so they stay
PROOF-INGREDIENT): `exists_eq_smul_dCoord` is `Submodule.span_singleton_eq_top_iff`,
and `finrank_omegaSpace_eq_indexOfSpecialty` is `Subspace.dual_finrank_eq`. Both were
proved in `Scratch.lean` from the mathlib lemma alone.

The whole `IsCurveOver` residue-degree block also collapses to one mathlib fact:
`Module.finrank_of_bijective_algebraMap (IsAlgClosed.algebraMap_bijective_of_isIntegral)`
gives `finrank k R = 1` for a finite integral algebra over an algebraically closed
field, which is `v.deg = 1` after unfolding the port's `Place.deg`.

## 4. Route options — chains that one mathlib fact could replace

* **R1 — the `differentialCoeff` block (`Def_ModularCurve_CanonicalDivisor` lines
  43–80).** The pin hand-rolls a coordinate functional on the rank-one `Ω[F⁄K]` and
  proves six properties by choice/uniqueness. Mathlib already owns this interface:
  `finrank_eq_one_iff_of_nonzero` turns `DCoordGenerates` + `dCoord_ne_zero` into
  `Module.finrank F Ω = 1` (and `IsCurveOver.finrank_kaehler` already gives it),
  `FiniteDimensional.basisSingleton` builds the basis with `b () = dCoord`, and
  `Module.Basis.repr`, `Module.Basis.coord`, `Module.Basis.repr_self`,
  `Module.Basis.sum_repr` supply `differentialCoeff`, `…_dCoord`, `…_zero`, `…_smul`.
  Recommended only if the port is willing to adopt `Module.Basis` as the interface
  (playbook §2.2 "adopt mathlib's type as the interface"); otherwise keep the pin's
  transcription. Scratch proves `FiniteDimensional.basisSingleton Unit h v hv` is
  available.
* **R2 — `lSpaceShiftEquiv` (S prelude).** The pin writes forward map, inverse map,
  `map_add'`, `map_smul'`, `left_inv`, `right_inv` by hand. Mathlib's
  `Units.mulLeftLinearEquiv` (used as `g.mulLeftLinearEquiv K F`, Scratch-verified)
  is exactly the ambient `F ≃ₗ[K] F` of multiplication by `g : Fˣ`; only the
  submodule compatibility (`LSpace D` ↦ `LSpace (D + Dg)`) remains bespoke. Route
  saves ~15 of the 35 lines and all the bijectivity bookkeeping.
* **R3 — `repartitions` (`Def_AlgebraicCurve_Repartitions` line 51).** The carrier
  `{α | {v | ¬ val(α v) ≤ 1}.Finite}` is definitionally mathlib's generic restricted
  product `Πʳ v : Place K F, [F, v.toValuationSubring]` (cofinite filter), and
  mathlib supplies `CommRing` on it (Scratch verifies `inferInstance`). **Limits:**
  (i) mathlib has no `Algebra F` instance for this restricted product, and the
  pointwise `Module F` instance *does not exist* (a valuation subring is not closed
  under arbitrary `F`-multiplication) — the pin's `F`-algebra structure is an
  almost-everywhere fact that must still be proved; (ii) `Algebra.adjoin` has no
  `adjoin_eq_self` shortcut. So R3 replaces the ring/carrier reasoning, not the
  `Subalgebra F` glue. Do **not** reach for `IsDedekindDomain.FiniteAdeleRing`: it is
  a restricted product of *completions* over `HeightOneSpectrum R`, whereas the pin's
  repartitions are functions `Place K F → F` with no completion (see N5).
* **R4 — the adelic index.** `finrank (omegaSpace D) = indexOfSpecialty D` is one
  fact (`Subspace.dual_finrank_eq`) once `omegaSpaceEquivIndexDual` is mathlib's
  `dualQuotEquivDualAnnihilator`; `ell_sub_le_indexOfSpecialty` is then one
  `LinearMap.finrank_le_finrank_of_injective`. The pin's 30-line index block is
  already at that cost after the SUBSTITUTE rows.
* **R5 — the `Submodule` chain helpers.** `finrank_quotient_chain`,
  `finrank_quotient_chain'`, `finrank_quotient_chain_top` and
  `comap_subtype_sup_of_le_of_le` exist only because mathlib has no packaged chain
  lemma; each is `Submodule.quotientQuotientEquivQuotient` +
  `Submodule.finrank_quotient_add_finrank`. Keeping one port-local helper is cheaper
  than inlining it four times.

## 5. Recorded negatives

1. **No `genus` anywhere in mathlib.** `grep -rin "\bgenus\b" Mathlib/` returns
   nothing: no arithmetic/geometric genus, no curve genus, no function-field genus.
   The pin's `genus` and `genusFF` are irreducible.
2. **No `RiemannRoch` / `Riemann–Roch` in mathlib** (any spelling).
3. **No function-field repartitions/adeles.** `repartition` matches only
   `BoxIntegral.*prepartition`. `NumberTheory.NumberField.AdeleRing` is
   `[NumberField K]`-only; **correction to the brief's seed:** the generic
   `IsDedekindDomain.FiniteAdeleRing` *does* exist for any Dedekind domain, but it is
   the restricted product of `adicCompletion`s over `HeightOneSpectrum R` with no
   `adeleBdd D`, no `adeleSpace` colimit, no quotient/index, and no relation to the
   pin's completion-free repartitions. No function-field `LSpace`/`ell`.
4. **No pin names:** `indexOfSpecialty`, `omegaSpace`, `weilDifferentialModule`,
   `WeilDifferentialRankOne`, `adeleBdd`, `adeleSpace`, `canonicalDivisor`,
   `HasCanonicalDivisor`, `ordDifferential`, `differentialCoeff`, `dCoord`,
   `StichtenothGenusExists`, `RiemannGenusReached(At)`, `H1`, `genusFF`.
5. **No `Algebra F` (and no pointwise `Module F`) on `RestrictedProduct`** over
   valuation subrings: the generic instances require `SMulMemClass (S v) F F`, false
   for `S v = v.toValuationSubring`. The pin's `repartitions` is an `F`-subalgebra by
   the a.e. argument, not pointwise.
6. **No `Submodule.mapQ_injective`.** Injectivity of the pin's
   `lSpaceQuotientToAdeleBddQuotient` must be proved through
   `Submodule.Quotient.mk_eq_zero` (as the pin does).
7. **No `Submodule.comap_subtype_sup_of_le_of_le`** (nor a `Submodule.comap_subtype_sup`).
8. **No `Submodule.finrank_quotient_chain` / `finrank_quotient_chain_top`**; only
   `Submodule.finrank_quotient_add_finrank` and
   `Submodule.quotientQuotientEquivQuotient` are packaged.
9. **No `Algebra.adjoin_eq_self`** (nor `adjoin_eq_top`); collapsing the pin's
   `Algebra.adjoin F` to the a.e.-integral subalgebra needs
   `le_antisymm` + `Algebra.adjoin_le_iff` + the closure facts.
10. **Seed correction — `Submodule.finrank_sup_add_finrank_inf_eq` is not used** by
    any of the seven modules or by the named S-prelude lemmas (`grep -c` = 0 in both
    the S file and `Def_AlgebraicCurve_AdelicIndex.lean`). It exists in mathlib but is
    not a proof ingredient here.
11. `port_advise`'s "already present" matches on the six `RiemannRochRows` predicates
    (against `EisensteinWeightOne.E1Chi3IsModular`) remain confirmed false positives.

## 6. What this changes for `WORKORDER-D-defs.md`

**Declarations whose proof the port does not owe** (mark as import-discharged in
`OWN_PROOFS` accounting; the *statements* still land for the checker):

- `AlgebraicCurve.omegaSpace` — alias of `Submodule.dualAnnihilator`.
- `AlgebraicCurve.omegaSpaceEquivIndexDual` — alias of
  `Submodule.dualQuotEquivDualAnnihilator`.
- `AlgebraicCurve.adeleBdd_le_adeleSpace` — `le_iSup`.
- `AlgebraicCurve.omegaSpace_le_weilDifferentialModule` — `le_iSup`.
- `AlgebraicCurve.diagonal_mem_globalSub` — `LinearMap.mem_range_self`.

**Declarations that are one mathlib call** (no bespoke mathematics; keep the pin
statements, drop the pin proof bodies in favour of the named lemma):
`Place.exists_eq_smul_dCoord`,
`Place.differentialCoeff_unique`/`_smul`/`_dCoord`/`_zero`,
`Place.dCoord_ne_zero`,
`IsCurveOver.instNontrivialKaehler`,
`Place.deg_eq_one_of_isAlgClosed_of_finite` (and its two corollaries),
`finrank_omegaSpace_eq_indexOfSpecialty`,
`ell_sub_le_indexOfSpecialty`,
`ell_zero_eq_one_of_constantsAreBase`,
`finrank_adeleBdd_inf_global_eq_ell`,
`mem_adeleSpace_iff`,
`mem_weilDifferentialModule_iff`,
`finiteDimensional_lSpace_zero_of_constantsAreBase`.

**Statements to re-examine before transcribing** (design decisions, not deletions):

- `Place.differentialCoeff` and its six lemmas: decide whether to keep the pin's
  choice-based interface or adopt `Module.Basis`/`FiniteDimensional.basisSingleton`
  (route R1). If kept, the port's faithful transcription is fine.
- `repartitions`: decide whether the carrier is the pin's `Algebra.adjoin` or
  mathlib's `RestrictedProduct` (route R3). The `F`-algebra structure is bespoke
  either way; only the ring/carrier part is mathlib's.
- `lSpaceShiftEquiv`: rewrite on `Units.mulLeftLinearEquiv` (route R2) or keep the
  hand-built equivalence.
- Keep the four `Submodule` chain helpers as port-local (R5): mathlib has no
  packaged versions (negatives 6–8), so inlining is *not* cheaper.

**No change:** the `genus`/`canonicalClass` `propDecidable` branches, the adelic
`indexOfSpecialty` (not `ell (K − D)`), the six `RiemannRochRows` predicates, and the
Stichtenoth / `PoleDivisorPackage` structures — all recorded as BESPOKE negatives
(§5.1–5.4) and must be written as the pin writes them.

**Scratch evidence (probe file removed at the phase-2 closeout):** `lean/Scratch.lean`
(§3 and §4 examples, plus the `#check`
ledger of every named mathlib constant); command
`timeout 90 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false Scratch.lean`
from `lean/`, clean in ~4 s. Each individual probe during the audit stayed below the
90 s bound; the only inconclusive probe was a whole-`import Mathlib` variant (over
90 s in this checkout), which is why every probe imports narrow mathlib modules.
