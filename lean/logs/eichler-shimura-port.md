# Porting the Eichler–Shimura period map

Record of the port of the general-weight Eichler–Shimura period map and its
injectivity ([topics/eichlerShimura/TOPIC-period-map-injectivity.md](../topics/eichlerShimura/TOPIC-period-map-injectivity.md))
from the FLT pin `aa2d8b3` into `FLTForHuman/ModularForms/EichlerShimura/`.
This file is appended to per tier; the playbook is
[porting-playbook.md](../porting-playbook.md).

## Tier 0 — externals

**Module (later dissolved — see the note below).**
`FLTForHuman/ModularForms/EichlerShimura/Externals.lean` (new
directory `EichlerShimura/`; the lakefile already globs `.submodules`, so no
build-file change). Five public declarations, five `private` helpers, one
module header. No `sorry`/`admit`, no bare `import Mathlib` (13 specific
imports), no `p2m_*`.

> **Superseded (2026-09-28): `Externals.lean` was dissolved into four subject
> homes** so the generic facts are found where their neighbours live, exactly as
> the topic's §2 plan anticipated (playbook §9). The declarations and their
> proofs are unchanged; only the files moved:
> * `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` →
>   `FLTForHuman/Algebra/MvPolynomialHomogeneous.lean` (44 lines);
> * `Complex.exists_hasDerivAt_of_starConvex` →
>   `FLTForHuman/ModularForms/Analytic/StarConvexPrimitive.lean` (175);
> * the two `UpperHalfPlane` facts plus the promoted
>   `UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero` →
>   `FLTForHuman/ModularForms/Analytic/CuspBoundedness.lean` (254);
> * `ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` →
>   `FLTForHuman/ModularForms/ModularGroup.lean` (143).
>
> `EichlerIntegral.lean` now imports `Analytic/CuspBoundedness`; `PeriodMap.lean`
> imports all four. The Tier-0 build timings below are the historical record for
> the original single module.

**Result.** All five green.

| # | declaration | status |
|---|---|---|
| 1 | `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | re-proved |
| 2 | `Complex.exists_hasDerivAt_of_starConvex` | re-proved |
| 3 | `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | re-proved |
| 4 | `UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty` | re-proved |
| 5 | `ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` | re-proved |

`#print axioms` on each: `propext, Classical.choice, Quot.sound` only.

### FLT → mathlib mapping

The pin's `p2m_export`/`p2m_open` list for these nodes is the FLT → mathlib
gap list; every name on it was checked against `v4.34.0`. **None** of the five
statements is in mathlib, so all five were re-proved — but four of them are
thin wrappers over mathlib machinery, and only (2) and (3) had to reconstruct
real analysis.

| FLT name | `v4.34.0` | verdict |
|---|---|---|
| `MvPolynomial.IsHomogeneous.pderiv` | present (`RingTheory/MvPolynomial/EulerIdentity.lean#L47`) | used |
| `MvPolynomial.totalDegree_eq_zero_iff_eq_C` | present (`Algebra/MvPolynomial/Degrees.lean#L587`) | used |
| `MvPolynomial.coeff` | **renamed away** — no qualified name; dot notation `p.coeff 0` | adaptation |
| `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` | present (`Analysis/Calculus/ParametricIntervalIntegral.lean#L97`) | used by (2) |
| `DifferentiableOn.analyticOnNhd` | present (`Analysis/Complex/CauchyIntegral.lean#L710`), takes `IsOpen` *second* | used by (2) |
| `Complex.continuous_ofReal`, `HasDerivAt.ofReal_comp` | present (`Analysis/Complex/RealDeriv.lean#L102` for the latter) | used by (2) |
| `Function.Periodic.cuspFunction` and its `UpperHalfPlane` alias | present (`Analysis/Complex/Periodic.lean#L119`, `NumberTheory/ModularForms/QExpansion.lean`) | used by (3),(4) |
| `UpperHalfPlane.differentiableOn_cuspFunction_ball` | present (`QExpansion.lean#L107`) | used by (3) |
| `UpperHalfPlane.analyticAt_cuspFunction_zero`, `cuspFunction_apply_zero` | present (`QExpansion.lean#L113,L119`) | used by (4) |
| `UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero` | present (`QExpansion.lean#L75`) | used by (4) |
| `IsZeroAtImInfty.boundedAtFilter` | still present on `ZeroAtFilter` | used by (4) |
| `UpperHalfPlane.isBoundedAtImInfty_iff` | present (`FunctionsBoundedAtInfty.lean#L65`) | used by (3) |
| `dslope`, `sub_smul_dslope`, `Complex.differentiableOn_dslope` | present (`Analysis/Calculus/DSlope.lean#L35,L67`, `Analysis/Complex/RemovableSingularity.lean#L60`) | used by (3),(4) |
| `DifferentiableOn.isExactOn_ball`, `IsExactOn.with_val_at` | present (`Analysis/Complex/HasPrimitives.lean#L291,L119`) | used by (3),(4) |
| `isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero`, `convex_halfSpace_im_gt` | present (`Analysis/Calculus/MeanValue.lean`, `Analysis/Complex/Convex.lean`) | used by (4),(3) |
| `Complex.exp_two_pi_mul_I` | present (`Analysis/SpecialFunctions/Trigonometric/Basic.lean#L1224`) | used by private `qParam_add_period` |
| `ModularGroup.T`, `coe_T_zpow`, `det_coe`, `coe_mul`, `coe_inv`, `coe_neg` | present (`NumberTheory/Modular.lean`, `LinearAlgebra/Matrix/SpecialLinearGroup.lean`) | used by (5) |
| `Int.exists_gcd_one`, `Int.isCoprime_iff_gcd_eq_one`, `Int.gcd_eq_zero_iff` | present | used by (5) |
| parabolic classification | **absent** — no `ModularGroup.IsParabolic` conjugacy normal form; (5) is genuinely new | re-proved |

### Deduplication

The pin proves `hasDerivAt_qParam`, `qParam_add_period` and
`apply_eq_apply_of_hasDerivAt_zero` **twice** (byte-identical inside both
`S_UpperHalfPlane_*` files). They are proved once here (playbook §2, §7 item 7).
The private helpers are:

* `mvPolynomial_isHomogeneous_iterate_pderiv`
* `complex_radialPrimitive` (body of (2))
* `UpperHalfPlane.hasDerivAt_qParam`, `UpperHalfPlane.qParam_add_period`,
  `UpperHalfPlane.ofComplex_coe_add_real`,
  `UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero`,
  `UpperHalfPlane.exists_periodic_primitive` (body of (4))
* `ModularGroup.det_entries`, `ModularGroup.mul_entry`, `ModularGroup.inv_entries`,
  `ModularGroup.exists_col_eq`, `ModularGroup.eq_T_zpow_of_col`,
  `ModularGroup.exists_isCoprime_fixed`,
  `ModularGroup.exists_conj_T_zpow_of_trace_eq_two`

### v4.34 adaptation friction

1. **`MvPolynomial.coeff` is gone as a qualified name.** The pin's
   `coeff 0 ((pderiv k)^[n] φ)` becomes `((pderiv k)^[n] φ).coeff 0`; the
   `totalDegree_eq_zero_iff_eq_C` statement still prints `p.coeff 0`.
2. **`differentiableOn_dslope` moved** from where the pin expected it
   (`Analysis/Complex/RemovableSingularity.lean`), and the `analyticOnNhd`
   introduction lives in `CauchyIntegral.lean`, not `FDeriv/Analytic.lean`.
3. **`convert h2 using 1` reorders goals at `v4.34.0`.** The pin's
   `convert h2 using 1; · rfl; · rfl; <derivative equality>` broke in two
   places; replaced by `refine h2.congr_deriv ?_` followed by the derivative
   computation, which is order-independent.
4. **`open UpperHalfPlane` re-introduces the `I` ambiguity** with `Complex.I`
   (the point `UpperHalfPlane.I` vs. the imaginary unit). Resolved by writing
   `UpperHalfPlane.I` explicitly at the seven sites; the notation scope
   `open scoped UpperHalfPlane` gives `ℍ` without opening the namespace.
5. **One `linter.unusedTactic` warning** in the pin's
   `all_goals first | rfl | simp | (funext z; simp)`: the last alternative is
   never reached at `v4.34.0`, so it was dropped to keep the module
   warning-free.

### Build discipline

Bounded throughout; `Scratch.lean` (gitignored) per component. Timings below;
all well inside the `≤ 30 s` expectation, no heartbeat change and no `set_option
maxHeartbeats`/`maxRecDepth` added.

* `lake env lean Externals.lean`: 3.2 s after the last edit.
* `lake build FLTForHuman.ModularForms.EichlerShimura.Externals`: 8.6 s wall
  (5.7 s build, 3100 jobs).
* whole `lake build` (after the module was cached): 3.3 s wall, 4344 jobs, green.

### Open item

None for this tier. The module is self-contained; the Tier 1 definitions
(`BinaryForm`, `CoeffCohomology`, `EichlerIntegral`) are the next consumer and
are not part of this tier.

## Tier 1 — definitions

**Modules.** Three, in dependency order, each built green before the next was
started:

| module | source (pin `aa2d8b3`) | lines |
|---|---|---|
| `FLTForHuman/ModularForms/EichlerShimura/BinaryForm.lean` | `Def_HeckeEis_BinaryFormRep.lean` L9–91 | 148 |
| `FLTForHuman/ModularForms/EichlerShimura/CoeffCohomology.lean` | `Def_Gamma0CoeffCohomology.lean` L9–122 | 188 |
| `FLTForHuman/ModularForms/EichlerShimura/EichlerIntegral.lean` | `Def_HeckeEis_EichlerIntegral.lean` L12–110 | 184 |

`BinaryForm.lean` was found already present (untracked) when this tier began —
the residue of the stalled first attempt. It was read, checked against the pin
declaration by declaration, and **verified green** (`lake build` 3.4 s) before
being kept; the two downstream modules were written in this session. All three
carry a header docstring (subject, pin and public URL, assumptions, divergence),
specific imports only — no bare `import Mathlib` — and no `sorry`/`admit`.

**Result.** All 46 transcribed declarations green; 3 deferred in total (below).
Chain: `BinaryForm → CoeffCohomology → EichlerIntegral`. No `set_option
maxHeartbeats`/`maxRecDepth` anywhere, and `Externals.lean` was not touched.

### Landed declarations

| module | declarations |
|---|---|
| `BinaryForm` | `eval_smul_of_isHomogeneous`, `BinaryForm`, `binarySubst`, `binarySubst_X`, `binarySubst_C`, `binarySubst_one`, `binarySubst_mul`, `binarySubst_mem`, `binaryFormRepSL`, `binaryFormRepSL_apply_coe`, `binaryFormAlphaAdj`, `binaryFormAlphaAdj_apply_coe` |
| `CoeffCohomology` | `coeffCocycles`, `mem_coeffCocycles_iff`, `coeffCoboundaryMap`, `coeffCoboundaryMap_apply`, `coeffCoboundaries`, `mem_coeffCoboundaries_iff`, `coeffCoboundaries_le_coeffCocycles`, `IsParabolicCocycle`, `coeffParabolicCocycles`, `mem_coeffParabolicCocycles_iff`, `coeffParabolicCocycles_le_coeffCocycles`, `coeffCoboundaries_le_coeffParabolicCocycles`, `coeffH1par`, `instAddCommGroupCoeffH1par`, `instModuleCoeffH1par`, `coeffH1parMk`, `coeffH1parMk_surjective`, `coeffH1parMk_eq_zero_iff` |
| `EichlerIntegral` | `isHomogeneous_line`, `isHomogeneous_linePow`, `linePow`, `coe_linePow`, `jFactor`, `jFactor_eq_denom`, `jFactor_ne_zero`, `coe_smul_mul_jFactor`, `binarySubst_line`, `binaryFormRepSL_linePow`, `IsEquivariantPrimitiveWith`, `IsEquivariantPrimitiveWith.cocycle`, `.sub_eq_cocycle`, `.apply_smul`, `.cocycle_mem_coeffCocycles`, `IsEichlerIntegral` |

All names and signatures are the pin's verbatim; the one textual change is
`IsEichlerIntegral`'s `MvPolynomial.coeff d p` → `p.coeff d` (the same
adaptation Tier 0 recorded for this name).

### Deferred / deliberately omitted

| declaration(s) | reason |
|---|---|
| `evalRow`, `evalRow_eq_of_unit_mul`, `binaryFormEval`, `binaryFormEval_mk` | projective-line `Eval` block; needs `Def_ProjectiveLineMatrixAction`, outside this cone (topic §6) |
| `coeffHeckeFun`, `coeffHeckeFun_apply`, `coeffHeckeFun_trivial` | Hecke section; needs `Def_Gamma0HeckeOperatorHom`, not in the period-map cone (topic §1) |
| `eichlerShimuraMap`, `eichlerShimuraMap_def`, `eichlerShimuraMap_of_not_exists` | **deliberate divergence** (topic §3 Tier 1): the `dif`ed map is replaced in Tier 3 by a structural `periodMap` built from `Classical.choose` of `exists_isEichlerIntegral`; recorded in the `EichlerIntegral.lean` header |
| `jFactor_pow_mul_eval_binaryFormRepSL` | Tier 2 leaf, not part of the definitions tier |
| `binarySubst_adjugate_comp_smul`, `binaryFormRepSL_neg_one_apply`, `coeff_single_one_eq_eval_of_mem_binaryForm`, `mem_range_binaryFormRepSL_T_zpow_sub_one` | Tier 2 leaves |

### FLT → mathlib mapping (the shape decisions)

| FLT construct | `v4.34.0` interface adopted | how |
|---|---|---|
| `BinaryForm K n` | `MvPolynomial.homogeneousSubmodule (Fin 2) K n` | `abbrev`; the port's type from the first declaration (playbook §3.8) |
| `binarySubst` | `MvPolynomial.aeval` + `C`/`X` | verbatim |
| `binaryFormRepSL` | `Representation K SL(2, ℤ) (BinaryForm K n)` | `.toLinearMap.restrict` of the substitution, verbatim |
| `coeffH1par` | `↥Z¹_par ⧸ (B¹).comap Z¹_par.subtype` | `Submodule.Quotient`, `Submodule.comap`, `Submodule.mkQ`; the pin's quotient spelled directly |
| `jFactor` | `UpperHalfPlane.denom ∘ Matrix.SpecialLinearGroup.mapGL ℝ` | `jFactor_eq_denom` is the bridge; `denom_apply` computes it |
| `IsEichlerIntegral` | `HasDerivAt` coefficientwise | `MvPolynomial.coeff`, verbatim apart from dot notation |
| `IsEquivariantPrimitiveWith` | `Representation` + `ℍ`-action | `Subgroup.coe_mul`, `mul_smul` in `cocycle_mem_coeffCocycles` |

### v4.34 adaptation friction (6 items, all resolved in-module)

1. **`Mathlib.LinearAlgebra.Quotient` is a directory, not a module.** Import
   `Mathlib.LinearAlgebra.Quotient.Basic`; the bare path errors with a missing
   `…/Quotient.olean`. (`Submodule.mkQ` is in `Quotient/Defs.lean`, reachable
   from `Basic`.)
2. **`Matrix.trace` needs its own import.** Without
   `Mathlib.LinearAlgebra.Matrix.Trace`, `(((γ : SL(2, ℤ)) : Matrix (Fin 2)
   (Fin 2) ℤ)).trace` fails with `Invalid field trace: The environment does not
   contain Function.trace` because the matrix coercion is a function type and
   dot notation looks for `Function.trace`. Adding the import fixes it; the
   statement is unchanged.
3. **`UpperHalfPlane.ofComplex` is not reachable through `MoebiusAction`.**
   `IsEichlerIntegral` needs `Mathlib.Analysis.Complex.UpperHalfPlane.Topology`
   (where the `OpenPartialHomeomorph` `ofComplex` is defined); `MoebiusAction`
   does not re-export it.
4. **`MvPolynomial.coeff` again** (as in Tier 0): written `p.coeff d` in
   `IsEichlerIntegral`.
5. **`denom` and `ModularGroup.denom_apply` live in**
   `Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` (`UpperHalfPlane.denom`
   for `GL (Fin 2) ℝ`, with the `SL(2, ℤ)` version under `namespace ModularGroup`),
   so no `NumberTheory.Modular` import is needed for `jFactor_eq_denom`.
6. **`Matrix.SpecialLinearGroup.mapGL`** is in
   `LinearAlgebra.Matrix.GeneralLinearGroup.Defs`, pulled in transitively by
   `MoebiusAction`; no extra import.

### Build discipline

Bounded throughout (`timeout 60 lake env lean`, `timeout 90 lake build
<module>`, `timeout 180 lake build`); no build approached its bound.

| command | wall | user |
|---|---|---|
| `lake build FLTForHuman.…BinaryForm` (cached deps) | 3.4 s build | — |
| `lake env lean FLTForHuman/…/CoeffCohomology.lean` | 3.9 s | 2.7 s |
| `lake build FLTForHuman.…EichlerIntegral` (incl. both deps) | 5.4 s | 3.9 s |
| whole `lake build` (all cached) | 8.7 s, 4348 jobs, **green** | 9.6 s |

No `sorryAx`: the three modules contain no `sorry`/`admit`, and the whole-tree
build completed successfully with 4348 jobs.

**Next.** Tier 2 leaves: `IsEichlerIntegral.add/.smul/.slash/.exists_sub_eq_const`,
`binaryFormRepSL_neg_one_apply`,
`coeff_single_one_eq_eval_of_mem_binaryForm`,
`mem_range_binaryFormRepSL_T_zpow_sub_one`,
`IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries`,
`jFactor_pow_mul_eval_binaryFormRepSL`.

## Tier 2 — leaves

**Modules touched.** `BinaryForm.lean` (148 → 324 lines) and
`EichlerIntegral.lean` (184 → 441 lines). No other module was edited except this
log. No `sorry`/`admit`, no bare `import Mathlib`, no `p2m_*`, and no
`set_option maxHeartbeats`/`maxRecDepth` added. `binarySubst_adjugate_comp_smul`
was **not** ported (Hecke-transport, outside this cone, topic §6).

**Result.** All nine leaves green; whole-tree `lake build` green (4348 jobs).
`#print axioms` on each of the nine: `propext, Classical.choice, Quot.sound` only.

| # | declaration | module | status |
|---|---|---|---|
| 1 | `binaryFormRepSL_neg_one_apply` | `BinaryForm` | proved |
| 2 | `coeff_single_one_eq_eval_of_mem_binaryForm` | `BinaryForm` | proved |
| 3 | `mem_range_binaryFormRepSL_T_zpow_sub_one` | `BinaryForm` | proved |
| 4 | `IsEichlerIntegral.add` | `EichlerIntegral` | proved |
| 5 | `IsEichlerIntegral.smul` | `EichlerIntegral` | proved |
| 6 | `IsEichlerIntegral.slash` | `EichlerIntegral` | proved |
| 7 | `IsEichlerIntegral.exists_sub_eq_const` | `EichlerIntegral` | proved |
| 8 | `jFactor_pow_mul_eval_binaryFormRepSL` | `EichlerIntegral` | proved |
| 9 | `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | `EichlerIntegral` | proved |

### Deduplication (playbook §2, §7 item 7)

`slash` and `exists_sub_eq_const` share the pin's byte-identical private
`EichlerIntegralAux` block. It is transcribed **once**, as eight `private`
declarations in `EichlerIntegral.lean`:

* `degExps`, `mem_degExps_iff`, `coeff_eq_zero_of_not_mem_degExps`,
  `eq_sum_degExps`, `coeff_binaryFormRepSL_eq_sum` — the weight-`n` monomial
  expansion;
* `hasDerivAt_smul_ofComplex`, `hasDerivAt_comp_smul`,
  `hasDerivAt_coeff_binaryFormRepSL` — the chain rule under the slash action.

The block's ninth member, the pin's `apply_eq_apply_of_hasDerivAt_zero`, is
**not** re-derived: `ModularForms/Analytic/CuspBoundedness.lean` publishes it as
`UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero`, and `exists_sub_eq_const`
uses that copy (playbook §9). `EichlerIntegral.lean` imports
`FLTForHuman.ModularForms.Analytic.CuspBoundedness`.

Two further private groups were needed, also factored rather than inlined:
`BinaryForm.lean` carries the unipotent computation as
`X_pow_mul_X_pow_mem`, `mono`, `coe_mono`, `binaryFormRepSL_T_zpow_mono`,
`mono_mem_range_T_zpow_sub_one`; and `EichlerIntegral.lean` carries the evaluation
bridge of #8 as `eval_binarySubst` and `det_entries_GL`.

### Checker-eye statement diff

Re-ran `lean/spec/check_flt_statements.py`'s `raw_declarations` (unmodified) over
the two port modules against the nine `Theorems/Thm_HeckeEis_*.lean` wrappers:
**7 of 9 token-identical, 2 differing** — and both differences are the same
recorded `v4.34.0` adaptation:

* `coeff_single_one_eq_eval_of_mem_binaryForm`: pin
  `MvPolynomial.coeff (Finsupp.single 1 n) P` → port
  `P.coeff (Finsupp.single 1 n)`;
* `mem_range_binaryFormRepSL_T_zpow_sub_one`: pin
  `MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) K) = 0` →
  port `(P : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 n) = 0`.

Both are forced: `MvPolynomial.coeff` is no longer a usable qualified name in
`v4.34.0` (`#check MvPolynomial.coeff` → `unknown constant`; the projection is
`AddMonoidAlgebra.coeff`, reached by dot notation). The Tier 0 and Tier 1 records
already list this adaptation, and the `BinaryForm.lean` Tier-2 docstring repeats
it. The remaining seven (including all six `EichlerIntegral` statements, with
`f ∣[((n : ℤ) + 2)] δ` spelled verbatim) match exactly.

### v4.34 adaptation friction (all resolved in-module)

1. **`SL_slash_apply` is namespaced.** It is `ModularForm.SL_slash_apply`
   (`NumberTheory/ModularForms/SlashActions.lean#L162`); the statement still uses
   the `∣[k]` notation, which requires `open scoped ModularForm`.
2. **`UpperHalfPlane.hasStrictDerivAt_smul` needed its own import.**
   `Mathlib.Analysis.Complex.UpperHalfPlane.Manifold`; neither `MoebiusAction`
   nor `Topology` re-exports it.
3. **`MvPolynomial.coeff_sub` lives in `Algebra/MvPolynomial/CommRing.lean`**
   (not reachable from `Homogeneous`); added that specific import for
   `exists_sub_eq_const`.
4. **`.coeff d` in a `HasDerivAt` *derivative* slot must be parenthesised.**
   `HasDerivAt A X.coeff d z₀` parses `X.coeff` as the derivative argument and
   `d`/`z₀` as further arguments to `HasDerivAt`; the pin's prefix form
   `coeff d X` did not have this problem. Fixed by writing
   `HasDerivAt A (X.coeff d) z₀`.
5. **A universe-polymorphic local `have` is rejected.**
   `have h : ∀ {K : Type*} [CommRing K] … := by …` fails with
   `AddConstAsyncResult.commitConst: constant has level params [u_1] but expected []`.
   The pin's `PeriodFnAux.eval_binarySubst`/`det_entries` were therefore promoted
   to `private` **top-level** declarations (`eval_binarySubst`,
   `det_entries_GL`) rather than kept as local hypotheses.
6. **Deprecations inherited from the pin, fixed for a warning-free module:**
   `dif_pos` → `dite_eq_left`; `if_neg` → `ite_eq_right`; `if_pos` →
   `ite_eq_left`; `MvPolynomial.coeff_add` → `AddMonoidAlgebra.coeff_add` plus
   `Finsupp.add_apply`; and one `convert … <;> try rfl` simplified to
   `convert …; try rfl`.

### Build discipline

Bounded throughout; no build approached its bound, and every `lake env lean` was
run on a cached tree.

| command | wall | note |
|---|---|---|
| `lake env lean …/BinaryForm.lean` (first, before warning cleanup) | 4.1 s | green |
| `lake build FLTForHuman.…BinaryForm` | 4.8 s | 3.2 s build, 1844 jobs |
| `lake env lean …/EichlerIntegral.lean` | 6.0 s | green, warning-free |
| `lake build FLTForHuman.…EichlerIntegral` | 6.8 s | 5.1 s build, 3105 jobs |
| whole `lake build` | 7.9 s | 4348 jobs, **green** |

No blocker. The one honest gap is the two-name statement divergence above, which
is a mathlib rename rather than a porting failure.

## Tier 3 — period map

**Module.** `FLTForHuman/ModularForms/EichlerShimura/PeriodMap.lean` (new, 1149
lines at landing). It imports the Tier 1–2 modules (`BinaryForm`,
`CoeffCohomology`, `EichlerIntegral`) and the four generic facts in their subject
homes — `Algebra/MvPolynomialHomogeneous`, `ModularForms/Analytic/StarConvexPrimitive`,
`ModularForms/Analytic/CuspBoundedness`, `ModularForms/ModularGroup` — plus the
specific mathlib modules
`NumberTheory/ModularForms/{Basic,CongruenceSubgroups,QExpansion,NormTrace,Cusps}`,
the `UpperHalfPlane` manifold/Moebius layer, `GeneralLinearGroup.FinTwo`,
`Mathlib.NumberTheory.Modular`, `Analysis/Calculus/Deriv/Polynomial` and
`Mathlib.Tactic`. No `sorry`/`admit`, no bare `import Mathlib`, no `p2m_*`, no
new `set_option maxHeartbeats`/`maxRecDepth`.

**Result.** Green: the eight-node analytic chain, the structural `periodMap`,
and the tier's target `periodMap_injective`.

### The analytic chain (group A)

| # | declaration (in `HeckeEis`) | status | pin `S_` lines |
|---|---|---|---|
| 1 | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | landed, token-identical | 305 |
| 2 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` | landed, token-identical | 92 |
| 3 | `IsEichlerIntegral.isBoundedAtImInfty_eval` | landed, token-identical | 178 |
| 4 | `exists_isEichlerIntegral` | landed, token-identical | 102 |
| 5 | `isEquivariantPrimitiveWith_of_isEichlerIntegral` | landed, token-identical | 46 |
| 6 | `IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range` | landed, token-identical | 85 |
| 7 | `isParabolicCocycle_cocycle_of_isEichlerIntegral` | landed, token-identical | 137 |
| 8 | `exists_isEichlerIntegral_isParabolicCocycle` | landed, token-identical | 27 |

**8 of 8 token-identical** to the pin's `Theorems/Thm_HeckeEis_*.lean` wrappers,
checked with the checker's own `raw_declarations`/`norm` (last confirmed after
the warning cleanup). The 305-line proof transcribed on the first full build
attempt; it needed three small shape fixes in `pm_coeff_ex_linePow` (`if_pos`
side conditions — see friction). The 186-line injectivity proof needed no shape
change beyond replacing the `dif`ed map by `periodMap`.

### The structural period map and injectivity (group B)

| declaration | status |
|---|---|
| `periodMap` — `CuspForm (Γ₀ N) (n+2) →ₗ[ℂ] coeffH1par ((binaryFormRepSL ℂ n).comp (Γ₀ N).subtype)` | landed, structural |
| `periodMap_eq_coeffH1parMk` | landed |
| `periodMap_injective` | **landed — the tier's target** |

`#print axioms HeckeEis.periodMap_injective` and
`HeckeEis.periodMap_eq_coeffH1parMk`: `[propext, Classical.choice, Quot.sound]`
only. No `sorryAx`.

### Recorded divergence (playbook §7.4)

The module does **not** declare `eichlerShimuraMap`, `eichlerShimuraMap_def`,
`eichlerShimuraMap_of_not_exists`; it does not state the pin's
`eichlerShimuraMap_add`/`_smul`/`existsEichlerShimuraMapLinear`, which the
linear `periodMap` subsumes. `periodMap` is defined on cusp forms from
`Classical.choose` of `exists_isEichlerIntegral_isParabolicCocycle`, mapping to
`coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩`. The class
is proved independent of the choice by the private
`periodClass_eq_coeffH1parMk`, through `IsEichlerIntegral.exists_sub_eq_const`,
`IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` and
`coeffH1parMk_eq_zero_iff`; that independence is what makes `map_add'` and
`map_smul'` structural (built from `IsEichlerIntegral.add`/`.smul` and the
`IsEquivariantPrimitiveWith.add`/`.smul` companions). The divergence is recorded
in the module header.

### Deduplication (playbook §2, §7 item 7, §9)

* The pin defines the `rung` ladder **twice** (`LadderAux` in
  `eq_zero_of_eval_eq_const`, `LadderAux2` in `isBoundedAtImInfty_eval`); the
  port defines `pm_rung` once and both proofs use it.
* The pin's `iterate_pderiv_one_eq_zero_of_lt` is a special case of the Tier 0
  external, so it is not re-derived; the public
  `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` is used instead.
* The pin's byte-identical `periodic_slash_comp_ofComplex_of_conj_T_zpow_mem`
  and `Gamma_le_Gamma0` (duplicated across
  `isParabolicCocycle_cocycle_of_isEichlerIntegral` and
  `eichlerShimuraMap_injective`) are written once as
  `pm_periodic_slash_comp_ofComplex_of_conj_T_zpow_mem` and
  `pm_Gamma_le_Gamma0`; the injectivity proof reuses A7's helper.
* The pin's `EichlerLinAux.add`/`smul` (duplicated across the `_add`/`_smul`
  files) are written once as private `IsEquivariantPrimitiveWith.add`/`.smul`
  with their `cocycle_add`/`cocycle_smul` companions.

### v4.34 adaptation friction (all resolved in-module)

1. **`ℂ[X]` needs `open scoped Polynomial`.** In `exists_isEichlerIntegral` the
   private `linePowPoly : MvPolynomial (Fin 2) ℂ[X]` did not elaborate until
   `Polynomial` joined the scoped opens; without it `ℂ[X]` parses as `GetElem`.
2. **`coeff_add` is `protected`.** The pin's bare `coeff_add` is an unknown
   identifier; the proof writes `MvPolynomial.coeff_add`.
3. **`if_pos`/`if_neg` are deprecated.** Replaced by `ite_eq_left`/`ite_eq_right`.
   The pin's bare `if_pos` leaves the exponent-equality side goal to the
   following `ext`/`omega`; that does not carry over syntactically, so the
   condition is provided explicitly (`hcond`).
4. **`CuspForm.coe_add`/`coe_smul` are deprecated aliases** for
   `FunLike.coe_add`/`FunLike.coe_smul`; the linearity proofs use the latter.
5. **`MvPolynomial.monomial_mul` is deprecated** (alias of
   `monomial_mul_monomial`); the `hmon` computation uses the new name.
6. **`haveI` style linter.** The `FiniteIndex` instance in the injectivity
   proof is a `have`; the copy the pin places in
   `isParabolicCocycle_cocycle_of_isEichlerIntegral` was unnecessary and is
   dropped.
7. **Cosmetic residue.** Three `MvPolynomial.coeff_add` deprecation warnings
   (two in `pm_coeff_pderiv_one`, one in the `hEI₁` proof). The recommended
   `AddMonoidAlgebra.coeff_add` is stated at function level, and neither
   `Pi.add_apply` nor `Finsupp.add_apply` matched the elaborated pointwise sum
   there, so the qualified deprecated name is kept rather than a fragile
   rewrite. Warning only; the module is green.

### Build discipline

Bounded throughout; nothing approached a bound, so nothing was quarantined.

| command | wall | note |
|---|---|---|
| `lake env lean …/PeriodMap.lean` (final) | 9.0 s | green, 3 deprecation warnings |
| `lake build FLTForHuman.…PeriodMap` | 13.7 s | 3638 jobs, green |
| whole `lake build` | 1.2 s cached (8.3 s on the first pass) | 4349 jobs, green |
| `#print axioms HeckeEis.periodMap_injective` | 4.7 s | `propext, Classical.choice, Quot.sound` |

### Faithfulness check (reproduction)

The checker's `SOURCES`/`PORT_FILES` do not yet list the Eichler–Shimura
modules, so the tier-3 statement diff is run directly against the wrappers with
the checker's own `raw_declarations`:

```bash
cd lean && python3 - <<'PY'
import importlib.util, os
spec = importlib.util.spec_from_file_location("chk", "spec/check_flt_statements.py")
chk = importlib.util.module_from_spec(spec); spec.loader.exec_module(chk)
port = {r: (k, s) for r, k, s in chk.raw_declarations(
    open("FLTForHuman/ModularForms/EichlerShimura/PeriodMap.lean").read())}
root = os.path.expanduser("~/proj/fermats-last-theorem/Theorems")
files = {
 "IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv": "Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv",
 "IsEichlerIntegral.eq_zero_of_eval_eq_const": "Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const",
 "IsEichlerIntegral.isBoundedAtImInfty_eval": "Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval",
 "exists_isEichlerIntegral": "Thm_HeckeEis_exists_isEichlerIntegral",
 "isEquivariantPrimitiveWith_of_isEichlerIntegral": "Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral",
 "IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range": "Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range",
 "isParabolicCocycle_cocycle_of_isEichlerIntegral": "Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral",
 "exists_isEichlerIntegral_isParabolicCocycle": "Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle",
}
ok = 0
for suffix, stem in files.items():
    nm = "HeckeEis." + suffix
    src = {r: (k, s) for r, k, s in chk.raw_declarations(
        open(os.path.join(root, stem + ".lean")).read())}
    same = port[nm] == src[nm]; ok += same
    print(("IDENTICAL " if same else "MISMATCH  ") + nm)
print(f"{ok}/{len(files)} chain declarations token-identical to pin wrappers")
PY
```

(prints `8/8 chain declarations token-identical to pin wrappers`; the three
`periodMap*` names will not match by design — they are the recorded divergence.)

No blocker. The tier's target is unconditional and `sorry`-free.

## Verification (2026-09-28)

The four tiers are complete. Final state of the effort:

| module | lines | warnings |
|---|---:|---:|
| `Algebra/MvPolynomialHomogeneous.lean` | 44 | 0 |
| `ModularForms/Analytic/StarConvexPrimitive.lean` | 175 | 0 |
| `ModularForms/Analytic/CuspBoundedness.lean` | 254 | 0 |
| `ModularForms/ModularGroup.lean` | 143 | 0 |
| `EichlerShimura/BinaryForm.lean` | 324 | 0 |
| `EichlerShimura/CoeffCohomology.lean` | 188 | 0 |
| `EichlerShimura/EichlerIntegral.lean` | 441 | 0 |
| `EichlerShimura/PeriodMap.lean` | 1,162 | 0 |
| **total (module lines)** | **2,731** | |
| `spec/EichlerShimuraConsumer.lean` | 104 | 0 |

The Tier-0 facts were dissolved from the single `EichlerShimura/Externals.lean`
into the four subject homes above on 2026-09-28 (see the Tier-0 note); the table
is the post-move state.

* `timeout 180 lake build`: green, 4,349 jobs, no `sorry`/`admit`, no bare
  `import Mathlib`, no new `set_option maxHeartbeats`/`maxRecDepth`.
* `python3 spec/check_flt_statements.py`: **1,485 identical (76 promoted from
  pin-private), 0 mismatched, 0 missing, 22 own-proof exempted (1,507 port
  declarations checked)**. The 22 exemptions are the 17 pre-existing ones plus
  five from this effort: the three `periodMap*` names (the recorded divergence)
  and `coeff_single_one_eq_eval_of_mem_binaryForm` /
  `mem_range_binaryFormRepSL_T_zpow_sub_one` (the v4.34 `MvPolynomial.coeff`
  rename forces `(·).coeff`).
* `spec/EichlerShimuraConsumer.lean`: 78 `#check` lines and four executed
  compositions, including the pin's `eichlerShimuraMap_injective` reproduced
  through `periodMap`; builds clean, 0 errors/warnings.
* `#print axioms HeckeEis.periodMap_injective`:
  `[propext, Classical.choice, Quot.sound]`.
* `python3 tools/check_math_delimiters.py` / `check_math_escaping.py` on the
  topic: clean.

**Dedup realised.** The pin's 123-line `EichlerIntegralAux` block
(byte-identical across `slash` and `exists_sub_eq_const`) is written once; the
projectiveline `evalRow`/`binaryFormEval`, the `coeffHeckeFun` block, and the
pin's `dif`ed `eichlerShimuraMap*`/`_add`/`_smul`/`existsEichlerShimuraMapLinear`
are not ported; `UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero` is promoted
once in Tier 0 and reused in Tier 2.

**Estimate vs actual.** The plan priced the cone at ~3,400 lines (2,759 theorem
nodes + 442 definition modules + ~200 wrappers); the port is 2,731 module lines,
with the saving coming from the two dedups and from not transcribing the
subsumed wrappers.
