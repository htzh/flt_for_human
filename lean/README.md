# lean/ — FLT fragments as a Lean project

Companion to the `base/` and `math/` notes. Where those explain a step in prose,
`lean/` re-runs selected pieces of the [FLT formalization][flt] as our own Lean
code: a claim can then be checked rather than taken on faith, and a proof can be
restated in a form we find easier to read.

## Ground rules

- **Fragments only.** We copy small, self-contained definitions and lemmas out of
  FLT and adapt them. We do **not** `require` the FLT project or `import` its
  modules — a single FLT import can pull in a very large dependency cone and a
  build measured in hours. Every module here imports mathlib only.
- **Adapt, do not mirror.** The FLT proof stays the source of truth for
  correctness ([PROOF-PATH.md][proof-path]: "Where this prose and the Lean
  differ, the Lean is right"), but the presentation is ours: we may restate a
  lemma, generalize it, split it, or take a different mathlib route.
- **Cite the origin.** Each module opens with a header comment naming the FLT
  file it came from, pinned to `aa2d8b3` (never `/main`), and saying what we
  changed.
- **No silent gaps.** A module either compiles or carries an explicit, commented
  `sorry`; nothing is left merely asserted.

## Toolchain and mathlib

| component | version | where |
|---|---|---|
| Lean | `leanprover/lean4:v4.34.0` | `lean-toolchain` |
| mathlib | `v4.34.0` | `lakefile.lean` |

We pin a **mathlib release tag** so `lake exe cache get` can fetch the
community-built `.olean`s instead of compiling mathlib from source (hours of
work). We deliberately do not track FLT's own mathlib pin (`v4.33.0`): since we
rewrite fragments rather than import them, matching FLT exactly buys nothing,
and the current release is the better long-term base.

## Building

```bash
cd lean
lake build                   # the default target, FLTForHuman (both efforts)
```

The prebuilt mathlib oleans are already in place for the pinned release, so a
build needs no download. On a fresh checkout, fetch them once first:

```bash
lake exe cache get   # one-off: download the prebuilt mathlib oleans
```

### The mathlib cache

`lake exe cache get` is the only step that uses the cache. It downloads `.ltar`
archives into a pool and decompresses the oleans into
`.lake/packages/mathlib/.lake/build/`. Builds read oleans from `.lake` and never
touch the pool, so **the pool's location does not affect `lake build`**.

The pool lives at the standard per-user location, `~/.cache/mathlib` — 8906
archives, ~450 MB, shared with any other mathlib4 checkout. The server is
missing 2 of the 8908 archives; those modules simply compile locally on the first
build.

A re-fetch is needed only when the mathlib revision changes or `lean/.lake` is
removed (mathlib's `post_update` hook also runs `cache get` automatically after
`lake update`). A session that cannot write to `~`, such as the sandboxed agent,
must point `MATHLIB_CACHE_DIR` at a writable directory for that one command:

```bash
MATHLIB_CACHE_DIR="$PWD/.cache/mathlib" lake exe cache get
```

Such an override creates a second, project-local pool; `.cache/` is gitignored
alongside `.lake/` in case it does.

## Layout

| module | topic | notes |
|---|---|---|
| `FLTForHuman/Elliptic/Basic.lean` | shared setup | base change preserves `IsElliptic`; the `W⟮S⟯` point-group notation |
| `FLTForHuman/Elliptic/Universal.lean` | universal curve | coefficients as indeterminates, `polyToField`, `ringEval`, `specialize`. Ported from `Def_WeierstrassCurve_EDSEngine.lean` |
| `FLTForHuman/Elliptic/DivisionPolynomial.lean` | `ω` extras | `invar`, `ψc` + `ψc_spec`, `invarNum`/`invarDenom`, `complEDSAux`, `redInvarNum`; the rest of the multiplication-formula bridge follows |
| `FLTForHuman/Elliptic/EDS.lean` | EDS plumbing | `map_invar*`, universal `Param` indices, `universalNormEDS`, `normEDS_eq_aeval` |
| `FLTForHuman/Elliptic/EllSequence.lean` | EDS relators | `addMulSub`/`rel₄`/`net` aliases to mathlib `atom`/`atomRel`/`rel`; `HaveSameParity₄`/`StrictAnti₄`/`avg₄` and the `transf` transfer lemmas; `IsEllipticSequence (normEDS b c d)` |
| `FLTForHuman/Elliptic/Complement.lean` | complement EDS | `normEDS_mul_complEDS` and `normEDS_mul_complEDS_div`: the complement witnesses `normEDS m ∣ normEDS (n*m)` |
| `FLTForHuman/Elliptic/RedInvar.lean` | `ω` denominator | `normEDS_six_eq_mul`, `redInvarDenom`, `invarDenom_eq_redInvarDenom_mul` |
| `FLTForHuman/Elliptic/Net.lean` | EDS net | `net_normEDS` (full `IsEllipticNet`), `invar_normEDS`, `invar₂_normEDS`, `redInvar_normEDS` |
| `FLTForHuman/Elliptic/Omega.lean` | `y`-numerator | `preΨ₄_add_Ψ₂Sq_sq`, `φ_mul_ψ`, `ωe` + `ωe_spec` + `two_mul_ωe` |
| `FLTForHuman/Elliptic/MulFormula.lean` | multiplication formula | evaluation at the universal point, `ψᵤ`, `smulX`/`smulY`, `zsmul_point_eq_smulX_smulY` |
| `FLTForHuman/Elliptic/JacobianMulFormula.lean` | projective form | `smulPoly`/`smulField`, `dblXYZ`/`addXYZ`, `zsmul_eq_smulEval` |
| `FLTForHuman/Elliptic/Bridge.lean` | torsion bridge | `evalEval_ψ_sq`, `evalEval_φ`, `smul_eq_zero_iff_evalEval_ψ` |
| `FLTForHuman/Elliptic/TorsionCard.lean` | `n`-torsion cardinality | the Wronskian coprimality, the double-fiber engine, and **`card_torsion_of_isAlgClosed`** (`#E[n] = n²`) |
| `FLTForHuman/FieldTheory/CommonRoot.lean` | the generic kernel | `Polynomial.mem_range_of_unique_common_root`, `Polynomial.mem_range_of_eval_eq_const`, `Polynomial.irreducible_of_transitive_ringAut` — the segment's mathematical engine (math/010 §4, §6), over an arbitrary `F ⊆ L`, mathlib-only, with three concrete instantiations over `ℚ ⊆ ℂ` as the wire test. The port's first generic area, beside (not inside) either curve theory. FLT `P2M/Sol/S_Polynomial_mem_range_of_unique_common_root` / the three `Thm_Polynomial_*` wrappers |
| `FLTForHuman/ModularCurve/Defs/Laurent.lean` | q-substitution + coefficient change | `qExpand`, `qExpandₐ`, `coeffMap`, `coeffEmb`, `laurentBaseChange`, plus the interface lemmas `coeffMap_qExpand`, `coeffEmb_qExpand`, `coeffMap_injective`, `coeffEmb_injective`. **T16 adds** the promoted `coeffMap_coeffEmb_algHom`, the coefficient automorphism `coeffMapEquiv` (routed through `RingEquiv.ofBijective`) with `coeffMapEquiv_apply`, and `iota_injective` (`coeffEmb ∘ qExpand`). **Post-effort** adds the generic `laurentBaseChange_mono` and `qExpand_mem_laurentBaseChange` (moved here from `Defs/HeckeOperator.lean`). FLT `Def_ModularCurve_X0` 25–105, `Def_ModularCurve_LaurentCoeff` 16–123 + `S_ModularCurve_PhiGen_splits_of_prime`/`S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem` |
| `FLTForHuman/ModularCurve/Defs/Twist.lean` | the unit twist `q ↦ u q` | `qTwistFun`, `qTwist` + functoriality, `qTwist_qExpand`. **T14 adds** the unit-root iota `qTwist_iota_of_pow_eq_one` and the twist equivalence `qTwistEquiv` with its `qTwistEquiv_apply`/`coe_qTwistEquiv` unfolding lemmas. **T16 adds** the promoted `coeffMap_qTwist` (the audit's 41-copy transport bridge; it lives here, not in `Defs/Laurent.lean`, because it mentions `qTwist`). FLT `Def_ModularCurve_PhiGen` 18–96 + `S_ModularCurve_jqN_prime_not_mem_full` 115–147 + `S_ModularCurve_PhiGen_exists_phiGenDescends` |
| `FLTForHuman/ModularCurve/Defs/Jq.lean` | the `j`-series | `eisenstein4`, `etaProd`, the `Δ` unit, `jNum`, `jq` + its pole lemmas, `jqN`, `dedekindPsi`, `evalAtJ`, plus the interface lemmas `dedekindPsi_prime`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`, `aeval_jq_eq_zero`, `transcendental_jq`, and the shared triangularity `coeff_aeval_jq_neg` (promoted from T7 by T9; FLT repeats it privately in nine files). **T14 adds** `jqN_congr`, which FLT repeats `private` in the FFG spine and the `jqN` files. **The 2026-09-22 audit sweep adds** the two out-of-cone ψ facts `dedekindPsi_mul_prime` (indeg 20) and `dedekindPsi_pos` (indeg 76), which FLT publishes as `Them_` wrappers but the port had been re-proving privately in `Spine.lean` and again in T19's pin block. FLT `Def_ModularCurve_X0` 111–212 + `S_ModularCurve_jqN_prime_not_mem_full` 739–742 + `S_ModularCurve_dedekindPsi_{mul_prime,pos}` |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean` | the target statement | `FunctionFieldGeneration` and its `M = 1` case. FLT `Def_ModularCurve_X0` 233–242 |
| `FLTForHuman/ModularCurve/Defs/Polynomial.lean` | the polynomial datum | `ModularPolynomialData`, `modularPolynomialDataOne`. FLT `Def_ModularCurve_X0` 215–232 |
| `FLTForHuman/ModularCurve/Defs/Fields.lean` | the two function fields | `modularFunctionField`, `modularFunctionFieldFull`, `toAdjoin`, the degeneracy lemmas. **T16 adds** `w1_relfinrank_insert`, the relative-degree bridge `relfinrank E ℚ(α, E) = [E(α) : E]` (mathlib's tower API inside). **T18 adds** the strong-induction invariants `Tight`/`Gen`/`Hall` (moved out of `Spine.lean`), their bases `tight_one`/`gen_one`, and `gen_prime` — the T19 substitution (`Gen p` is definitional: both sides are `ℚ(j, j(q^p))`). FLT `Def_ModularCurve_X0` 246–348 + `S_ModularCurve_relfinrank_full_eq_mul`; `Tight`/`Gen`/`Hall`/`tight_one`/`gen_one` from `S_ModularCurve_functionFieldGeneration.lean` |
| `FLTForHuman/ModularCurve/Defs/PhiGen.lean` | the slot vocabulary | `cosetSubst`, `conj`, `phiProd`, `EvalSymm`, `PhiGenDescends`, `PoleOrderLE`/`TPoleOrderLE` + the promoted triangularity `poleOrderLE_aeval_jq`, **and the shared `TPoleOrderLE` prelude T10 promoted** (the closure `mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`, `jSimplePole_jqK`/`tPoleOrderLE_coeffEmb_iff`/`tPoleOrderLE_of_qExpand`, the conjugate bounds `conjPoleBound`/`tPoleOrderLE_conj*` and the coefficient bounds `tPoleOrderLE_coeff_X_sub_C`/`_mul`/`_prod`/`tPoleOrderLE_phiProd_coeff`) — FLT repeats that block across six developments (physically twelve `S_` files), so it is written once here and **T11 imports it**. FLT `Def_ModularCurve_PhiGen` 111–309 + the `S_` copies |
| `FLTForHuman/ModularCurve/Defs/TS.lean` | `j(u q ^ e)` | `TS` and its nine coefficient/substitution lemmas. **T14 adds** the `TS`-dependent shared prelude: `iota_jqN` (`coeffEmb (qExpand ℚ N (jqN d)) = TS K (N*d) 1`), the cycle `qTwist_TS_one_cycle`, the composition `qExpand_qTwist_TS` and `qExpand_qTwist_notMem_range_qExpand`. **T16 adds** the promoted `coeffMap_TS` (the audit's 14-copy transport bridge; it lives here, not in `Defs/Laurent.lean`, because it mentions `TS`). FLT `P2M/Sol/S_ModularCurve_functionFieldGeneration` 39–101 + `S_ModularCurve_jqN_prime_not_mem_full` 102–105, 149–156, 237–251 + `S_ModularCurve_jqN_pow_not_mem_adjoin_full` 431–442 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean` | the §2 collapse | `functionFieldGeneration_iff_full_eq`, Layer 0's only theorem. FLT `Thm_…_iff_full_eq` line 6 / `S_…_iff_full_eq` 11–21 |
| `FLTForHuman/ModularCurve/JqCoefficients.lean` | the low coefficients of `jq` | `coeff_jq_zero` (`744`), `coeff_jq_one` (`196884`). A *result*, not a definition: statement from base/004, proof by mathlib's pentagonal route (`tprod_one_sub_X_pow`) rather than FLT's cluster |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` | the conditional capstone | `Tight`/`Gen`/`Hall`, the proved strong induction `hall_all` (public since T20, for the capstone's corollary layer), the structure `Inputs` (FLT's 7 significant remaining statements), and `functionFieldGeneration_of (h : Inputs) : FunctionFieldGeneration N` — proved, with no `sorryAx`. T15–T19 discharged all seven fields, so `Capstone.lean` now makes it total |
| `FLTForHuman/ModularForms/QExpansionPrinciple.lean` | R1, the level-one q-expansion principle | `coeff_eq_zero_of_hasSum_of_slash_invariant` (verbatim from its pin wrapper): a holomorphic, `SL₂(ℤ)`-invariant `q`-series is constant. Plus our `mem_adjoin_jq_of_poleOrderLE_zero`, the `n = 0` end of R1's Hauptmodul form and the wire test. The port's first analytic module: the analysis is mathlib's `ModularForm.eq_const_of_weight_zero`; of the pin's 14 helpers only `mdifferentiable` needed a proof, one (`coeff_unique`) kept its pin argument because mathlib's replacement blows up on the bare function type, and the rest became mathlib calls. FLT `S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant` (186 lines) |
| `FLTForHuman/ModularForms/JqAnalyticModel.lean` | the analytic model of `jq` | `hasSum_jq_qParam` (verbatim): the formal Laurent series `jq` sums to `E₄(τ)³/Δ(τ)` on `ℍ`, coefficient by coefficient — the realization hypothesis T7 consumes, and the only bridge from `Defs/Jq.lean`'s `PowerSeries`-built `jq` to mathlib's `E₄`/`Δ`. Plus `E4_cube_div_discriminant_smul`, its `SL₂(ℤ)`-invariance. The pin's `qExpansion_*` cluster and its gluing to `eisenstein4`/`dedekindEtaUnit`/`jNum`; `hasSum_jNum_qParam` stays private. FLT `S_ModularCurve_hasSum_jq_qParam` + `…_hasSum_jNum_qParam` + `qExpansion_{E4,discriminant_*}` (~589 lines) |
| `FLTForHuman/ModularForms/Hauptmodul.lean` | the Hauptmodul form — R1 complete | `mem_adjoin_jq_of_hasSum_of_slash_invariant` (verbatim): a Laurent series realized by an `SL₂(ℤ)`-invariant function on `ℍ` lies in `ℚ[jq]`. It composes T5's kernel (on the holomorphic remainder) with this module's pole killing and T6's realization. Also **exports** `RealL` + its closure and `hasSum_qParam_mul{,_laurent}`: FLT duplicates the `RealL` block in its T8 file, so the port defines it once here and T8 imports it. FLT `S_ModularCurve_hasSum_qParam_mul` + `…_mul_laurent` + `…_exists_aeval_jq_sub_holomorphicAtInfty` + `…_mem_adjoin_jq_of_hasSum_of_slash_invariant` (~462 lines) |
| `FLTForHuman/ModularForms/Defs/HeckeOperator.lean` | the Hecke matrices and the operators `U_p`/`T_p` | `heckeMatrix` (`!![1, j; 0, p]`), `heckeDiagMatrix` (`!![p, 0; 0, 1]`) and their action on `ℍ`, plus the full FLT operator block (Hecke topic, Tier 0): `σ_hecke*`, `slash_hecke*_apply`, `heckeU`/`heckeT`, the three definitional rewrites, the `_apply`/`_zero` displays, the linearity algebra (`add`/`smul`/`neg`/`sub`) and `coeffHeckeT`/`coeffHeckeU` with its nine lemmas. mathlib has **no** Hecke operators, so this is a definitions port of `Def_ModularForm_HeckeOperator` lines 11–200 (41 declarations, verbatim). `val_heckeMatrix` is public because the Fricke pair consumes it, `val_heckeDiagMatrix` because the analytic layer does (SET-2 T3), and `upperTriangularGL`/`val_upperTriangularGL` because the cusp-class layer's rational model needs them (SET-2 T4; the pin has all three pairs public). The other `val_*`/`det_*`/`denom_*` helpers stay private |
| `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` | the Hecke representatives on `ℙ¹(𝔽_p)` | the shared block FLT writes publicly in `Def_CuspForm_Gamma1HeckeOperators.lean:82–455` and re-inlines into every slash-invariance `S_` file: `det_eq`, the four `_mul_of_eq` lemmas (**with the pin's `g' 1 0 = …` conjunct** the port's old private `PhiGenDescends` copy had dropped), `heckeRep`/`redMatrix`/`heckeRep_mul`, the `ZMod p` reindexing (`sum_range_eq_sum_zmod`/`heckeU_eq_sum_zmod`/`affinePerm`/`heckeMatrix_mul_of_dvd`) and the two workhorses `heckeU_slash_mapGL`/`heckeT_slash_mapGL`. Own module because the port has no `Gamma1` yet (the pin's placement divergence) |
| `FLTForHuman/ModularForms/HeckeInvariance.lean` | where `U_p`/`T_p` land (Tier 1, the `Γ₀` half) | the three public `Γ₀` slash-invariance statements, verbatim from their `Theorems/` wrappers: `heckeU_slash_eq_self_of_mem_Gamma0` (`p ∣ N`), `heckeT_slash_eq_self_of_mem_Gamma0` (`p` prime, `p ∤ N`), `heckeU_slash_eq_self_of_mem_Gamma0_div` (`p² ∣ N`). They wrap the representative workhorses; the `_div` case's `Γ₀(N/p) ↪ Γ₀(N)` bookkeeping is private. The Fricke pair moved to `HeckeFricke.lean` (SET-2 T2); this module imports it. FLT `S_ModularForm_hecke{U,T}_slash_eq_self_of_mem_Gamma0{,_div}` (~584 lines) |
| `FLTForHuman/ModularForms/HeckeFricke.lean` | the Fricke pair (SET-2 T2 — one development for two statements) | the two public Fricke statements, verbatim: `heckeU_add_slash_fricke_eq_zero` (`U_p f + f ∣ W = 0`) and `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke` (the `U_p`-plus-Fricke combination is a level-one form). FLT proves them in two independent `S_` files whose second re-derives a hand-rolled trace (`traceFun`/`traceForm`/`trace_slash_*`/`trace_holo`/`trace_bdd` + 15 `T`/`S`-generator helpers); the port writes that trace **once** as mathlib's `ModularForm.trace` and bridges it to the explicit `∑ j ∈ range p, X ∣ (S * T^j)` form through `coe_trace` + `sum_quotientFunc_eq`. Also `R j = S * T^j` once, one general `slash_scalar` (`f ∣[k] scalar u = u^(k-2) • f`) and one general `heckeU_slash_W`. FLT `S_ModularForm_heckeU_add_slash_fricke_eq_zero` + `…_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke` (531 lines) |
| `FLTForHuman/ModularForms/HeckeAnalytic.lean` | analytic regularity of `U_p`/`T_p` (SET-2 T3 — six `S_` files to one) | the seven public targets, verbatim from their `Theorems/` wrappers: `mdifferentiable_hecke{U,T}`, `mdifferentiable_slash_heckeDiagMatrix` (its own 9-line pin file), `isBoundedAtImInfty_hecke{U,T}` and `periodic_hecke{U,T}_comp_ofComplex`. FLT repeats the ~132-line analytic head in **ten** 353-line `S_` files; the port writes it once and leaves the four `q`-coefficient files' tail (`hasSum_*`, `qCoeff_*`) to SET 3. The block-internal `isZeroAtImInfty_*` and the `vadd`/periodicity machinery are `private`. `val_heckeDiagMatrix` was promoted public in `Defs/HeckeOperator.lean` for the `1 0 = 0` helper. FLT `S_ModularForm_{mdifferentiable,isBoundedAtImInfty,periodic}_hecke{U,T}` + `…_mdifferentiable_slash_heckeDiagMatrix` (6×353 + 9) |
| `FLTForHuman/ModularForms/HeckeCusps.lean` | the cusp-class layer (SET-2 T4 — four `S_` files to one) | the four public targets, verbatim from their `Theorems/` wrappers: `ModularFormClass.isBoundedAt_hecke{U,T}` and `CuspFormClass.isZeroAt_hecke{U,T}`. FLT states them in four 132-line `S_` files with an identical ~95-line block (rational-cusp transport along `GL₂(ℚ)`, the `ℚ`-model `ratUpperTriangularGL`, the two `Finset` extension lemmas); the port writes the block once, all `private`. `upperTriangularGL`/`val_upperTriangularGL` were promoted public in `Defs/HeckeOperator.lean` for the rational model. FLT `S_ModularFormClass_isBoundedAt_hecke{U,T}` + `S_CuspFormClass_isZeroAt_hecke{U,T}` (4×132) |
| `FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean` | the formal `PowerSeries` Hecke operators (SET-3 T5) | the pin's 43-line `Def_PowerSeries_FormalHeckeOperators.lean` verbatim: `heckeU ℓ` (`f ↦ ∑ n, f (ℓ*n) X^n`), the dilation `heckeV ℓ`, `heckeU_heckeV` (`U` is a left inverse of `V` for `ℓ ≠ 0`), and `heckeT ℓ k = heckeU ℓ + ℓ^(k-1) • heckeV ℓ` with its two coefficient lemmas. The weight here is a `ℕ` (the pin's split; `ModularForm.heckeT` takes `k : ℤ`, and only `ModularFormClass.qExpansion_heckeT_eq_heckeT` identifies them). The declarations are written with qualified names because `heckeU`/`heckeT` collide by last name with the surface operators — see `OWN_PROOFS` in the checker |
| `FLTForHuman/ModularForms/HeckeQCoeff.lean` | the `q`-coefficient layer (SET-3 T5 — the four-file tail to one) | `ModularFormClass.qCoeff` (the pin's definition from `Def_FLTPrelim_Modularity.lean`), the shared tail of the four 353-line `qCoeff` `S_` files written once (`qExpansion_coeff_unique'`, `hasSum_qCoeff`, `qParam_*`, `sum_rootOfUnity_pow`, `hasSum_average`/`hasSum_diag`/`hasSum_hecke{U,T}`, `qCoeff_hecke{U,T}_bare/class`, all `private`), and the public targets verbatim: `UpperHalfPlane.qCoeff_hecke{U,T}`, `ModularFormClass.qCoeff_hecke{U,T}`, the dilation pair `…qCoeff_comp_heckeDiagMatrix_smul`, `…qExpansion_hecke{U,T}_eq_hecke{U,T}`, `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`, `UpperHalfPlane.eq_of_forall_qCoeff_eq`, and the coefficient algebra `coeffHecke{T,U}_comm`/`…coeffHeckeT_coeffHeckeU_comm`/`coeffHecke{T,U}_int`. The `ℍ → ℂ` `qExpansion_coeff_unique'` shape held (no `DFunLike` stall). FLT `S_UpperHalfPlane_qCoeff_hecke{U,T}` + `S_ModularFormClass_qCoeff_hecke{U,T}` (4×353) + the two 120-line dilation files + eight more short files (~1,900 lines) |
| `FLTForHuman/ModularForms/HeckeOperatorForms.lean` | the bundled `T_p`/`U_p` (SET-3 T6 — pure assembly) | `ModularForm.heckeTLin`/`heckeULin` and `CuspForm.heckeTLin`/`heckeULin` as `ℂ`-linear endomorphisms of `ModularForm (Γ₀ N) k`/`CuspForm (Γ₀ N) k`, with their `@[simp] coe_*`/`_apply_apply` `rfl`s — the twelve declarations of the pin's `Def_ModularForm_HeckeOperatorForms.lean` verbatim — plus the three thin wrappers `CuspForm.qExpansion_heckeTLin`, `CuspForm.exists_coe_eq_hecke{T,U}`. Every structure field is one SET 1–2 export (T1 invariance, T3 holomorphy, T4 boundedness/cusp vanishing, T0 linearity); no new lemma was needed. Placed at the top level (the pin calls it a definition module) because the bundling consumes the invariance/analytic/cusp layers. The `heckeULin` `[NeZero N]` asymmetry is the pin's. FLT `Definitions/Def_ModularForm_HeckeOperatorForms.lean` (112 lines) + three `S_` files |
| `FLTForHuman/ModularCurve/Defs/LaurentSeriesHecke.lean` | the formal `LaurentSeries` Hecke operators (SET-3 T7) | the pin's `Def_LaurentSeries_Hecke{U,V}.lean` (50 + 48) in one module: `heckeU R ℓ hℓ` (`(U f).coeff n = f.coeff (ℓ * n)`, with `heckeU_ofPowerSeries` matching `PowerSeries.heckeU`), the dilation `heckeV R ℓ hℓ`, `heckeT = heckeU + ℓ^(k-1) • heckeV`, and the two `bddBelow_support_coeff_*` support bounds. Built on `HahnSeries.ofSuppBddBelow`; mathlib `v4.34.0` names the coefficient lemma `HahnSeries.coeff_ofSuppBddBelow` (a function equality), not the pin's pointwise `ofSuppBddBelow_coeff`. Placed in `ModularCurve/Defs/` beside the `qExpand`/`qTwist` series vocabulary |
| `FLTForHuman/ModularForms/HeckeCommute.lean` | commutation of the Hecke operators (SET-3 T7) | the three function-level `ModularFormClass.heckeU_heckeU_comm`/`heckeT_heckeT_comm`/`heckeT_heckeU_comm`, the four bundled `CuspForm.heckeTLin_comm`/`heckeULin_comm`/`heckeTLin_heckeULin_comm`/`ModularForm.heckeTLin_comm`, and the five formal-series `LaurentSeries.commute_hecke*` — all verbatim from their `Theorems/` wrappers. Shape: compare `q`-coefficients through T5's `coeffHecke*_comm` and close with T5's `UpperHalfPlane.eq_of_forall_qCoeff_eq`; the pin's three private `W2WsF.eq_of_forall_qCoeff_eq` twins are **not** copied (only `private mf_bdd` stays local, and the unused `qCoeff_const_smul`/`periodic_const_smul` are dropped). The bundled ones reduce pointwise; the `LaurentSeries` corner is self-contained and needed no `maxHeartbeats` override. FLT three 86/90-line `S_` files + four bundled + five 20-line `S_` files |
| `FLTForHuman/ModularForms/HeckeAlgebra.lean` | the `ℤ`-Hecke algebra (SET-3 T7 — survey Stage C endpoint) | the fourteen declarations of the pin's `Def_CuspForm_HeckeAlgebra.lean` verbatim: `heckeGenerators` (the `T_ℓ` with `ℓ ∤ N`, `ℓ ∉ S`, and the `U_q` with `q ∣ N`, `q ∉ S`), `heckeAlgebra = Algebra.adjoin ℤ heckeGenerators`, the two membership and two monotonicity lemmas, `commute_of_mem_heckeGenerators`, and the pin's instances `heckeAlgebra.instIsMulCommutative` (`Algebra.isMulCommutative_adjoin`), `heckeAlgebra.instCommRing`, `heckeAlgebra.instIsAddTorsionFree` (`smul_right_injective`), plus `heckeAlgebra.T`/`.U` and their `@[simp] coe_*` `rfl`s. The finite/free algebra and the integral lattice are SET 4. FLT `Definitions/Def_CuspForm_HeckeAlgebra.lean` (93 lines) |
| `FLTForHuman/ModularForms/Defs/Eigenform.lean` | the normalized eigenform predicate (SET-4 T8) | the pin's `CuspForm.IsNormalizedEigenform` structure verbatim from `Def_FLTPrelim_Modularity.lean:26–40`, four coefficient clauses with load-bearing field names `qCoeff_one`, `qCoeff_mul_of_coprime`, `qCoeff_prime_pow_of_not_dvd`, `qCoeff_prime_pow_of_dvd`. Definition module (no `Theorems/` wrapper); the dictionary is `HeckeEigenform.lean` |
| `FLTForHuman/ModularForms/HeckeEigenform.lean` | the eigenform interface (SET-4 T8) | the 13 `Theorems/` targets verbatim plus `CuspForm.qCoeff_zero` (an extra dependency, ported publicly): the three characterisations `isNormalizedEigenform_iff_{coeffHecke,heckeT,heckeTLin}`, the single-operator `iff`s `CuspForm.hecke{T,U}Lin_apply_eq_smul_iff` and `ModularFormClass.hecke{T,U}_eq_smul_iff`, the forward `IsNormalizedEigenform.hecke{T,U}Lin_apply_eq_qCoeff_smul`, the coefficient pair `ModularForm.{coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one,eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero}`, the multiplicity one `LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero`, and `PowerSeries.coeff_heckeT_pow_sub_mem_span`. **Dedup:** the coefficient `iff` is proved once (the pin's 200-line `S_` file); `iff_heckeT` is derived from it through the two `ModularFormClass` iff's, `iff_heckeTLin` from `iff_heckeT` by coercion rewriting, and the two `hecke*Lin_apply_eq_qCoeff_smul` are the forward directions of `iff_heckeTLin` — the pin's 26 + 13 + 175 + 132 lines are replaced by ~25 port lines. The pin's private `W2WsF.eq_of_forall_qCoeff_eq` is T5's public lemma |
| `FLTForHuman/ModularForms/Defs/IntegralStructure.lean` | the integral lattice (SET-4 T9) | `CuspForm.intLattice N k` (the `ℤ`-span of the forms with integral `q`-coefficients) and `CuspForm.HasIntegralStructure N k` (`span ℂ intLattice = ⊤`), verbatim from the pin's 8-line `Def_CuspForm_IntegralStructure.lean`. The weight-2 vocabulary `qIntegralSet`/`qIntegralLattice`/`HasIntegralBasis` is T10's `Defs/IntegralLattice.lean`, a different object |
| `FLTForHuman/ModularForms/HeckeLattice.lean` | the Hecke algebra preserves the lattice (SET-4 T9) | the three `Theorems/` targets verbatim: `CuspForm.mem_intLattice_of_coe_eq_heckeT` (`1 ≤ k`, `p ≠ 0`), `…_heckeU` (`p ≠ 0`, no `k` bound) and `…_mem_heckeAlgebra` (`[NeZero N]`, `1 ≤ k`). **Shape:** the defining set is shown to be a `ℤ`-submodule (`intSubmodule`), so `Submodule.span_eq` gives `intLattice = intSubmodule` and `mem_intLattice_iff`; the two `_coe_eq_` targets then transport T5's `coeffHecke{T,U}_int`, and the algebra target is an `Algebra.adjoin_induction` over `heckeGenerators`. `grep -c qIntegralLattice` = 0 |
| `FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean` | the `χ₋₃` Eisenstein vocabulary (SET-4 T10, definitions) | `chiNegThree` (the nontrivial character mod `3`), `sigmaChi` (its divisor sum), `e1Chi3` (`1 + 6∑σ_χ(n)qⁿ`), `e1Chi3In R` (base change) and `E1Chi3IsModular`, verbatim from the pin's 27-line `Def_ModularForm_EisensteinChiNegThree.lean`. Self-contained (mathlib `PowerSeries` + modular-form vocabulary) |
| `FLTForHuman/ModularForms/Defs/IntegralLattice.lean` | the weight-2 auxiliary lattice (SET-4 T10, definitions) | `qIntegralSet N`, `qIntegralLattice N`, `HasIntegralBasis N`, `bridgeProduct` (`PowerSeries.mk a * e1Chi3In R`) and `IsLatticeRealized N a`, verbatim from the pin's 32-line `Def_CuspForm_IntegralLattice.lean`. Distinct from T9's all-weight `intLattice`; feeds the `χ₋₃`/mod-`3` congruence machinery |
| *(not created)* `FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean` | the finite/free Hecke algebra (SET-4 T10, **blocked**) | All twelve targets are unreachable in SET-4 scope: `hasIntegralStructure_of_two_le` (the pin's 515-line `S_` file) needs the `HeckeEis` coefficient-cohomology/Eichler–Shimura package, the period package and `Def_CuspForm_ModPForms` (explicitly out of scope); `intLattice_fg` needs the Sturm bound (absent from mathlib `v4.34.0`); the eigenbasis family needs the Petersson inner product and `finiteDimensional_Gamma0`. The two headline one-liners (`moduleFinite_heckeAlgebra_two` = the `k = 2` case of `moduleFinite_heckeAlgebra`; `hasIntegralStructure_two` = `hasIntegralStructure_of_two_le N 2 le_rfl`) could therefore not be stated, and the 4,308- and 212-line pin `_two` files were neither transcribed nor needed. See `logs/hecke-port.md` §T10 |
| `FLTForHuman/ModularForms/HeckeQExpansion.lean` | the Hecke translates of a `q`-expansion | `hasSum_qParam_heckeMatrix_smul` (`τ ↦ (τ+b)/ℓ` twists the coefficients and changes the period `1 ↦ ℓ`) and `hasSum_qParam_heckeDiagMatrix_smul` (`τ ↦ ℓτ`, coefficients `qExpand ℂ (ℓ*ℓ)`). base/013 §5.2's analytic face of the Hecke action. FLT `S_ModularCurve_hasSum_qParam_hecke{Matrix,DiagMatrix}_smul` (~109 lines) |
| `FLTForHuman/ModularForms/PhiGenDescends.lean` | the cone's (c) | `PhiGen.mem_adjoin_jq_of_phiGenDescends` (verbatim): a descended coefficient of the conjugate product lies in `ℚ[jq]`. It proves `cosetPoly_smul` (the coset polynomial's `SL₂(ℤ)`-invariance through the action on `ℙ¹(𝔽_ℓ)`) and privately realizes `c k` via the Hecke translates (the `σ : ℚ(ζ_ℓ) → ℂ` embedding), then applies T7's headline. The pin duplicates T7's `RealL`/glue here; the port imports instead (~97 lines saved), and since the Hecke topic it imports the promoted `Defs/HeckeRepresentatives` block — its old private, weakened copies of `det_eq`/`_mul_of_eq`/`heckeRep`/`redMatrix`/`heckeRep_mul` are gone (the T8 payload `apply_heckeRep_smul_smul`/`cosetPoly_*` stays). FLT `S_ModularCurve_cosetPoly_smul` + `…_hasSum_cosetPoly_coeff` + `…_mem_adjoin_jq_of_phiGenDescends` (~572 lines) |
| `Reserve/ModularForms/CuspFormNorm.lean` | the norm of a cusp form (**Reserve** library; retired from the `base/003` route) | `CuspForm.norm` (the product of the translates `f ∣[k] g_q⁻¹` over `ℋ ⧸ 𝒢`, as a cusp form of weight `k · Nat.card (ℋ ⧸ 𝒢)`), the bridge `CuspForm.coe_norm_eq_coe_modularFormNorm`, and `CuspForm.norm_eq_zero_iff` (the norm vanishes only on zero forms; it is homogeneous, not linear). Mathlib's `ModularForm.norm` produces only a *modular* form; this module supplies the missing `zero_at_cusps'` from `CuspForm.translate` and `of_isFiniteRelIndex_conj`. v4.34: `CuspForm` no longer extends `ModularForm` (the `__ := ModularForm.norm` inheritance still fills `toFun`/`slash_action_eq'`/`holo'`), `tendsto_finset_prod` is `tendsto_finsetProd`, and the `coe_zero` lemmas are `map_zero`. Used by the reserve norm-route proof `Reserve/ModularForms/LevelTwoCuspVanishing.lean`; the main tree proves the same two theorems via the Sturm bound. FLT `S_ModularForm_S2_Gamma0_2_eq_zero` 18–70 |
| `FLTForHuman/ModularForms/Gamma0TwoIndex.lean` | `[SL(2, ℤ) : Γ₀(2)] = 3` (`base/003` move 1) | The first-column bijection `SL(2, ℤ) ⧸ Γ₀(2) ≃ {p : (ZMod 2)² // p ≠ 0}` — the private `firstColMod2`, `det_eq_one_mod2`, `firstColMod2_ne_zero`, `Gamma0_two_diag_eq_one`, `firstColMod2_mul_mem` and the private `cosetToProj` with its injectivity/surjectivity — and the public `Gamma0_two_index_eq_three`. The pin's inline `!![⋯]` witnesses are `private def`s here, since `by decide` needs the matrix type known. FLT `S_ModularForm_S2_Gamma0_2_eq_zero` 94–174 |
| `Reserve/ModularForms/LevelTwoCuspVanishing.lean` | no weight-2 cusp forms on `Γ(1)` and `Γ₀(2)` — the **reserve norm route** (`base/003`) | `ModularForm.S2_Gamma0_2_eq_zero` and `ModularForm.S2_Gamma0_one_eq_zero`, verbatim from their `Theorems/` wrappers, by the original **norm** proof: `CuspForm.norm` to a level-one weight-`6` form (`CuspForm.norm_eq_zero_iff`, the quotient card `Nat.card (Γ(1) ⧸ Γ₀(2)) = 3`), then mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve`. Restored verbatim from commit `4c4f588` and parked here because the main tree now proves the same theorems as Sturm-bound corollaries (`FLTForHuman/ModularForms/SturmBound.lean`); the two modules declare the same wrapper names and must not be imported together. The `Reserve`-local companion is `Reserve/ModularForms/CuspFormNorm.lean`. FLT `S_ModularForm_S2_Gamma0_2_eq_zero` 77–92, 176–206 + `S_ModularForm_S2_Gamma0_one_eq_zero` |
| `FLTForHuman/ModularForms/QExpansionOrder.lean` | two `q`-expansion order lemmas | `UpperHalfPlane.qExpansion_coeff_nat_mul` — multiplying the period by `M` reindexes the coefficients (`n` survives only when `M ∣ n`, at `n / M`) — and `UpperHalfPlane.qExpansion_prod` — the `q`-expansion of a finite product is the product of the `q`-expansions when each factor is analytic at the cusp. Proved from mathlib's `qExpansion_mul`/`cuspFunction_mul`/`qExpansion_coeff_unique`; the first is the pin's, written once (the pin repeats it privately inside `S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean`). FLT `S_UpperHalfPlane_qExpansion_coeff_nat_mul` (54) + `S_UpperHalfPlane_qExpansion_prod` (35) |
| `FLTForHuman/ModularForms/SturmBound.lean` | the **Sturm bound** and its inputs (`math/012`) | `ModularForm.sturm_bound_Gamma0` (verbatim: a `Γ₀(N)` form whose `q`-expansion vanishes below `k · (Γ₀ N).index / 12` is zero) and `ModularForm.sturm_bound_of_isArithmetic` (the general arithmetic level, `k · relIndex 𝒮ℒ / 12`), via `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` (the norm to level one + `qExpansion_prod` + the order comparison), `ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` (a corollary of mathlib's `ModularForm.sturm_bound_levelOne` + the coefficient reindexing), `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` (the normal core's index is a strict period of every conjugate) and `CongruenceSubgroup.one_mem_strictPeriods_Gamma0`. The `relIndex_map_mapGL_W2D` and norm-analyticity helpers stay `private`. The final section adds the weight-`2` **cusp-form vanishing corollaries** `ModularForm.S2_Gamma0_{2,1}_eq_zero` (the `Γ(1) = 𝒮ℒ` bridge, `cuspForm_eq_zero_of_subgroup_eq`, `CuspFormClass.qExpansion_coeff_zero` and `CuspForm.toModularFormₗ`; the level-2 index value `(Γ₀ 2).index = 3` comes from `Gamma0TwoIndex.lean`). This is the cheap mandatory sub-cone of the finiteness targets (see `studies/hecke-finiteness-coverage.md`). FLT the six `S_` files (29 + 26 + 56 + 82 + 31 + 18 raw) + the two cusp-vanishing wrappers |
| `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` | the cone's (b) integrality | `PhiGen.PhiGenDescends.intCoeffs` (the descended family has integer `q`-expansion coefficients) and `PhiGen.aeval_jq_intCoeffs_descent` (`IntCoeffs (P(jq))` forces `P ∈ ℤ[X]`), both verbatim from their pin wrappers. The module is the first **deliberate route deviation**: Route A lifts `jq` and the conjugates to `LaurentSeries (integralClosure ℤ K)` and pushes `coeffMap` through `qExpand`/`qTwist`/`phiProd`, replacing FLT's `CoeffsIntegral` closure block (~83 pin lines, plus 24 of manual root-of-unity lemmas) with ring structure; the two root-of-unity lemmas become one `mem_integralClosure_of_pow_eq_one`. It also **promotes** the shared triangularity `coeff_aeval_jq_neg` (to `Defs/Jq.lean`) and `poleOrderLE_aeval_jq` (to `Defs/PhiGen.lean`), which FLT repeats privately in nine files. FLT `S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs` + the descent half of `S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent` (~347 lines, of which ~180 is an out-of-scope `TPoleOrderLE` block) |
| `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` | the cone's (b) pole bounds | `PhiGen.phiProd_conj_coeff_zero_lead` (the constant term of `phiProd` has pole exactly `q ^ (-(ℓ * ℓ + ℓ))` with residue `1`) and `PhiGen.phiProd_conj_coeff_eq_zero_of_le` (every non-constant coefficient is bounded by the same order), both verbatim from their pin wrappers — with T9's integrality, the completed (b). The distinctive part only: the shared `TPoleOrderLE` prelude is **public in `Defs/PhiGen.lean`** because FLT repeats it in twelve `S_` files and T11 imports it. The pin's `pow_sum_range_isPrimitiveRoot` (the *product* of the powers of a primitive root, where mathlib has only the *sum*) is the one near-miss of the audit and ported whole. Both exports have a concrete wire instance (`ℂ`, `ℓ = 2`, `ζ = -1`, via `IsPrimitiveRoot.neg_one`), named `wire_zero_lead`/`wire_eq_zero_of_le`. FLT `S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le` (391 lines; its `_zero_lead` twin is byte-equivalent) |
| `FLTForHuman/ModularCurve/PhiGenDescent.lean` | the cone's (a): descent to `ℚ((q))` | `PhiGen.exists_phiGenDescends` (verbatim): the coefficients of `phiProd ℓ (conj ℓ ζ)` are fixed by the nome twist `q ↦ ζq` — hence in the range of `qExpand ℚ ℓ` — and by every `σ : K ≃ₐ[ℚ] K` — hence in the range of `coeffEmb K`; intersecting the ranges gives the descended family. base/006 §6.2 verbatim, no analysis. FLT `S_ModularCurve_PhiGen_exists_phiGenDescends` (315 lines) |
| `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` | the 328 block: the shape of a descended family | `PhiGenDescends.c_top` (`c (ℓ+1) = 1`), `.c_eq_zero` (vanishing above degree `ℓ+1`), `.poleOrderLE` (pole `≤ ℓ+1`, from T10's `ℓ²+ℓ` bound divided by the level substitution), `.sum_mul_jqN_pow_eq_zero` (the modular-equation relation) and the public `evalAtJ_injective` — the last by the **mathlib route** through the public `transcendental_jq`, so T12's 895 block imports it rather than carrying the pin's private copy. The ~170-line `TPoleOrderLE` prelude is T10's. FLT the 328-line `PhiGenDescends` block (shipped in seven files; 84 distinctive lines) |
| `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean` | the cone's (d): the assembled datum | `PhiGen.exists_modularPolynomialData_coeff_eq` (verbatim from its wrapper): a descended integral family in `ℚ[jq]` assembles into a `ModularPolynomialData ℓ` with `evalAtJ (Φ.coeff k) = c k`, using T9's `aeval_jq_intCoeffs_descent` and `Polynomial.lifts`. Plus `splits_of_coeff_evalAtJ_eq` (verbatim), the coefficient comparison that turns the datum back into the product and feeds (e)/(f). FLT `S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq` (191 lines) |
| `FLTForHuman/ModularCurve/JqCoeffPositivity.lean` | the coefficients of `j` are positive | `one_le_coeff_jq` (verbatim): every regular coefficient of `j = q⁻¹ + 744 + 196884q + ⋯` is at least `1`, via the eta product `jNum = E₄³·Δ⁻¹` (no analysis). Two of the audit's mathlib substitutions landed (`coeff_mul_prod_one_sub_of_lt_order`, `PowerSeries.expand` + `mk_one_mul_one_sub_eq_one`); the eta-truncation comparison and the truncation-stable inverse comparison are the pin's. Plus the one-line `coeff_jq_ne_zero`. FLT `S_ModularCurve_one_le_coeff_jq` (386 lines) |
| `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` | the properties I: irreducibility and the transpose | The **895 block written once** — FLT ships it in five files (`5 × 895 ≈ 4,475` lines). `conj_injective` (the conjugates are distinct), `aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq` (the twist-sum refutation, using `one_le_coeff_jq` at `n = ℓ`), `phiIrreducible_of_splits` (the factor-counting engine), `swapBivar_monic_of_coeff_bounds` and `transposeToAdjoin_monic_of_qExpansion` (the transpose's degree from the pole bounds), `evalSymm_of_irreducible`/`evalSymm_of_splits` (symmetry by minimal-polynomial uniqueness), `evalAtJGen_injective`, `swapBivar_eq_of_evalSymm`, `aeval_jqN_toAdjoin`, `minpoly_jqN_eq`. `evalAtJGen_injective` reuses T11's `evalAtJ_injective`; `evalAtJ_eq_aeval_map` is the new `Defs/Jq` lemma. FLT `S_ModularCurve_PhiGen_evalSymm_of_splits` (895) + `S_ModularCurve_swapBivar_eq_of_evalSymm` (95) |
| `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` | the properties II: symmetry from the family, and existence | `evalSymm_of_coeff_evalAtJ_eq` (verbatim): T10's two pole-bound exports give the three coefficient hypotheses of `transposeToAdjoin_monic_of_qExpansion`, and `evalSymm_of_splits` concludes. Plus the capstone `exists_phiIrreducible_evalSymm` (verbatim), the cone's own construction of an irreducible symmetric datum — the join of (a)–(e) in `CyclotomicField ℓ ℚ`. FLT `S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq` (124) + `S_ModularCurve_exists_phiIrreducible_evalSymm` (62) |
| `FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean` | the cone's consequence I: uniqueness and the degree | `ModularCurve.finrank_adjoin_jqN_eq_of_prime` (verbatim: `[ℚ(j)(j(q^ℓ)) : ℚ(j)] = ℓ + 1`, from T12's `exists_phiIrreducible_evalSymm` and `dedekindPsi_prime`) and `ModularPolynomialData.eq_of_prime` (verbatim: any two prime-level data are equal, both `toAdjoin`s being the minimal polynomial of `j(q^ℓ)`). FLT `S_ModularCurve_finrank_adjoin_jqN_eq_of_prime` (52) + `S_ModularCurve_ModularPolynomialData_eq_of_prime` (73) |
| `FLTForHuman/ModularCurve/PhiGenSplits.lean` | the cone's consequence II: the splitting — **the cone's headline** | `PhiGen.splits_of_prime` (verbatim): the datum, read at the level-`p` nome, is the conjugate product; proved over `CyclotomicField p ℚ` (T11's descent + T9's integrality + T8's membership + T11's assembly + `eq_of_prime` + T11's `splits_of_coeff_evalAtJ_eq`) and transported along an embedding `CyclotomicField p ℚ →ₐ[ℚ] K`. `PhiGen.splits_prime_at_slot` (verbatim), the cone's exported statement, is one `qExpand K e ∘ qTwist u` transport. The shared `TS` prelude is `Defs/TS.lean`'s; ~200 pin prelude lines dead for the exports (they belong to the char-`p` variants) are dropped. FLT `S_ModularCurve_PhiGen_splits_of_prime` (353) + `S_ModularCurve_PhiGen_splits_prime_at_slot` (288) |
| `FLTForHuman/ModularCurve/Defs/Cyclotomic.lean` | a primitive root of unity in `CyclotomicField N ℚ` | `exists_isPrimitiveRoot_cyclotomicField` and the chosen `cycUnit`, its `cycUnit_spec`/`cycUnit_pow`, and `isPrimitiveRoot_pow_div` — promoted by T13 from the private twins in the FFG spine and in `PhiGenSplits.lean`, so both import one copy. FLT `S_ModularCurve_PhiGen_splits_of_prime` (188–203) + `S_ModularCurve_PhiGen_splits_prime_at_slot` (123–133) |
| `FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean` | the modular polynomial at the slot, written once (T14) | the `conj`/`TS` bridges `iota_jq`/`conj_zero_eq`/`conj_succ_eq` (promoted out of T13's private copies), the conjugate product `phiProd_conj_eq` with its roots `roots_phiProd_conj`/`_nodup`, and `phiAtSeed` with its eight naturality/monicity/degree/vanishing lemmas plus `aeval_intermediateField_eq_zero`, `phiAtSeed_eval_of_injective`/`_symm` and `phiAtSeed_jqN_eval_down`. Upstream of the cone; T15–T19 import it instead of re-copying the pin's shared block (which up to thirteen files repeat). FLT `S_ModularCurve_jqN_prime_not_mem_full` 106–194, 351–404 + `S_ModularCurve_jqN_pow_not_mem_adjoin_full` 400–430 |
| `FLTForHuman/ModularCurve/PhiSlotRoots.lean` | the at-slot roots API (T14) | `prod_form_ne_zero`, `roots_prime_at_slot`, `roots_prime_at_slot_nodup`, `roots_prime_at_slot_roots_nodup` and `isRoot_prime_at_slot_iff` — the roots of `Φ`, read at the twisted/dilated slot, via T13's `PhiGen.splits_prime_at_slot`. The one T14 module downstream of the cone (which is why the API cannot live in `Defs/`); `prod_form_ne_zero` is `private` in the pin and is promoted here. FLT `S_ModularCurve_jqN_prime_not_mem_full` 252–350 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean` | descent by one prime, and the one-prime reduction (T15) | `jqN_div_mem_modularFunctionField` (verbatim from its wrapper): math/010 §4's unique-common-root descent `j(q^M) ∈ ℚ(j(q), j(q^{Mp}))`, with the slot hypotheses `htw`/`hsp` left as arguments for T19. Composes T14's `phiAtSeed*`/`isRoot_prime_at_slot_iff`/`roots_prime_at_slot_roots_nodup`/`iota_jqN`, T13's `splits_prime_at_slot` and T4's `Polynomial.mem_range_of_unique_common_root`, plus the `coeffEmb`/`qExpand` injectivity strip. And `modularFunctionField_eq_full_of` (verbatim): math/010 §5's one-prime `Gen` reduction. Both are `Inputs` fields, so the capstone's debt is **7 → 5**. The pin's 735-line file is one development shipped twice and ~542 of its lines are T14's prelude; nothing is re-copied. FLT `S_ModularCurve_jqN_div_mem_modularFunctionField` ≡ `S_ModularCurve_modularFunctionField_eq_full_of` 553–727 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/DegreeStep.lean` | the degree of one prime-power step (T16) | `finrank_adjoin_jqN_prime_of_not_mem` (verbatim): the first prime power, `[F(j(q^p)) : F] = p + 1`, from `Φ_p`'s `p + 1` roots cycled by the nome twist `qTwistEquiv ζ` and T4's `irreducible_of_transitive_ringAut`. `finrank_adjoin_jqN_pow_succ_of_not_mem` (verbatim): later powers, `= p`, by peeling the factor `(X - j(q^{p^k}))` and cycling its `p` roots with the cyclotomic coefficient automorphism `coeffMapEquiv τ` (`IsCyclotomicExtension.autEquivPow`/`IsPrimitiveRoot.autToPow`). `relfinrank_full_eq_mul` (verbatim): the tower dispatcher `p + 1`/`p`, via `w1_relfinrank_insert`. The third is an `Inputs` field, so the capstone's debt is **5 → 4**. Private helpers: `phiAtSeed_iota_jq_eq_phiProd`, `rUnit`, `range_map_eq_rUnit`; the redundant `coeffEmb_injective'`/`jqN_congr'` are dropped. FLT `S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem` 293–344, `S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem` 563–749, `S_ModularCurve_relfinrank_full_eq_mul` 49–72 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Nonmembership.lean` | the non-membership tower and the two-prime separation (T17) | `jqN_pow_not_mem_adjoin_full` (verbatim): the prime-power tower `j(q^{p^{a+2}}) ∉ ℚ(F_M^full, j(q^p), …, j(q^{p^{a+1}}))`, by strong induction on `a` over the chain `C_i = ℚ(F_M^full, j(q^{p^j}) : j ≤ i)` and a compatible family of `ℚ`-algebra homs `σ_i : C_i → K((q))` built with `algHomAdjoinIntegralEquiv`/`adjoin.powerBasis`; `Φ_p` forces `j(q^{p^{a+2}})` and `j(q^{p^a})` to the same root, and the `q^{-p^a}` coefficient clash (1 vs 0) closes it. It is an `Inputs` field, so the capstone's debt is **4 → 3**. And `jqN_prime_not_mem_adjoin` (verbatim, public `Theorems/` API): `jqN r ∉ ℚ(j, j(q^p) : p ∈ S)` for a finite prime set `S ∌ r`, by the Finset induction `jqN_prime_not_mem_adjoin_key` over `step_contradiction`, which instantiates T4's `mem_range_of_eval_eq_const` on the `p + 1` roots of `Φ_p(jq, ·)` against T16's degree step. Private declarations (14): `nat_ne_of_mul`, `mem_range_qExpand_of_mul`, `range_qExpand_congr`, `chainField` + five lemmas, `chain_extend`, `chain_endgame`, `step_contradiction` and the two keys; the pin's two local `maxHeartbeats 3200000` bumps are omitted (the global cap is `4000000`). FLT `S_ModularCurve_jqN_pow_not_mem_adjoin_full` 443–985 + `S_ModularCurve_jqN_prime_not_mem_adjoin` 426–651 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Generation.lean` | one new generator per prime power (T18) | `full_eq_adjoin_full_div_prime` (verbatim): for `p ∤ M`, `F^full_{M p^{a+1}} = ℚ(F^full_{M p^a}, j(q^{p^{a+1}}))`. The engine is the two-prime descent `jqN_mem_of_div_primes` — ported **once** although the pin carries it in three files — the unique-common-root principle on `φ_p` and `φ_q`; the strong induction `w1_jqN_mem_adjoin_top_insert` either lands in `F^full_{M p^a}` or peels a prime `q` from the `M`-part. It is the fifth `Inputs` field, so the capstone's debt is **3 → 2**. The original topic's nodes 2–6 (the squarefree generation/degree block) are deferred optional API; T19 uses `Defs/Fields.lean`'s `gen_prime` instead. FLT `S_ModularCurve_full_eq_adjoin_full_div_prime` 397–620 |
| `FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean` | the slot product and the prime non-membership (T19) | `minpoly_jqN_map_eq_prod_slots` (verbatim): the mapped minimal polynomial of `j(q^M)` is the product of `(X - C (sv K ζ a b))` over the `ψ(M)` slots, by strong induction on `M` from T13's `splits_prime_at_slot` (the pin's 680-line `rval_aux`, whose 493-line `hslot_root` the audit finds irreducible). `jqN_prime_not_mem_full` (verbatim): `j(q^p) ∉ F_M^full` for `p ∤ M`, by T4's `mem_range_of_eval_eq_const` on the slot list. These are the last two `Inputs` fields, so the debt is **2 → 0** and the capstone is reachable. Route wins: the slot count uses the closed form `slotAt n d = (d / gcd (n/d) d) * φ (gcd (n/d) d)` with `slots_mul` via mathlib `Nat.Coprime.divisors_mul` (the pin's 108-line CRT `slotAt_mul` is dropped), the `ψ` facts are the public `Defs/Jq.lean` lemmas, and the M-arbitrary `hallp` uses `gen_prime`/`tight_one`/`gen_one`. FLT `S_ModularCurve_jqN_prime_not_mem_full` 405–2002 (twinned) |

| `FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean` | the unconditional capstone (T20) | `inputs` — the port's assembly of T15–T19's seven proved theorems into `Inputs`; `functionFieldGeneration` (verbatim): **the headline, now unconditional** — every `j(q^d)` with `d ∣ N` lies in `ℚ(j(q), j(q^N))`. The corollary layer `modularFunctionField_eq_full`, `finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi` (all verbatim), and the interface tail `exists_monic_evalAtJ_jqN_eq_zero`, `exists_phiIrreducible_of_finrank_eq` (§2.1's last out-of-cone node, via the `Polynomial ℤ → ℚ⟮jq⟯` fraction ring), `exists_phiIrreducible`. FLT `S_ModularCurve_functionFieldGeneration` 713–754 + `S_ModularCurve_exists_{monic_evalAtJ_jqN_eq_zero,phiIrreducible_of_finrank_eq}` |

| `FLTForHuman/AlgebraicCurve/Defs/Place.lean` | the `Place` vocabulary and ord interface (AC0 + T1) | FLT's `Place` **is** a `ValuationSubring F` with three side conditions, and the bridge to mathlib is built inside the structure (`heightOneSpectrum` = `IsDiscreteValuationRing.maximalIdeal`, `adicValuation`, `ord f = -(log (adicValuation f))`). AC0 transcribes the structure, the four instances, `ResidueField`/`deg`/`FiniteResidue`/`heightOneSpectrum`/`adicValuation`/`ord` and its zpow/unit lemmas, plus `isPrincipalIdealRing_valuationSubring`/`ofHeightOneSpectrum`; T1 adds the outbound interface (`ord_algebraMap`, `ord_smul_of_ne_zero`, `mem_iff_adicValuation_le_one`, `adicValuation_valuationSubring`, `isEquiv_adicValuation_of_valuationSubring_eq`, `ord_eq_neg_log_of_valuationSubring_eq`, `adicValuation_isRankOneDiscrete`/`isTrivialOn`, `mem_toValuationSubring_of_isIntegral_adjoin`, `ord_eq_zero_of_isIntegral_adjoin`) at the `Theorems/` wrappers' binders. FLT `Def_AlgebraicCurve_DivisorClassGroup` 22–179, 456–485 + the `Thm_AlgebraicCurve_Place_*` wrappers |
| `FLTForHuman/AlgebraicCurve/Defs/Divisor.lean` | divisors, principal divisors, `Pic0` (AC0) | `Divisor K F := Place K F →₀ ℤ`, `Divisor.degree` (the `Finsupp.liftAddHom` of `AddMonoidHom.mulRight`), `degZero`, `IsPrincipal`, `principal`, `HasPrincipalDivisors`, `Pic0`, `Pic0.mk`/`mk_surjective`/`mk_add`/`mk_zero`. The `Pic`/`torsion`/`AbelJacobiCard` block is dropped (0 corpus occurrences; modular Hecke/Galois-rep API). FLT `Def_AlgebraicCurve_DivisorClassGroup` 179–247 |
| `FLTForHuman/AlgebraicCurve/Defs/PushPull.lean` | the ord/comap, ramification, residue and push-pull interface (AC0) | `Place.ord_nonneg_of_mem`/`mem_of_ord_nonneg`/`mem_iff_ord_nonneg`/`exists_ord_pos` (promoted out of the pin's `private`), `ramificationIndex` + its dvd/pos/exists leaves, `irreducible_mk_comap`, `Place.restrict` and `ord_restrict`, `restrictInclusion`/`restrictResidueMap`/`inertiaDeg`/`deg_restrict_mul_inertiaDeg`, `Divisor.pushforward`/`pullback`/`pullback_apply`, `FundamentalIdentity`/`SumRamificationInertia` and the `Pic0` pullback/pushforward homs. `mapRestrict` dropped (0 occurrences). FLT `Def_AlgebraicCurve_DivisorPushPull` |
| `FLTForHuman/AlgebraicCurve/Defs/PlacesOverDVR.lean` | places over a DVR: centres, the integral closure and `fiberOver` (AC0) | `Place.center`/`centerHeightOneSpectrum`/`fiberCenter`, the `@[reducible] valuationSubringAlgebra`, the `abbrev integralClosureAt` with its `IsDedekindDomain`/`IsFractionRing`/`Module.Finite` instances, `placeOfPrime`, `fiberEquiv`, `fiberOver`, `subset_fiberOver_of_forall_restrict_eq`. The chart block is kept only `private` as far as `center` needs it; `card_fiberOver_eq`/`fiber_eq_fiberOver` and `finite_setOf_forall_mem_and_ord_pos` are not written (0 occurrences; T5 re-adds the first). FLT `Def_AlgebraicCurve_PlacesOverDVR` |
| `FLTForHuman/AlgebraicCurve/Defs/Correspondence.lean` | the along-map correspondence layer (AC0) | `abbrev algebraAlong φ := φ.toRingHom.toAlgebra` (load-bearing: T4/T7's `rfl` bridges), `FundamentalIdentityAlong`/`FiniteAlong`/`NormFormulaAlong`/`SeparableAlong`/`finrankAlong` (with the promoted helpers `finrankAlong_comp`, `finrankAlong_id`, `finrankAlong_eq_relfinrank_fieldRange`), `Divisor.pullbackAlong`/`pushforwardAlong`/`correspondence`, `Pic0.correspondence`, `Place.restrictAlong`/`ramificationIndexAlong`/`inertiaDegAlong`, `fiberAlong`, `IntertwinesAlong`. Every definition opens with the pin's `letI`/`haveI` wall. FLT `Def_AlgebraicCurve_Correspondence` |
| `FLTForHuman/AlgebraicCurve/Defs/SemilinearAut.lean` | the `K`-semilinear automorphism group and its action on places (AC0) | `SemilinearAut K F` as a subgroup of `RingAut F × RingAut K`, its `MulSemiringAction`/`MulAction` on `F` and on `Place`, `smulValuationSubringEquiv`/`smulResidueRingEquiv`, `ord_smul` and `deg_smul`. The `Divisor`/`Pic0` action-and-torsion block (lines 206–356) stays deferred with this module as its decided home (0 occurrences); the pin's anonymous `SMul (F ≃ₐ[K] F) (Place K F)` is restored here beside `ofAlgAut`. FLT `Def_AlgebraicCurve_BaseChangeGalois` 15–206 |
| `FLTForHuman/AlgebraicCurve/Defs/RatFuncPlaces.lean` | the `P¹` place vocabulary (AC0 + T1) | the `ofHeightOneSpectrum` bridge (`adicValuation_valuationSubring`, `mem_iff_adicValuation_le_one`, `isEquiv_adicValuation_ofHeightOneSpectrum`, `ord_ofHeightOneSpectrum_ne_zero_iff`, `ofHeightOneSpectrum_injective`), `heightOneSpectrumOfIrreducible`, `finitePlace`, the residue field `K[X] ⧸ (p) ≃ₐ[K] ResidueField`, `deg_ofHeightOneSpectrum`/`deg_finitePlace` — and, from the file the blueprint's six-module table omits, `nontrivial_valueGroup_inftyValuation`/`placeInfty` for the place at infinity. `placeOfPoint` and the `Place.Congr` section are dropped (0 occurrences). FLT `Def_AlgebraicCurve_RatFuncPlaces` 18–236 + `Def_AlgebraicCurve_RatFuncPlaceInfty` |
| `FLTForHuman/AlgebraicCurve/Defs/IntegralAdjoin.lean` | generic `Algebra.adjoin` integrality transport (T1) | `isIntegral_adjoin_intermediateField_mk`, `isIntegral_adjoin_map_algHom`, `isIntegral_adjoin_of_isScalarTower` — pure `Algebra.adjoin`/`IsIntegral` algebra with no `Place`, consumed by T5 and T9 too. Statements are the pin wrappers. FLT `Thm_AlgebraicCurve_isIntegral_adjoin_*` |
| `FLTForHuman/AlgebraicCurve/Defs/PlaceDictionary.lean` | the fibre-centre dictionary, written once (T2) | the pin's shared 17-declaration block — `eq_ord_of_addHom_of_nonneg_iff` (kept `private`), `neg_log_valuation_fiberCenter_eq_ord`, `le_ord_iff_mem_pow_fiberCenter`, `ramificationIndex_eq_ramificationIdx_fiberCenter`, `toValuationSubringOfRestrictEq` + its `coe`, `residueOfCenter` + `_apply`/`ker_`/`surjective_`, `residueFieldEquivQuotientCenter` + `_mk`, `placeCongrEquiv` + `coe_`, `restrictResidueFieldEquiv` + `_residue`, `inertiaDeg_eq_inertiaDeg_fiberCenter` — public at the pinned names under `AlgebraicCurve.Place`. FLT copies it byte-for-byte into `fiberOver`, `le_finrank`, `hasPrincipalDivisors_of_transcendental` and `inertiaDeg_pos`; the port writes one copy and lets the checker's dotted fallback read the pin's `private` originals. Statements keep the pin's primed `Ideal.inertiaDeg'` text under `linter.deprecated false`; proofs use the v4.34 names. FLT `S_..._fiberOver` 28–378 |
| `FLTForHuman/AlgebraicCurve/WeilExchange/FiberOverCount.lean` | the bifibre count (T2) | `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (the pin's 45-line Assembly, shipped twice, written once), `Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank` (one line from the `⊆` lemma + nonnegativity), `Place.inertiaDeg_pos`. The v4.34 shape adaptation against `Ideal.sum_ramification_inertia_eq_finrank` uses `IsFractionRing.finrank_eq`, `Finset.sum_subtype` via `mem_primesOverFinset_iff`, and the primed/unprimed `Ideal` bridges. FLT `S_..._fiberOver` / `S_..._le_finrank` / `S_..._inertiaDeg_pos` |
| `FLTForHuman/AlgebraicCurve/WeilExchange/GaloisRamification.lean` | Galois ramification and inertia (T3) | `Place.exists_algEquiv_smul_eq_of_restrict_eq` (places over the same place of `F'` are Galois-conjugate, via `Ideal.exists_smul_eq_of_isGaloisGroup` on the two fibre-centre primes), `Place.restrict_ofAlgAut_smul` (written once; the pin's private twin in the first node's file is not), `SemilinearAut.{ord_algebraMap_smul, ramificationIndex_smul, inertiaDeg_smul}` and the corollaries `Place.{ramificationIndex_eq_of_restrict_eq, inertiaDeg_eq_of_restrict_eq}`. FLT the seven `S_AlgebraicCurve_{Place,SemilinearAut}_*` files |
| `FLTForHuman/AlgebraicCurve/WeilExchange/Transport.lean` | along-map transport and `Pic0` descent (T4) | the 16 nodes — `Place.{restrictAlong_restrictAlong, ramificationIndexAlong_comp, inertiaDegAlong_comp}`, `Divisor.{pushforwardAlong_pushforwardAlong, pullbackAlong_pullbackAlong, correspondence_congr, correspondence_correspondence}`, `Pic0.{correspondence_correspondence_comm, mk_eq_zero_iff, zsmul_mk, zsmul_mk_eq_zero_of_isPrincipal, nsmul_mk_eq_zero_of_isPrincipal, addOrderOf_mk_dvd_of_isPrincipal}`, `finiteAlong_comp`, `finiteAlong_of_surjective`, `separableAlong_of_charZero` — **plus the shared prelude written once**: `BifibreDev.{inertiaDegAlong_congr, isIntegral_toAlgHom, toAlgHom_comp_toAlgHom, restrict_restrict}` and `Place.{ramificationIndex_eq_mul_ramificationIndex_restrict, inertiaDeg_eq_mul_inertiaDeg_restrict}`. The pin copies that prelude into `bifiber`/`exchange`/`divisor_exchange` (as `BifibreDev.*`/`BifibreW2.*`/`BifibreWEX.*`); T5/T6/T7 import it. `restrictAlong_restrictAlong` is the `rfl`-level canary that keeps `algebraAlong` an `abbrev`. FLT the sixteen `S_AlgebraicCurve_{Place,Divisor,Pic0,finiteAlong,separableAlong}_*` files + `S_..._bifiber` (prelude) |
| `FLTForHuman/FieldTheory/FiniteGroupAction.lean` | the generic orbit/index engine (T5) | `MulAction.ncard_orbit_inter_orbit_mul_card` — for a finite pretransitive `G`-set and `H₁ H₂ ≤ G` with `G = H₁ · H₂`, `#(H₁x₁ ∩ H₂x₂) · #X = #(H₁x₁) · #(H₂x₂)` — and `Subgroup.exists_eq_mul_of_index_inf_eq` (`[G : H₁ ⊓ H₂] = [G : H₁] · [G : H₂] ⟹ G = H₁ · H₂`). Neither is in mathlib v4.34; the proofs are the pin's, with its seven helpers (`card_eq_mul_of_card_fiber`, `card_preimage_eq_mul_of_card_fiber`, `card_fiber_smul_eq`, `card_smul_mem_eq`, `card_fiber_psi_eq`, `ncard_orbit_inter_orbit_mul_card_eq`, `stabilizer_mk_one_eq`) written once and kept `private`. The route was scouted first (3.2 s); the only v4.34 drift is `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` and the `haveI` style lint. FLT `S_MulAction_ncard_orbit_inter_orbit_mul_card` + `S_Subgroup_exists_eq_mul_of_index_inf_eq` |
| `FLTForHuman/AlgebraicCurve/WeilExchange/Bifibre.lean` | the bifibre count (T5) | `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` (a Galois fibre's weight is `finrank F' M`, concentrated at `W`), `Place.exists_restrict_eq` (restriction is surjective along a finite separable extension), and `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` (the `F`-weighted sum over the bifibre `T` is `(e₁f₁)(e₂f₂)`, by the generic orbit count at `X = Gal(M/F) · P₁`). Also the supporting `BifibreDev` API (`resHom`, `galAction` — `@[reducible]`, `gal_smul_def`, `mem_range_resHom_iff`, `card_range_resHom`, `index_range_resHom`, `orbit_range_resHom_eq`, `orbit_gal_eq`, `image_val_orbit`, `forall_apply_algebraMap_eq_of_adjoin_eq_top`). The T4 prelude is imported, never restated. FLT `S_AlgebraicCurve_Place_{card_fiberOver_mul_ramificationIndex_mul_inertiaDeg, exists_restrict_eq}` + `S_..._bifiber` |
| `FLTForHuman/AlgebraicCurve/WeilExchange/LocalExchange.lean` | the local exchange and the normal closure (T6) | `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` — the local identity T7's divisor exchange reduces to, `∑ W ∈ T, e_{F₁}(W)·f_{F₂}(W) = f_F(w₁)·e_F(w₂)` — proved by the pin's two public stages: the Galois case `BifibreW2.exchange_of_isGalois` (cancelling inside T5's bifibre count, with the positivity of `w₂.inertiaDeg F` from T5's card lemma) and the separable reduction `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable` through the normal closure `Env F E`, whose `Algebra`/`IsScalarTower`/`IsGalois` envelope (`Env`, `algebraEnv`, the four `isScalarTower_env_*`) is `private`. The pin's `BifibreW2` prelude copies are not reproduced. FLT `S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange` |
| `FLTForHuman/AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean` | the `P¹` places and degree (T8) | the classification `RationalFunctionField.{subsingleton_setOf_forall_ne_ofHeightOneSpectrum, exists_forall_ne_ofHeightOneSpectrum, finite_setOf_ord_ne_zero}`, the `ord` leaves `{ord_ofHeightOneSpectrum_eq_neg_log, ord_ofHeightOneSpectrum_of_span, ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum}`, the residue-field `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` (Ostrowski + the `WFg` `intDegree` helper), and the `P¹` base case `{degree_eq_zero_of_forall_eq_ord_algebraMap, degree_eq_zero_of_forall_eq_ord}` — the last reducing a rational function to numerator/denominator. `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` is Ostrowski in mathlib's `or` shape. `deg_ofHeightOneSpectrum` was already AC0's and is not rewritten. Only T8-local private helpers are written (the dichotomy, `finite_setOf_valuation_ne_one`, the `WFg`/`WFj` blocks); the pin's ≈214-line `'`-copy prelude is never reproduced. FLT the ten `S_AlgebraicCurve_RationalFunctionField_*` files |
| `FLTForHuman/AlgebraicCurve/PrincipalDivisors/Transcendence.lean` | `HasPrincipalDivisors` via transcendence (T9) | `hasPrincipalDivisors_of_transcendental` (char-zero `K`, `F` finite over `K(x)`, `x` transcendental) and its `adjoin` form `hasPrincipalDivisors_adjoin_of_transcendental`, plus the public shared statement `hasPrincipalDivisors_of_finiteDimensional_ratFunc` (risk 9) and the pin's public `W2.hasPrincipalDivisors_adjoin`. The engine is the norm formula `ord_v(N f) = ∑_{w | v} f(w)·ord_w(f)`: the `private` block `Place.{aeval_mem, exists_coeff_ord_ne_zero, ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal, relNorm_fiberCenter, count_normalizedFactors_span_singleton, relNorm_span_singleton, ord_norm_algebraMap_integralClosureAt, ord_norm_eq_sum_fiberOver}`, `Divisor.pushforwardNormFormula_of_finiteDimensional`, `finite_setOf_ord_ne_zero_of_finiteDimensional` — built on the T2 fibre-centre dictionary (imported, not restated) and transferred from T8's `P¹` base case. `PerfectField (FractionRing v.toValuationSubring)` fires from `PerfectField.ofCharZero` via a private `CharZero v.toValuationSubring` instance; the `relNorm`/`normalizedFactors` core is irreducible. FLT `S_AlgebraicCurve_hasPrincipalDivisors_{of_transcendental, adjoin_of_transcendental, of_finiteDimensional_ratFunc}` |

| `FLTForHuman/ModularCurve/Defs/HeckeOperator.lean` | the Hecke degeneracy maps and the correspondence (SET-M1 m1) | `heckeAlphaBar` (the inclusion underlying the `N ∣ Nℓ` degeneracy) and `heckeBetaBar` (`q ↦ q ^ ℓ`), their integrality predicates `HeckeAlphaBarIntegral`/`HeckeBetaBarIntegral`, the divisor correspondence `heckeDivBar`/`heckePic0Bar` and the transposes. The pin's four supply lemmas are all in `Defs/Laurent.lean`: two dedup to its `coeffMap_qExpand`/`coeffEmb_qExpand`, and the two generic `Theorems/`-wrapper targets `laurentBaseChange_mono`/`qExpand_mem_laurentBaseChange` were moved there (post-effort) although FLT repeats them privately (`'` in `HeckeOperator`, `''` in `DegeneracyTower`). `heckeAlphaBar = towerInclBar` is `rfl`. FLT `Def_ModularCurve_HeckeOperator` (191) |
| `FLTForHuman/ModularCurve/Defs/DegeneracyTower.lean` | the degeneracy tower and `HeckeExchangeAt` (SET-M1 m1) | `towerInclBar` (`N ∣ M`), `towerSubstBar` (`= towerInclBar ∘ heckeBetaBar`), the six definitional composites (`heckeAlphaBar_eq_towerInclBar` is `rfl`; `heckeBetaBar_eq_towerSubstBar` is a `Subtype.ext`), the square `heckeSquareBar_commutes`, and `HeckeExchangeAt` — the predicate the effort targets. The pin's private `laurentBaseChange_mono''` is imported from `Defs/Laurent.lean` instead of repeated. FLT `Def_ModularCurve_DegeneracyTower` (138) |
| `FLTForHuman/ModularCurve/Defs/HeckeTotal.lean` | the total Hecke operator with its junk branch (SET-M1 m1) | `HeckeInputsAlong` (the five inputs of the correspondence at `(N, ℓ)`), `heckeOperatorAlong` (the `if h : … then … else 0` with `open Classical`), `heckeInputsAlong_intro`/`heckeOperatorAlong_eq`/`heckeOperatorAlong_of_not`, and `HeckeInputsAll` — the pin's `Def_ModularCurve_HeckeOperatorTotal` (54) + `Def_ModularCurve_HeckeInputsAll` (13) in one module |
| `FLTForHuman/ModularCurve/Defs/HeckeModule.lean` | the operators on `JZero`, the target proposition, and the `HeckeAlg` payoff (SET-M1 m1) | In-cone: `heckeOperatorBar : Module.End ℤ (JZero N)`, `HeckeOperatorsCommuteBar`, `isMulCommutative_adjoin_heckeOperatorBar`. Out-of-cone tail: `HeckeAlg`/`heckeGen` are restated locally (3 lines, the pin imports them from the large-cone `Def_HeckeGalois_EichlerShimura`) and the `MvPolynomial`-module structure `heckeEvalBar*`/`heckeModuleBar*` is ported whole. FLT `Def_ModularCurve_HeckeModule` (122) |
| `FLTForHuman/ModularCurve/Defs/ArithmeticGalois.lean` | the `bar` layer of `ArithmeticGalois` (SET-M1 m1) | `arithmeticRingAut` (the coefficientwise action of `L ≃ₐ[ℚ] L`), its `SemilinearAut` packaging `arithmeticGalois`, and the two `bar` abbreviations `modularFunctionFieldBar`/`JZero`. The pin's `PicAction` section and `JZero.torsionGaloisRep` are **deferred** (they need the `SMul (SemilinearAut K F) (Pic0 K F)` instance the AC port deliberately dropped). FLT `Def_ModularCurve_ArithmeticGalois` (140) |
| `FLTForHuman/ModularCurve/Defs/JqCoeff.lean` | the `j`-constants over a general field (SET-M1 m2) | `jqModC`/`jqNModC` (the `PowerSeries.map` analogues of `jq`/`jqN`), the field `modularFunctionFieldC`, and the base-change family `map_jqModC`/`jqModC_eq_map_intCast`; `jqModC_rat`/`modularFunctionFieldC_rat` are `rfl`. FLT `Def_ModularCurve_JqCoeff` (83) |
| `FLTForHuman/ModularCurve/Defs/GeometricBaseChange.lean` | the tensor-product model of base change (SET-M1 m2) | The effort's **one-time shape decision**: `L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀` (`baseChangeHom`/`baseChangeEquiv`), `exists_baseChangeHom_eq`, and the geometric automorphism `geomAut`. v4.34 drift: `Subfield.toIntermediateField'` is gone, so `exists_baseChangeHom_eq` builds its field from `AlgHom.range.toIntermediateField'`; `TensorProduct.inductionOn` has no `zero` case. FLT `Def_ModularCurve_GeometricBaseChange` (227) |
| `FLTForHuman/ModularCurve/Defs/QAdicPlace.lean` | the `q`-adic place and the rational cusps (SET-M1 m2) | `order_jq`, the `HahnSeries.order` arithmetic `order_{mul,inv,pow,zpow,div}_of_ne_zero_bar`, `qSeriesBar` + its algebra laws, the valuation subring `qIntegersBar`, the uniformizer block (`uniformizerBar`, `irreducible_uniformizerBar`), `qIntegersBar_isPrincipalIdealRing`, the places `qInftyPlaceBar`/`qInftyPlaceRat` and the rational cusps `cuspInfty`/`cuspInftyFull`, and `IsCusp`. v4.34: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. FLT `Def_ModularCurve_QAdicPlace` (380) |
| `FLTForHuman/ModularCurve/Defs/ModularUnit.lean` | the modular unit `Δ / Δ(q ^ p)` (SET-M1 m2) | `IsMonicOfOrder` + its namespace (`ne_zero`/`coeff_self`/`coeff_of_lt`/`single`/`ofPowerSeries`/`mul`/`of_mul_right`/`qExpand`), `dedekindEtaUnitQ`, the discriminant series `deltaSeries`/`deltaSeriesN`, the modular unit `modularUnitSeries` with its order/coefficient lemmas and multiplicativity, and `eisensteinNumerator`. FLT `Def_ModularCurve_ModularUnit` (185) |
| `FLTForHuman/ModularCurve/Defs/AtkinLehner.lean` | the Fricke involutions and the `bar` cusp (SET-M1 m2) | `IsFrickeAut`/`frickeInvolution` and the `Full` pair `IsFrickeAutFull`/`frickeInvolutionFull`, the rational cusps `cuspZero`/`cuspZeroFull`, `order_coeffEmb_jq` and `cuspInftyBar`. The pin's `SMul (F ≃ₐ[K] F) (Place K F)` lives in AC's `Defs/SemilinearAut.lean` (moved there post-effort). v4.34: `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`. FLT `Def_ModularCurve_AtkinLehner` (107) |
| `FLTForHuman/ModularCurve/Defs/CuspidalClass.lean` | the Fricke `bar` involution and the cuspidal class (SET-M1 m2) | `frickeInvolutionBar = geomAut … (frickeInvolutionFull N)`, `cuspZeroBar`, the cuspidal divisor `cuspidalDivisor = [cuspZeroBar] - [cuspInftyBar]` with `degree_cuspidalDivisor = 0` (through the ported `SemilinearAut.deg_smul`), `cuspidalDivisor₀` and `cuspidalClass`. FLT `Def_ModularCurve_CuspidalClass` (55) |
| `FLTForHuman/ModularCurve/Analytic/QParamUnique.lean` | `qParam`-expansion uniqueness (SET-M1 m3) | `qParam_coeff_unique` over the bare `F : ℍ → ℂ` (the pin's `HasFPowerSeriesOnBall`/`FormalMultilinearSeries` route, all helpers `private`) and the `ℤ`-indexed Laurent version `laurent_qParam_coeff_unique`. The bare-function shape held in v4.34 (no `DFunLike` stall). FLT `S_ModularCurve_qParam_coeff_unique` (158) + `…_laurent_qParam_coeff_unique` (71) |
| `FLTForHuman/ModularCurve/Analytic/Gamma0Cosets.lean` | the `Γ₀` coset permutation and the `SL₂` diagonal transport (SET-M1 m3) | `exists_perm_gamma0_cosetReps` (the `ℓ + 1` representatives `1`, `S * T^b` permuted by right multiplication), `exists_sl2_heckeDiagMatrix_smul_eq` (a `Γ₀(N)`-element pushed through `heckeDiagMatrix N`, denominators matching) and `discriminant_div_discriminant_heckeDiagMatrix_smul` (`Δ(τ)/Δ(Nτ)` is `Γ₀(N)`-invariant). v4.34 drift: `SpecialLinearGroup.map`'s matrix coercion no longer reduces under `simp`, so the conj-matrix identity is stated once (`mapGL_conjSL`). FLT the three `S_ModularCurve_{exists_perm_gamma0_cosetReps, exists_sl2_heckeDiagMatrix_smul_eq, discriminant_div_discriminant_heckeDiagMatrix_smul}` files |
| `FLTForHuman/ModularCurve/Analytic/ModularUnitQExpansion.lean` | the modular-unit `q`-expansion core (SET-M1 m3) | The four `hasSum_{,smul_}modularUnitSeries{_inv,}_qParam` headlines, derived from the two public generic heads `hasSum_modularUnit`/`hasSum_modularUnitInv` and the `Δ`-ratio invariance. FLT repeats a **byte-identical 165-line prelude** (`ratNRH`/`theta`/`gfun`/`discriminant_eq_qParam_mul_gfun`/`hasSum_theta_deltaSeries`/`theta_deltaSeriesN_ne_zero`/`phiFun`/`psiFun`/`taylorCoeff`/`hasSum_taylorCoeff`) in **four** `S_` files; the port writes it **once**, all helpers `private`. FLT the four `S_ModularCurve_hasSum_{,smul_}modularUnitSeries{_inv,}_qParam` files (258 + 263 + 321 + 325) |
| `FLTForHuman/ModularCurve/Analytic/Gamma0InvariantCore.lean` | the shared Γ₀-invariant prelude (SET-M2 m4) | FLT's M8 prelude written **once** (the pin repeats a **651-content-line block** in three `S_` files; the first two differ by 12 lines total): `interpPoly`/`conjPoly` + their permutation/evaluation lemmas, `slotH`/`liftPerm`, `coeffMap_{qTwist,conj}`, `qTwist_slotH`/`qTwist_conj`, `interpK`/`conjK`/`exists_interpK_coeff_eq`/`exists_conjK_coeff_eq`, the missing `RealL.sum`/`RealL.interpPoly_coeff`/`RealL.conjPoly_coeff` (the rest imported from `Hauptmodul.lean`), `realL_*`, `jt`/`jtN`, `cosetRep`/`slotF`/`slotJ`, `interpFun`/`conjFun`, `mem_adjoin_of_{interpK,conjK}_coeff_eq`, `iota`/`dHat`/`exists_sum_eq_mul_dHat`, `mem_modularFunctionField_of_data`, `isIntegral_of_data`, `sigma`. FLT the three `S_ModularCurve_*_of_hasSum_of_gamma0_invariant` files (870 + 870 + 1,155) |
| `FLTForHuman/ModularCurve/Analytic/FrickeInvariance.lean` | the Fricke/inclusion headlines and the `q ↦ q^ℓ` transport (SET-M2 m4) | `mem_modularFunctionField_of_hasSum_of_gamma0_invariant`, `isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant`, the four small `modularUnitSeries` targets, and the pin's third-file block `natDegree_interpPoly_lt`/`realL_jtN_S`/`realL_sum_qExpand_mul_jq_pow`/`coeffMap_castC_injective`/`embW*`/`fricke_transport` (parametrised in the automorphism; the third headline itself is delivered in `FrickeAut.lean`) |
| `FLTForHuman/ModularCurve/Degree/PhiData.lean` | the Φ datum family (SET-M2 m6) | `modularPolynomialFamily` and `exists_modularPolynomialData_evalSymm` (one-liners over the ported `exists_phiIrreducible_evalSymm`), `nonempty_modularPolynomialData_of_squarefree` (the biresultant), `ModularPolynomialData.eval_jqNModC_{mul_eq_zero,of_mul_eq_zero}`, `isIntegral_jqNModC_mul`/`isIntegral_jqNModC_all_of_modularPolynomialFamily`, `ModularPolynomialData.isIntegral_jqN`, `full_eq_of_prime`, `functionFieldGeneration_of_prime`. FLT the fourteen M5 `S_` files |
| `FLTForHuman/ModularCurve/Degree/PhiDegree.lean` | the Φ degree tail (SET-M2 m6) | `transcendental_jqModC`, `finiteDimensional_adjoin_jqNModC`, `finrank_adjoin_jqNModC_le` (the private `phiAt`/`phiOver` argument). FLT the three `S_` files |
| `FLTForHuman/ModularCurve/Analytic/CuspBookkeeping.lean` | the cusp bookkeeping (SET-M2 m5) | The 11 M9 nodes: `ord_qInftyPlaceBar` (the one real proof — `qSeriesBar`'s order through `qInftyPlaceBar`), `ord_cuspInftyBar{_coeffEmb_jq,_coeffEmb_qExpand}`, `ord_cuspZeroBar_coeffEmb_{jq,qExpand}`, `frickeInvolutionBar_coeffEmb_qExpand`, `cuspZeroBar_ne_cuspInftyBar`, `isCusp_iff_ord_neg`, `isCusp_cuspInftyBar`/`isCusp_cuspZeroBar`. FLT the eleven `S_ModularCurve_{ord_*,isCusp_*,cuspZeroBar_ne_cuspInftyBar,frickeInvolutionBar_coeffEmb_qExpand}` files |
| `FLTForHuman/ModularCurve/Analytic/FrickeAut.lean` | the Fricke automorphisms (SET-M2 m5) | `exists_isFrickeAut_of_modularPolynomialData` (the `AdjoinRoot`/`frickeAbsoluteHom` route over `modularPolynomialData`), `exists_isFrickeAut`, `exists_isFrickeAutFull` (transport along `full_eq_of_prime`), `isFrickeAutFull_frickeInvolutionFull_prime`, and the deferred m4 third headline `coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant` + `coe_frickeInvolutionFull_modularUnitSeries`. FLT `S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData` (197 content) + the four wrappers |
| `FLTForHuman/ModularCurve/Analytic/CuspDichotomy.lean` | the `RatFunc` cusp model, the dichotomy, the folded prime degree, the restrict-scalars identity (SET-M2 m5b) | The pin's **160-content-line `RatFunc 𝕂` model of `modularFunctionFieldBar ℓ` written once** (`jb`, `σa`, `jTr`, `φ`, the `IsScalarTower`/`Module.Finite`/`IsSeparable` instances, `finrank_le`, `restrict_eq_of_isCusp`, `e_infty`/`e_zero`, `le_finrank`, `finrank_tower_eq`), shared by `eq_cuspInftyBar_or_eq_cuspZeroBar` and the folded `finrank_adjoin_jqNModC_eq_of_prime`; `modularFunctionFieldBar_eq_restrictScalars` is the model's `bar_eq_restrictScalars`. **Kernel-timeout fix:** `jTr` is built from a generic `private ifRE (S T) (h : S = T) : ↥S ≃+* ↥T` whose coercion lemma `ifRE_coe` is `rfl` at the abstract `S, T, h`, so the kernel never normalises the two `IntermediateField.adjoin` carriers; `φ_algebraMap` uses `IntermediateField.coe_algebraMap_apply` and the `haveI` became `have`. `lake env lean` **15.9 s** (was a 3 m 09 s `(kernel) deterministic timeout`). FLT the two shared-block `S_` files + `S_ModularCurve_modularFunctionFieldBar_eq_restrictScalars` |
| `FLTForHuman/ModularCurve/Degree/LaurentGlue.lean` | the Laurent/`coeffEmb` glue (SET-M3 m7) | The eight short M4 nodes: `coeffEmb_jq`/`coeffEmb_jqN` (the pin's local `map_qExpand_aux` dedups to the ported `coeffEmb_qExpand`), `order_qExpand`/`order_coeffEmb` (also proved `private` in `CuspBookkeeping` before this module existed; these are the promoted public homes), `laurentBaseChange_adjoin{,_modularFunctionField,_modularFunctionFieldFull}` and `transcendental_jqN`. FLT the eight `S_ModularCurve_{coeffEmb_jq,coeffEmb_jqN,order_qExpand,order_coeffEmb,laurentBaseChange_adjoin,laurentBaseChange_modularFunctionField,laurentBaseChange_modularFunctionFieldFull,transcendental_jqN}` files |
| `FLTForHuman/ModularCurve/Degree/Relfinrank.lean` | the two relative-degree theorems (SET-M3 m7) | `relfinrank_laurentBaseChange` — the pin's `TransportDev` block (`K₀`/`K`, `φ`/`ψ`, `mem_span_image`/`mem_span_range`, `finite_and_finrank_le`, `linearIndependent_pow_mul`, `exists_common_denom`, `linearIndependent_ψ`, `relfinrank_eq`), all helpers `private`; the pin's `_full`/`_restrictScalars`/`_full_prime` tail is omitted (`_full_prime` needs m5 and is not an M4 node). And `relfinrank_qExpand_full` — the pin's 357-line `TS`/slot prelude is **imported** (`Defs/{TS,PhiAtSlot,Twist,Cyclotomic}.lean`, `PhiSlotRoots.lean`, `PhiGenSplits.lean`), the new block being `g2_relfinrank_union_left`/`g2_{zeta_mod,seed_eq,y0_eq,twist_fix}` plus the two `finrank_adjoin_jq_of_subset_range_qExpand{,_of_mem}` heads. Two instance-search timeouts were fixed by explicit `Module.Free.of_divisionRing`/`Algebra.IsIntegral.of_finite` locals, **not** by raising any heartbeat cap. FLT `S_ModularCurve_relfinrank_laurentBaseChange` (265 content) + `S_ModularCurve_relfinrank_qExpand_full` (631 content, 357 prelude) |
| `FLTForHuman/ModularCurve/Degree/Roof.lean` | the roof generation and the diagonal degree (SET-M3 m9) | `heckeRoof_adjoin_range_union_eq_top` (the roof's two legs generate the top field; `jqN_congr`/`mem_range_towerInclBar_iff`/`laurentBaseChange_adjoin_pair` + m6's `isIntegral_jqNModC_mul`) and `finrankAlong_towerSubstBar_comp_heckeAlphaBar` (the diagonal degree is the product; `fieldRange_heckeBetaBar`/`finrankAlong_heckeBetaBar`/`finrankAlong_towerInclBar_of_eq`/`finrankAlong_towerSubstBar_roof`). The three generic `AlgebraicCurve.finrankAlong` helpers (`finrankAlong_comp`, `finrankAlong_id`, `finrankAlong_eq_relfinrank_fieldRange`) were promoted post-effort to `AlgebraicCurve/Defs/Correspondence.lean`, beside `finrankAlong`. The pin's `maxHeartbeats 6400000`/`synthInstance.maxHeartbeats 3200000` bumps are **not** needed: the port builds under the project's global `4000000` in **15 s**. FLT `S_ModularCurve_heckeRoof_adjoin_range_union_eq_top` (418 content, 356 prelude) + `S_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar` (441 content, 356 prelude) |
| `FLTForHuman/ModularCurve/HeckeInputs/Integrality.lean` | tower integrality/finiteness and the Hecke integrality predicates (SET-M4 m10) | The 13 M10 nodes: the two `finiteAlong_hecke{Alpha,Beta}Bar_of_modularPolynomialData` heads (the target field written as `adjoin L (gens L (N * ℓ))` with `gens L N = {jqNModC L d | d ∣ N}`, each generator integral by m6's `isIntegral_jqNModC_mul`/`eval_jqNModC_of_mul_eq_zero`, then `fg_adjoin_of_finite`), the two `hecke{Alpha,Beta}BarIntegral_of_modularPolynomialData` (`Algebra.IsIntegral.of_finite`), the four `_of_prime` forms (`exists_modularPolynomialData_evalSymm`), and the five tower nodes (`towerInclBar_surjective_of_dvd_dvd`, plus `towerInclBar_isIntegral`/`towerSubstBar_isIntegral`/`_finiteAlong` by strong induction on the quotient). The pin's `private` `dvd_mul_prime_cases`/`gens`/`gens_finite`/`jqNModC_mem_bar`/`isIntegral_gens`/`qExpand_jqNModC`/`isIntegralElem_heckeBetaBar_gens` block is reproduced `private`. FLT the thirteen `S_ModularCurve_*` files (447 raw / 301 content) |
| `FLTForHuman/ModularCurve/PrincipalDivisors/ModularCurveBar.lean` | `HasPrincipalDivisors` for the modular function fields (SET-M4 m11) | `hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull` **collapses onto AC's** `hasPrincipalDivisors_adjoin_of_transcendental`: `laurentBaseChange_modularFunctionFieldFull` writes the field as `adjoin L (insert (jqModC L) (gens L N))`, `transcendental_jqModC` is the `hx`, and each `jqNModC L d` is integral by m6's `isIntegral_jqNModC_all_of_modularPolynomialFamily` (which consumes `hΦ`); the pin's `private` `Finset` `gens`/`mem_gens_iff`/`insert_gens` block is reproduced `private`. `hasPrincipalDivisors_modularFunctionFieldBar` is the layer form at `AlgebraicClosure ℚ` (the `bar` abbrev is definitional). The coverage report's "nearly a corollary" prediction **held**: 81 port lines against the pin's 82 raw / 38 content. FLT `S_ModularCurve_hasPrincipalDivisors_{laurentBaseChange_modularFunctionFieldFull,modularFunctionFieldBar}` |
| `FLTForHuman/ModularCurve/HeckeExchange/Reduction.lean` | the divisor/`Pic0` exchange reduction (SET-M4 m12) | The four M2 nodes, pure assembly: `heckeDivBar_heckeDivBar_of_heckeExchangeAt` (`Divisor.correspondence_correspondence` + `HeckeExchangeAt` + `correspondence_congr` with `towerSubstBar_comp_heckeBetaBar`/`towerInclBar_comp_heckeAlphaBar`), `heckeDivBar_comm_of_heckeExchangeAt` (the previous at `(ℓ, ℓ')` and `(ℓ', ℓ)` + `correspondence_congr` with `mul_comm`), `heckeOperatorBar_comm_of_heckeExchangeAt` (the `HeckeInputsAlong` junk split, `heckeOperatorAlong_eq`, `Pic0.correspondence_correspondence_comm`) and `heckeOperatorsCommuteBar_of_heckeExchangeAt` (the `Nat.Primes` bookkeeping; `ℓ = ℓ'` is `rfl`); tower integrality from m10. The junk branches use `heckeOperatorAlong_of_not` at the bare linear-map shape — the pin's pointwise `heckeOperatorBar_apply` rewrite fails `rw`'s implicit-transparency type check on the `Nat.Primes` subtype. FLT the four `S_ModularCurve_*_of_heckeExchangeAt` files (111 raw / 68 content) |
| `FLTForHuman/ModularCurve/HeckeCommuteBar.lean` | **the capstone** — `ModularCurve.heckeOperatorsCommuteBar` (m13, reserved for the reviewer) | The ported `math/009` theorem, unconditional: `heckeExchangeAt_of_WEX` applies the ported `AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` to the Hecke roof square; `heckeExchangeAt_of_rows` feeds it m9's `heckeRoof_adjoin_range_union_eq_top` (`hgen`) and `finrankAlong_towerSubstBar_comp_heckeAlphaBar` (`hLD`) plus m10's `hfin_of_legR`; the dischargers are `hP_of_rows` (m11 + m6's `modularPolynomialFamily`), `dataAll_of_rows` (the same family's `.choose`) and `hsepS_of_rows` (m10's integralities + AC's `separableAlong_of_charZero`); `heckeOperatorsCommuteBar_of_rows` and the target go through m12's reduction, with FFG's `functionFieldGeneration`. `#print axioms ModularCurve.heckeOperatorsCommuteBar` = `[propext, Classical.choice, Quot.sound]`. FLT `S_ModularCurve_heckeOperatorsCommuteBar` (112 raw / 63 content) |

`FLTForHuman/ModularCurve/` also carries the Hecke layer
([PORTING-MC.md](topics/PORTING-MC.md), run briefs
[hecke/SET-M1.md](topics/hecke/SET-M1.md), [SET-M2.md](topics/hecke/SET-M2.md),
[SET-M3.md](topics/hecke/SET-M3.md), [SET-M4.md](topics/hecke/SET-M4.md)):
the divisor-correspondence Hecke face's vocabulary (m1/m2) and its analytic layers
(m3 modular-unit q-expansion, m4 Fricke/inclusion, m6 Φ data, m5 cusp
bookkeeping/Fricke automorphisms, the m5b `RatFunc` cusp model, SET-M3's m7
Laurent/relative-degree glue and m9 roof/diagonal degree, and SET-M4's m10
tower integrality/Hecke integrality predicates, m11 principal divisors and m12
exchange reduction). Its consumer is `spec/ModularCurveHeckeConsumer.lean`
(Zones A–B, C–E, G, I `[relfinrank]`, F `[roof]`, J `[inputs]` and H
`[reduction]`, at 0 errors / 0 warnings). Namespace `ModularCurve`, matching FLT.

`FLTForHuman/AlgebraicCurve/` is the third port's area ([PORTING-AC.md](topics/PORTING-AC.md),
run briefs [topics/algebraicCurve/SET-1.md](topics/algebraicCurve/SET-1.md) and
[SET-2.md](topics/algebraicCurve/SET-2.md)): the generic curve layer with no
schemes, mathlib-only, namespace `AlgebraicCurve`, whose consumer is
`spec/AlgebraicCurveConsumer.lean`. **SET 1 (AC0, T1–T4) is complete**: 12 modules
(2,617 + 1,019 lines, 269 public declarations) are green with zero warnings and
zero `sorry`, `spec/check_flt_statements.py` reports **586 identical, 0 mismatched,
0 missing**, and the consumer's Zones A–E are at **0 errors** (with real
cross-module wire tests). **SET 2 (T5, T6, T8, T9) is also complete**: five new
modules — `FLTForHuman/FieldTheory/FiniteGroupAction.lean`,
`WeilExchange/{Bifibre, LocalExchange}.lean` and
`PrincipalDivisors/{RatFuncDegree, Transcendence}.lean` — 1,780 lines / 31 public
declarations. **T7, the divisor-exchange capstone, is complete too**:
`WeilExchange/DivisorExchange.lean` proves
`Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` — the
declaration `ModularCurve.heckeOperatorsCommuteBar` calls — from the local exchange,
and consumer Zone J composes it with T4's `correspondence_correspondence`. The
effort's final numbers: **`lake build` 4,034 jobs, zero warnings, zero `sorry`**;
checker **618 identical, 0 mismatched, 0 missing**; consumer **Zones A–J 0 errors**;
`#print axioms` clean on every headline. The three generic inputs of `math/009`'s
exchange reduction are now ported theorems. The record is
[logs/ac-port.md](logs/ac-port.md).

`FLTForHuman/ModularForms/` also carries the fourth port, the **Hecke-operator
face** (the slash operators `heckeU`/`heckeT`, their invariance / analytic /
coefficient layers, the bundled `heckeTLin`/`heckeULin`, the Hecke algebra, the
eigenform dictionary and the integral lattice). **Paused 2026-09-23**: the
survey's Stages A–C are done (18 modules / 3,920 lines / checker 802 identical,
0 mismatched), Stage D (Γ_H / Γ₁ / Atkin–Lehner) remains, and the Hecke algebra's
finiteness half is ruled out of scope. The status and remaining-work map is
[topics/PORTING-Hecke.md](topics/PORTING-Hecke.md); the per-set work orders are
[topics/hecke/](topics/hecke/) and the measured record is
[logs/hecke-port.md](logs/hecke-port.md).

The `base/003` endgame — `S₂(Γ₀(2)) = 0` and its level-one analogue — is the
smallest port so far: the two theorems now live as **corollaries of the Sturm
bound** at the end of `FLTForHuman/ModularForms/SturmBound.lean` (with the index
`[SL(2,ℤ) : Γ₀(2)] = 3` in `Gamma0TwoIndex.lean`), and they are the first entry
into the **modularity/level-lowering** branch rather than the Hecke cone. The
superseded norm-route proof, with its cusp-form norm, is parked in the `Reserve`
library
([`Reserve/ModularForms/LevelTwoCuspVanishing.lean`](Reserve/ModularForms/LevelTwoCuspVanishing.lean),
[`Reserve/ModularForms/CuspFormNorm.lean`](Reserve/ModularForms/CuspFormNorm.lean),
restored from commit `4c4f588`). Its consumer is
[spec/LevelTwoCuspConsumer.lean](spec/LevelTwoCuspConsumer.lean); the measured
record is [logs/level2-cusp-port.md](logs/level2-cusp-port.md).

The port of `#E[n](K) = n²` (math/005) has its own working record:
[logs/card-torsion-port.md](logs/card-torsion-port.md) — dependency trace,
dropped clutter, and port order — with the reusable lessons (method, gotchas,
v4.34.0 API drift, and a checklist) in [porting-playbook.md](porting-playbook.md).
The `functionFieldGeneration` effort keeps its record in
[logs/ffg-port.md](logs/ffg-port.md).

The Φₚ splitting plan,
[PORTING-PhiGen.md](topics/PORTING-PhiGen.md) — **retired into `topics/` when the
cone closed** — inventories the Φₚ splitting cone that gates the conditional
capstone (PORTING-FFG §7.1/§7.7). It records the cone's math-content
decomposition, the measurement that its
headline 11,034-line count is ~1.6× inflated by the one-`S_`-file-per-theorem
layout, and the decision to isolate the cone's only analytic input — the
level-one q-expansion principle — as the next topic. The mathematics of that
input is in
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md),
which separates the level-one q-expansion principle (R1, the analytic input)
from the level-`N` degree statement (R2, reconstructed algebraically).

`FLTForHuman/ModularCurve/` holds the definitions of `PORTING-FFG.md` Layer 0
(the `jq` / `qExpand` / `qTwist` objects of math/010), plus the topic modules
that followed. `FLTForHuman/FieldTheory/` is its generic companion: the
mathematical engine the segment runs on, stated for an arbitrary `F ⊆ L` and
mentioning no curve — the place a future `ModularCurve` theory puts its generic
prerequisites, not a theory directory itself. `FLTForHuman/ModularForms/` is the
`Φ_p`-splitting sub-effort's analytic area (R1, the level-one q-expansion
principle): modular forms on `ℍ`, with no modular-curve object in sight. All
three sit beside `FLTForHuman/Elliptic/` under the **single**
`FLTForHuman` library — Layer 0 landed with no `sorry`, so the separate build
target it used to have was no longer needed. There is no `import Mathlib` anywhere.
**Layer 0 and all four topics are done**: twelve modules (68 declarations in 0a,
69 in 0b, 24 in `JqCoefficients`, 25 in `Spine`, 3 in `CommonRoot` plus its three
checked instantiation `example`s, and 9 public interface lemmas in
`Defs/Laurent.lean` and `Defs/Jq.lean`) are green with zero warnings and zero
`sorry`, and the deliverable measure
[spec/ModularCurveConsumer.lean](spec/ModularCurveConsumer.lean) reports **0
errors** with Zones A, B and C all bound. Its only remaining `sorry` is the
deferred theorem's capstone. `PORTING-FFG.md` records why the theorem itself stays
deferred; the consumer's tail carries the v4.34.0 friction list, and
[spec/check_flt_statements.py](spec/check_flt_statements.py) diffs every port
declaration's statement against the pinned source (288 of 288 identical through
T16, with the own-proof declarations exempted explicitly).

Both Layer 0 work orders are gone: they were finished, their durable material
moved into §7 of [porting-playbook.md](porting-playbook.md) — the math-clarity
principles, the overlap with the first port, and the measured cost model — and
[logs/ffg-port.md](logs/ffg-port.md) carries the record and the calibration.
Both layers finished in a single goal round against a much larger budget.

The first topic is also complete:
[TOPIC-jq-coefficients.md](topics/functionFieldGeneration/TOPIC-jq-coefficients.md) closed the last two consumer
items (`jq.coeff 0 = 744`, `jq.coeff 1 = 196884`) by a mathlib route FLT does not
use — the pentagonal theorem for `∏' n, (1 - X ^ (n+1))` — rather than the
modular-form cluster. It is the first topic whose proof is ours rather than a
transcription; [logs/ffg-port.md](logs/ffg-port.md) §2c and §8.3 carry its
measured cost and the finding that FLT's own proof of these coefficients is a
standalone 237-line file, not the cluster.

The second topic is complete too:
[TOPIC-conditional-capstone.md](topics/functionFieldGeneration/TOPIC-conditional-capstone.md) checked the
*architecture* of the theorem — `hall_all`, the strong induction carrying
`Tight ∧ Gen` over the divisor lattice — with FLT's significant remaining
statements as the named fields of an `Inputs` structure, and proved
`functionFieldGeneration_of (h : Inputs)`. The auxiliaries turned out to be glue,
so what remains of the deferred theorem is now a list of fields to discharge
one at a time. [logs/ffg-port.md](logs/ffg-port.md) §2d carries its measured cost
and §8.4 the field list with the reason each survives.

The third topic is complete:
[TOPIC-interface-tier.md](topics/functionFieldGeneration/TOPIC-interface-tier.md) added the cone's **outbound
interface** — the nine declarations the rest of FLT reaches this segment through,
`coeffMap_qExpand` (indeg 194) down to `coeffEmb_injective` (19) — as public
lemmas placed with the objects they concern. Two of them are also `Inputs` fields,
so it shrank the debt from 10 fields to 8 while exposing 520 of the cone's
≥5-indegree tier (which sums to 946, so 55%). The two surveys in
[studies/](../studies/) are why it exists; see
[logs/ffg-port.md](logs/ffg-port.md) §2e and §8.5, and `PORTING-FFG.md` §2.1.

The fourth topic is complete too:
[TOPIC-generic-kernel.md](topics/functionFieldGeneration/TOPIC-generic-kernel.md) built the three
`Polynomial.*` lemmas that are the segment's mathematical engine — absent
from mathlib, ~166 lines, generic over any `F ⊆ L` — as the new
`FLTForHuman/FieldTheory/` area, and peeled the third `cites = 0` `Inputs` field,
`relfinrank_modularFunctionField`, into `Defs/Fields.lean`; the debt is now **7**
fields. It is the first module in this port that belongs to neither curve theory,
and the survey's own recommendation
([studies/flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) §4);
[logs/ffg-port.md](logs/ffg-port.md) §2f carries its measured cost and §8.4 the
shrunk field table.

The `Φ_p`-splitting / R1 sub-effort's first topic is complete:
[TOPIC-r1-kernel.md](topics/phiGenSplitting/TOPIC-r1-kernel.md) named R1's
analytic input as
`ModularCurve.coeff_eq_zero_of_hasSum_of_slash_invariant` (base/013 §6's
recommendation) in the new `FLTForHuman/ModularForms/` area, together with the
`n = 0` corollary that is the wire test. It is the port's first module whose
content is analysis on `ℍ`: mathlib's `ModularForm.eq_const_of_weight_zero`
supplied the mathematics, the audit replaced almost all of the pin's 186-line
helper block with public mathlib lemmas, and only the `MDiff`-from-`HasSum`
bridge needed a proof of its own. [logs/phiGen-port.md](logs/phiGen-port.md)
carries the measured cost and the two audit deviations.

The sub-effort's second topic is complete too:
[TOPIC-jq-model.md](topics/phiGenSplitting/TOPIC-jq-model.md) gives `jq` its
analytic model (`jq` sums to `E₄³/Δ` on `ℍ`) and its `SL₂(ℤ)`-invariance, in
`FLTForHuman/ModularForms/JqAnalyticModel.lean`. Its mathlib-first audit came out
**half** the way the work order predicted: `EisensteinSeries.E_qExpansion_coeff`,
`discriminant_eq_q_prod`, `differentiableOn_tprod_one_sub_pow_pow` and
`hasSum_qExpansion` all applied, but `discriminant_cuspFunction_eqOn` did **not**
replace the pin's 199-line eta-product file — it gives the value of
`cuspFunction 1 Δ`, not the Taylor coefficients of `∏' (1-qⁿ)²⁴` — so that
argument was ported. The port is 622 lines against the ~589-line pin, and the
consumer gained Zone D (the model composed with the `jq`-coefficient module);
[logs/phiGen-port.md](logs/phiGen-port.md) §6 carries the accounting.

The sub-effort's third topic is complete, and it **completes R1**:
[TOPIC-hauptmodul.md](topics/phiGenSplitting/TOPIC-hauptmodul.md) proves the
Hauptmodul form — a pole-bounded realized invariant series is a polynomial in
`jq` — in `FLTForHuman/ModularForms/Hauptmodul.lean`. Its audit confirmed it is
the **glue topic**: no mathlib-replaceable leaves (`RealL`, its closure, the
pole-killing lemma and the headline are all ported), and the port is 483 lines
against the ~462-line pin (ratio 1.05). It exports the `RealL` API so the cone
application (T8) reuses it instead of duplicating FLT's copy, and the consumer
gained Zone E (the wire test runs the headline on `jq` with T6's two theorems);
[logs/phiGen-port.md](logs/phiGen-port.md) §7 carries the accounting and the one
checker constraint it discovered.

The sub-effort's fourth topic is complete too, **completing the planned sequence
and discharging the Φ_p cone's item (c)**:
[TOPIC-phiGen-descends.md](topics/phiGenSplitting/TOPIC-phiGen-descends.md) proves
`PhiGen.mem_adjoin_jq_of_phiGenDescends` — the descended coefficients lie in
`ℚ[jq]` — in `FLTForHuman/ModularForms/PhiGenDescends.lean`, over the new Hecke
layer (`Defs/HeckeOperator.lean`, `HeckeQExpansion.lean`). Its audit found that
**mathlib has no Hecke operators** at all, so it adds the sub-effort's first
definition module (the minimal `heckeMatrix`/`heckeDiagMatrix` subset; the
`heckeU`/`heckeT` block is unused by the cone — the later Hecke-operator topic
extends the same module with the full operator block and the Tier-1
slash-invariance layer, `Defs/HeckeRepresentatives.lean` + `HeckeInvariance.lean`,
see [logs/hecke-port.md](logs/hecke-port.md)), and it imports T7's `RealL` API
rather than copying the ~97 lines FLT duplicates — the port is 725 lines against
~741 of pin content (ratio 0.98, the sub-effort's cheapest). The consumer gained
Zone F; [logs/phiGen-port.md](logs/phiGen-port.md) §8 carries the accounting and
the `mapGL`-transparency finding. What remains of the cone is its other five
pieces, not this sub-effort.

The cone's (b) is now **complete**. T9 proved the integrality of the descended
coefficients in `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` — the first
deliberate deviation from a compiled FLT script, and **Route A shipped** (`jq` and
the conjugate family lift to `LaurentSeries (integralClosure ℤ K)`, and `coeffMap`
is pushed through `qExpand`/`qTwist`/`phiProd`, replacing FLT's `CoeffsIntegral`
closure block with ring structure); it also promoted the shared triangularity
`coeff_aeval_jq_neg` (to `Defs/Jq.lean`) and `poleOrderLE_aeval_jq` (to
`Defs/PhiGen.lean`). T10 added the pole bounds in
`FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` and promoted the shared
`TPoleOrderLE` prelude (23 public declarations) into `Defs/PhiGen.lean` — the pin
copies it into twelve `S_` files, so **T11 imports it unchanged**.

T11 then built the cone's **construction** end-to-end in three modules:
`PhiGenDescent.lean` (a, `exists_phiGenDescends`),
`PhiGenDescendsStructure.lean` (the 328 block, with `evalAtJ_injective` by the
mathlib `transcendental_jq` route) and `ModularPolynomialAssembly.lean` (d,
`exists_modularPolynomialData_coeff_eq` + `splits_of_coeff_evalAtJ_eq`). Together
with T9/T8 the whole (a)→(b)→(c)→(d) chain now runs concretely — the consumer's
Zone I wire test does exactly that on `K = CyclotomicField ℓ ℚ`.

T12 then proved the datum's **properties** in three more modules:
`JqCoeffPositivity.lean` (`one_le_coeff_jq`, with two of the audit's mathlib
substitutions landing), `ModularPolynomialIrreducible.lean` (the 895 block written
once, where FLT ships it **five** times) and `ModularPolynomialProperties.lean`
(`evalSymm_of_coeff_evalAtJ_eq` and the capstone
`exists_phiIrreducible_evalSymm`). It also promoted `evalAtJ_eq_aeval_map` to
`Defs/Jq.lean`, deleting T11's two private copies. The consumer's Zone J wire test
is the first **unconditional** one (`exists_phiIrreducible_evalSymm` at `ℓ = 2`).
The five topics moved the consumer to Zones G/H/I/J and the checker 176 → 233;
[logs/phiGen-port.md](logs/phiGen-port.md) §9–§12 carry the measured cost and the
route decisions.

T13 then closed the cone: `ModularPolynomialUniqueness.lean` proves the degree
`[ℚ(j)(j(q^ℓ)) : ℚ(j)] = ℓ + 1` and the uniqueness of the datum, and
`PhiGenSplits.lean` proves `splits_of_prime` and the headline
`splits_prime_at_slot`. It also promoted the cyclotomic roots from the FFG spine's
private copies to the public `Defs/Cyclotomic.lean`, and dropped ~200 pin prelude
lines that the exports never use (they belong to the char-`p`
`*_of_isPrimitiveRoot` variants, outside the cone). The port is 407 lines against
766 deduplicated pin lines, ratio **0.53** — the sub-effort's cheapest. The checker
moved 233 → 242 and the consumer gained Zone K with the capstone wire
(`splits_prime_at_slot` at `K = CyclotomicField 2 ℚ`, `N = p = 2`, `e = u = 1`).
**All 44 nodes of the cone are now ported.** The consumer's remaining `sorry` is
the FFG `Inputs` gap; PORTING-FFG §7.8's T14–T19 proceed with
`splits_prime_at_slot` as a theorem.
[logs/phiGen-port.md](logs/phiGen-port.md) §13 carries the measured cost.

T14, the first topic of the parent remainder, then wrote the pin's **shared slot
prelude once**: `Defs/PhiAtSlot.lean` (the `conj`/`TS` bridges, `phiProd_conj_eq` and
the roots, `phiAtSeed` and its eight lemmas), the twist equivalence
`qTwistEquiv` + `qTwist_iota_of_pow_eq_one` in `Defs/Twist.lean`, four
`TS`-dependent bridges in `Defs/TS.lean`/`Defs/Jq.lean`, and the downstream
`PhiSlotRoots.lean` with the at-slot roots API. It also promoted six `private`
twins out of `Spine.lean`/`PhiGenSplits.lean`, so no shared declaration has two
homes. The prelude is carried by up to thirteen of the seventeen remaining pin
files (`phiAtSeed` at 26–74 uses per carrier), so writing it once is the largest
single dedup left. The checker moved 244 → 276, all 32 declarations verified (its
`DECL_RE` gained an optional leading-attribute group so the pin's one-line
`@[scoped simp] theorem qTwistEquiv_apply` is visible on both sides), and the
consumer gained Zone L, whose chosen wire is `roots_phiProd_conj_nodup` at
`p = 2`, `K = ℂ`, `ζ = -1`. `PORTING-FFG.md` §7.8's row estimated ~250 lines; the
port is **503**. [logs/ffg-port.md](logs/ffg-port.md) §2g carries the measured cost
and the layering finding.

T15, the first topic whose output is proof content, then proved the two `Inputs`
fields that are math/010 §4–§5 in `FunctionFieldGeneration/Descent.lean`:
`jqN_div_mem_modularFunctionField` (the unique-common-root descent, `htw`/`hsp`
left as arguments for T19) and `modularFunctionField_eq_full_of` (the one-prime
`Gen` reduction). It is a pure consumer — T14's prelude, T13's
`splits_prime_at_slot`, T12's `exists_phiIrreducible_evalSymm` and T4's
`mem_range_of_unique_common_root` were all public — and the pin's 735-line file is
one development shipped twice, ~542 lines of which are the T14 prelude. The port
is **252 lines** against the 173-line tail (ratio ≈1.46); the checker moved
276 → 278 and the consumer gained Zone M, whose wire builds a *partially
discharged* `Inputs` with the two T15 fields filled, so the capstone's debt is now
**5**. [logs/ffg-port.md](logs/ffg-port.md) §2h carries the measured cost.

T16, the last purely field-theoretic topic, then proved the **degree** half of
the induction in `FunctionFieldGeneration/DegreeStep.lean`: the first prime power
`[F(j(q^p)) : F] = p + 1` (the nome twist cycles `Φ_p`'s roots), the later powers
`= p` (the peeled factor's roots are cycled by the cyclotomic coefficient
automorphism `coeffMapEquiv τ`), and the tower dispatcher
`relfinrank_full_eq_mul`, which is the third `Inputs` field — so the capstone's
debt is now **4**. It is **605 lines** (455 new module + 150 promoted bridges)
against ≈435 pin lines (ratio ≈1.39), and it also deduplicated the transport
bridges `coeffMap_qTwist`/`coeffMap_TS`/`coeffMap_coeffEmb_algHom` and deleted
the private twins in `PhiGenDescent.lean`/`PhiGenSplits.lean`/
`PhiGenIntegrality.lean`. The checker moved 278 → 288 and the consumer gained
Zone N, whose wire fills three of the seven `Inputs` fields.
[logs/ffg-port.md](logs/ffg-port.md) §2i carries the measured cost.

## Where things live

The documentation has four roles, and they are kept apart on purpose:

| path | role |
|---|---|
| any plan still at the top level | an **active plan** — the blueprint for work in progress. A finished effort's plan is retired into `topics/` (see below); the `functionFieldGeneration` plan is now [topics/PORTING-FFG.md](topics/PORTING-FFG.md) |
| `topics/<effort>/TOPIC-*.md` | **work orders, then executed plans**: one per topic. New work orders open with the mandatory build-discipline block (playbook §3.11); finished ones keep the record of what was learned and what it cost |
| `logs/` | the **linear record** of what happened, in order — `card-torsion-port.md` for the first port, `ffg-port.md` for this one |
| `porting-playbook.md` | the **reusable method**, not tied to any one effort |
| `spec/` | the **deliverable measures**: the consumer and the statement checker |
| `Reserve/` | the **reserve library**: verified modules kept off the critical path (superseded routes, deferred API). It may import `FLTForHuman`; `FLTForHuman` must never import it. Built by default so it stays green and checked |

An executed plan is not deleted: it is the record of a decision and its cost, and
`logs/` cross-references it. When an effort finishes, its plan is retired from the
top level into `topics/`, and the log gains the entry that summarises it.
`topics/functionFieldGeneration/` holds the seven topics of the
`functionFieldGeneration` effort, and `topics/phiGenSplitting/` holds the nine
topics of its Φ_p splitting / R1 sub-effort, whose plan
[PORTING-PhiGen.md](topics/PORTING-PhiGen.md) is retired there. That effort is now
**complete** too: its plan [PORTING-FFG.md](topics/PORTING-FFG.md) is retired to
`topics/` (with a RETIRED banner), and
[ffg-retrospective.md](topics/ffg-retrospective.md) is the closing review of its
decisions, clarity and redundancy cuts. The R1 work orders
[TOPIC-r1-kernel.md](topics/phiGenSplitting/TOPIC-r1-kernel.md),
[TOPIC-jq-model.md](topics/phiGenSplitting/TOPIC-jq-model.md),
[TOPIC-hauptmodul.md](topics/phiGenSplitting/TOPIC-hauptmodul.md) and
[TOPIC-phiGen-descends.md](topics/phiGenSplitting/TOPIC-phiGen-descends.md) are
complete (R1 is done and the cone's (c) is discharged), the cone-algebra topics
[TOPIC-integrality.md](topics/phiGenSplitting/TOPIC-integrality.md) through
[TOPIC-splitting.md](topics/phiGenSplitting/TOPIC-splitting.md) are complete (the
cone is closed), and [logs/phiGen-port.md](logs/phiGen-port.md) is the
sub-effort's record.

## Sources

- FLT: <https://github.com/anthropics/fermats-last-theorem>, local clone pinned at
  `aa2d8b3`. Per-file raw URLs follow
  `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/<path>`;
  the generated module glosses are served at
  <https://tianyipeng.github.io/fermats-last-theorem/>.
- mathlib at `v4.34.0`:
  <https://github.com/leanprover-community/mathlib4/tree/v4.34.0>.

[flt]: https://github.com/anthropics/fermats-last-theorem
[proof-path]: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md
