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
| `FLTForHuman/ModularCurve/Defs/Laurent.lean` | q-substitution + coefficient change | `qExpand`, `qExpandₐ`, `coeffMap`, `coeffEmb`, `laurentBaseChange`, plus the interface lemmas `coeffMap_qExpand`, `coeffEmb_qExpand`, `coeffMap_injective`, `coeffEmb_injective`. **T16 adds** the promoted `coeffMap_coeffEmb_algHom`, the coefficient automorphism `coeffMapEquiv` (routed through `RingEquiv.ofBijective`) with `coeffMapEquiv_apply`, and `iota_injective` (`coeffEmb ∘ qExpand`). FLT `Def_ModularCurve_X0` 25–105, `Def_ModularCurve_LaurentCoeff` 16–123 + `S_ModularCurve_PhiGen_splits_of_prime`/`S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem` |
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
| `FLTForHuman/ModularForms/Defs/HeckeOperator.lean` | the Hecke matrices | `heckeMatrix` (`!![1, j; 0, p]`) and `heckeDiagMatrix` (`!![p, 0; 0, 1]`) with their action on `ℍ`. mathlib has **no** Hecke operators, so this is a definitions port: the 60-line subset the Φ_p cone uses, from FLT's 204-line `Def_ModularForm_HeckeOperator`; the `heckeU`/`heckeT` operator block is not ported (0 occurrences in the cone) |
| `FLTForHuman/ModularForms/HeckeQExpansion.lean` | the Hecke translates of a `q`-expansion | `hasSum_qParam_heckeMatrix_smul` (`τ ↦ (τ+b)/ℓ` twists the coefficients and changes the period `1 ↦ ℓ`) and `hasSum_qParam_heckeDiagMatrix_smul` (`τ ↦ ℓτ`, coefficients `qExpand ℂ (ℓ*ℓ)`). base/013 §5.2's analytic face of the Hecke action. FLT `S_ModularCurve_hasSum_qParam_hecke{Matrix,DiagMatrix}_smul` (~109 lines) |
| `FLTForHuman/ModularForms/PhiGenDescends.lean` | the cone's (c) | `PhiGen.mem_adjoin_jq_of_phiGenDescends` (verbatim): a descended coefficient of the conjugate product lies in `ℚ[jq]`. It proves `cosetPoly_smul` (the coset polynomial's `SL₂(ℤ)`-invariance through the action on `ℙ¹(𝔽_ℓ)`) and privately realizes `c k` via the Hecke translates (the `σ : ℚ(ζ_ℓ) → ℂ` embedding), then applies T7's headline. The pin duplicates T7's `RealL`/glue here; the port imports instead (~97 lines saved). FLT `S_ModularCurve_cosetPoly_smul` + `…_hasSum_cosetPoly_coeff` + `…_mem_adjoin_jq_of_phiGenDescends` (~572 lines) |
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
`heckeU`/`heckeT` block is unused by the cone), and it imports T7's `RealL` API
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
| `PORTING-FFG.md` and any other plan at the top level | an **active plan** — the blueprint for work in progress |
| `topics/<effort>/TOPIC-*.md` | **work orders, then executed plans**: one per topic. New work orders open with the mandatory build-discipline block (playbook §3.11); finished ones keep the record of what was learned and what it cost |
| `logs/` | the **linear record** of what happened, in order — `card-torsion-port.md` for the first port, `ffg-port.md` for this one |
| `porting-playbook.md` | the **reusable method**, not tied to any one effort |
| `spec/` | the **deliverable measures**: the consumer and the statement checker |

An executed plan is not deleted: it is the record of a decision and its cost, and
`logs/` cross-references it. When an effort finishes, its plan is retired from the
top level into `topics/`, and the log gains the entry that summarises it.
`topics/functionFieldGeneration/` holds the four topics of the
`functionFieldGeneration` effort, and `topics/phiGenSplitting/` holds the nine
topics of its Φ_p splitting / R1 sub-effort, whose plan
[PORTING-PhiGen.md](topics/PORTING-PhiGen.md) is retired there; the R1 work orders
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
