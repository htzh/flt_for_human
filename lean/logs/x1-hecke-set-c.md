# SET-X1-C — the Hecke/diamond statement nodes

Work order: SET-X1-C of
[TOPIC-x1-hecke-diamond-inputs.md](../topics/hecke/TOPIC-x1-hecke-diamond-inputs.md) §5.
Pin: `aa2d8b3` (mathlib `v4.34.0`). Statement modules only; the capstone
`X1/Inputs.lean` and `ModularCurve.heckeDiamondInputsAll` are the manager's review
instrument and were **not** written.

**Result.** 3 new modules (1,143 lines), 1 checker wiring, 1 consumer zone, 1
friction-list update. Checker `4431 → 4435 identical (150 promoted), 0 mismatched,
0 missing, 30 own` (delta **+4**, one per headline). Consumer
`spec/ModularCurveHeckeConsumer.lean` Zone X1-C `[x1-c]` error+warning count `0`;
delete-fail count `4`. Whole-tree `lake build` green (4960 jobs). Axioms on all
four headlines `[propext, Classical.choice, Quot.sound]`.

## 1. Cover scout: pre-scout vs post-scout, and the chosen route

Scout option (ii) (the tensor-product route) was probed directly in
`X1/BaseChangeCover.lean` under the ordinary edit loop; it closed, so the pin's
`S3d`/`S4H` fallback was **not** transcribed.

| | raw | content |
|---|---:|---:|
| pre-scout — pin `S_…exists_algEquiv_laurentBaseChange_cover.lean` | 423 | 281 |
| post-scout — `X1/BaseChangeCover.lean` (route (ii), chosen) | 186 | 135 |

**Chosen route: (ii), the tensor-product route.** The whole construction is
~90 content lines instead of ~240, and it uses the port's already-public
`baseChangeHom`/`baseChangeHom_injective` (`Defs/GeometricBaseChange.lean`), which
are available **without** `[Algebra.IsAlgebraic ℚ L]` (the pin's `geomAut`/
`baseChangeEquiv` are algebraic-only and cannot state the general theorem). The
route:

1. `β := (baseChangeHom L F₀).codRestrict (Algebra.adjoin L (Set.range φ₀)) hcod`
   is injective and surjective onto `Algebra.adjoin L (Set.range φ₀)` (the range
   of `baseChangeHom` is exactly that subalgebra), so `AlgEquiv.ofBijective β`
   gives `L ⊗[ℚ] F₀ ≃ₐ[L] Algebra.adjoin L (Set.range φ₀)` — **no basis and no
   `[Algebra.IsAlgebraic]`**.
2. `Algebra.TensorProduct.congr (AlgEquiv.refl L) σ` transports `σ`; conjugating
   by the equivalence gives `rho : Algebra.adjoin … ≃ₐ[L] Algebra.adjoin …`.
   `σ₀ : F₀ ≃+* F₀` is first upgraded to `F₀ ≃ₐ[ℚ] F₀` by `ratAlgEquiv`
   (`Subsingleton (ℚ →+* F₀)`); this is the step that makes the tensor-product
   `congr` applicable.
3. The scoped mathlib instance
   `IsFractionRing (Algebra.adjoin F S) (adjoin F S)`
   (`Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:58`) plus
   `IsFractionRing.algEquivOfAlgEquiv` extends `rho` to
   `laurentBaseChange L F₀`, and the generator property follows from
   `algEquivOfAlgEquiv_algebraMap` and `rho_apply_gen`.

The pin's `S4A.linearIndependent_coeffEmb` / `S4C` module-instance shim (the
`HahnSeries.instModule` vs `Algebra.toModule` conversion) is unnecessary here:
`ModularCurve.linearIndependent_coeffEmb` and `baseChangeHom` already live on the
default module structure.

## 2. Per-module line counts

| module | raw | content | pin source (raw / content) |
|---|---:|---:|---|
| `FLTForHuman/ModularCurve/X1/QExpandStretch.lean` | 218 | 176 | `S_ModularCurve_qExpand_image_intFormRatiosC_subset.lean` (198 / 145) |
| `FLTForHuman/ModularCurve/X1/DiamondAut.lean` | 739 | 580 | `S_…exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean` (92 / 65) + `S_…exists_isDiamondAut.lean` (675 / 525) |
| `FLTForHuman/ModularCurve/X1/BaseChangeCover.lean` | 186 | 135 | `S_…exists_algEquiv_laurentBaseChange_cover.lean` (423 / 281) |
| **new total** | **1,143** | **891** | 1,388 / 1,016 |

(content = raw minus `import`/`attribute`/`namespace`/`end`/`open`/`section`/
`variable`/`#`/comment/blank lines, the plan §1 recipe, so module doc bodies
count — that is why `QExpandStretch` reads slightly over its pin.)

Edits:

| file | +/− | content |
|---|---|---|
| `spec/check_flt_statements.py` | +14/−0 | four `SOURCES` and three `PORT_FILES` entries appended last |
| `spec/ModularCurveHeckeConsumer.lean` | +5 imports / +104 zone | Zone X1-C (`[x1-c]`) |

No `X1/Inputs.lean` was added; no frozen module was edited.

## 3. Checker

| run | identical | mismatched | missing | own |
|---|---:|---:|---:|---:|
| baseline (after SET-X1-B) | 4431 (150 promoted) | 0 | 0 | 30 |
| with SET-X1-C wired | **4435 (150 promoted)** | **0** | **0** | 30 |
| one-token mutation (`⊆ → ⊂` on the `QExpandStretch` headline) | 4434 | 1 | 0 | 30 |
| reverted | 4435 | 0 | 0 | 30 |

Delta **+4**, exactly the four public headlines. Every helper in the three
modules is `private`, so none enters the diffed surface. The mutation was
`qExpand_image_intFormRatiosC_subset`'s `⊆`; the checker reported exactly that
one mismatch and then reverted clean.

## 4. Consumer

Zone X1-C `[x1-c]` appended to `spec/ModularCurveHeckeConsumer.lean`:

* **Node 1** at `(K, Γ, Γ', ℓ) = (ℚ, ⊤, Γ₁(2), 2)`, with the `hΓ'` hypothesis
  discharged from the concrete matrix entries of `γ ∈ Γ₁(2)` (the stretched
  matrix `γ₁ = !![γ₀₀, 2γ₀₁; γ₁₀/2, γ₁₁]`, `2 ∣ γ₁₀`), and consumed at the
  concrete ratio `qExpand ℚ 2 1 ∈ intFormRatiosC ℚ Γ₁(2)`;
* **Node 2** at `M = 2` on the constant form `f = 1` with `p = 1` (a real
  integral `q`-expansion);
* **Node 3** at `(M, d) = (2, 1)`, the resulting `σ` applied to `1`;
* **Node 4** at `L = ℚ̄`, `F₀ = x1FunctionField 2`,
  `σ₀ = (diamondAut 2 1).toRingEquiv`, applied to the coefficient image of `1`;
* a final executed composition: `exists_isDiamondAut 2 1` produces `σ`, its
  `toRingEquiv` feeds `exists_algEquiv_laurentBaseChange_cover`, and the resulting
  `ℚ̄`-automorphism is applied to `1`.

`timeout 90 lake env lean spec/ModularCurveHeckeConsumer.lean 2>&1 | grep -c
'error\|warning'` → **0** (all zones; the pre-existing Zones A…X1-FF remain
green). Delete-fail (rename one headline call) → **4**. No `#check`/`sorry`/
unported hypothesis in the zone.

## 5. Build discipline and times

| command | result | wall | user | sys |
|---|---|---:|---:|---:|
| `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` | edit loop | — | — | — |
| `flock … timeout 90 lake build FLTForHuman.ModularCurve.X1.QExpandStretch` | ✔ 4112 jobs | 10.93s | 8.02s | 8.58s |
| `flock … timeout 90 lake build FLTForHuman.ModularCurve.X1.BaseChangeCover` | ✔ 2586 jobs | 8.87s | 12.03s | 3.46s |
| `flock … timeout 90 lake build FLTForHuman.ModularCurve.X1.DiamondAut` | ✔ 4109 jobs | 12.90s | 15.75s | 5.22s |
| `flock … timeout 300 lake build` (set boundary, whole tree) | ✔ 4960 jobs | 3.80s | 2.59s | 3.66s |

Per-module `lean`-reported times: `QExpandStretch` 7.3s, `BaseChangeCover` 7.9s,
`DiamondAut` 10s. No bound was hit; `maxHeartbeats`/`maxRecDepth` were never
raised; every command was bounded; every `lake build` was serialized with
`flock /tmp/flt-lake.lock`.

`#print axioms` (via `tmp/Scratch.lean`):

```
ModularCurve.qExpand_image_intFormRatiosC_subset            [propext, Classical.choice, Quot.sound]
ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 [propext, Classical.choice, Quot.sound]
ModularCurve.exists_isDiamondAut                            [propext, Classical.choice, Quot.sound]
ModularCurve.exists_algEquiv_laurentBaseChange_cover        [propext, Classical.choice, Quot.sound]
```

## 6. Per-declaration table

`pin` = `P2M/Sol/S_ModularCurve_qExpand_image_intFormRatiosC_subset.lean`;
`2a` = `S_…exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean`;
`2b` = `S_…exists_isDiamondAut.lean`;
`4` = `S_…exists_algEquiv_laurentBaseChange_cover.lean`. All rows are
`ModularCurve.*`; every helper is `private`, only the four headlines are public.

| declaration | module | vis | pin |
|---|---|---|---|
| `mapGL_coe_eq` | `QExpandStretch` | private | pin:22 |
| `heckeDiagMatrix_mul_eq` | `QExpandStretch` | private | pin:26 |
| `isCusp_heckeDiagMatrix_smul` | `QExpandStretch` | private | pin:45 |
| `stretchSlash` | `QExpandStretch` | private | pin:62 |
| `stretchSlash_apply` | `QExpandStretch` | private | pin:85 |
| `stretch` | `QExpandStretch` | private | pin:90 |
| `stretch_apply` | `QExpandStretch` | private | pin:94 |
| `coe_stretch` | `QExpandStretch` | private | pin:100 |
| `periodic_comp_ofComplex` | `QExpandStretch` | private | pin:104 |
| `qCoeff_stretch` | `QExpandStretch` | private | pin:116 |
| `expandPS` | `QExpandStretch` | private | pin:124 |
| `coeff_expandPS` | `QExpandStretch` | private | pin:127 |
| `isIntegralQExp_stretch` | `QExpandStretch` | private | pin:131 |
| `intSeriesC_expandPS` | `QExpandStretch` | private | pin:144 |
| **`qExpand_image_intFormRatiosC_subset`** | `QExpandStretch` | **public** | pin:161 (`solution`) |
| `rat_of_isIntegralQExp` | `DiamondAut` | private | 2a:65 |
| `isBoundedAt_slash` | `DiamondAut` | private | 2b:116 |
| `diamondSlash` | `DiamondAut` | private | 2a:37 / 2b:124 |
| `coe_diamondSlash` | `DiamondAut` | private | 2b:144 |
| `coe_diamondSlash_SL` | `DiamondAut` | private | 2b:148 |
| `slash_inv_slash` | `DiamondAut` | private | 2b:153 |
| `slash_slash_inv` | `DiamondAut` | private | 2b:156 |
| `diamondSlash_ne_zero` | `DiamondAut` | private | 2b:159 |
| `mul_inv_mem_Gamma1` | `DiamondAut` | private | 2b:169 |
| `slash_eq_of_apply_eq` | `DiamondAut` | private | 2b:200 |
| **`exists_isIntegralQExp_smul_slash_of_mem_Gamma0`** | `DiamondAut` | **public** | 2a:72 (`solution`) |
| `qC` | `DiamondAut` | private | 2b:23 |
| `one_mem_strictPeriods` | `DiamondAut` | private | 2b:29 |
| `qC_mul` | `DiamondAut` | private | 2b:33 |
| `qC_coe_mul` | `DiamondAut` | private | 2b:38 |
| `qC_add` | `DiamondAut` | private | 2b:42 |
| `qC_neg` | `DiamondAut` | private | 2b:48 |
| `qC_smul` | `DiamondAut` | private | 2b:53 |
| `qC_zero` | `DiamondAut` | private | 2b:58 |
| `qC_one` | `DiamondAut` | private | 2b:61 |
| `qC_coe_zero` | `DiamondAut` | private | 2b:64 |
| `qC_coe_one` | `DiamondAut` | private | 2b:67 |
| `hasSum_qC` | `DiamondAut` | private | 2b:72 |
| `coe_eq_of_qC_eq` | `DiamondAut` | private | 2b:77 |
| `qC_eq_zero_iff` | `DiamondAut` | private | 2b:87 |
| `IsRatio` | `DiamondAut` | private | 2b:218 |
| `isRatio_of_eq` | `DiamondAut` | private | 2b:224 |
| `qC_coe_one_ne_zero` | `DiamondAut` | private | 2b:228 |
| `isRatio_zero` | `DiamondAut` | private | 2b:231 |
| `isRatio_one` | `DiamondAut` | private | 2b:234 |
| `IsRatio.add` | `DiamondAut` | private | 2b:237 |
| `IsRatio.neg` | `DiamondAut` | private | 2b:246 |
| `IsRatio.mul` | `DiamondAut` | private | 2b:250 |
| `IsRatio.inv` | `DiamondAut` | private | 2b:258 |
| `isRatio_C` | `DiamondAut` | private | 2b:264 |
| `ratioField` | `DiamondAut` | private | 2b:270 |
| `mem_ratioField` | `DiamondAut` | private | 2b:279 |
| `qC_slash_ne_zero` | `DiamondAut` | private | 2b:281 |
| `cross` | `DiamondAut` | private | 2b:286 |
| `pull` | `DiamondAut` | private | 2b:310 |
| `pull_eq` | `DiamondAut` | private | 2b:314 |
| `pull_one` | `DiamondAut` | private | 2b:320 |
| `pull_zero` | `DiamondAut` | private | 2b:325 |
| `pull_mul` | `DiamondAut` | private | 2b:330 |
| `pull_add` | `DiamondAut` | private | 2b:341 |
| `pullHom` | `DiamondAut` | private | 2b:364 |
| `pullHom_apply` | `DiamondAut` | private | 2b:371 |
| `pull_mem` | `DiamondAut` | private | 2b:373 |
| `pull_pull_inv` | `DiamondAut` | private | 2b:378 |
| `toC` | `DiamondAut` | private | 2b:395 |
| `toC_injective` | `DiamondAut` | private | 2b:398 |
| `toC_intSeriesC` | `DiamondAut` | private | 2b:409 |
| `toC_ratio` | `DiamondAut` | private | 2b:418 |
| `qC_ne_zero_of_intSeriesC_ne_zero` | `DiamondAut` | private | 2b:424 |
| `toC_algebraMap` | `DiamondAut` | private | 2b:430 |
| `toC_comp_algebraMap` | `DiamondAut` | private | 2b:436 |
| `toC_mem_ratioField` | `DiamondAut` | private | 2b:440 |
| `iota` | `DiamondAut` | private | 2b:453 |
| `coe_iota` | `DiamondAut` | private | 2b:457 |
| `jC` | `DiamondAut` | private | 2b:460 |
| `jC_apply` | `DiamondAut` | private | 2b:464 |
| `jC_injective` | `DiamondAut` | private | 2b:467 |
| `psi` | `DiamondAut` | private | 2b:472 |
| `psi_apply` | `DiamondAut` | private | 2b:475 |
| `exists_psi_generator_eq` | `DiamondAut` | private | 2b:477 |
| `exists_psi_eq` | `DiamondAut` | private | 2b:526 |
| `psi_mem_range` | `DiamondAut` | private | 2b:560 |
| `eC` | `DiamondAut` | private | 2b:564 |
| `coe_eC` | `DiamondAut` | private | 2b:572 |
| `jC_eC_symm` | `DiamondAut` | private | 2b:576 |
| `sigma0` | `DiamondAut` | private | 2b:580 |
| `jC_sigma0` | `DiamondAut` | private | 2b:583 |
| `sigma0_injective` | `DiamondAut` | private | 2b:588 |
| `sigma0_surjective` | `DiamondAut` | private | 2b:593 |
| `sigma` | `DiamondAut` | private | 2b:605 |
| `sigma_apply` | `DiamondAut` | private | 2b:612 |
| `toC_sigma_generator` | `DiamondAut` | private | 2b:614 |
| `exists_gamma0_apply_eq` | `DiamondAut` | private | 2b:632 |
| `isDiamondAut_sigma` | `DiamondAut` | private | 2b:644 |
| **`exists_isDiamondAut`** | `DiamondAut` | **public** | 2b:671 (`solution`) |
| `φ₀` | `BaseChangeCover` | private | 4:340 (`φ₀`) |
| `φ₀_apply` | `BaseChangeCover` | private | 4:357 |
| `range_φ₀` | `BaseChangeCover` | private | 4:344 |
| `laurentBaseChange_eq_adjoin` | `BaseChangeCover` | private | 4:352 |
| `Rg` | `BaseChangeCover` | private | 4:147 (`Rg`) |
| `baseChangeHom_mem_Rg` | `BaseChangeCover` | private | **ours** (route (ii)) |
| `beta` | `BaseChangeCover` | private | **ours** |
| `beta_injective` | `BaseChangeCover` | private | **ours** |
| `range_baseChangeHom` | `BaseChangeCover` | private | **ours** |
| `beta_surjective` | `BaseChangeCover` | private | **ours** |
| `e` | `BaseChangeCover` | private | **ours** |
| `e_one_tmul` | `BaseChangeCover` | private | **ours** |
| `rho` | `BaseChangeCover` | private | 4:263/295 (`ρₗ`/`ρ`) |
| `rho_apply_gen` | `BaseChangeCover` | private | 4:298 (`ρ_mk`) |
| `exists_cover_adjoin` | `BaseChangeCover` | private | 4:325 (`exists_cover`) |
| `ratAlgEquiv` | `BaseChangeCover` | private | **ours** (`≃+*` → `≃ₐ[ℚ]`) |
| **`exists_algEquiv_laurentBaseChange_cover`** | `BaseChangeCover` | **public** | 4:411 (`solution`) |

## 7. Friction log

Appended as hit (the task's "friction log appended as hit"), for the refactor
round:

1. **Third `private diamondSlash` copy.** The port now has `diamondSlash`/
   `coe_diamondSlash` at `ModularForms/WeightOne/Gamma0Integral.lean:1425,1449`
   *and* in `X1/DiamondAut.lean` (one copy serving both headlines). The pin has
   three copies (its two `S_` files and `Gamma0Integral`). Dedup was deferred
   rather than promoting: the public `ModularForm.Level.slashOfMemGamma0`
   (`Level/Diamond.lean:209`) is on the `CuspForm` carrier and the two private
   copies are direct `ModularForm` structure constructions, so a clean promotion
   would have to add a new public `ModularForm`-carrier name (against the
   "no public name without a pin wrapper" rule) and rewire `Gamma0Integral`'s
   uses. **Refactor round: promote one `diamondSlash`/`coe_diamondSlash` pair to
   `ModularForm.Level` and delete the private copies.**
2. **`set_option backward.isDefEq.respectTransparency.types false` needed twice.**
   `mul_inv_mem_Gamma1` and `exists_gamma0_apply_eq` both fail without it: the
   `SpecialLinearGroup`-vs-`{A // A.det = 1}` transparency mismatch is the same
   one the port already hit at `Gamma0Integral.lean:1465` and
   `Level/Diamond.lean:230`. Not a heartbeat bump; recorded because the work
   order forbids raising `maxHeartbeats`.
3. **v4.34 deprecations hit while transcribing.** `ModularForm.IsGLPos.coe_smul`
   and `ModularForm.IsGLPos.smul_apply` → `FunLike.coe_smul` / `smul_apply`;
   `ModularForm.coe_zero`/`coe_add`/`coe_neg` → `FunLike.coe_zero`/`_add`/`_neg`;
   `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`.
4. **`hasSum_qExpansion` name collision.** mathlib v4.34 added
   `ModularForm.hasSum_qExpansion`, which collides with the pin's (unqualified)
   `UpperHalfPlane.hasSum_qExpansion` under the two `open`s with different
   binders. Qualified `UpperHalfPlane.hasSum_qExpansion` explicitly.
5. **`subset_adjoin` argument shapes.** `IntermediateField.subset_adjoin` takes
   `F S hx` explicitly; `Algebra.subset_adjoin` takes only `hx`. The pin's
   `S3d` uses both; the port's route (ii) uses each at the right arity.
6. **`IsFractionRing.algEquivOfAlgEquiv` implicit fraction-ring variables.** They
   must be named `(R := L) (A := Rg L F₀) (B := Rg L F₀) (K := …) (L := …)`;
   with `K`/`L` left implicit the elaborator defaults the fraction ring to
   `LaurentSeries L`, fails `IsFractionRing Rg (LaurentSeries L)`, and then hits
   the `whnf` heartbeat cap. The explicit form closes instantly.
7. **`Subsingleton.elim` for the `≃+*` → `≃ₐ[ℚ]` upgrade.** The bare
   `Subsingleton.elim (α := ℚ →+* F₀) _ _` still left metavariables; naming the
   two maps (`(σ₀ : ↥F₀ →+* ↥F₀).comp (algebraMap ℚ ↥F₀)` and
   `algebraMap ℚ ↥F₀`) is what closes it.
8. **Dedups applied (no friction).** `T_mem_Gamma1` reused from
   `X1DiamondRational.T_mem_Gamma1`; `ModularForm.Level.conj_mem_Gamma1`
   imported; the public `X1/Integral.lean` `isIntegralQExp_iff`/`.coeff` used and
   not inlined; the pin's `S4A`/`S4C` linear-independence shim dispensed with
   entirely.

## 8. What the manager needs for `X1/Inputs.lean`

Importable at the wrapper binders (checker-verified, standard axioms):

* `ModularCurve.qExpand_image_intFormRatiosC_subset` — `X1/QExpandStretch.lean`.
* `ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0` and
  `ModularCurve.exists_isDiamondAut` — `X1/DiamondAut.lean`.
* `ModularCurve.exists_algEquiv_laurentBaseChange_cover` —
  `X1/BaseChangeCover.lean`.

For the capstone `ModularCurve.heckeDiamondInputsAll` (`X1/Inputs.lean`, manager's
file):

* the `diamond_inputs` field: `exists_isDiamondAut M d hd` gives `∃ σ,
  IsDiamondAut M d σ`; `isDiamondAut_diamondAut` (`X1/Diamond.lean`) turns it into
  `IsDiamondAut M d (diamondAut M d)`, and the cover is instantiated at
  `L = AlgebraicClosure ℚ`, `F₀ = x1FunctionField M`,
  `σ₀ = (diamondAut M d).toRingEquiv : ↥(x1FunctionField M) ≃+* ↥(x1FunctionField M)`
  (`σ₀` is a bare `≃+*`; the headline upgrades it internally), then paired with
  `IsBaseChangeAutOf`/`baseChangeAut` from `X1/Diamond.lean`;
* the `heckeInputsOneAlong` field: unchanged from SET-X1-A/B — the
  `heckeBetaOneDefined`/`alphaIntegral`/`betaIntegral`/`fundamentalIdentityAlong`/
  `finiteAlong_alpha`/`normFormulaAlong` supply already importable from
  `X1/HeckeOperator`, `X1/Diamond`, `X1/FunctionField`,
  `X1/FunctionFieldBaseChange` and the two `AlgebraicCurve` along-lemmas.
* `exists_isDiamondAut` is the **upper-left** convention (`γ 0 0 ≡ d`); the ported
  `ModularForm.Level.IsDiamondLift` is the lower-right inverse convention and was
  deliberately not used.
* Every `X1`/`X1HeckeOperator`/`X1HeckeModule`/`X1Diamond` declaration, the
  `X1/A…B` modules and the SET-X1-A `AlgebraicCurve` edits are frozen and were
  not touched.
