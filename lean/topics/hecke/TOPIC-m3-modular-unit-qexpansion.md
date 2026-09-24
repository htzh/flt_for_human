# Topic m3 — the modular-unit `q`-expansion core (M7)

**Status: work order written, not started.** Third topic of
[SET-M1](SET-M1.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Three modules:

- `FLTForHuman/ModularCurve/Analytic/QParamUnique.lean` — the two
  `qParam`-expansion uniqueness lemmas.
- `FLTForHuman/ModularCurve/Analytic/ModularUnitQExpansion.lean` — the four
  `hasSum_*modularUnitSeries*` headlines, with the pin's four-way prelude written
  **once**.
- `FLTForHuman/ModularCurve/Analytic/Gamma0Cosets.lean` — the `Γ₀` coset
  permutation, the `SL₂` diagonal transport, and the `Δ`-ratio invariance.

**Why this topic.** These nine nodes are the analytic input the whole Fricke
cluster (SET-M2's M8) consumes:
`hasSum_smul_modularUnitSeries_inv_qParam` and friends feed
`isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant` and
`mem_modularFunctionField_of_hasSum_of_gamma0_invariant`. They are also the
effort's cleanest redundancy: FLT writes the same 165-line prelude in four files.

## 1. The nine targets

Statements are the `Theorems/` wrappers; quote them verbatim.

| target | raw | content |
|---|---|---|
| `ModularCurve.hasSum_modularUnitSeries_qParam` | 258 | 205 |
| `ModularCurve.hasSum_modularUnitSeries_inv_qParam` | 263 | 209 |
| `ModularCurve.hasSum_smul_modularUnitSeries_qParam` | 321 | 266 |
| `ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam` | 325 | 269 |
| `ModularCurve.qParam_coeff_unique` | 158 | 121 |
| `ModularCurve.laurent_qParam_coeff_unique` | 71 | 46 |
| `ModularCurve.exists_perm_gamma0_cosetReps` | 134 | 98 |
| `ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq` | 68 | 38 |
| `ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul` | 55 | 30 |

The four headline statements (verbatim; note the different periods `1` vs `N`):

```lean
theorem ModularCurve.hasSum_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ))

theorem ModularCurve.hasSum_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ)

theorem ModularCurve.hasSum_smul_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((((N : ℚ) ^ 12)⁻¹ • ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam N (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ) /
        ModularForm.discriminant (ModularGroup.S • τ))

theorem ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((((N : ℚ) ^ 12 • (ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) *
      Function.Periodic.qParam N (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularGroup.S • τ) /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ))
```

## 2. The dedup — the pin's four-way prelude

`S_ModularCurve_hasSum_{,smul_}modularUnitSeries{_inv,}_qParam.lean` share lines
28–192 **byte-identically** (diff between any pair: 69–108 changed lines, all
below line 192 or in the tail). The block is:

`ratNRH`, `theta` (+ `theta_coeff`, `theta_mul`), `gfun`,
`differentiableOn_gfun`, `gfun_ne_zero`, `discriminant_eq_qParam_mul_gfun`,
`hasSum_single_mul_coe_iff`, `hasSum_theta_deltaSeries`,
`qParam_heckeDiagMatrix_smul`, `hasSum_theta_deltaSeriesN`,
`theta_deltaSeriesN_ne_zero`, `theta_deltaSeries_ne_zero`, `phiFun`, `psiFun`,
`pow_mem_ball`, `differentiableOn_gfun_pow`, `differentiableOn_phiFun`,
`differentiableOn_psiFun`, `taylorCoeff`, `hasSum_taylorCoeff`, and the two
generic heads `hasSum_modularUnit` / `hasSum_modularUnitInv`.

**Write it once**, in `ModularUnitQExpansion.lean`. Keep `hasSum_modularUnit`
and `hasSum_modularUnitInv` public (they are the generic `N` statements the four
heads specialize); keep the rest `private`. Prove the four headline targets as
short derivations from the two generic heads. Record `diff | grep -c` before and
after.

**Port dependencies (already present, import them):**

| need | ported home |
|---|---|
| `ModularCurve.modularUnitSeries` (+ order/coefficient lemmas) | `Defs/ModularUnit.lean` (m2) |
| `ModularCurve.dedekindEtaUnit`, `deltaSeries` | `Defs/Jq.lean`, m2 |
| `ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` | `ModularForms/JqAnalyticModel.lean` |
| `ModularCurve.hasSum_qParam_mul_laurent` | `ModularForms/Hauptmodul.lean` |
| `ModularForm.discriminant`, `heckeDiagMatrix`, `ModularGroup.S/T`, `Function.Periodic.qParam` | mathlib + `ModularForms/Defs/HeckeOperator.lean` |

If the pin's prelude mentions `deltaSeries`/`theta` in a form the port's
`Defs/ModularUnit.lean` cannot supply, report the gap rather than re-deriving it.

## 3. The three coset/`SL₂` targets

- `ModularCurve.exists_perm_gamma0_cosetReps (ℓ) [Fact (Nat.Prime ℓ)]
  (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ∃ e : Equiv.Perm (Fin (ℓ + 1)), …`
  — pure finite group theory on `Gamma0 ℓ` and the `ℓ+1` coset representatives
  `1` and `S * T^b`. mathlib's `CongruenceSubgroup.Gamma0`, `Fin.cases`,
  `Equiv.Perm`; the pin's proof is a `ZMod ℓ` reindexing. Transcribe.
- `ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq (N) [NeZero N] (γ) (hγ : γ ∈
  Gamma0 N) : ∃ γ', (∀ τ, heckeDiagMatrix N • γ • τ = γ' • heckeDiagMatrix N • τ)
  ∧ ∀ τ, UpperHalfPlane.denom γ' … = UpperHalfPlane.denom γ …` — the diagonal
  transport. mathlib's `UpperHalfPlane.denom`, `MoebiusAction`.
- `ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul` — the
  `Γ₀(N)`-invariance of `Δ(τ)/Δ(heckeDiagMatrix N • τ)`, from the previous one
  and `ModularForm.discriminant`'s weight-12 transformation. mathlib's
  `ModularForm.discriminant` API.

## 4. The two uniqueness lemmas

- `ModularCurve.qParam_coeff_unique` (121 content): two `HasSum` expansions in
  `qParam h` with **`ℕ`-indexed** coefficients agree.
- `ModularCurve.laurent_qParam_coeff_unique` (46): the `ℤ`-indexed Laurent
  version, derived from the first.

**Route risk (the topic's one stall candidate).** The pin states
`qParam_coeff_unique` over a bare `F : UpperHalfPlane → ℂ`; the port's
`QExpansionPrinciple.lean` records that mathlib's replacement for the pin's
analogue blew up on the bare function type. Scout the pin's proof in
`Scratch.lean` first: if the `HasSum`-at-each-`τ` shape is what mathlib's
`qParam` API wants, transcribe; if not, restate over the natural type (e.g. a
`ModularForm`/`CuspForm`) **only if the wrapper's statement still matches** — a
statement change is not allowed here, so if the bare shape resists, report it.
`laurent_qParam_coeff_unique` imports the complex version and is short.

**Manager's API pre-check (2026-09-23).** All ten mathlib names the pin's
`coeff_unique` proof uses exist in v4.34 with compatible signatures:
`Periodic.norm_qParam`, `Periodic.im_invQParam_pos_of_norm_lt_one`,
`Periodic.cuspFunction_eq_of_nonzero`, `Periodic.qParam_right_inv`,
`Periodic.differentiable_qParam`, `qParam_tendsto_atImInfty`,
`UpperHalfPlane.mdifferentiable_iff`, `cuspFunction` (root namespace),
`HasFPowerSeriesAt.eq_formalMultilinearSeries`,
`FormalMultilinearSeries.le_radius_of_summable`. So the pin's `Realized` block
(`norm_qParam_lt_one_of_pos`, `hasSum_cuspFunction_punctured`,
`hasFPowerSeriesOnBall_update`, `discFun` + its lemmas, `mdifferentiable`,
`tendsto_atImInfty`, `isBoundedAtImInfty`, `periodic`, `coeff_unique`) should
transcribe; the only expected work is the `𝕢`-notation and `open`-scope setup.

## 5. Verification

- Append the nine wrappers to `SOURCES`; the three modules to `PORT_FILES`.
- `python3 spec/check_flt_statements.py`: 0 mismatched, 0 missing.
- `#print axioms` on all nine headlines.
- Consumer Zone B: the four `hasSum` heads instantiated at `N = 2`
  (`modularUnitSeries 2`), the `discriminant` identity at `N = 2`, and one
  `Γ₀`-coset permutation at `ℓ = 2`.
- `grep -c` the prelude's declaration names to show each occurs once in the port.

## 6. Budget

**3 goal rounds, checkpoint at 1 and 2.** Round 1: `QParamUnique` +
`Gamma0Cosets` (the two self-contained targets) and the prelude scout. Round 2:
`ModularUnitQExpansion` (the shared prelude + `hasSum_modularUnit` and
`hasSum_modularUnitInv`). Round 3: the four headline derivations + log/README/
consumer.

**Stop early on**: `qParam_coeff_unique`'s bare-`F` shape resisting mathlib
(report; do not weaken the statement); `discriminant_eq_qParam_mul_gfun` needing
an `UpperHalfPlane.qExpansion` API mathlib lacks; or the `Γ₀` coset proof
needing a level of `CongruenceSubgroup` the port does not import.

## 7. Reporting back

1. Module/line/decl table and checker before/after.
2. **The dedup, measured**: the shared prelude's line count, the four `diff` counts,
   and the port's single copy.
3. `qParam_coeff_unique`'s route: the final statement shape and whether mathlib's
   `qParam` API was enough.
4. Whether the four headline targets were derived from the two generic heads, or
   needed separate proofs; the shape of each derivation.
5. Anything the Fricke/inclusion topic (SET-M2's m4) must import from here, with
   the exact names.
