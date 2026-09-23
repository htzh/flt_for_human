# Survey: where FLT defines the modular-form Hecke operators, and what it proves

Research survey to prepare the extension of
[`FLTForHuman/ModularForms/Defs/HeckeOperator.lean`](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean)
beyond the two matrices, and to orient a future `base/` note. It answers one
question with a map and a count: **where does FLT define the Hecke
*operators* (as opposed to the Hecke *matrices*), and what does it prove about
them?**

Everything is read from the local clone `~/proj/fermats-last-theorem` pinned at
`aa2d8b3`; all citations below are public URLs at that sha. Scope, decided with
the requester:

- **In scope** — the slash-level operators `heckeU`/`heckeT` on
  $`\mathbb{H} \to \mathbb{C}`$, the coefficient maps `coeffHeckeU`/`coeffHeckeT`,
  the bundled linear maps `heckeTLin`/`heckeULin`, the Hecke algebra
  `heckeAlgebra`, the eigenform interface, the `GammaH`/`Gamma1` (Nebentypus and
  diamond) variants, and the formal $`q`$-expansion operators on
  `LaurentSeries`/`PowerSeries`.
- **Out of scope, named in §12** — the Hecke *correspondences* on $`J_0(N)`$
  ([math/009](../math/009-hecke-jacobian-commute.md)), the group-cohomology
  Hecke operator (`Def_Gamma0HeckeOperatorHom.lean`, `CohCarrier.heckeT`), and
  the Galois/adelic/quaternion Hecke-algebra machinery.

Conventions are those of [../AGENTS.md](../AGENTS.md).

## 0. The answer in one paragraph

FLT defines the operator in exactly one place —
[`Definitions/Def_ModularForm_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean)
— as the slash average
$`U_p f = \sum_{j \lt p} f \mid_k [[1,j],[0,p]]`$ and
$`T_p f = U_p f + f \mid_k \mathrm{diag}(p,1)`$; every other module either
*bundles* that operator into a linear map on a space of forms, or *uses* it.
The operator block of that file is lines 72–200 (**34 declarations**: the two
`σ` lemmas, the two `slash_*_apply` normalisations, `heckeU`/`heckeT`, the three
definitional rewrites, the two `_zero_left` and the two `@[simp]` zeros, the two
`_apply` displays, `add`/`smul`/`neg`/`sub` in both, and `coeffHeckeT`/
`coeffHeckeU` with nine coefficient lemmas). FLT then proves about it:

1. **Slash-invariance exactly at the levels where it should hold** (§4) — `U_p`
   on $`\Gamma_0(N)`$ for $`p \mid N`$, on $`\Gamma_0(N/p)`$ for $`p^2 \mid N`$,
   on `GammaH`; `T_p` on $`\Gamma_0(N)`$ for $`p`$ prime, $`p \nmid N`$; and the
   diamond-twisted combinations on `Gamma1`/`GammaH`.
2. **Preservation of regularity and cuspidality** (§5): `mdifferentiable`,
   `periodic`, `IsBoundedAtImInfty`, `IsZeroAt` at the cusps.
3. **The coefficient action** (§6):
   $`U_p : a_n \mapsto a_{np}`$, $`T_p : a_n \mapsto a_{np} + p^{k-1}[p \mid n]\,a_{n/p}`$,
   with `qCoeff`/`qExpansion` computed by the corresponding `PowerSeries`
   operator.
4. **Commutation for coprime indices** (§7) — at the level of functions
   (`ModularFormClass`), of bundled maps (`CuspForm`/`ModularForm`), and of
   formal series. The composite product formula
   $`T_m T_n = T_{mn}`$ for $`(m,n)=1`$ is **not** stated; only commutation is,
   and the multiplication law lives inside `IsNormalizedEigenform`'s coefficient
   clauses.
5. **The eigenform dictionary** (§8): three equivalent characterisations of
   `IsNormalizedEigenform` (operator form, bundled form, coefficient form).
6. **The Hecke algebra** (§9): `heckeAlgebra = Algebra.adjoin ℤ heckeGenerators`
   is commutative, finite and free over $`\mathbb{Z}`$, contains each
   $`T_\ell`$/$`U_q`$, acts on the integral lattice, and spans an eigenbasis.

**Counts** (`grep` over the `aa2d8b3` tree, §0.1): the operator names occur in
**272 `Theorems/` wrapper files** and **508 `P2M/Sol/S_*` solution files**;
**45** of the 272 wrappers are the `ModularForm`/`ModularFormClass` operator API
proper and **64** are the `CuspForm` API; the remaining 163 are downstream
consumers (76 group-cohomology `CohCarrier.heckeT`, 31 Taylor–Wiles/Galois-rep,
and so on — §12).

### 0.1 How the counts were taken

```bash
cd ~/proj/fermats-last-theorem
grep -rlE '\b(heckeU|heckeT|heckeULin|heckeTLin|coeffHeckeU|coeffHeckeT)\b' Theorems/ | wc -l   # 272
```
The category split is a filename-prefix partition of those 272 files; it is a
*usage* count, not a count of declarations *about* the operators — the
declaration counts per definition module in §1 are the more honest measure.

## 1. The definition sites

Ten modules define a Hecke operator in the in-scope faces; three of them are the
backbone.

| module (pinned `aa2d8b3`) | role | key declarations | decls |
|---|---|---|---|
| [`Def_ModularForm_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean) | the operator itself | `heckeMatrix`, `heckeDiagMatrix`, `heckeU`, `heckeT`, `coeffHeckeT`, `coeffHeckeU` | 41 |
| [`Def_ModularForm_HeckeOperatorForms.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean) | bundles into `→ₗ[ℂ]` on `ModularForm`/`CuspForm` over `Gamma0 N` | `ModularForm.heckeTLin` (L20), `ModularForm.heckeULin` (L34), `CuspForm.heckeTLin` (L69), `CuspForm.heckeULin` (L83) | 8 |
| [`Def_CuspForm_HeckeAlgebra.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean) | generators, algebra, commutativity | `heckeGenerators` (L14), `heckeAlgebra` (L18), `heckeAlgebra.instIsMulCommutative` (L59), `heckeAlgebra.T` (L77), `.U` (L80) | 14 |
| [`Def_CuspForm_HeckeULower.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeULower.lean) | $`U_p`$ *lowering* $`S_k(\Gamma_0(N)) \to S_k(\Gamma_0(N/p))`$ | `heckeULowerLin` (L15) | 2 |
| [`Def_CuspForm_HeckeOperatorFormsGammaH.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean) | Nebentypus/`GammaH` diamond + $`T`$/$`U`$ | `StableD` (L72), `StableU` (L77), `StableT` (L85), `diamondLinH` (L132), `heckeULinH` (L171), `heckeTLinH` (L224) | 25 |
| [`Def_CuspForm_Gamma1HeckeOperators.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean) | `Gamma1`, Hecke representatives, diamond | `heckeMatrixQ` (L23), `heckeDiagMatrixQ` (L27), `isZeroAt_heckeU` (L68), `heckeU_eq_sum_zmod` (L175), `heckeRep` (L186), `heckeRep_mul` (L281), `slashOfMemGamma0` (L535), `diamondLinOne` (L592), `heckeTOne` (L634), `heckeTLinOne` (L652) | 56 |
| [`Def_Gamma0HeckeOperatorHom.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Gamma0HeckeOperatorHom.lean) | group-cohomology transfer $`H^1(\Gamma_0(N))`$ (**boundary**, §12) | `heckeConjMat`, `heckeUpper`, `heckeConj`, `coresHom`, `heckeOperatorHom` (L285) | 36 |
| [`Def_LaurentSeries_HeckeU.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LaurentSeries_HeckeU.lean) | formal `U` on `LaurentSeries` | `heckeU` (L22), `coeff_heckeU` (L33), `heckeU_ofPowerSeries` (L37) | 4 |
| [`Def_LaurentSeries_HeckeV.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LaurentSeries_HeckeV.lean) | formal `V` (`q ↦ q^ℓ`) and `T` | `heckeV` (L23), `coeff_heckeV` (L35), `heckeT` (L39), `coeff_heckeT` (L43) | 5 |
| [`Def_PowerSeries_FormalHeckeOperators.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PowerSeries_FormalHeckeOperators.lean) | formal `U`/`V`/`T` on `R⟦X⟧` | `heckeU` (L11), `heckeV` (L20), `heckeU_heckeV` (L29), `heckeT` (L33), `coeff_heckeT` (L36) | 5 |
| [`Def_CuspForm_HeckeEvalForms.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeEvalForms.lean) | the abstract algebra evaluating onto the concrete one | `heckeFormsGen` (L12), `heckeEvalForms` (L26) | 8 |

The `ModularCurve`-side modules `Def_ModularCurve_HeckeOperator*.lean`,
`Def_ModularCurve_HeckeModule.lean`, `Def_ModularCurve_HeckeAlgebraHom.lean`
belong to [math/009](../math/009-hecke-jacobian-commute.md)'s correspondence
face and are not in this survey.

## 2. The core block: the operator is a `Finset.sum` of slashes

The matrices are the port's current content; lines 18–70 of the FLT file. The
operator proper begins at line 72. The two normalisations are

```lean
-- Def_ModularForm_HeckeOperator.lean, lines 78–91
theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ)
theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ)
```

and the operators are literally a range sum plus the diagonal term:

```lean
-- lines 93–97
def heckeU (k : ℤ) (p : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j
def heckeT (k : ℤ) (p : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p
```

The block also carries, **proved in the definition file itself** (so a port gets
them for free once it ports the block):

- `σ_heckeMatrix`, `σ_heckeDiagMatrix` (the determinant is positive, so the
  `σ`-twist is the identity);
- `heckeU_def`, `heckeT_eq_heckeU_add`, `heckeT_def` (all `rfl`);
- `heckeU_zero_left : heckeU k 0 f = 0` and
  `heckeT_zero_left : heckeT k 0 f = f` (the junk `p = 0` branch of
  `heckeMatrix` makes $`T_0`$ the identity);
- `heckeU_apply` / `heckeT_apply`, the unfolded displays
  $`U_p f(\tau) = p^{-1}\sum_j f([[1,j],[0,p]]\,\tau)`$ and
  $`T_p f(\tau) = U_p f(\tau) + p^{k-1} f(p\tau)`$;
- the `@[simp]` zero lemmas `heckeU_zero`, `heckeT_zero` and the linearity
  algebra `heckeU_add`/`heckeT_add` (L129/L133), `_smul` (L138/L143),
  `_neg` (L148/L151), `_sub` (L154/L158).

The port header's note that the doc-site toolchain disables
`ModularForm.heckeU_zero` with `attribute [-simp]` is about these `@[simp]`
attributes being *too eager* downstream; the declarations themselves are the
algebra that makes `heckeU`/`heckeT` linear.

The coefficient maps close the file (lines 162–200):

```lean
-- lines 162–166
def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0
def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)
```

with `coeffHeckeT_apply`/`coeffHeckeU_apply` (`rfl`), the `_of_dvd`/
`_of_not_dvd` split, `coeffHeckeT_eq_coeffHeckeU_add`, and
`coeffHeckeT_add`/`_smul`, `coeffHeckeU_add`/`_smul`.

## 3. Bundling: `heckeTLin` / `heckeULin`, and the level split

`Def_ModularForm_HeckeOperatorForms.lean` is the only place the operator becomes
a bundled linear endomorphism of a space of forms. The split is in the
hypotheses, and it is the mathematical $`p \mid N`$ / $`p \nmid N`$ dichotomy:

```lean
-- Def_ModularForm_HeckeOperatorForms.lean, lines 20 and 34
def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k
def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k
```

and the same two names inside `namespace CuspForm` (L69, L83). The
`toFun` fields are built from four pieces, which is exactly the dependency
footprint a port must satisfy first:

| field | source theorem |
|---|---|
| `slash_action_eq'` | `heckeT_slash_eq_self_of_mem_Gamma0` / `heckeU_slash_eq_self_of_mem_Gamma0` |
| `holo'` | `mdifferentiable_heckeT` / `mdifferentiable_heckeU` |
| `bdd_at_cusps'` | `ModularFormClass.isBoundedAt_heckeT` / `…heckeU` |
| `zero_at_cusps'` | `CuspFormClass.isZeroAt_heckeT` / `…heckeU` |
| `map_add'`, `map_smul'` | `heckeT_add`/`heckeT_smul`, `heckeU_add`/`heckeU_smul` (from §2) |

The file also proves the computation rules `coe_heckeTLin_apply`,
`coe_heckeULin_apply`, `heckeTLin_apply_apply`, `heckeULin_apply_apply` (all
`rfl`) for both `ModularForm` and `CuspForm`.

`Def_CuspForm_HeckeULower.lean` is the lowering face: `heckeULowerLin k hp2N`
maps $`S_k(\Gamma_0(N)) \to S_k(\Gamma_0(N/p))`$ when $`p^2 \mid N`$ (L15),
using `heckeU_slash_eq_self_of_mem_Gamma0_div`.

## 4. What is proved I: slash-invariance, i.e. where the operator lands

This is the largest thematic block, and the one that fixes the *correctness* of
the level split. All statements are on functions $`\mathbb{H} \to \mathbb{C}`$
(not bundled forms), with the invariance hypothesis on $`f`$ explicit.

| statement (file, theorem line) | content |
|---|---|
| [`heckeU_slash_eq_self_of_mem_Gamma0`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean#L6) | $`p \mid N`$, $`f`$ invariant under $`\Gamma_0(N)`$ $`\Rightarrow`$ $`U_p f`$ too |
| [`heckeU_slash_eq_self_of_mem_Gamma0_div`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean#L6) | $`p^2 \mid N`$, $`f`$ invariant under $`\Gamma_0(N)`$ $`\Rightarrow`$ $`U_p f`$ is invariant under $`\Gamma_0(N/p)`$ (the lowering step) |
| [`heckeU_slash_eq_self_of_mem_GammaH`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L10) | `GammaH` version for $`q \mid M`$ |
| [`heckeT_slash_eq_self_of_mem_Gamma0`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean#L6) | $`p`$ prime, $`p \nmid N`$: $`T_p`$ preserves $`\Gamma_0(N)`$-invariance |
| [`heckeU_add_slash_slash_eq_self_of_mem_GammaH`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH.lean#L10) | the `GammaH` $`T`$-operator written as $`U_\ell + (\text{slash by } \rho)\,\mathrm{diag}(\ell)`$ |
| [`heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean#L9) | same shape on `Gamma1` |
| [`heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0.lean#L11) | Nebentypus twist $`\varepsilon(p)`$ on the diagonal term |

The Atkin–Lehner combinations form a sub-theme (the `alSlash` operator is the
$`W_q`$ slash on a `ModularForm.AtkinLehnerDatum`):

- `ModularForm.add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0` (L7),
  `alSlash_add_heckeU_slash_eq_self_of_mem_GammaH` (L10) — the $`W_q`$-twisted
  $`U`$ is invariant;
- `alSlash_heckeT_comm` (L7) — $`W_q`$ commutes with $`T_\ell`$ for
  $`\ell \nmid M`$;
- `alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix` (L11) — the
  `diamondLinH` / `heckeDiagMatrix` description of `alSlash`;
- `heckeU_add_slash_fricke_eq_zero` (L8) and
  `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke` (L8) — the
  $`U_p`$-plus-Fricke relation that produces level-one forms;
- `heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd` (L9),
  `heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div` (L10),
  `heckeT_trace_alSlash_of_eigen` (L7),
  `alSlash_add_heckeU_alSlash_alSlash` (L7).

The last few are the ones the *level-lowering* route consumes; they are the
operator-level content behind [math/008](../math/008-ribet-level-lowering.md).

## 5. What is proved II: analytic regularity and cuspidality

These are what the `→ₗ[ℂ]` bundling needs (§3), and they are stated for the
slash average directly. Note that they carry **no level hypothesis**: the
operator preserves `MDifferentiable`, periodicity, boundedness at $`\infty`$
and vanishing at cusps for *any* $`p`$.

| statement | content |
|---|---|
| [`ModularForm.mdifferentiable_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean#L7) / [`_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean#L7) | holomorphy is preserved |
| [`ModularForm.mdifferentiable_slash_heckeDiagMatrix`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean#L8) | the diagonal term alone |
| [`ModularForm.periodic_heckeU_comp_ofComplex`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_periodic_heckeU_comp_ofComplex.lean#L7) / [`_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_periodic_heckeT_comp_ofComplex.lean#L7) | $`1`$-periodicity is preserved |
| [`ModularForm.isBoundedAtImInfty_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeU.lean#L7) / [`_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeT.lean#L7) | bounded at the cusp |
| [`ModularFormClass.isBoundedAt_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_isBoundedAt_heckeU.lean#L6) / [`_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_isBoundedAt_heckeT.lean#L6) | `OnePoint.IsBoundedAt` at every cusp of $`\Gamma`$ |
| [`CuspFormClass.isZeroAt_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean#L6) / [`_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean#L6) | vanishing at cusps is preserved |
| [`ModularForm.isZeroAt_add_heckeU_alSlash`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_isZeroAt_add_heckeU_alSlash.lean#L7), [`mdifferentiable_add_heckeU_alSlash`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_mdifferentiable_add_heckeU_alSlash.lean#L7) | the level-lowering combination $`f + U_q(W_q f)`$ |

## 6. What is proved III: the coefficient action

The function-level operators and the coefficient maps are proved to agree. This
is where the classical $`q`$-expansion formulas live, and where the arithmetic
content of $`T_p`$/$`U_p`$ sits.

At the level of `qCoeff` (no modularity needed, only periodicity/holomorphy/boundedness):

- [`UpperHalfPlane.qCoeff_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean#L7):
  `qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n`;
- [`UpperHalfPlane.qCoeff_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_UpperHalfPlane_qCoeff_heckeT.lean#L7);
- [`UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean#L6):
  the diagonal translate alone is the dilation filter
  $`n \mapsto [d \mid n]\,a_{n/d}`$.

For a `ModularFormClass` with $`1 \in \Gamma`$ the same in `ModularFormClass`
form: `qCoeff_heckeU` / `qCoeff_heckeT` / `qCoeff_comp_heckeDiagMatrix_smul`
(same-named files under `Thm_ModularFormClass_*`), and the full series form

- [`ModularFormClass.qExpansion_heckeU_eq_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean#L8):
  `qExpansion 1 (heckeU k p f) = PowerSeries.heckeU p (qExpansion 1 f)`;
- [`…_heckeT_eq_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT.lean#L8):
  `qExpansion 1 (heckeT k p f) = PowerSeries.heckeT p k (qExpansion 1 f)`;
- [`CuspForm.qExpansion_heckeTLin`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_qExpansion_heckeTLin.lean#L9)
  for the bundled map;
- [`ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean#L9):
  $`\tau \mapsto N\tau`$ gives the level-one `qExpand ℂ N`.

The coefficient-level algebra is:

| statement | content |
|---|---|
| [`coeffHeckeT_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHeckeT_comm.lean#L6) | $`T_p T_q = T_q T_p`$ on coefficient sequences, $`(p,q)=1`$ |
| [`coeffHeckeU_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHeckeU_comm.lean#L6) | $`U_p U_q = U_q U_p`$ (no coprimality needed) |
| [`coeffHeckeT_coeffHeckeU_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean#L6) | $`T_p U_q = U_q T_p`$, $`(p,q)=1`$ |
| [`coeffHeckeT_int`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHeckeT_int.lean#L5) / [`coeffHeckeU_int`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHeckeU_int.lean#L5) | integral coefficients stay integral for $`k \ge 1`$ (resp. always) |
| [`coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean#L7) | a normalised eigenform has $`c_p = a_p`$ |
| [`eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean#L6) | $`a_1 = 0`$ + eigen $`\Rightarrow`$ $`a_n = 0`$ for $`n \ne 0`$ |
| [`exists_cuspForm_coeffHeckeT_eq_of_modEq_one`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one.lean#L6) | for $`\ell \equiv 1 \pmod{N'}`$, the $`T_\ell`$-transformed coefficients differ from $`(1+\ell^{k-1})a_n`$ by a cusp form's coefficients |

There is one further coefficient theorem at the `PowerSeries`/Frobenius end:
[`PowerSeries.coeff_heckeT_pow_sub_mem_span`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PowerSeries_coeff_heckeT_pow_sub_mem_span.lean#L7)
controls `heckeT` applied to a $`p^j`$-th power of a normalized eigenform's
coefficient series, modulo the ideal $`(p)`$ — the input to the mod-$`p`$
congruence machinery.

## 7. What is proved IV: commutation of the operators

Commutation is the structural reason an eigenform can be *simultaneous*, and
FLT proves it in three encodings. All the operator-level commutations are for
**coprime** indices (the non-coprime case is what requires the extra
$`T_\ell T_{\ell^r} = T_{\ell^{r+1}} + \ell^{k-1} T_{\ell^{r-1}}`$ relation,
which FLT encodes in `IsNormalizedEigenform` rather than as an operator
identity — §8).

| layer | statement | hypothesis |
|---|---|---|
| function/`ModularFormClass` | [`heckeU_heckeU_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_heckeU_heckeU_comm.lean#L7) | none |
| function/`ModularFormClass` | [`heckeT_heckeT_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_heckeT_heckeT_comm.lean#L7), [`heckeT_heckeU_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_heckeT_heckeU_comm.lean#L7) | $`(p,q)=1`$ |
| bundled `CuspForm` | [`heckeULin_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeULin_comm.lean#L6) | $`p,q \mid N`$ |
| bundled `CuspForm` | [`heckeTLin_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeTLin_comm.lean#L6), [`heckeTLin_heckeULin_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeTLin_heckeULin_comm.lean#L6) | $`p,q`$ prime with $`p \nmid N`$, $`q \mid N`$ |
| bundled `ModularForm` | [`heckeTLin_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeTLin_comm.lean#L6) | $`p,q`$ prime, $`\nmid N`$ |
| `GammaH` | [`heckeTLinH_heckeULinH_diamondLinH_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.lean#L11), [`heckeULinH_comm`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeULinH_comm.lean#L10) | $`\ell \nmid M`$ / $`q \mid M`$ |
| formal series | [`LaurentSeries.commute_heckeU_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_commute_heckeU_heckeU.lean#L15) | none |
| formal series | [`…_heckeU_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_commute_heckeU_heckeT.lean#L15), [`…_heckeT_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_commute_heckeT_heckeT.lean#L15), [`…_heckeU_heckeV`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_commute_heckeU_heckeV.lean#L15), [`…_heckeV_heckeV`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_commute_heckeV_heckeV.lean#L15) | $`(p,\ell)=1`$ |

**Gap to keep in mind.** No declaration in the tree is named `heckeT_mul` or
`heckeT_comp`; a `grep` for product-shaped Hecke names
(`grep -rhoE '…' | grep -iE 'mul|pow|comp'`) returns only unrelated
`mem_modPCusp_mul`-style names and the Frobenius theorem of §6. So FLT does
**not** state $`T_m T_n = T_{mn}`$ for the operators themselves; it gets the
same arithmetic through `coeffHeckeT_*` and through `IsNormalizedEigenform`.

## 8. What is proved V: the eigenform dictionary

`IsNormalizedEigenform` itself
([`Def_FLTPrelim_Modularity.lean`, lines 26–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L26-L40))
is four coefficient clauses — $`a_1 = 1`$, multiplicativity on coprime
indices, and the two prime-power recursions. The Hecke operators never appear
in the structure. What FLT proves is that this coefficient predicate is
*equivalent* to being an eigenvector of the operators, in three forms:

- [`CuspForm.isNormalizedEigenform_iff_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean#L7):
  for every prime $`p`$, $`T_p f = a_p f`$ if $`p \nmid N`$ and
  $`U_p f = a_p f`$ if $`p \mid N`$;
- [`…_iff_heckeTLin`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean#L7):
  the same with the bundled maps;
- [`…_iff_coeffHecke`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean#L7):
  the same with the coefficient maps acting on `qCoeff f`.

The one-directional forms used downstream:

- [`IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul.lean#L7),
  [`…heckeULin_apply_eq_qCoeff_smul`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul.lean#L8);
- the *iff* forms for a single operator/eigenvalue
  [`CuspForm.heckeTLin_apply_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeTLin_apply_eq_smul_iff.lean#L7),
  [`heckeULin_apply_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeULin_apply_eq_smul_iff.lean#L7),
  and the `ModularFormClass` counterparts
  [`heckeU_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean#L7),
  [`heckeT_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean#L7):
  $`T f = c f \iff`$ coefficientwise $`\mathrm{coeffHeckeT}(a)_n = c\,a_n`$;
- **multiplicity one / vanishing**,
  [`LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero.lean#L9):
  a formal series that is a simultaneous eigenvector for all $`T_\ell`$
  ($`\ell \nmid M`$) and $`U_q`$ ($`q \mid M`$) with nonnegative support and
  $`a_1 = 0`$ is zero;
- the newform-level eigenvalue of $`U_q`$ at a *non-dividing* level,
  [`heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div.lean#L12),
  and its quadratic relation
  [`sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform.lean#L10),
  $`u^2 - a_q\,u + q = 0`$ — this is where the missing $`T_q^2`$ relation
  resurfaces for newforms.

## 9. What is proved VI: the Hecke algebra

`heckeGenerators` is the set of `heckeTLin k hℓ hℓN` for primes
$`\ell \notin S`$, $`\ell \nmid N`$, together with the `heckeULin k hqN` for
$`q \mid N`$; `heckeAlgebra = Algebra.adjoin ℤ heckeGenerators`
([`Def_CuspForm_HeckeAlgebra.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L14-L19)).
Proved in the same file: each generator and each algebra element is a member
(`heckeTLin_mem_heckeAlgebra`, `heckeULin_mem_heckeAlgebra`), monotonicity in
the excluded set $`S`$, the pairwise commutation
`commute_of_mem_heckeGenerators`, and the instances
`heckeAlgebra.instIsMulCommutative` (L59), `…instCommRing` (L64),
`…instIsAddTorsionFree` (L66), plus the generators `heckeAlgebra.T`, `.U`.

The theorem layer adds the finite-type facts:

| statement | content |
|---|---|
| [`CuspForm.moduleFinite_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra.lean#L19) | `Module.Finite ℤ (heckeAlgebra N k S)` |
| [`HasIntegralStructure.moduleFinite_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean) / [`…moduleFree_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean) | finite and **free** over $`\mathbb{Z}`$ under `HasIntegralStructure` |
| [`mem_intLattice_of_mem_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra.lean#L6), [`mem_intLattice_of_coe_eq_heckeT`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT.lean#L8), [`…heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU.lean#L8) | the algebra preserves the integral lattice |
| [`span_heckeTLin_eigen_eq_top`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean#L7) | the simultaneous $`T_\ell`$-eigenvectors span $`S_2(\Gamma_0(N))`$ |
| [`finrank_span_heckeAlgebra_eq_finrank`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank.lean), [`exists_cyclic_span_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_cyclic_span_heckeAlgebra.lean#L7), [`exists_top_eq_heckeAlgebra_adjoin_smul`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_top_eq_heckeAlgebra_adjoin_smul.lean) | the algebra spans the full endomorphism space on weight 2 |
| [`heckeEvalForms_range_eq_top`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeEvalForms_range_eq_top.lean#L5) | the abstract evaluation $`\mathbb{T} = \mathbb{Z}[X_\ell] \to`$ `heckeAlgebra` is surjective |
| [`fg_toSubmodule_heckeAlgebra`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_fg_toSubmodule_heckeAlgebra.lean) | f.g. as a submodule |

The `T`/`U` commutation used by `commute_of_mem_heckeGenerators` is exactly §7.
This is the layer that makes `heckeAlgebra` usable as a coefficient ring for
eigenforms; downstream Taylor–Wiles uses are §12.

## 10. The `GammaH`/`Gamma1` variants, and level lowering

`GammaH` (`Def_CuspForm_HeckeOperatorFormsGammaH.lean`) does not assume
`U_q`/`T_\ell` preserve the space; it *asserts* it as the predicates
`StableU`/`StableT`/`StableD`, and then defines `heckeULinH`, `heckeTLinH`,
`diamondLinH` as the map when the predicate holds and `0` otherwise. The
`qCoeff` rules are the Nebentypus-twisted classical formulas:

- [`qCoeff_heckeULinH_eq_qCoeff_mul`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul.lean#L11):
  $`U_q`$ still substitutes $`n \mapsto nq`$;
- [`qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH.lean#L11):
  $`a_{n\ell} + \ell^{k-1}[\ell \mid n]\,(\text{diamond-twisted } a_{n/\ell})`$.

`Gamma1` (`Def_CuspForm_Gamma1HeckeOperators.lean`, 56 declarations) works with
$`\mathbb{Q}`$-matrices `heckeMatrixQ`/`heckeDiagMatrixQ` (L23/L27) and
$`\mathbb{Z}`$-representatives, and proves the Hecke-representative
permutation `heckeRep_mul` (L281) — the group-theoretic core of the double
coset — leading to `slashOfMemGamma0` (L535), `diamondLinOne` (L592) and
`heckeTLinOne` (L652). Its theorem layer:

- [`qCoeff_heckeTLinOne`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_qCoeff_heckeTLinOne.lean#L7):
  the same coefficient formula with the diamond twist;
- [`heckeTLinOne_slashOfMemGamma0`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_heckeTLinOne_slashOfMemGamma0.lean#L11):
  $`T_\ell`$ commutes with the $`\Gamma_0`$-slash transport.

Level lowering / level raising at the operator level:

- [`CuspForm.exists_coe_eq_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean#L7) — $`U_p f`$ is again a cusp form at the same level;
- [`exists_coe_eq_heckeU_of_mul_eq_of_dvd`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd.lean#L6) — the lowering $`S_k(\Gamma_0(qR)) \to S_k(\Gamma_0(R))`$ when $`q \mid R`$;
- [`exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span.lean#L9) — the $`\mathrm{Frob}`$-twisted lowering $`S_k(\Gamma_0(M)) \to S_{pk}(\Gamma_0(M/p))`$ when $`p^2 \mid M`$, with the $`a^p`$ congruence mod $`(p)`$;
- [`exists_gamma1_coe_eq_heckeU_of_dvd`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.lean#L13) and [`exists_gamma1_div_coe_eq_heckeU_of_dvd_div`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean#L13) — `Gamma1` versions preserving `HasNebentypus`, the second lowering to $`\Gamma_1(N/\ell)`$;
- [`exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd.lean#L11) — level raising producing an eigenform whose $`U_q`$ eigenvalues vanish exactly at $`q^2 \mid N`$.

## 11. The formal $`q`$-expansion operators

`LaurentSeries.heckeU`/`heckeV`/`heckeT` and `PowerSeries.heckeU`/`heckeV`/
`heckeT` are the coefficient-space versions, and they are where the
$`q`$-expansion theorems of §6 land. The proved facts:

- `PowerSeries.heckeU_heckeV`: $`U_\ell V_\ell = 1`$ (the two are inverse in one
  direction);
- `LaurentSeries.heckeV_eq_qExpand`: $`V_\ell =`$ `qExpand R ℓ` (the
  $`q \mapsto q^\ell`$ substitution);
- the four commutation theorems in the table of §7;
- the multiplicity-one vanishing of §8;
- `coeff_heckeT`: the coefficient formula matching `coeffHeckeT`.

The `PowerSeries` file is not imported by
`Def_ModularForm_HeckeOperatorForms.lean`; it is the target of the §6
`qExpansion` equalities (whose own `Thm_*` wrappers import it).

## 12. Boundary: the faces this survey deliberately leaves out

These are the *consumers* that make the operator names appear in 163 further
`Theorems/` files. They are different mathematical objects (Hecke
correspondences, cohomology operators, Galois representations) and are owned by
other notes, but a reader counting `grep` hits should know they exist:

| face | where | note |
|---|---|---|
| divisor correspondences on $`J_0(N)`$ | `Def_ModularCurve_HeckeOperator.lean`, `Def_ModularCurve_HeckeModule.lean`, `Thm_ModularCurve_heckeOperatorsCommuteBar.lean` | [math/009](../math/009-hecke-jacobian-commute.md), [`studies/hecke-commute-bar-survey.md`](hecke-commute-bar-survey.md) |
| period map ↔ cohomology operator | [`periodMap_heckeTLin`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_periodMap_heckeTLin.lean#L7), [`periodMap_heckeULin`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_periodMap_heckeULin.lean#L7), [`periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.lean#L13) | this is the bridge where the §2 operator is intertwined with `HeckeEis.heckeOperatorHom` |
| group-cohomology `CohCarrier.heckeT` | 76 `Thm_CohCarrier_*` files, `Def_Gamma0HeckeOperatorHom.lean` | a transfer on $`H^1`$, not the slash average |
| Eichler–Shimura | `Thm_HeckeEis_eichlerShimuraMap_heckeTLin`, `…_heckeULin` | comparison of the two |
| mod-$`p`$ forms | `Thm_ModPForms_heckeT_apply_eq_heckePS`, `heckeU_mem_modPCusp_*` | |
| Taylor–Wiles / Galois reps | 31 `Thm_CuspForm_heckeLocal_*`, `heckeAlgebra_*`, `IsNormalizedEigenform_*` files | uses `heckeAlgebra` as a coefficient ring, [base/011](../base/011-deformations-hecke-algebras-and-r-equals-t.md) |
| adelic / quaternion / local Langlands | `Def_AbstractHeckeOperator.lean`, `Def_LocalLanglands_Hecke*.lean`, `Def_QuaternionAlgebra_ClassSetHecke.lean` | [base/012](../base/012-adeles-and-automorphic-representations.md) |

## 13. Port implications

**Status (2026-09-23, after SETs 1–4).** Stages A, B and C are **done** and
independently verified (checker 802 identical, 0 mismatched; full build green;
[../lean/logs/hecke-port.md](../lean/logs/hecke-port.md),
[../lean/topics/hecke/](../lean/topics/hecke/)). Stage D is **half done**: its
formal-operator part landed, its Γ_H / Γ₁ / level-lowering part did not.

| stage | content | state | port modules |
|---|---|---|---|
| A | the operator block (pin 72–200) | **done** | `ModularForms/Defs/HeckeOperator.lean` |
| B | the analytic lemmas (§5) | **done** | `HeckeAnalytic.lean`, `HeckeCusps.lean` |
| C | bundling + commutation + the algebra structure (§3, §7, §9's algebra half) | **done** | `HeckeOperatorForms.lean`, `HeckeCommute.lean`, `HeckeAlgebra.lean` |
| D | Γ_H / Γ₁ / level lowering | **remaining** | — |
| D | the formal `PowerSeries`/`LaurentSeries` operators | **done** | `Defs/FormalHeckeOperators.lean`, `ModularCurve/Defs/LaurentSeriesHecke.lean` |
| — | the coefficient action (§6) | **done** | `HeckeQCoeff.lean` |
| — | the eigenform dictionary (§8) | **done** | `Defs/Eigenform.lean`, `HeckeEigenform.lean` |
| — | the Hecke algebra's finite/free half (§9) | **out of scope (decided)** | `Defs/IntegralStructure.lean`, `HeckeLattice.lean` are the definitions only |
| §12 | the boundary faces | **out of scope** | — |

**What Stage D still needs**, with the pin's module sizes:
`Def_CuspForm_HeckeULower.lean` (46 lines, 2 decls — `heckeULowerLin` and its
`coe_*`), consumed by the §10 level-lowering wrappers (`exists_coe_eq_heckeU`,
`exists_coe_eq_heckeU_of_mul_eq_of_dvd`, `exists_gamma1_*`);
`Def_CuspForm_HeckeOperatorFormsGammaH.lean` (262 lines, 25 decls — the Γ_H
diamond/`T`/`U` layer, the survey's Tier 3); and
`Def_CuspForm_Gamma1HeckeOperators.lean` (680 lines, 56 decls — the
Γ₁/Nebentypus layer, with its own `heckeMatrixQ`/`heckeRep` matrix block, the
survey's Tier 2). Atkin–Lehner (`Def_ModularForm_AtkinLehnerDatum.lean`, 157
lines, plus the `alSlash`/`diamondLinH`/`traceLin` tree — the survey's Tier 4) is
a fourth, unlettered remainder. Port state confirmed by `grep`: `heckeULowerLin`,
`heckeTLinH`, `heckeULinH`, `diamondLinH`, `heckeTLinOne`, `diamondLinOne`,
`slashOfMemGamma0` all occur **0** times in `FLTForHuman/`.

**The finiteness decision.** The §9 *structure* (generators, `heckeAlgebra`,
commutativity) is ported; the §9 *finite/free* half is deliberately out of scope:
the general `moduleFinite_heckeAlgebra`/`HasIntegralStructure` need the
Eichler–Shimura/cohomology comparison (657 nodes / 263,720 raw `S_` lines), and
the only cheap route is the standalone 4,308-line `moduleFinite_heckeAlgebra_two`
at `k = 2`. See [../lean/topics/hecke/TOPIC-t10-finite-algebra.md](../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
§7 for the measured cones.

The staged reading below is the *original* sketch, kept for the record; the table
above supersedes its tense.

The port's `Defs/HeckeOperator.lean` currently stops after
`coe_heckeDiagMatrix_smul` (port line 110). The FLT file continues for another
130 lines. The staged reading below is what the §2–§10 map suggests; it keeps
each stage's dependency footprint honest.

**Stage A — the self-contained operator block.** Port FLT lines 72–200 into
`Defs/HeckeOperator.lean` after the two `coe_*_smul` theorems. This is pure
`Mathlib` + the already-ported matrices: `σ_hecke*`, `slash_hecke*_apply`,
`heckeU`/`heckeT`, their `_def`/`_apply`/zero/linearity lemmas, and
`coeffHeckeT`/`coeffHeckeU` with the coefficient lemmas. Nothing about
`ModularFormClass` or cusps is needed, so it compiles against the current
imports (`SlashActions`, `UpperHalfPlane.Exp`). This is the natural next commit.

**Stage B — analytic lemmas.** The `mdifferentiable`/`periodic`/`bounded`/
`isZeroAt` theorems of §5 are what the bundling needs. They are stated for
`UpperHalfPlane → ℂ` and `ModularFormClass`/`CuspFormClass`, so a port must
first decide whether those class definitions are in the port's
`ModularForms/Defs`.

**Stage C — bundling and the algebra.** `Def_ModularForm_HeckeOperatorForms.lean`
(8 declarations) plus `Def_CuspForm_HeckeAlgebra.lean` (14 declarations) give
`heckeTLin`/`heckeULin` and `heckeAlgebra`; the four `toFun` obligations map
exactly onto the §5 lemmas. The commutativity theorems of §7 are the inputs to
the `IsMulCommutative` instance.

**Stage D — only if a later cone needs them.** `Def_CuspForm_HeckeULower.lean`
(2), `Def_CuspForm_HeckeOperatorFormsGammaH.lean` (25),
`Def_CuspForm_Gamma1HeckeOperators.lean` (56), and the formal
`LaurentSeries`/`PowerSeries` operators (9) are independent faces. The
`Gamma1` file is the largest single module and contains its own matrix layer
(`heckeMatrixQ`, `heckeRep`), so it should not be pulled in until the
$`\Gamma_0`$ API is ported.

A porting note for the statement checker: the `Thm_*` wrappers are the public
statements (e.g.
[`Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean#L6)),
while the mathematics is in `P2M/Sol/S_*` (508 files, per §0.1); the
`Definitions/` file is where the *definitions* live and is the only one the port
needs to mirror declaration-for-declaration.

## 14. Links

FLT at the pinned sha `aa2d8b3`:

- Definitions: [`Def_ModularForm_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean),
  [`Def_ModularForm_HeckeOperatorForms.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean),
  [`Def_CuspForm_HeckeAlgebra.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean),
  [`Def_CuspForm_HeckeULower.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeULower.lean),
  [`Def_CuspForm_HeckeOperatorFormsGammaH.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean),
  [`Def_CuspForm_Gamma1HeckeOperators.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean),
  [`Def_Gamma0HeckeOperatorHom.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Gamma0HeckeOperatorHom.lean),
  [`Def_LaurentSeries_HeckeU.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LaurentSeries_HeckeU.lean),
  [`Def_LaurentSeries_HeckeV.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_LaurentSeries_HeckeV.lean),
  [`Def_PowerSeries_FormalHeckeOperators.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PowerSeries_FormalHeckeOperators.lean),
  [`Def_CuspForm_HeckeEvalForms.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeEvalForms.lean),
  [`Def_FLTPrelim_Modularity.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean).
- The headline wrappers cited above are under
  [`Theorems/Thm_ModularForm_*.lean`](https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3/Theorems)
  and `Theorems/Thm_CuspForm_*.lean`; the mathematical proofs are under
  `P2M/Sol/S_*`.

Port modules in this repository:

- [`lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean`](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) — the current matrices-only state
- [`lean/FLTForHuman/ModularForms/HeckeQExpansion.lean`](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean) — the two Hecke translates on the $`q`$-expansion
- [`lean/FLTForHuman/ModularForms/PhiGenDescends.lean`](../lean/FLTForHuman/ModularForms/PhiGenDescends.lean) — the `cosetPoly_smul` consumer

Companion notes:

- [base/014 — Hecke operators: cosets, q-expansions, and the two matrices](../base/014-hecke-operators.md) — the mathematical narrative and the coset-polynomial application
- [base/002 — Modular forms at the mathlib level](../base/002-modular-forms-basics.md) — the mathlib gap this file fills
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) and [`studies/hecke-commute-bar-survey.md`](hecke-commute-bar-survey.md) — the divisor-correspondence face
- [base/011 — Deformations, Hecke algebras, and R = T](../base/011-deformations-hecke-algebras-and-r-equals-t.md) — the abstract Hecke algebra

Background:

- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 — the double-coset definition and the $`T_p`$/$`U_p`$ split.
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton 1971, Ch. 3 — the Hecke ring and its action.
