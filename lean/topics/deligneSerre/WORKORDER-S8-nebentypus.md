# WORKORDER-S8 — the Γ₁/Nebentypus pair: existence and Fricke inversion

**Status: landed 2026-10-11.** The promotion wave and both row-modules are in the tree and
verified (checker 7,639 → **7,641 identical, 0 mismatched, 0 missing, 38 own**; tier-1 green;
`#print axioms` `[propext, Classical.choice, Quot.sound]`). The two ready
`CuspForm` rows at the head of the column shelf, cut as one set because they are the two headlines
of one subject — the nebentypus character of a Γ₁ Hecke eigenform:

| row | `S_` | content |
|---|---:|---|
| `CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen` | 591 | existence: a nonzero `f : CuspForm (Gamma1 N) k` whose `q`-coefficients satisfy a Hecke-eigenvalue relation against some `χ : ℕ → ℂ` has a Dirichlet character `ε` with `HasNebentypus ε f` and `ε (p) * p ^ (k-1) = χ p` |
| `CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke` | 667 | Fricke inversion: if `g` has nebentypus `ε` and `h` is its Fricke transform, then `h` has nebentypus `ε⁻¹` and the Hecke eigenvalue transforms by `ε⁻¹ (p)` |

**The two pin files are *not* twins** (unlike `WORKORDER-E`): their `diff` is 1,019 lines, the
namespaces are `NebentypusFromMultipliers` and `FrickeHecke`, and neither imports the other.
`port_plan` prices the pair at 1,258 raw / 1,203 declaration lines / **92 duplicate** / once-cost
1,111 / 167 already in the port / **944 net new math lines**, with 31 trusted and 0 suspect
substitutions. So this is a genuine two-module set, not a dedup.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. The promotion wave (manager's, landed before dispatch)

`ModularForms/HeckeEigenNebentypus.lean` (the S3 predecessor, `slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`)
had its `dd`/Γ₁ vocabulary `private`. It is stated by the two successors, so it is shared API, not
per-file glue, and is promoted **for clarity** (playbook §4(b)):

`dd`, `dd_mul`, `isUnit_dd`, `mem_Gamma1_iff_dd`, `inv_mul_mem_Gamma1`, `exists_lift`, `dd_pow`
— all now public under `CuspForm.HeckeEigenNebentypus`. Checker 7,632 → **7,639 identical**, 0
mismatched, 0 missing; the wave build (module + `DeligneSerre.CoefficientRing` +
`DeligneSerre.Lifting`) is green.

Kept `private`: the predecessor's own proof internals (`sl2`, `slash_eq_smul_prime`,
`slash_pow_of_slash_eq_smul`, `exists_lift_slash_eq`, `main`) and the generic adaptors
`det_eq`/`det_mod`/`T_mem_Gamma1`/`T_pow_mem_Gamma1`/`periodic_add_smul` — the first four already
have public homes (`ModularForm.HeckeRepresentatives.det_eq`, `ModularForm.Level.det_mod`,
`X1DiamondRational.T_mem_Gamma1`/`T_pow_mem_Gamma1`), so the rows import those rather than a second
copy.

## 2. The reuse map (hand-checked)

`port_advise` reports 31 trusted substitutions (20 public + 11 port-private, of which 7 are now the
promotion above). The hand-check against the whole port corpus adds the rest. **Import, never
re-prove:**

| port home | declarations |
|---|---|
| `ModularForms/HeckeEigenNebentypus.lean` | `dd`, `dd_mul`, `isUnit_dd`, `mem_Gamma1_iff_dd`, `inv_mul_mem_Gamma1`, `conj_mem_Gamma1`, `exists_lift`, `dd_pow` (all public now) |
| `ModularForms/HeckePrelude.lean` | `heckeDiagMatrix_mul_T`, `periodic_of_slash_T`, `slash_heckeDiagMatrix_slash_T`, `isBoundedAtImInfty_slash_heckeMatrix`, `isBoundedAtImInfty_slash_heckeDiagMatrix`, `cusp_periodic`, `cusp_bdd`, `cusp_slash_T_pow` |
| `ModularForms/HeckeAnalytic.lean` | `mdifferentiable_heckeU`, and the `isBoundedAtImInfty_heckeU` statement (binder-renamed — take the port's binders) |
| `ModularForms/Defs/HeckeRepresentatives.lean` | `det_eq`, `mapGL_apply` |
| `ModularForms/Level/Diamond.lean` | `det_mod` |
| `ModularForms/WeightOne/Defs/GammaRational.lean` | `T_mem_Gamma1`, `T_pow_mem_Gamma1`, `conj_mem_Gamma1` |
| `ModularForms/WeightOne/Defs/RatAt.lean` | `periodic_smul` |
| `ModularForms/HeckeFricke.lean` | the `frickeConj`/`frickeGL` vocabulary (binder-renamed — take the port's binders) |

The two `NEAR` rows that need care are `slash_eq_smul_prime` (pin) vs the port's public
`CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen` (ratio 0.931 — the pin's is the
`χ : ℕ → ℂ` version, so it may be genuinely new rather than a rename) and
`isBoundedAtImInfty_heckeU` (binder-only). Read both copies before deciding.

## 3. The two modules

| module | public surface |
|---|---|
| `FLTForHuman/ModularForms/HeckeNebentypusExistence.lean` | `CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen` only; every helper `private` in the pin's own sub-namespace |
| `FLTForHuman/ModularForms/HeckeNebentypusFricke.lean` | `CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke` only; every helper `private` |

Each module's public headline is the pin's `Theorems/` wrapper **verbatim** (statement), with the
proof from the matching `P2M/Sol/S_*.lean`. The genuinely new mathematics: the
`IsDiamondScalar`/`diamondScalar` diamond-scalar vocabulary (existence module) and the
`frickeGL`/`frickeConj`/`sig`/`gam` Fricke-conjugation calculus (Fricke module). Keep them
`private` unless a later row states them.

**Outcome.** `HeckeNebentypusExistence.lean` (481 lines) and `HeckeNebentypusFricke.lean` (619
lines), each one public headline, 0 warnings. The one drift: the pin's
`heckeMatrix_mul_frickeGL` proof reduced the `SL → GL` coercion of
`Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (gam …)` through the default `simp` set, whose
key changed in `v4.34.0` (the port's `mapGL_apply` is keyed on `mapGL ℝ`, only definitionally equal).
The port restates that factor as `mapGL ℝ (gam …)` (`change`) and then follows the already-ported
`HeckeFricke.fricke_mul_mapGL`'s drift-free route — `rw [Units.val_mul, …, val_heckeMatrix hp,
val_frickeGL, Matrix.SpecialLinearGroup.mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply]`
then `fin_cases` + `simp [Matrix.mul_apply, Fin.sum_univ_two, val_heckeMatrix hp, gam,
Matrix.map_apply] <;> nlinarith [hreal]`. No statement moved.

## 4. Build discipline and stop conditions

* `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` for the edit loop;
* `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularForms.<module>` when done;
* no whole-tree build; never raise the heartbeat cap;
* **hub prohibition**: no existing Lean module is edited. A helper that seems to need a promotion
  stops and reports with the declaration, host and `build_ladder.py --edit` price.

## 5. Verification per module

Checker `0 mismatched / 0 missing` with the `identical` delta equal to the one new headline; tier-0
0 warnings; tier-1 green; `#print axioms` `[propext, Classical.choice, Quot.sound]`; one-token
mutation on the headline caught and reverted; no `sorry`/`admit`/bare `import Mathlib`.

FLT provenance, pinned `aa2d8b3`:
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.lean>

## 6. Deferred: the third Nebentypus-shelf row

`CuspForm.exists_degeneracy_gamma1_hasNebentypus` (218 silo lines) was considered for this set and
is **deferred to its own definition-first order**. The frontier lists it ready, but that is the
known `Definitions/` blind spot: its `S_` file imports and uses
`FreyPackage.ModMCarrier.rescaleSlash_isZeroAt`, and neither
`Definitions/Def_ModularForm_AtkinLehnerDatum.lean` (157 lines, 21 declarations) nor
`Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean` (176 lines, 10 declarations) is ported. It is
also a different subject (nebentypus under the `V_d` rescaling), so it does not share this set's
one-story cut.
