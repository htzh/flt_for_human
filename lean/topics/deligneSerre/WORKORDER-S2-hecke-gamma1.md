# Work order — S2: Hecke / Γ₁ vanishing and nebentypus (9 nodes)

**Status: ready to dispatch — phase H2 is closed and green (checker 2301/0/0) and
S1 is closed (2444/0/0).** The second theorem set. Method handbook: `lean/porting-playbook.md` (§2.4, §3.1–§3.5, §4, §7.4
for the near-duplicate binders). Mathematics: `math/019` §3.

## 0. Scope and prerequisite

The two substantive results — the **oddness derivation** (the Hecke eigen-relation
forces the nebentypus, `CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`) and
the **Γ₁-vanishing lemma** (a Γ₁-cusp form invariant under `diag(p,1)`, after the
diamond correction, is zero) — plus the `q`-coefficient / slash commutation plumbing
that feeds them and the Ihara group-theory input.

**Prerequisite: phase H2 must be closed and green.** S2's proofs sit on the Hecke
vocabulary H2 reconciles: `heckeRep_mul` (the pin's Γ₁ form), `mdifferentiable_heckeU`,
`isUnit_wt`, `det_mod`, the four `…_mul_of_eq` three-conjunct statements (promoted
from the `_11` refinements), `isZeroAt_heckeU`, and the `sum_range_eq_sum_zmod`
binder rename. Dispatch after H2's review, not before.

**Explicitly not this set:** the relèvement/lifting (S3), S1 (already ported), S4–S8.
Edit only `FLTForHuman/ModularForms/` and `FLTForHuman/ModularCurve/` (plus the
checker config).

## 1. The nine public targets — statements verbatim from the pin wrappers

```lean
theorem ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p
```

```lean
theorem CuspForm.qCoeff_heckeTLinOne {M : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLinOne k hp hpM f) n =
      ModularFormClass.qCoeff f (p * n) +
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff (CuspForm.diamondLinOne M k p f) (n / p) else 0)
```

```lean
theorem CuspForm.heckeTLinOne_slashOfMemGamma0
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f)
```

```lean
theorem CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g
```

```lean
theorem CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q')
    (j : ℕ) (τ : ℍ) :
    y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ
```

```lean
theorem CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0
```

```lean
theorem CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
    {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M) (k : ℤ)
    (y : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    y = 0
```

```lean
theorem CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
    {M : ℕ} [NeZero M] (k : ℤ)
    (g : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ)
```

```lean
theorem Ihara.amalgamToGamma0Away_surjective (N q : ℕ) (hNq : Nat.Coprime N q)
    (hq : q.Prime) :
    Function.Surjective (Ihara.amalgamToGamma0Away N q)
```

## 2. Homes and dependency order

Import, do not re-prove: `ModularForms/Defs/Gamma1HeckeOperators.lean` (D1:
`heckeTLinOne`, `diamondLinOne`, `slashOfMemGamma0`, `heckeU_eq_sum_zmod`, …),
`ModularForms/Level/Diamond.lean`, `ModularForms/Defs/HeckeRepresentatives.lean`,
`ModularForms/HeckeQCoeff.lean`, `ModularForms/HeckeAnalytic.lean`,
`ModularForms/Defs/PrimitiveFormGamma1.lean` (D1: `HasNebentypus`),
`ModularCurve/Defs/IharaAmalgamMap.lean` (D2: `amalgamToGamma0Away`), and the H1
`ModularForms/HeckePrelude.lean`.

New modules — port in this dependency order, leaves first (`T0` order), all under
the subject homes the topic note fixes (no new directory):

| order | new port module | public target landed |
|---:|---|---|
| 1 | `ModularForms/HeckeTLinOneQCoeff.lean` | `CuspForm.qCoeff_heckeTLinOne`, `CuspForm.heckeTLinOne_slashOfMemGamma0` |
| 2 | `ModularForms/HeckeNebentypus.lean` | `CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul` |
| 3 | `ModularForms/Gamma1Vanishing.lean` | `ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`, `CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant`, `CuspForm.eq_zero_of_forall_vadd_inv_pow_eq`, `CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` |
| 4 | `ModularForms/HeckeEigenNebentypus.lean` | `CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen` |
| 5 | `ModularCurve/IharaSurjective.lean` | `Ihara.amalgamToGamma0Away_surjective` (independent of 1–4; may be written first) |

The `Ihara` target keeps the pin's `Ihara.*` name; the `CuspForm`/`ModularForm`
targets keep their pin namespaces. Helpers stay `private`.

## 3. Route, reuse, risk

- **The H2 reconciliations are the interface.** Before writing, `#check` the port
  spellings of `heckeRep_mul`, `mdifferentiable_heckeU`, `isUnit_wt`, `det_mod`,
  the four `…_mul_of_eq`, `heckeU_eq_sum_zmod`, `sum_range_eq_sum_zmod`; if any
  still carries the pre-H2 statement, stop — H2 is not closed.

  **H2's reconciled copies live in these names — open or qualify them:**
  `ModularForm.HeckeGamma1.mdifferentiable_heckeU`;
  `HeckeRepresentatives.HeckeGamma1.heckeRep_mul` (the pin Γ₁ form);
  `X1DiamondRational.PeriodOne.periodic_smul` (the pin unit-period form);
  `CuspForm.Gamma1Hecke.isZeroAt_heckeU` (the pin `hp : p ≠ 0` form);
  `T_pow_mem_Gamma1` (public ℕ statement, `WeightOne/Defs/GammaRational.lean`);
  `T_zpow_mem_Gamma1` (public ℤ statement, `WeightOne/Gamma1Basis.lean`). Further:
  `isUnit_wt` now sits under `[Fact p.Prime]`; `sum_range_eq_sum_zmod` uses the pin
  `{A} (G)` binders; `mapGL_apply` uses `Matrix.SpecialLinearGroup.mapGL`; the four
  `…_mul_of_eq` are the public three-conjunct statements with the two-conjunct
  copies renamed `…_two`; `coe_smul_eq` (Reserve) is at the pin statement.
- **Substitution list (pin → port), from `port_advise`:** `det_eq`, `det_mod`,
  `heckeRep`, `heckeRep_infty`, `heckeT_eq_sum_onePoint`, `heckeU_eq_sum_zmod`,
  `redMatrix`, `redMatrix_apply_one_one`, `lift`, `lift_mem`, `lift_apply_one_one`,
  `lift_infty`, `wt_infty`, `d_mul`, `mem_Gamma1_of_d_eq_one`,
  `sum_range_eq_sum_zmod`, `d_mul` — import from
  `HeckeRepresentatives.lean`/`Diamond.lean`; do not re-prove.
- **The oddness derivation is the risk:** it is 436 pin lines and uses the
  `Ihara`/coset machinery through `amalgamToGamma0Away_surjective`. If a step needs
  an unported Ihara lemma, port it into the Ihara module of this set (or log it) —
  do not weaken the statement.
- Recorded negatives: none yet; append any mathlib search that finds nothing.

## 4. Verification, build discipline, closing

Same as `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands. Stop and
report on a faithful-statement failure or an unbounded build.

---

## Appendix — per-file pin declaration inventory

#### S2a — pin `P2M/Sol/S_Ihara_amalgamToGamma0Away_surjective.lean` (612 lines, 33 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `IsClearedBy` | def | 27 | 4 |  |
| `exists_pow_mul_intCast` | theorem | 31 | 9 |  |
| `exists_isClearedBy` | theorem | 40 | 34 |  |
| `IsClearedBy.map_eq` | theorem | 74 | 7 |  |
| `IsClearedBy.reduce_of_dvd` | theorem | 81 | 34 |  |
| `IsClearedBy.det_eq` | theorem | 115 | 11 |  |
| `IsClearedBy.integral_of_zero` | theorem | 126 | 8 |  |
| `IsClearedBy.of_map_mul` | theorem | 134 | 16 |  |
| `IsClearedBy.unique` | theorem | 150 | 6 |  |
| `IsClearedBy.succ` | theorem | 156 | 12 |  |
| `exists_row_scalar` | theorem | 168 | 44 |  |
| `rowReducerMat` | def | 212 | 12 |  |
| `isCoprime_reducer_row` | theorem | 224 | 8 |  |
| `rowReducerGamma0` | def | 232 | 15 |  |
| `rowReducerGamma0_apply_one_zero` | theorem | 247 | 5 |  |
| `rowReducerGamma0_apply_one_one` | theorem | 252 | 5 |  |
| `rowReducer_mul_row_one_dvd` | theorem | 257 | 23 |  |
| `colReducerMat` | def | 280 | 8 |  |
| `colReducerMat_det` | theorem | 288 | 6 |  |
| `colReducerGamma0` | def | 294 | 7 |  |
| `colReducerGamma0_coe` | theorem | 301 | 5 |  |
| `exists_colReducer_scalar` | theorem | 306 | 17 |  |
| `det_row_factor` | theorem | 323 | 13 |  |
| `vertexOne_colReducer_mul_row_zero` | theorem | 336 | 19 |  |
| `vertexOne_colReducer_mul_row_one` | theorem | 355 | 18 |  |
| `vertexOne_colReducer_mul_cleared` | theorem | 373 | 41 |  |
| `dvd_descent` | theorem | 414 | 13 |  |
| `mem_range_vertexZero_of_integral` | theorem | 427 | 29 |  |
| `vertexZero_mem_range` | theorem | 456 | 4 |  |
| `vertexOne_mem_range` | theorem | 460 | 4 |  |
| `exists_range_mul_isClearedBy` | theorem | 464 | 111 |  |
| `mem_range_amalgamToAway` | theorem | 575 | 33 |  |
| `solution` | theorem | 608 | 5 |  |

#### S2b — pin `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean` (379 lines, 23 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `det_eq` | theorem | 23 | 9 |  |
| `heckeMatrix_mul_of_eq` | theorem | 32 | 16 |  |
| `heckeMatrix_mul_of_eq'` | theorem | 48 | 16 |  |
| `heckeDiagMatrix_mul_of_eq` | theorem | 64 | 16 |  |
| `heckeDiagMatrix_mul_of_eq'` | theorem | 80 | 21 |  |
| `sum_range_eq_sum_zmod` | theorem | 101 | 8 |  |
| `heckeU_eq_sum_zmod` | theorem | 109 | 11 |  |
| `heckeRep` | def | 120 | 7 |  |
| `heckeT_eq_sum_onePoint` | theorem | 127 | 9 |  |
| `redMatrix` | def | 136 | 31 |  |
| `wt` | def | 167 | 6 |  |
| `isUnit_wt` | theorem | 173 | 5 |  |
| `heckeRep_mul` | theorem | 178 | 81 |  |
| `lift` | def | 259 | 6 |  |
| `lift_mem` | theorem | 265 | 6 |  |
| `lift_apply_one_one` | theorem | 271 | 6 |  |
| `sum_eq` | theorem | 277 | 11 |  |
| `d_mul` | theorem | 288 | 6 |  |
| `det_mod` | theorem | 294 | 8 |  |
| `mem_Gamma1_of_d_eq_one` | theorem | 302 | 7 |  |
| `isUnit_p` | theorem | 309 | 3 |  |
| `sum_slash_mapGL` | theorem | 312 | 52 |  |
| `solution` | theorem | 364 | 16 |  |

#### S2c — pin `P2M/Sol/S_CuspForm_qCoeff_heckeTLinOne.lean` (178 lines, 15 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `T_pow_mem_Gamma1` | theorem | 23 | 8 |  |
| `heckeDiagMatrix_mul_T` | theorem | 31 | 12 |  |
| `periodic_of_slash_T` | theorem | 43 | 22 |  |
| `slash_heckeDiagMatrix_slash_T` | theorem | 65 | 6 |  |
| `isBoundedAtImInfty_slash_heckeMatrix` | theorem | 71 | 4 |  |
| `isBoundedAtImInfty_slash_heckeDiagMatrix` | theorem | 75 | 4 |  |
| `isBoundedAtImInfty_heckeU` | theorem | 79 | 9 |  |
| `mdifferentiable_heckeU` | theorem | 88 | 10 |  |
| `periodic_smul` | theorem | 98 | 9 |  |
| `cusp_slash_T_pow` | theorem | 107 | 4 |  |
| `cusp_periodic` | theorem | 111 | 3 |  |
| `cusp_holo` | theorem | 114 | 2 |  |
| `cusp_bdd` | theorem | 116 | 6 |  |
| `qCoeff_heckeU_add_slash` | theorem | 122 | 49 |  |
| `solution` | theorem | 171 | 8 |  |

#### S2d — pin `P2M/Sol/S_CuspForm_heckeTLinOne_slashOfMemGamma0.lean` (22 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 11 | 12 |  |

#### S2e — pin `P2M/Sol/S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean` (29 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 12 | 18 |  |

#### S2f — pin `P2M/Sol/S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.lean` (173 lines, 17 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `slashStab` | def | 18 | 13 |  |
| `mem_slashStab` | theorem | 31 | 3 |  |
| `transGL` | def | 34 | 2 |  |
| `val_transGL` | theorem | 36 | 2 |  |
| `det_transGL` | theorem | 38 | 3 |  |
| `slash_transGL_apply` | theorem | 41 | 16 |  |
| `awayToReal` | def | 57 | 4 |  |
| `awayToReal_algebraMap` | theorem | 61 | 3 |  |
| `awayToReal_invSelf` | theorem | 64 | 6 |  |
| `rho` | def | 70 | 4 |  |
| `rho_apply_coe` | theorem | 74 | 5 |  |
| `map_wMat` | theorem | 79 | 4 |  |
| `map_wMatInv` | theorem | 83 | 4 |  |
| `rho_wConj_mul` | theorem | 87 | 11 |  |
| `rho_wConj_eq` | theorem | 98 | 4 |  |
| `rho_vertexZero` | theorem | 102 | 10 |  |
| `solution` | theorem | 112 | 62 |  |

#### S2g — pin `P2M/Sol/S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean` (76 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 8 | 69 |  |

#### S2h — pin `P2M/Sol/S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean` (381 lines, 42 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `mapGL_injective` | theorem | 25 | 6 |  |
| `mem_coe_iff` | theorem | 31 | 7 |  |
| `det_eq` | theorem | 38 | 4 |  |
| `det_mod` | theorem | 42 | 8 |  |
| `mem_Gamma1_iff_of_mem_Gamma0` | theorem | 50 | 10 |  |
| `inv_mul_apply_one_one` | theorem | 60 | 6 |  |
| `inv_mul_mem_Gamma1_iff` | theorem | 66 | 21 |  |
| `T_zpow_mem_Gamma1` | theorem | 87 | 4 |  |
| `lowerV` | def | 91 | 2 |  |
| `lowerV_mem_Gamma1` | theorem | 93 | 4 |  |
| `mul_T_zpow_apply_zero_one` | theorem | 97 | 6 |  |
| `mul_lowerV_apply_zero_zero` | theorem | 103 | 5 |  |
| `mul_lowerV_apply_zero_one` | theorem | 108 | 5 |  |
| `exists_T_zpow_dvd` | theorem | 113 | 9 |  |
| `exists_mul_mem_Gamma1_dvd` | theorem | 122 | 25 |  |
| `conjRep` | def | 147 | 11 |  |
| `conjRep_mem_Gamma0` | theorem | 158 | 7 |  |
| `mapGL_mul_heckeDiagMatrix` | theorem | 165 | 14 |  |
| `diagQ` | def | 179 | 4 |  |
| `map_diagQ` | theorem | 183 | 5 |  |
| `isArithmetic_conj_heckeDiagMatrix` | theorem | 188 | 8 |  |
| `stretch` | def | 196 | 20 |  |
| `CosetQ` | abbrev | 216 | 4 |  |
| `normCusp` | def | 220 | 16 |  |
| `coe_normCusp` | theorem | 236 | 11 |  |
| `quotientFunc_mk'` | theorem | 247 | 5 |  |
| `exists_rep` | theorem | 252 | 14 |  |
| `rep` | def | 266 | 2 |  |
| `rep_mem` | theorem | 268 | 3 |  |
| `rep_dvd` | theorem | 271 | 3 |  |
| `mk_rep` | theorem | 274 | 5 |  |
| `repE` | def | 279 | 2 |  |
| `rep_eq` | theorem | 281 | 3 |  |
| `rep'` | def | 284 | 2 |  |
| `rep'_mem` | theorem | 286 | 3 |  |
| `Phi` | def | 289 | 4 |  |
| `Phi_injective` | theorem | 293 | 13 |  |
| `Phi_bijective` | theorem | 306 | 3 |  |
| `quotientFunc_slash_heckeDiagMatrix` | theorem | 309 | 16 |  |
| `normCusp_slash_heckeDiagMatrix` | theorem | 325 | 12 |  |
| `main` | theorem | 337 | 36 |  |
| `solution` | theorem | 373 | 9 |  |

#### S2i — pin `P2M/Sol/S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean` (436 lines, 26 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `det_eq` | theorem | 29 | 4 |  |
| `det_mod` | theorem | 33 | 8 |  |
| `dd` | def | 41 | 2 |  |
| `dd_mul` | theorem | 43 | 5 |  |
| `isUnit_dd` | theorem | 48 | 3 |  |
| `mem_Gamma1_iff_dd` | theorem | 51 | 10 |  |
| `inv_mul_mem_Gamma1` | theorem | 61 | 9 |  |
| `conj_mem_Gamma1` | theorem | 70 | 10 |  |
| `exists_lift` | theorem | 80 | 12 |  |
| `T_mem_Gamma1` | theorem | 92 | 3 |  |
| `T_pow_mem_Gamma1` | theorem | 95 | 7 |  |
| `heckeDiagMatrix_mul_T` | theorem | 102 | 12 |  |
| `periodic_of_slash_T` | theorem | 114 | 22 |  |
| `slash_heckeDiagMatrix_slash_T` | theorem | 136 | 6 |  |
| `isBoundedAtImInfty_slash_heckeMatrix` | theorem | 142 | 4 |  |
| `isBoundedAtImInfty_slash_heckeDiagMatrix` | theorem | 146 | 4 |  |
| `isBoundedAtImInfty_heckeU` | theorem | 150 | 9 |  |
| `mdifferentiable_heckeU` | theorem | 159 | 16 |  |
| `periodic_add_smul` | theorem | 175 | 8 |  |
| `periodic_smul` | theorem | 183 | 7 |  |
| `slash_eq_smul_prime` | theorem | 190 | 156 |  |
| `dd_pow` | theorem | 346 | 6 |  |
| `slash_pow_of_slash_eq_smul` | theorem | 352 | 7 |  |
| `exists_lift_slash_eq` | theorem | 359 | 36 |  |
| `main` | theorem | 395 | 30 |  |
| `solution` | theorem | 425 | 12 |  |
