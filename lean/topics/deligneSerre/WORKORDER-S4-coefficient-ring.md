# Work order — S4: coefficient ring and Galois conjugation (6 nodes)

**Status: ready to dispatch — H2, S1, S2 and S3 are closed and green (checker 2457/0/0).**
Method handbook: `lean/porting-playbook.md` (§2.4, §3.1–§3.5, §4). Mathematics: `math/019`
§3 (the coefficient ring).

## 0. Scope

The finiteness of the coefficient ring of a weight-one newform and the Galois
action on weight-one newforms. Five of the six nodes are **generic algebra**
(the pin's `DeligneSerre.` prefix on one of them is incidental); only
`DeligneSerre.exists_subalgebra_qCoeff_mem_…` is weight-one specific.

**Dependencies.** S4b–S4f are generic algebra, independent of S1–S3. S4a's pin file
uses the Hecke prelude (`periodic_of_slash_T`, `cusp_bdd`, `cusp_holo`,
`cusp_periodic`, `T_pow_mem_Gamma1`), so it needs the H1
`ModularForms/HeckePrelude.lean` and the H2 reconciliation of `T_pow_mem_Gamma1`
(ℕ-indexed pin spelling). Dispatch only after H2 is closed.

**Explicitly not this set:** S5–S8, the Hecke vanishing (S2), the lifting (S3).

## 1. The six public targets — statements verbatim from the pin wrappers

```lean
theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y
```

```lean
theorem Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam))
```

```lean
theorem Module.Basis.repr_mem_range_ratCast_of_forall_dual
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ)
```

```lean
theorem Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J) (i i' : ι), b.repr (S j (b i)) i' ∈ Set.range ((↑) : ℚ → ℂ))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ i : ι, ℓ (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (lam : J → ℂ) (v : V) (hv : ∀ j : J, S j v = lam j • v) (hℓv : ℓ v ≠ 0)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (hR : ∀ j : J, lam j ∈ R) (τ : R →+* ℂ) :
    ∃ w : V, ℓ w ≠ 0 ∧ ∀ j : J, S j w = τ ⟨lam j, hR j⟩ • w
```

```lean
theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x
```

```lean
theorem DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ R : Subalgebra ℤ ℂ, Module.Finite ℤ R ∧
      ∃ (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
        (hε : ∀ x : ZMod N, ε x ∈ R),
      ∀ τ : R →+* ℂ, ∃ (ε' : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) 1),
        (∀ x : ZMod N, ε' x = τ ⟨ε x, hε x⟩) ∧
        ModularFormClass.qCoeff g 1 = 1 ∧
        (∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
          ModularFormClass.qCoeff g p = τ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              ε' (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n
```

## 2. Homes and order

Leaves first, then the two `DeligneSerre` conclusions:

| order | node | home |
|---:|---|---|
| 1 | `Module.Basis.repr_mem_range_ratCast_of_forall_dual` | `Algebra/LatticeEigenvalues.lean` (new) |
| 2 | `Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast` | `Algebra/LatticeEigenvalues.lean` |
| 3 | `Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top` | `Algebra/LatticeEigenvalues.lean` |
| 4 | `integralClosure.exists_complex_ringEquiv_apply_eq` | `Algebra/IntegralExtensionCharacters.lean` (extend) |
| 5 | `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul` | `Algebra/FaithfulLatticeEigenvector.lean` (extend) |
| 6 | `DeligneSerre.exists_subalgebra_qCoeff_mem_…` | `DeligneSerre/CoefficientRing.lean` (new) |

The last node keeps the pin's `DeligneSerre.*` namespace; the generic five keep the
pin's `integralClosure`/`Submodule`/`Module.Basis`/`DeligneSerre` names (the
`DeligneSerre.*` prefix on node 5 is the pin's, not a signal of DS-specific
mathematics — home it with the algebra it belongs to).

## 3. Reuse and risk

- **S3 already carries a private copy of node 5.** `DeligneSerre/Relevement.lean`
  transcribes `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul`
  as `private exists_eigenvector_minimalPrimes_aux` (~113 lines, at the pin
  statement) because the relèvement needed it before S4. Port the **public** version
  here into `Algebra/FaithfulLatticeEigenvector.lean` (do not re-prove from scratch);
  the refactor round then points `Relevement.lean` at it and deletes the private copy.
- **S3 also ported `locKer` and `adjoinRoot'` public** in
  `DeligneSerre/Lifting.lean` (checker-verified). If node 6 needs them, import them;
  the refactor round may move them to `DeligneSerre/CoefficientRing.lean`.
- **Existing engines:** `Algebra/IntegralExtensionCharacters.lean` already has
  `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` and
  `Ideal.exists_ringHom_integralClosure_ker_eq`; `Algebra/FaithfulLatticeEigenvector.lean`
  has `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom` plus the private
  `engine3`/`engine4`/`engine5a`. `#check` these first: the S4 statements may follow
  from them with a thin wrapper, or need the engines generalised rather than copied.
- **S4a** imports the H1 `ModularForms/HeckePrelude.lean` and
  `ModularForms/Defs/PrimitiveFormGamma1.lean`; its `T_pow_mem_Gamma1` comes from the
  H2-reconciled `ModularForms/WeightOne/Defs/GammaRational.lean` (ℕ index).
- **Route:** generic algebra; mathlib has `Ideal.minimalPrimes`, `IsAlgClosed`,
  `Module.Finite`, `Algebra.adjoin`, `Module.Basis.repr`, `Subalgebra`. Record a
  negative for any search that finds nothing.
- Risk: node 3's lattice/eigenvalue finiteness is the substantive step; node 6 is a
  long assembly (491 pin lines) but should be glue over 1–5 once they land.

## 4. Verification, build discipline, closing

As `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands.

---

## Appendix — per-file pin declaration inventory

#### S4a — pin `P2M/Sol/S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean` (491 lines, 45 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `T_pow_mem_Gamma1` | theorem | 32 | 4 |  |
| `periodic_of_slash_T` | theorem | 36 | 26 |  |
| `cusp_slash_T` | theorem | 62 | 5 |  |
| `cusp_periodic` | theorem | 67 | 3 |  |
| `cusp_holo` | theorem | 70 | 3 |  |
| `cusp_bdd` | theorem | 73 | 6 |  |
| `cusp_analytic` | theorem | 79 | 5 |  |
| `qCoeff_add` | theorem | 84 | 5 |  |
| `qCoeff_smul` | theorem | 89 | 4 |  |
| `qcLin` | def | 93 | 7 |  |
| `qCoeff_zero_fun` | theorem | 100 | 3 |  |
| `eq_zero_of_forall_qCoeff` | theorem | 103 | 7 |  |
| `eq_of_forall_qCoeff` | theorem | 110 | 9 |  |
| `IntegralQExp` | def | 119 | 2 |  |
| `integralQExp_zero` | theorem | 121 | 2 |  |
| `IntegralQExp.add` | theorem | 123 | 5 |  |
| `IntegralQExp.zsmul` | theorem | 128 | 6 |  |
| `coe_slashOf` | theorem | 134 | 5 |  |
| `latt` | def | 139 | 19 |  |
| `mem_latt` | theorem | 158 | 3 |  |
| `integralQExp_of_mem_latt` | theorem | 161 | 4 |  |
| `intCast_mem_range_ratCast` | theorem | 165 | 4 |  |
| `exists_finset_separating` | theorem | 169 | 23 |  |
| `intSub` | def | 192 | 2 |  |
| `mem_intSub` | theorem | 194 | 6 |  |
| `latt_fg` | theorem | 200 | 31 |  |
| `slashOf_mem_latt` | theorem | 231 | 6 |  |
| `diamond_mem_latt` | theorem | 237 | 9 |  |
| `qCoeff_hecke` | theorem | 246 | 6 |  |
| `hecke_mem_latt` | theorem | 252 | 14 |  |
| `latt_span` | theorem | 266 | 8 |  |
| `coprime_of_prime` | theorem | 274 | 11 |  |
| `slash_eq_smul` | theorem | 285 | 7 |  |
| `diamond_apply_eq` | theorem | 292 | 10 |  |
| `hecke_apply_eq` | theorem | 302 | 14 |  |
| `Idx` | def | 316 | 4 |  |
| `opFam` | def | 320 | 6 |  |
| `evFam` | def | 326 | 4 |  |
| `opFam_mem_latt` | theorem | 330 | 6 |  |
| `opFam_apply_eq` | theorem | 336 | 14 |  |
| `evFam_inr_of_coprime` | theorem | 350 | 6 |  |
| `dirichlet_mem_adjoin` | theorem | 356 | 9 |  |
| `repr_opFam_mem_range` | theorem | 365 | 8 |  |
| `main` | theorem | 373 | 99 |  |
| `solution` | theorem | 472 | 20 |  |

#### S4b — pin `P2M/Sol/S_integralClosure_exists_complex_ringEquiv_apply_eq.lean` (277 lines, 16 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_ringEquiv_comp_eq` | theorem | 11 | 42 |  |
| `splits_map_int` | theorem | 53 | 16 |  |
| `range_eq_setOf_isIntegral` | theorem | 69 | 24 |  |
| `isAlgClosure_rat` | theorem | 93 | 3 |  |
| `isFractionRing_aux` | theorem | 96 | 8 |  |
| `core` | theorem | 104 | 82 |  |
| `Qbar` | abbrev | 186 | 2 |  |
| `Zbar` | abbrev | 188 | 2 |  |
| `mem_Qbar_of_mem_Zbar` | theorem | 190 | 6 |  |
| `zbarToQbar` | def | 196 | 15 |  |
| `isIntegralClosure_Zbar_Qbar` | theorem | 211 | 15 |  |
| `isAlgClosed_Qbar` | theorem | 226 | 2 |  |
| `isAlgebraic_Qbar` | theorem | 228 | 5 |  |
| `exists_ringEquiv_extend` | theorem | 233 | 22 |  |
| `main` | theorem | 255 | 19 |  |
| `solution` | theorem | 274 | 4 |  |

#### S4c — pin `P2M/Sol/S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean` (163 lines, 16 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `isAddTorsionFree_submodule` | theorem | 13 | 12 |  |
| `moduleFinite_end` | theorem | 25 | 7 |  |
| `opAlg` | def | 32 | 3 |  |
| `opAlg_preserves` | theorem | 35 | 14 |  |
| `res` | def | 49 | 6 |  |
| `res_apply` | theorem | 55 | 4 |  |
| `res_injective` | theorem | 59 | 10 |  |
| `moduleFinite_opAlg` | theorem | 69 | 7 |  |
| `eigAlg` | def | 76 | 13 |  |
| `mem_eigAlg` | theorem | 89 | 2 |  |
| `ev` | def | 91 | 2 |  |
| `ev_spec` | theorem | 93 | 2 |  |
| `ev_unique` | theorem | 95 | 6 |  |
| `evHom` | def | 101 | 11 |  |
| `main` | theorem | 112 | 45 |  |
| `solution` | theorem | 157 | 7 |  |

#### S4d — pin `P2M/Sol/S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean` (144 lines, 2 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul_impl` | theorem | 18 | 116 |  |
| `solution` | theorem | 134 | 11 |  |

#### S4e — pin `P2M/Sol/S_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean` (143 lines, 4 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_sum_smul_eq_of_algebraMap` | theorem | 11 | 52 |  |
| `exists_finset_separating` | theorem | 63 | 15 |  |
| `main` | theorem | 78 | 58 |  |
| `solution` | theorem | 136 | 8 |  |

#### S4f — pin `P2M/Sol/S_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean` (131 lines, 5 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_ringEquiv_apply_eq` | theorem | 13 | 42 |  |
| `ringEquiv_ratCast` | theorem | 55 | 3 |  |
| `ringEquiv_of_mem_range` | theorem | 58 | 5 |  |
| `main` | theorem | 63 | 60 |  |
| `solution` | theorem | 123 | 9 |  |
