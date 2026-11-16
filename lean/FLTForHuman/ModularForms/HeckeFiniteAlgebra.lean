/-
  The pin's conditional statements of the Hecke finiteness cluster, kept as a facade.

  Every declaration here is a one-line restatement of the unconditional theorem of the
  same subject in `HeckeFiniteness/`: the finiteness, freeness and span results hold in
  every weight and need no hypothesis at all. The pin states them under a full-rank
  hypothesis `HasIntegralStructure N k` (and `1 ≤ k`), and these are the names its still
  unported consumers arrive by — `exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis`,
  `heckeAlgebra.exists_mem_modPCusp_isModPEigen_of_ringHom`,
  `exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two`,
  `WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra`,
  `exists_isNormalizedEigenform_congruent_of_isMaximal`,
  `exists_isNormalizedEigenform_ker_le_of_isPrime`, `exists_isNormalizedEigenform_ker_of_isMaximal`,
  `goodEigensystemOccursAt_of_divisible`, `isResiduallyModularOfLevel_of_exitIdeal_ne_top`.

  Retire a declaration, with its two `spec-pin:` lines, once its last consumer is ported
  and retargeted to the unconditional theorem; delete the file when it is empty.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`.

  spec-pin: Theorems/Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean
  spec-pin: Theorems/Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean
  spec-pin: Theorems/Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean
  spec-pin: Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra_two.lean
  spec-pin: Theorems/Thm_CuspForm_fg_toSubmodule_heckeAlgebra.lean
  spec-pin: Theorems/Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean
  spec-pin: Theorems/Thm_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.lean
  spec-pin: P2M/Sol/S_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean
  spec-pin: P2M/Sol/S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean
  spec-pin: P2M/Sol/S_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean
  spec-pin: P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean
  spec-pin: P2M/Sol/S_CuspForm_fg_toSubmodule_heckeAlgebra.lean
  spec-pin: P2M/Sol/S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean
  spec-pin: P2M/Sol/S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.lean
-/
import FLTForHuman.ModularForms.HeckeFiniteness.Finiteness
import FLTForHuman.ModularForms.HeckeFiniteness.Eigenform
import FLTForHuman.ModularForms.HeckeFiniteness.Span

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace CuspForm

/-- Full rank plus vanishing on the lattice makes a `ℂ`-linear endomorphism zero. -/
theorem HasIntegralStructure.eq_zero_of_forall_mem_intLattice {N : ℕ} {k : ℤ}
    (hN : CuspForm.HasIntegralStructure N k)
    (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))
    (h : ∀ f ∈ CuspForm.intLattice N k, t f = 0) : t = 0 :=
  LinearMap.ext_on hN fun f hf ↦ by rw [LinearMap.zero_apply]; exact h f hf

/-- Full rank makes the Hecke algebra finite over `ℤ` (it is finite in every weight). -/
theorem HasIntegralStructure.moduleFinite_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ}
    (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N k S) :=
  _root_.CuspForm.moduleFinite_heckeAlgebra N k S

/-- Full rank makes the Hecke algebra free over `ℤ` (it is free in every weight). -/
theorem HasIntegralStructure.moduleFree_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ}
    (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) :
    Module.Free ℤ (CuspForm.heckeAlgebra N k S) :=
  _root_.CuspForm.moduleFree_heckeAlgebra N k S

/-- The `k = 2` case of finiteness. -/
theorem moduleFinite_heckeAlgebra_two (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S) :=
  _root_.CuspForm.moduleFinite_heckeAlgebra N 2 S

/-- The `k = 2` case of the `FG` form. -/
theorem fg_toSubmodule_heckeAlgebra (N : ℕ) [NeZero N] (S : Set ℕ) :
    (Subalgebra.toSubmodule (CuspForm.heckeAlgebra N 2 S)).FG :=
  _root_.CuspForm.toSubmodule_heckeAlgebra_fg N 2 S

/-- The eigenvector for a Hecke character (no hypothesis is needed: the lattice spans
the space in every weight). -/
theorem HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul {N : ℕ} [NeZero N] {k : ℤ}
    (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N k S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧
      ∀ t : CuspForm.heckeAlgebra N k S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f :=
  _root_.CuspForm.exists_ne_zero_forall_apply_eq_smul χ

/-- The character's eigenvalue system is a normalised eigenform. -/
theorem HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq {N : ℕ} [NeZero N]
    (hN : CuspForm.HasIntegralStructure N 2) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ModularFormClass.qCoeff f ℓ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        ModularFormClass.qCoeff f q = χ (CuspForm.heckeAlgebra.U hq hqN hqS) :=
  _root_.CuspForm.exists_isNormalizedEigenform_qCoeff_eq χ

end CuspForm

end
