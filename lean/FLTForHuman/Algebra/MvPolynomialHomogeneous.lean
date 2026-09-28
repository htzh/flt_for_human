/-
  Iterated partial derivatives of a homogeneous `MvPolynomial`.

  `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt`: a homogeneous
  polynomial of degree `n` is killed by `i > n` iterated partial derivatives.
  Generic algebra — mathlib `v4.34.0` has `MvPolynomial.IsHomogeneous.pderiv`
  but not the iterated vanishing. Used by the Eichler–Shimura period map
  (`FLTForHuman/ModularForms/EichlerShimura/PeriodMap.lean`) to kill the high
  `∂₁` iterates of a binary form.

  FLT provenance, pinned `aa2d8b3`:
  * `Theorems/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`
  * `P2M/Sol/S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`

  Public source:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean>.
-/
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! ## 1. Iterated partial derivatives of a homogeneous polynomial -/

/-- A homogeneous polynomial of degree `n` stays homogeneous of degree `n - j`
after `j` partial derivatives. Helper for
`MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt`. -/
private theorem mvPolynomial_isHomogeneous_iterate_pderiv {σ R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} {n : ℕ} (k : σ) (hφ : φ.IsHomogeneous n) (j : ℕ) :
    ((MvPolynomial.pderiv k)^[j] φ).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

/-- A homogeneous polynomial of degree `n` is killed by `i > n` iterated partial
derivatives. FLT `aa2d8b3`, `Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt`. -/
theorem MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) : (MvPolynomial.pderiv k)^[i] φ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show n + m + 1 = m + 1 + n by ring, Function.iterate_add_apply, Function.iterate_succ_apply]
  have h0 : ((MvPolynomial.pderiv k)^[n] φ).IsHomogeneous 0 := by
    simpa using mvPolynomial_isHomogeneous_iterate_pderiv k hφ n
  have hC : (MvPolynomial.pderiv k)^[n] φ = MvPolynomial.C (((MvPolynomial.pderiv k)^[n] φ).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h0.totalDegree_le)
  rw [hC, MvPolynomial.pderiv_C]
  exact Function.iterate_fixed (map_zero _) m
