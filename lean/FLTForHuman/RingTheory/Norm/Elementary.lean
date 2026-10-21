/-
  Elementary computations with the algebra norm: the norm of an element whose
  difference from `algebraMap R A μ` is nilpotent is `μ ^ finrank R A`; the norm on a
  product algebra is the product of the norms of the two components; and the norm of an
  element of a subsingleton algebra is `1`.

  The port of the pin leaves
  `Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap` (18 pin lines),
  `Algebra.norm_prod` (10) and `Algebra.norm_of_subsingleton` (6), statements from their
  `Theorems/` wrappers and proofs from the matching `P2M/Sol/S_…` files (pinned
  `aa2d8b3`).

  This module is the port's name for the block a mathlib PR would append to
  `Mathlib/RingTheory/Norm/Basic.lean`. The port may not add to mathlib, and
  `RingTheory/Norm/` is mathlib's home for `Algebra.norm`, so a reader looking for norm
  computations finds these here rather than in a bespoke directory.

  The mathematics: `Algebra.norm R a` is `LinearMap.det` of multiplication by `a`. On
  `A × B` that map is the `prodMap` of the two multiplications, and `det` is
  multiplicative on `prodMap`; on a subsingleton algebra it is the determinant of an
  endomorphism of a subsingleton module, which is `1`; and if `a - μ` is nilpotent then
  `lmul a` is `μ • 1 - (-(lmul (a - μ)))` with the second summand nilpotent, so its
  characteristic polynomial is `(X - μ) ^ finrank R A` and evaluating at `0` gives
  `μ ^ finrank R A`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): no name of the three pin files occurs in `Mathlib/`
  at `5ed29652` / `v4.34.0`. `Mathlib/RingTheory/Norm/` (`Basic`, `Defs`, `Transitivity`)
  has no `norm_prod` for the product algebra, no `norm_of_subsingleton` and no
  `IsNilpotent` lemma; the mathlib hits for those two names are the normed-group and
  normed-space lemmas — a different namespace with a different statement. The headline
  is stated at `Algebra.norm_of_subsingleton`, not at root: inside `namespace Algebra`
  the root-level normed-group `norm_of_subsingleton` stays visible, and a root-level
  redeclaration would merge with it silently.

  spec-pin: Theorems/Thm_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap.lean
  spec-pin: Theorems/Thm_Algebra_norm_prod.lean
  spec-pin: Theorems/Thm_Algebra_norm_of_subsingleton.lean
  spec-pin: P2M/Sol/S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap.lean
  spec-pin: P2M/Sol/S_Algebra_norm_prod.lean
  spec-pin: P2M/Sol/S_Algebra_norm_of_subsingleton.lean
-/
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange

set_option autoImplicit false

namespace Algebra

/-- If `a - algebraMap R A μ` is nilpotent, the norm of `a` is `μ ^ finrank R A`: the
characteristic polynomial of the nilpotent derivation is `X ^ finrank`. -/
theorem norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R]
    [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A}
    {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) :
    Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]

/-- The norm on a product algebra is the product of the norms of the components:
multiplication by `x` is the `prodMap` of the two multiplications. -/
theorem norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B]
    [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]

/-- The norm of an element of a subsingleton algebra is `1`: it is the determinant of an
endomorphism of a subsingleton module. -/
theorem norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

end Algebra
