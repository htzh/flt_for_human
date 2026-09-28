/-
Copyright (c) 2026 FLT-for-human contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT-for-human contributors
-/

import FLTForHuman.Algebra.MvPolynomialHomogeneous
import FLTForHuman.ModularForms.Analytic.CuspBoundedness
import FLTForHuman.ModularForms.Analytic.StarConvexPrimitive
import FLTForHuman.ModularForms.EichlerShimura.BinaryForm
import FLTForHuman.ModularForms.EichlerShimura.CoeffCohomology
import FLTForHuman.ModularForms.EichlerShimura.EichlerIntegral
import FLTForHuman.ModularForms.ModularGroup
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.NumberTheory.Modular
import Mathlib.Tactic

/-!
# The general-weight Eichler–Shimura period map and its injectivity

## Subject

For every level `N ≥ 1` and weight `k = n + 2`, this module builds the
`ℂ`-linear **period map**

`periodMap n N : CuspForm (Γ₀ N) ((n : ℤ) + 2) →ₗ[ℂ] coeffH1par ((binaryFormRepSL ℂ n).comp (Γ₀ N).subtype)`

sending a cusp form to the parabolic cohomology class of the period cocycle of an
Eichler integral, and proves it **injective**:

`theorem periodMap_injective (n N : ℕ) [NeZero N] : Function.Injective (periodMap n N)`.

This is Tier 3 of the port plan
[`topics/eichlerShimura/TOPIC-period-map-injectivity.md`](../../../topics/eichlerShimura/TOPIC-period-map-injectivity.md):
the analytic chain (`hasDerivAt_eval_iterate_pderiv`, `eq_zero_of_eval_eq_const`,
`isBoundedAtImInfty_eval`), the existence and parabolicity of an Eichler integral
(`exists_isEichlerIntegral`, `isEquivariantPrimitiveWith_of_isEichlerIntegral`,
`vadd_sub_T_zpow_apply_mem_range`,
`isParabolicCocycle_cocycle_of_isEichlerIntegral`,
`exists_isEichlerIntegral_isParabolicCocycle`), and the structural period map.

## FLT source and pin

Pin `aa2d8b3`. Statement authority is the `Theorems/` wrapper; the proof body was
read from the matching `P2M/Sol/S_*.lean` node:

* `Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv` /
  `S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv`
* `Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const` /
  `S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const`
* `Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval` /
  `S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval`
* `Thm_HeckeEis_exists_isEichlerIntegral` /
  `S_HeckeEis_exists_isEichlerIntegral`
* `Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral` /
  `S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral`
* `Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range` /
  `S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range`
* `Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral` /
  `S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral`
* `Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle` /
  `S_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle`
* `S_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk`,
  `S_HeckeEis_eichlerShimuraMap_add`, `S_HeckeEis_eichlerShimuraMap_smul`,
  `S_HeckeEis_existsEichlerShimuraMapLinear`,
  `S_HeckeEis_eichlerShimuraMap_injective`.

Public sources (e.g.)
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_HeckeEis_eichlerShimuraMap_injective.lean>.

## Recorded divergence from the pin (playbook §7.4)

The pin defines `eichlerShimuraMap` on `f : ℍ → ℂ` by a `dif` on the existence of
an Eichler integral admitting an equivariant primitive with parabolic cocycle,
falling back to `0`, and derives linearity by a case split
(`eichlerShimuraMap_add`, `eichlerShimuraMap_smul`,
`existsEichlerShimuraMapLinear`, `eichlerShimuraMap_def`,
`eichlerShimuraMap_of_not_exists`). **The port does not mirror this.** It defines
`periodMap` directly on cusp forms from a chosen Eichler integral
(`Classical.choose` of `exists_isEichlerIntegral_isParabolicCocycle`), proves the
resulting class independent of the choice through
`IsEichlerIntegral.exists_sub_eq_const` and
`IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries`, and builds
the linear map structurally. Consequently the pin's `eichlerShimuraMap`,
`eichlerShimuraMap_def`, `eichlerShimuraMap_of_not_exists`, `eichlerShimuraMap_add`,
`eichlerShimuraMap_smul` and `existsEichlerShimuraMapLinear` are deliberately
absent; `periodMap_eq_coeffH1parMk` is the counterpart of
`eichlerShimuraMap_eq_coeffH1parMk`, and injectivity is stated for the linear map.

## What this module assumes

The Tier 1–2 modules `BinaryForm.lean`, `CoeffCohomology.lean` and
`EichlerIntegral.lean`, plus the four generic facts now kept in their subject
homes: `FLTForHuman/Algebra/MvPolynomialHomogeneous.lean`,
`ModularForms/Analytic/StarConvexPrimitive.lean`,
`ModularForms/Analytic/CuspBoundedness.lean` and `ModularForms/ModularGroup.lean`.
Then mathlib's modular-forms layer (`CuspForm`, congruence subgroups, slash
actions, q-expansions and `NormTrace` for the negative-weight vanishing used by
the injectivity proof). Nothing else from `FLTForHuman`.

## Adaptation notes (mathlib `v4.34.0`)

* `MvPolynomial.coeff` is not a usable qualified name; the pin's
  `MvPolynomial.coeff d p` is written `p.coeff d` (as in the Tier 1–2 modules).
* `CuspForm.coe_add` / `CuspForm.coe_smul` are deprecated aliases in `v4.34.0`;
  the proofs use `FunLike.coe_add` / `FunLike.coe_smul`.
* `MvPolynomial.monomial_mul` is deprecated; the proof uses
  `MvPolynomial.monomial_mul_monomial`.
* The pin's local `iterate_pderiv_one_eq_zero_of_lt` is not re-derived: the
  public `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` from
  `FLTForHuman/Algebra/MvPolynomialHomogeneous.lean` is used (playbook §9).
-/

noncomputable section

open UpperHalfPlane MvPolynomial Function Filter CongruenceSubgroup
open scoped MatrixGroups Manifold Topology ModularForm Polynomial

namespace HeckeEis

/-- Monomorphic form of the (function-level) `AddMonoidAlgebra.coeff_add`, so that
`rw`/`simp` can split the coefficient of a sum at a fixed exponent. -/
private theorem pm_coeff_add {K : Type*} [CommRing K] (d : Fin 2 →₀ ℕ)
    (p q : MvPolynomial (Fin 2) K) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  rw [AddMonoidAlgebra.coeff_add]
  rfl

/-! ## A. The analytic chain -/

/-! ### A.1 The iterated `∂₁` identity

FLT `aa2d8b3`, `Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv`. -/

private theorem pm_coeff_pderiv_one {K : Type*} [CommRing K] (P : MvPolynomial (Fin 2) K)
    (d : Fin 2 →₀ ℕ) :
    (MvPolynomial.pderiv 1 P).coeff d
      = ((d 1 + 1 : ℕ) : K) * P.coeff (d + Finsupp.single 1 1) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s = d + Finsupp.single 1 1
    · subst hs
      simp only [add_tsub_cancel_right, ↓reduceIte, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · rw [ite_eq_right hs, mul_zero]
      split_ifs with h
      · have hs1 : s 1 = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          ext i
          fin_cases i
          · simp
          · simp only [Fin.mk_one, Fin.isValue, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]
            omega
        simp [hs1]
      · rfl
  | add p q hp hq =>
    rw [map_add, pm_coeff_add, pm_coeff_add, hp, hq, mul_add]

private theorem pm_coeff_iterate_pderiv_one {K : Type*} [CommRing K] (P : MvPolynomial (Fin 2) K)
    (j : ℕ) (d : Fin 2 →₀ ℕ) :
    ((MvPolynomial.pderiv 1)^[j] P).coeff d
      = ((d 1 + j).descFactorial j : K) * P.coeff (d + Finsupp.single 1 j) := by
  induction j generalizing d with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', pm_coeff_pderiv_one, ih]
    have e1 : d + Finsupp.single 1 1 + Finsupp.single 1 j = d + Finsupp.single 1 (j + 1) := by
      rw [add_assoc, ← Finsupp.single_add, add_comm 1 j]
    have e2 : ((d 1 + 1 : ℕ) : K) * ((((d + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 + j).descFactorial j : ℕ) : K)
        = (((d 1 + (j + 1)).descFactorial (j + 1) : ℕ) : K) := by
      rw [← Nat.cast_mul]
      congr 1
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      rw [show d 1 + (j + 1) = d 1 + 1 + j by ring, Nat.descFactorial_succ, Nat.add_sub_cancel]
    rw [e1, ← mul_assoc, e2]

private theorem pm_isHomogeneous_iterate_pderiv {K : Type*} [CommRing K] {σ : Type*} {P : MvPolynomial σ K}
    {n : ℕ} (i : σ) (hP : P.IsHomogeneous n) (j : ℕ) :
    ((MvPolynomial.pderiv i)^[j] P).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hP
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

private abbrev pm_ex (n m : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (n - m) + Finsupp.single 1 m

@[simp] private theorem pm_ex_zero (n m : ℕ) : pm_ex n m 0 = n - m := by
  simp [pm_ex]

@[simp] private theorem pm_ex_one (n m : ℕ) : pm_ex n m 1 = m := by
  simp [pm_ex]

private theorem pm_eq_ex_of_degree {m : ℕ} {d : Fin 2 →₀ ℕ} (hd : d.degree = m) :
    d = pm_ex m (d 1) := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
  ext i
  fin_cases i
  · simp; omega
  · simp

private theorem pm_eval_one_eq_sum {K : Type*} [CommRing K] {m : ℕ} {Q : MvPolynomial (Fin 2) K}
    (hQ : Q.IsHomogeneous m) (w : K) :
    eval ![1, w] Q = ∑ k ∈ Finset.range (m + 1), Q.coeff (pm_ex m k) * w ^ k := by
  classical
  have hF : ∀ d : Fin 2 →₀ ℕ, Q.coeff d * ∏ i, (![1, w] : Fin 2 → K) i ^ d i = Q.coeff d * w ^ (d 1) := by
    intro d
    simp [Fin.prod_univ_two]
  rw [eval_eq', Finset.sum_congr rfl (fun d _ => hF d)]
  have hinj : Set.InjOn (pm_ex m) (Finset.range (m + 1) : Set ℕ) := by
    intro a _ b _ h
    have := congrArg (fun f => f 1) h
    simpa using this
  rw [show (∑ k ∈ Finset.range (m + 1), Q.coeff (pm_ex m k) * w ^ k)
      = ∑ d ∈ (Finset.range (m + 1)).image (pm_ex m), Q.coeff d * w ^ (d 1) by
    rw [Finset.sum_image hinj]
    simp]
  apply Finset.sum_subset
  · intro d hd
    have hdeg : d.degree = m := by
      by_contra hc
      exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero hc)
    rw [Finset.mem_image]
    refine ⟨d 1, ?_, (pm_eq_ex_of_degree hdeg).symm⟩
    rw [Finset.mem_range, Finsupp.degree_eq_sum, Fin.sum_univ_two] at *
    omega
  · intro d _ hd
    rw [notMem_support_iff.mp hd, zero_mul]

private theorem pm_eval_iterate_pderiv_eq_sum {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P.IsHomogeneous n) (i : ℕ) (w : K) :
    eval ![1, w] ((MvPolynomial.pderiv 1)^[i] P)
      = ∑ k ∈ Finset.range (n + 1 - i),
          ((k + i).descFactorial i : K) * P.coeff (pm_ex n (k + i)) * w ^ k := by
  rcases Nat.lt_or_ge n i with hi | hi
  swap
  · rw [pm_eval_one_eq_sum (pm_isHomogeneous_iterate_pderiv 1 hP i), show n + 1 - i = n - i + 1 by omega]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [pm_coeff_iterate_pderiv_one, pm_ex_one]
    have hex : pm_ex (n - i) k + Finsupp.single 1 i = pm_ex n (k + i) := by
      ext t
      fin_cases t
      · simp [pm_ex]; omega
      · simp [pm_ex]
    rw [hex]
  · rw [MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt hP 1 hi, map_zero,
      show n + 1 - i = 0 by omega, Finset.range_zero, Finset.sum_empty]

private theorem pm_coeff_ex_linePow {K : Type*} [CommRing K] (n m : ℕ) (hm : m ≤ n) (t : K) :
    ((C t * X 0 + X 1) ^ n : MvPolynomial (Fin 2) K).coeff (pm_ex n m)
      = (n.choose m : K) * t ^ (n - m) := by
  classical
  rw [add_pow, coeff_sum]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((C t * X 0) ^ k * X 1 ^ (n - k) * (n.choose k : MvPolynomial (Fin 2) K)).coeff (pm_ex n m)
        = if k = n - m then (n.choose m : K) * t ^ (n - m) else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hmon : (C t * X 0) ^ k * X 1 ^ (n - k) * (n.choose k : MvPolynomial (Fin 2) K)
        = monomial (Finsupp.single 0 k + Finsupp.single 1 (n - k)) (t ^ k * (n.choose k : K)) := by
      rw [mul_pow, ← map_pow, X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial,
        ← map_natCast C, mul_comm (monomial _ _) (C _), C_mul_monomial]
      congr 1; simp [mul_comm]
    rw [hmon, coeff_monomial]
    by_cases hk' : k = n - m
    · subst hk'
      have hcond : Finsupp.single 0 (n - m) + Finsupp.single 1 (n - (n - m)) = pm_ex n m := by
        ext i; fin_cases i <;> simp [pm_ex]; omega
      rw [ite_eq_left hcond, ite_eq_left rfl, Nat.choose_symm hm, mul_comm]
    · have hcond : ¬ (Finsupp.single 0 k + Finsupp.single 1 (n - k) = pm_ex n m) := by
        intro h
        apply hk'
        have := congrArg (fun f => f 0) h
        simp [pm_ex] at this
        omega
      rw [ite_eq_right hcond, ite_eq_right hk']
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (n + 1)) (n - m),
    ite_eq_left (Finset.mem_range.mpr (by omega))]

private theorem pm_sum_descFactorial_mul_choose_mul_neg_one_pow {K : Type*} [CommRing K]
    (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1 - j),
        (((k + j).descFactorial j : ℕ) : K) * ((n.choose (k + j) : ℕ) : K) * (-1 : K) ^ k
      = if j = n then ((n.factorial : ℕ) : K) else 0 := by
  have hkey : ∀ k : ℕ, (k + j).descFactorial j * n.choose (k + j) = n.descFactorial j * (n - j).choose k := by
    intro k
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose, mul_assoc, mul_assoc,
      mul_comm ((k + j).choose j), Nat.choose_mul (Nat.le_add_left j k), Nat.add_sub_cancel]
  have hcast : ∀ k : ℕ, (((k + j).descFactorial j : ℕ) : K) * ((n.choose (k + j) : ℕ) : K)
      = ((n.descFactorial j : ℕ) : K) * ((n - j).choose k : K) := by
    intro k
    have := congrArg (Nat.cast (R := K)) (hkey k)
    push_cast at this
    exact this
  simp_rw [hcast, mul_assoc, ← Finset.mul_sum]
  have halt : ∑ k ∈ Finset.range (n + 1 - j), ((n - j).choose k : K) * (-1 : K) ^ k
      = if n - j = 0 then 1 else 0 := by
    have h := (Int.alternating_sum_range_choose (n := n - j))
    rw [show n + 1 - j = n - j + 1 by omega]
    have : (∑ k ∈ Finset.range (n - j + 1), ((n - j).choose k : K) * (-1 : K) ^ k)
        = ((∑ m ∈ Finset.range (n - j + 1), (-1 : ℤ) ^ m * ((n - j).choose m : ℤ) : ℤ) : K) := by
      push_cast
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h]
    split_ifs <;> simp
  rw [halt]
  by_cases hjn : j = n
  · subst hjn; simp [Nat.descFactorial_self]
  · rw [ite_eq_right (by omega), ite_eq_right hjn, mul_zero]

theorem IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {j : ℕ}
    (hj : j ≤ n) (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => MvPolynomial.eval ![(1 : ℂ), -z]
        ((MvPolynomial.pderiv 1)^[j]
          ((G (UpperHalfPlane.ofComplex z) : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)
        - MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
          ((MvPolynomial.pderiv 1)^[j + 1] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      (τ : ℂ) := by

  have hhom : ∀ σ : ℍ, ((G σ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).IsHomogeneous n := fun σ =>
    (mem_homogeneousSubmodule n _).mp (G σ).2

  set c : ℕ → ℂ → ℂ := fun m z => ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff (pm_ex n m)
    with hcdef
  have hc : ∀ m, m ≤ n → HasDerivAt (c m) (g τ * ((n.choose m : ℂ) * (τ : ℂ) ^ (n - m))) (τ : ℂ) := by
    intro m hm
    have h := hG (pm_ex n m) τ
    rw [coe_linePow, pm_coeff_ex_linePow n m hm] at h
    exact h

  have hfun : (fun z : ℂ => MvPolynomial.eval ![(1 : ℂ), -z]
        ((MvPolynomial.pderiv 1)^[j] ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      = fun z : ℂ => ∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ) * c (k + j) z * (-z) ^ k := by
    funext z
    rw [pm_eval_iterate_pderiv_eq_sum (hhom (ofComplex z)) j (-z)]
  rw [hfun]

  have hsum : HasDerivAt (fun z : ℂ => ∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ) * c (k + j) z * (-z) ^ k)
      (∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ)
        * (g τ * ((n.choose (k + j) : ℂ) * (τ : ℂ) ^ (n - (k + j))) * (-(τ : ℂ)) ^ k
            + c (k + j) τ * ((k : ℂ) * (-(τ : ℂ)) ^ (k - 1) * (-1)))) (τ : ℂ) := by
    rw [show (fun z : ℂ => ∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ) * c (k + j) z * (-z) ^ k)
        = ∑ k ∈ Finset.range (n + 1 - j), ((fun z : ℂ => ((k + j).descFactorial j : ℂ) * c (k + j) z * (-z) ^ k) : ℂ → ℂ) from
      (Finset.sum_fn (Finset.range (n + 1 - j)) _).symm]
    apply HasDerivAt.sum
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 := hc (k + j) (by omega)
    have h2 : HasDerivAt (fun z : ℂ => (-z) ^ k) ((k : ℂ) * (-(τ : ℂ)) ^ (k - 1) * (-1)) (τ : ℂ) :=
      (hasDerivAt_neg' (τ : ℂ)).pow k
    have h3 := (h1.mul h2).const_mul ((k + j).descFactorial j : ℂ)
    have hcofc : c (k + j) (τ : ℂ) = c (k + j) τ := rfl
    simpa [mul_assoc, ofComplex_apply] using h3
  refine hsum.congr_deriv ?_

  rw [Finset.sum_congr rfl fun k _ => mul_add _ _ _, Finset.sum_add_distrib]

  have hA : ∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ)
        * (g τ * ((n.choose (k + j) : ℂ) * (τ : ℂ) ^ (n - (k + j))) * (-(τ : ℂ)) ^ k)
      = (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) := by
    calc _ = g τ * (τ : ℂ) ^ (n - j) * ∑ k ∈ Finset.range (n + 1 - j),
              ((k + j).descFactorial j : ℂ) * (n.choose (k + j) : ℂ) * (-1 : ℂ) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          rw [neg_pow, show n - j = (n - (k + j)) + k by omega, pow_add]
          ring
      _ = _ := by
          rw [pm_sum_descFactorial_mul_choose_mul_neg_one_pow n j hj]
          split_ifs with h
          · subst h
            rw [Nat.sub_self, pow_zero, mul_one, mul_comm]
          · rw [mul_zero]

  have hB : ∑ k ∈ Finset.range (n + 1 - j), ((k + j).descFactorial j : ℂ)
        * (c (k + j) τ * ((k : ℂ) * (-(τ : ℂ)) ^ (k - 1) * (-1)))
      = - MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
          ((MvPolynomial.pderiv 1)^[j + 1] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by
    rw [pm_eval_iterate_pderiv_eq_sum (hhom τ) (j + 1), show n + 1 - j = (n - j) + 1 by omega,
      Finset.sum_range_succ', show n + 1 - (j + 1) = n - j by omega]
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hcτ : c (k + 1 + j) (τ : ℂ) = ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff (pm_ex n (k + 1 + j)) := by
      simp only [hcdef, ofComplex_apply]
    have hidx : k + (j + 1) = k + 1 + j := by ring
    have hdesc : (((k + 1 + j).descFactorial (j + 1) : ℕ) : ℂ) = (((k + 1 + j).descFactorial j : ℕ) : ℂ) * ((k : ℂ) + 1) := by
      rw [Nat.descFactorial_succ, show k + 1 + j - j = k + 1 by omega]
      push_cast
      ring
    rw [hidx, hcτ, hdesc, Nat.add_sub_cancel]
    push_cast
    ring
  rw [hA, hB, sub_eq_add_neg]

/-! ### A.2 The ladder: vanishing from a constant top coefficient

FLT `aa2d8b3`, `Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const`. -/

private def pm_rung {n : ℕ} (G : ℍ → ↥(BinaryForm ℂ n)) (j : ℕ) (τ : ℍ) : ℂ :=
  MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
    ((MvPolynomial.pderiv 1)^[j] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))

private theorem pm_rung_zero {n : ℕ} (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) :
    pm_rung G 0 τ = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := rfl

private theorem pm_rung_succ_n {n : ℕ} (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) : pm_rung G (n + 1) τ = 0 := by
  rw [pm_rung, MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt ((mem_homogeneousSubmodule n _).mp (G τ).2) 1
    (Nat.lt_succ_self n), map_zero]

private theorem pm_hasDerivAt_rung {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) (τ : ℍ) :
    HasDerivAt (pm_rung G j ∘ ofComplex)
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - pm_rung G (j + 1) τ) (τ : ℂ) := by
  have h := hG.hasDerivAt_eval_iterate_pderiv hj τ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
  simp only [Function.comp_apply, pm_rung]
  rw [ofComplex_apply_of_im_pos hz]

private theorem pm_mdifferentiable_rung {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (pm_rung G j) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (pm_hasDerivAt_rung hG hj ⟨z, hz⟩).differentiableAt.differentiableWithinAt

private theorem pm_eq_zero_of_rung_zero_const {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hG : IsEichlerIntegral n g G) {c : ℂ} (hc : ∀ τ : ℍ, pm_rung G 0 τ = c) :
    ∀ τ : ℍ, g τ = 0 := by
  have hstep : ∀ j : ℕ, j ≤ n → (∃ c : ℂ, ∀ τ : ℍ, pm_rung G j τ = c) →
      ∀ τ : ℍ, (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - pm_rung G (j + 1) τ = 0 := by
    rintro j hj ⟨c', hc'⟩ τ
    have h1 := pm_hasDerivAt_rung hG hj τ
    have h2 : HasDerivAt (pm_rung G j ∘ ofComplex) 0 (τ : ℂ) := by
      refine (hasDerivAt_const (τ : ℂ) c').congr_of_eventuallyEq ?_
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
      simp only [Function.comp_apply]
      exact hc' _
    exact h1.unique h2
  have hconst : ∀ j : ℕ, j ≤ n → ∃ c : ℂ, ∀ τ : ℍ, pm_rung G j τ = c := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨c, hc⟩
    | succ j ih =>
      intro hj
      refine ⟨0, fun τ => ?_⟩
      have := hstep j (by omega) (ih (by omega)) τ
      rw [ite_eq_right (by omega), zero_sub, neg_eq_zero] at this
      exact this
  intro τ
  have := hstep n le_rfl (hconst n le_rfl) τ
  rw [ite_eq_left rfl, pm_rung_succ_n, sub_zero] at this
  have hn : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact (mul_eq_zero.mp this).resolve_left hn

theorem IsEichlerIntegral.eq_zero_of_eval_eq_const {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {c : ℂ}
    (hc : ∀ τ : UpperHalfPlane,
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = c) :
    g = 0 :=
  funext fun τ => pm_eq_zero_of_rung_zero_const hG hc τ

/-! ### A.3 Boundedness at the cusp of the top coefficient

FLT `aa2d8b3`, `Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval`. -/

private theorem pm_ofComplex_coe_add_real (τ : ℍ) (p : ℝ) : ofComplex ((τ : ℂ) + (p : ℂ)) = (p +ᵥ τ) := by
  have him : 0 < ((τ : ℂ) + (p : ℂ)).im := by simpa using τ.im_pos
  rw [ofComplex_apply_of_im_pos him]
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_vadd, add_comm]

section BoundedLadder

variable {h : ℤ}

private theorem pm_periodic_comp_ofComplex {φ : ℍ → ℂ} {p : ℝ} (hφ : ∀ τ : ℍ, φ (p +ᵥ τ) = φ τ) :
    Periodic (φ ∘ ofComplex) (p : ℂ) := by
  intro z
  simp only [Function.comp_apply]
  rcases lt_or_ge 0 z.im with hz | hz
  · rw [← hφ (ofComplex z), ← pm_ofComplex_coe_add_real (ofComplex z) p,
      ofComplex_apply_of_im_pos hz]
  · have hz' : (z + (p : ℂ)).im ≤ 0 := by simpa using hz
    rw [ofComplex_apply_of_im_nonpos hz', ofComplex_apply_of_im_nonpos hz]

private theorem pm_rung_zero_vadd {n : ℕ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) (τ : ℍ) :
    pm_rung G 0 ((h : ℝ) +ᵥ τ) = pm_rung G 0 τ := by
  rw [pm_rung_zero, pm_rung_zero, hT]
  have key := jFactor_pow_mul_eval_binaryFormRepSL n (ModularGroup.T ^ h) τ (G τ)
  have hj : jFactor (ModularGroup.T ^ h) τ = 1 := by
    simp [jFactor, ModularGroup.coe_T_zpow]
  rw [hj, one_pow, one_mul, UpperHalfPlane.modular_T_zpow_smul] at key
  simpa using key

private theorem pm_rung_vadd {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)} (hG : IsEichlerIntegral n g G)
    (hper : ∀ τ : ℍ, g ((h : ℝ) +ᵥ τ) = g τ)
    (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    ∀ j : ℕ, j ≤ n + 1 → ∀ τ : ℍ, pm_rung G j ((h : ℝ) +ᵥ τ) = pm_rung G j τ := by
  intro j
  induction j with
  | zero => exact fun _ τ => pm_rung_zero_vadd hT τ
  | succ j ih =>
    intro hj τ
    have hj' : j ≤ n := by omega
    have hperj : Periodic (pm_rung G j ∘ ofComplex) ((h : ℝ) : ℂ) := pm_periodic_comp_ofComplex (ih (by omega))
    have h1 : HasDerivAt (pm_rung G j ∘ ofComplex)
        ((if j = n then ((n.factorial : ℕ) : ℂ) * g ((h : ℝ) +ᵥ τ) else 0) - pm_rung G (j + 1) ((h : ℝ) +ᵥ τ))
        (τ : ℂ) := by
      have h0 := pm_hasDerivAt_rung hG hj' ((h : ℝ) +ᵥ τ)
      rw [UpperHalfPlane.coe_vadd, add_comm ((h : ℝ) : ℂ) (τ : ℂ)] at h0
      have h2 := h0.comp_add_const (τ : ℂ) ((h : ℝ) : ℂ)
      have hfun : (fun x : ℂ => (pm_rung G j ∘ ofComplex) (x + ((h : ℝ) : ℂ))) = pm_rung G j ∘ ofComplex :=
        funext hperj
      rwa [hfun] at h2
    have h3 := pm_hasDerivAt_rung hG hj' τ
    have h4 := h1.unique h3
    rw [hper τ] at h4
    have := congrArg (fun w => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - w) h4
    simpa using this

private theorem pm_isBoundedAtImInfty_rung_zero {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hG : IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) ((h : ℝ) : ℂ)) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hbdd : IsBoundedAtImInfty g)
    (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    IsBoundedAtImInfty (pm_rung G 0) := by
  have hh' : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hperℍ : ∀ τ : ℍ, g ((h : ℝ) +ᵥ τ) = g τ := by
    intro τ
    have := hper (τ : ℂ)
    simp only [Function.comp_apply] at this
    rw [pm_ofComplex_coe_add_real τ h, ofComplex_apply] at this
    exact this
  have hrper := pm_rung_vadd hG hperℍ hT

  have key : ∀ i : ℕ, i ≤ n + 1 → IsBoundedAtImInfty (pm_rung G (n + 1 - i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : pm_rung G (n + 1 - 0) = 0 := funext fun τ => by simpa using pm_rung_succ_n G τ
      rw [this]
      exact UpperHalfPlane.zero_form_isBoundedAtImInfty
    | succ i ih =>
      intro hi
      set j := n + 1 - (i + 1) with hjdef
      have hj : j ≤ n := by omega
      have hj1 : n + 1 - i = j + 1 := by omega
      have ih' : IsBoundedAtImInfty (pm_rung G (j + 1)) := by rw [← hj1]; exact ih (by omega)

      set u : ℍ → ℂ := fun τ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - pm_rung G (j + 1) τ with hu
      have hu_per : Periodic (u ∘ ofComplex) ((h : ℝ) : ℂ) := by
        apply pm_periodic_comp_ofComplex
        intro τ
        simp only [hu, hperℍ τ, hrper (j + 1) (by omega) τ]
      have hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u := by
        have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (pm_rung G (j + 1)) := by
          rcases eq_or_lt_of_le hj with hjn | hjn
          · have : pm_rung G (j + 1) = fun _ => 0 := funext fun τ => by rw [hjn]; exact pm_rung_succ_n G τ
            rw [this]; exact mdifferentiable_const
          · exact pm_mdifferentiable_rung hG (by omega)
        have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)) := by
          split_ifs
          · exact mdifferentiable_const.mul hhol
          · exact mdifferentiable_const
        exact h1.sub h2
      have hu_bdd : IsBoundedAtImInfty u := by
        have h1 : IsBoundedAtImInfty (fun τ : ℍ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)) := by
          split_ifs
          · exact hbdd.const_mul_left _
          · exact UpperHalfPlane.zero_form_isBoundedAtImInfty
        exact h1.sub ih'
      have hv : ∀ τ : ℍ, HasDerivAt (pm_rung G j ∘ ofComplex) (u τ) (τ : ℂ) := fun τ => pm_hasDerivAt_rung hG hj τ
      have hv_per : Periodic (pm_rung G j ∘ ofComplex) ((h : ℝ) : ℂ) :=
        pm_periodic_comp_ofComplex (hrper j (by omega))
      exact UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic hh' hu_per hu_hol hu_bdd hv hv_per
  simpa using key (n + 1) le_rfl

end BoundedLadder

theorem IsEichlerIntegral.isBoundedAtImInfty_eval {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) :=
  pm_isBoundedAtImInfty_rung_zero hG hh hper hhol hbdd hT

/-! ### A.4 Existence of an Eichler integral

FLT `aa2d8b3`, `Thm_HeckeEis_exists_isEichlerIntegral`. -/

private def pm_degExps (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

private theorem pm_mem_degExps_iff (n : ℕ) (d : Fin 2 →₀ ℕ) : d ∈ pm_degExps n ↔ d.degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [pm_degExps, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp
    omega
  · intro h
    refine ⟨d 0, by omega, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      omega

private def pm_linePowPoly (n : ℕ) : MvPolynomial (Fin 2) ℂ[X] :=
  (C Polynomial.X * X 0 + X 1) ^ n

private theorem pm_coeff_linePow_eq_eval (n : ℕ) (d : Fin 2 →₀ ℕ) (z : ℂ) :
    ((C z * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n).coeff d
      = Polynomial.eval z ((pm_linePowPoly n).coeff d) := by
  have h : ((C z * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n)
      = MvPolynomial.map (Polynomial.evalRingHom z) (pm_linePowPoly n) := by
    simp [pm_linePowPoly, MvPolynomial.map_X, MvPolynomial.map_C]
  rw [h, MvPolynomial.coeff_map]
  rfl

private def pm_assemble (n : ℕ) (g : (Fin 2 →₀ ℕ) → ℂ → ℂ) (τ : ℍ) : ↥(BinaryForm ℂ n) :=
  ⟨∑ d ∈ pm_degExps n, monomial d (g d (τ : ℂ)), Submodule.sum_mem _ fun d hd =>
    (mem_homogeneousSubmodule n _).mpr (isHomogeneous_monomial _ ((pm_mem_degExps_iff n d).mp hd))⟩

private theorem pm_coeff_assemble (n : ℕ) (g : (Fin 2 →₀ ℕ) → ℂ → ℂ) (τ : ℍ) (d : Fin 2 →₀ ℕ) :
    (pm_assemble n g τ : MvPolynomial (Fin 2) ℂ).coeff d = if d ∈ pm_degExps n then g d (τ : ℂ) else 0 := by
  show (∑ e ∈ pm_degExps n, monomial e (g e (τ : ℂ))).coeff d = _
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']

theorem exists_isEichlerIntegral (n : ℕ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F := by
  let U : Set ℂ := {z | 0 < z.im}
  have hU : IsOpen U := isOpen_upperHalfPlaneSet
  have hI : ((I : ℍ) : ℂ) ∈ U := (I : ℍ).im_pos
  have hstar : StarConvex ℝ ((I : ℍ) : ℂ) U := (convex_halfSpace_im_gt 0).starConvex hI
  have hfd : DifferentiableOn ℂ (f ∘ ofComplex) U := UpperHalfPlane.mdifferentiable_iff.mp hf
  have key : ∀ d : Fin 2 →₀ ℕ, ∃ g : ℂ → ℂ, ∀ z ∈ U,
      HasDerivAt g ((f ∘ ofComplex) z * Polynomial.eval z ((pm_linePowPoly n).coeff d)) z := by
    intro d
    obtain ⟨g, -, hg⟩ := Complex.exists_hasDerivAt_of_starConvex hU hI hstar
      (hfd.mul (Polynomial.differentiable ((pm_linePowPoly n).coeff d)).differentiableOn)
    exact ⟨g, hg⟩
  choose g hg using key
  refine ⟨pm_assemble n g, fun d τ => ?_⟩
  simp only [pm_coeff_assemble]
  by_cases hd : d ∈ pm_degExps n
  · simp only [ite_eq_left hd]
    have h2 : (f ∘ ofComplex) (τ : ℂ) * Polynomial.eval (τ : ℂ) ((pm_linePowPoly n).coeff d)
        = f τ * ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d := by
      rw [Function.comp_apply, ofComplex_apply, coe_linePow, pm_coeff_linePow_eq_eval]
    rw [← h2]
    refine (hg d (τ : ℂ) τ.im_pos).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds τ.im_pos] with z hz
    rw [ofComplex_apply_of_im_pos hz]
  · simp only [ite_eq_right hd]
    have h0 : ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d = 0 :=
      (isHomogeneous_linePow n τ).coeff_eq_zero (by rwa [pm_mem_degExps_iff] at hd)
    rw [h0, mul_zero]
    exact hasDerivAt_const _ _

/-! ### A.5 Equivariance of the primitive

FLT `aa2d8b3`, `Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral`. -/

theorem isEquivariantPrimitiveWith_of_isEichlerIntegral
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F := by
  intro γ
  have hslash := hF.slash (γ : SL(2, ℤ))
  rw [hf _ γ.2] at hslash
  obtain ⟨v, hv⟩ := hslash.exists_sub_eq_const hF
  refine ⟨binaryFormRepSL ℂ n (γ : SL(2, ℤ)) v, fun τ => ?_⟩
  change F ((γ : SL(2, ℤ)) • τ) - binaryFormRepSL ℂ n (γ : SL(2, ℤ)) (F τ) = _
  rw [← hv τ, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-! ### A.6 The value at `T^h` is a coboundary

FLT `aa2d8b3`, `Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range`. -/

private theorem pm_eval_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![0, 1] (binarySubst ℂ ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = MvPolynomial.eval ![0, 1] P := by
  have key : (fun j : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℂ) (![0, 1] : Fin 2 → ℂ)
      (∑ i : Fin 2, C ((((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) * X i))
      = (![0, 1] : Fin 2 → ℂ) := by
    funext j
    fin_cases j <;> simp [ModularGroup.coe_T_zpow, Fin.sum_univ_two]
  rw [binarySubst, MvPolynomial.aeval_eq_bind₁, MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁, key]

private theorem pm_coeff_single_one_binaryFormRepSL_T_zpow (n : ℕ) (h : ℤ) (P : ↥(BinaryForm ℂ n)) :
    ((binaryFormRepSL ℂ n (ModularGroup.T ^ h) P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff (Finsupp.single 1 n)
      = (P : MvPolynomial (Fin 2) ℂ).coeff (Finsupp.single 1 n) := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (binaryFormRepSL ℂ n _ P).2,
    coeff_single_one_eq_eval_of_mem_binaryForm P.2, binaryFormRepSL_apply_coe, pm_eval_binarySubst_T_zpow]

private theorem pm_coeff_single_one_linePow (n : ℕ) (z : ℂ) :
    ((linePow n z : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff (Finsupp.single 1 n) = 1 := by
  rw [coeff_single_one_eq_eval_of_mem_binaryForm (linePow n z).2, coe_linePow]
  simp

theorem IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range {n : ℕ} {h : ℤ} (hh : h ≠ 0)
    {g : UpperHalfPlane → ℂ} {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) (τ : UpperHalfPlane) :
    G ((h : ℝ) +ᵥ τ) - HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)
      ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) - 1) := by
  apply mem_range_binaryFormRepSL_T_zpow_sub_one n hh
  rw [Submodule.coe_sub, coeff_sub, pm_coeff_single_one_binaryFormRepSL_T_zpow, sub_eq_zero]
  set φ : ℂ → ℂ := fun z =>
    ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff (Finsupp.single 1 n) with hφdef
  have hφ : ∀ σ : ℍ, HasDerivAt φ (g σ) ↑σ := fun σ => by
    have := hG (Finsupp.single 1 n) σ
    rw [pm_coeff_single_one_linePow, mul_one] at this
    exact this
  suffices hs : φ ((((h : ℝ) +ᵥ τ : ℍ) : ℂ)) = φ (τ : ℂ) by
    simpa only [hφdef, ofComplex_apply] using hs
  rw [coe_vadd, add_comm]
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have hper' : Function.Periodic (g ∘ ofComplex) (((-h : ℤ) : ℝ) : ℂ) := by
      push_cast
      exact hper.neg
    have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((-h : ℤ) : ℝ))
      (by exact_mod_cast (neg_pos.mpr hneg)) hper' hhol hzero hφ ((h : ℝ) +ᵥ τ)
    rw [coe_vadd] at key
    push_cast at key ⊢
    have e : (h : ℂ) + (τ : ℂ) + -(h : ℂ) = (τ : ℂ) := by ring
    rw [e] at key
    rw [add_comm]
    exact key.symm
  · have key := UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty (h := ((h : ℤ) : ℝ))
      (by exact_mod_cast hpos) hper hhol hzero hφ τ
    push_cast at key ⊢
    exact key

/-! ### A.7 The period cocycle is parabolic

FLT `aa2d8b3`, `Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral`. -/

private theorem pm_periodic_slash_comp_ofComplex_of_conj_T_zpow_mem {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F' : Type*}
    [FunLike F' ℍ ℂ] [SlashInvariantFormClass F' (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F') (δ : SL(2, ℤ)) {h : ℤ}
    (hmem : δ * ModularGroup.T ^ h * δ⁻¹ ∈ Γ) :
    Function.Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) ((h : ℝ) : ℂ) := by
  refine SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ)) ?_
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hTh : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ h)
      = Matrix.GeneralLinearGroup.upperRightHom (h : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow, Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← hTh, ← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem _ hmem

private theorem pm_Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hA =>
  Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

theorem isParabolicCocycle_cocycle_of_isEichlerIntegral (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F) :
    HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by
  set ρ := (binaryFormRepSL ℂ n).comp (Gamma0 N).subtype with hρ
  set R := binaryFormRepSL ℂ n with hR
  have hρapp : ∀ γ : Gamma0 N, ρ γ = R (γ : SL(2, ℤ)) := fun γ => rfl
  have hneg1 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have hRinv : ∀ (x : SL(2, ℤ)) (v : ↥(BinaryForm ℂ n)), R x⁻¹ (R x v) = v := fun x v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hRinv' : ∀ (x : SL(2, ℤ)) (v : ↥(BinaryForm ℂ n)), R x (R x⁻¹ v) = v := fun x v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro γ hγ
  rcases Nat.even_or_odd n with heven | hodd
  ·
    obtain ⟨ε, δ, h, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
    have hRε : R ε = 1 := by
      rcases hε with rfl | rfl
      · exact map_one R
      · refine LinearMap.ext fun P => ?_
        rw [hR, binaryFormRepSL_neg_one_apply, Even.neg_one_pow heven, one_smul, Module.End.one_apply]
    have hRεx : ∀ x : SL(2, ℤ), R (ε * x) = R x := fun x => by rw [map_mul, hRε, one_mul]
    have hεsmul : ∀ (x : SL(2, ℤ)) (τ : ℍ), (ε * x) • τ = x • τ := by
      rcases hε with rfl | rfl
      · intro x τ; rw [one_mul]
      · intro x τ; rw [neg_one_mul]; exact ModularGroup.SL_neg_smul x τ
    have hσ : δ * ModularGroup.T ^ h * δ⁻¹ ∈ Gamma0 N := by
      rcases hε with rfl | rfl
      · rw [one_mul] at hγeq; rw [← hγeq]; exact γ.2
      · have e : δ * ModularGroup.T ^ h * δ⁻¹ = -1 * (γ : SL(2, ℤ)) := by
          rw [hγeq, ← mul_assoc, neg_one_mul, neg_neg, one_mul]
        rw [e]; exact Subgroup.mul_mem _ hneg1 γ.2

    set g : ℍ → ℂ := (f : ℍ → ℂ) ∣[((n : ℤ) + 2)] δ with hg
    set G : ℍ → ↥(BinaryForm ℂ n) := fun τ => R δ⁻¹ (F (δ • τ)) with hGdef
    have hGEI : IsEichlerIntegral n g G := hEI.slash δ
    have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := (CuspFormClass.holo f).slash _ _
    have hgzero : IsZeroAtImInfty g := CuspFormClass.zero_at_infty_slash f δ
    have hgper : Function.Periodic (g ∘ ofComplex) ((h : ℝ) : ℂ) :=
      pm_periodic_slash_comp_ofComplex_of_conj_T_zpow_mem f δ hσ
    have hFG : ∀ u : ℍ, F (δ • u) = R δ (G u) := fun u => by rw [hGdef, hRinv']

    have hcoc : hF.cocycle γ = R δ (G (ModularGroup.T ^ h • I) - R (ModularGroup.T ^ h) (G I)) := by
      rw [← hF.sub_eq_cocycle γ (δ • I), hρapp, hγeq, hεsmul, hRεx, ← mul_smul, inv_mul_cancel_right, mul_smul,
        hFG, hFG, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hRinv, map_sub]

    have htrans : ∀ y ∈ LinearMap.range (R (ModularGroup.T ^ h) - 1), R δ y ∈ LinearMap.range (ρ γ - 1) := by
      rintro _ ⟨w, rfl⟩
      refine ⟨R δ w, ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply, hρapp, hγeq, hRεx, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hRinv, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [hcoc]
    apply htrans
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    · rw [UpperHalfPlane.modular_T_zpow_smul]
      exact hGEI.vadd_sub_T_zpow_apply_mem_range hh hgper hghol hgzero I
  ·
    set m : Gamma0 N := ⟨-1, hneg1⟩ with hm
    have hρm : ∀ v, ρ m v = -v := fun v => by
      rw [hρapp]
      show binaryFormRepSL ℂ n (-1) v = -v
      rw [binaryFormRepSL_neg_one_apply, Odd.neg_one_pow hodd]
      exact neg_one_smul ℂ v
    have hz := hF.cocycle_mem_coeffCocycles
    have hcomm : γ * m = m * γ := Subtype.ext (by simp [hm])
    have h1 := hz γ m
    have h2 := hz m γ
    rw [hcomm, h2, hρm] at h1

    have h4 : hF.cocycle γ + hF.cocycle γ = hF.cocycle m - ρ γ (hF.cocycle m) := by
      rw [eq_sub_iff_add_eq]
      calc hF.cocycle γ + hF.cocycle γ + ρ γ (hF.cocycle m)
          = hF.cocycle γ + (hF.cocycle γ + ρ γ (hF.cocycle m)) := by abel
        _ = hF.cocycle γ + (hF.cocycle m + -hF.cocycle γ) := by rw [h1]
        _ = hF.cocycle m := by abel
    refine ⟨-((2 : ℂ)⁻¹ • hF.cocycle m), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, map_neg, map_smul, sub_neg_eq_add]
    calc -((2 : ℂ)⁻¹ • ρ γ (hF.cocycle m)) + (2 : ℂ)⁻¹ • hF.cocycle m
        = (2 : ℂ)⁻¹ • (hF.cocycle m - ρ γ (hF.cocycle m)) := by rw [smul_sub]; abel
      _ = (2 : ℂ)⁻¹ • (hF.cocycle γ + hF.cocycle γ) := by rw [h4]
      _ = hF.cocycle γ := by rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-! ### A.8 Existence of an Eichler integral with parabolic cocycle

FLT `aa2d8b3`, `Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle`. -/

theorem exists_isEichlerIntegral_isParabolicCocycle (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F ∧
      ∃ hF : HeckeEis.IsEquivariantPrimitiveWith
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F,
        HeckeEis.IsParabolicCocycle
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by
  obtain ⟨F, hEI⟩ := HeckeEis.exists_isEichlerIntegral n (f := (f : UpperHalfPlane → ℂ)) (CuspFormClass.holo f)
  have hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F :=
    HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral hEI
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ))
  exact ⟨F, hEI, hF, HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral N n f hEI hF⟩

/-! ## B. The structural period map

The deliberate divergence of the port (topic §3 Tier 1): `periodMap` is built
structurally from a chosen Eichler integral whose class is shown independent of
the choice, instead of the pin's `dif`ed `eichlerShimuraMap`. -/

private theorem IsEquivariantPrimitiveWith.add {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)}
    {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K Γ V} {F G : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G) :
    IsEquivariantPrimitiveWith ρ (F + G) := fun γ =>
  ⟨hF.cocycle γ + hG.cocycle γ, fun τ => by
    rw [Pi.add_apply, Pi.add_apply, map_add, ← hF.sub_eq_cocycle γ τ, ← hG.sub_eq_cocycle γ τ]; abel⟩

private theorem IsEquivariantPrimitiveWith.cocycle_add {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)}
    {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K Γ V} {F G : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G) :
    (IsEquivariantPrimitiveWith.add hF hG).cocycle = hF.cocycle + hG.cocycle := by
  funext γ
  change (F + G) ((γ : SL(2, ℤ)) • I) - ρ γ ((F + G) I) = (F _ - ρ γ (F I)) + (G _ - ρ γ (G I))
  rw [Pi.add_apply, Pi.add_apply, map_add]
  abel

private theorem IsEquivariantPrimitiveWith.smul {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)}
    {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K Γ V} {F : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    IsEquivariantPrimitiveWith ρ (c • F) := fun γ =>
  ⟨c • hF.cocycle γ, fun τ => by
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← hF.sub_eq_cocycle γ τ, smul_sub]⟩

private theorem IsEquivariantPrimitiveWith.cocycle_smul {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)}
    {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K Γ V} {F : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    (IsEquivariantPrimitiveWith.smul hF c).cocycle = c • hF.cocycle := by
  funext γ
  change (c • F) ((γ : SL(2, ℤ)) • I) - ρ γ ((c • F) I) = c • (F _ - ρ γ (F I))
  rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_sub]

private noncomputable abbrev pm_chosenF (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) : ℍ → ↥(BinaryForm ℂ n) :=
  Classical.choose (exists_isEichlerIntegral_isParabolicCocycle N n f)

private theorem pm_chosenEI (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    IsEichlerIntegral n f (pm_chosenF n N f) :=
  (Classical.choose_spec (exists_isEichlerIntegral_isParabolicCocycle N n f)).1

private noncomputable abbrev pm_chosenHF (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (pm_chosenF n N f) :=
  Classical.choose (Classical.choose_spec (exists_isEichlerIntegral_isParabolicCocycle N n f)).2

private theorem pm_chosenHpar (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (pm_chosenHF n N f).cocycle :=
  Classical.choose_spec (Classical.choose_spec (exists_isEichlerIntegral_isParabolicCocycle N n f)).2

private noncomputable def periodClass (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    coeffH1par ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  coeffH1parMk _ ⟨(pm_chosenHF n N f).cocycle,
    ⟨(pm_chosenHF n N f).cocycle_mem_coeffCocycles, pm_chosenHpar n N f⟩⟩

private theorem periodClass_eq_coeffH1parMk (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    {F : ℍ → ↥(BinaryForm ℂ n)} (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    periodClass n N f = coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := by
  rw [show periodClass n N f = coeffH1parMk _ ⟨(pm_chosenHF n N f).cocycle,
        ⟨(pm_chosenHF n N f).cocycle_mem_coeffCocycles, pm_chosenHpar n N f⟩⟩ from rfl,
    ← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]
  obtain ⟨v, hv⟩ := (pm_chosenEI n N f).exists_sub_eq_const hEI
  exact (pm_chosenHF n N f).cocycle_sub_cocycle_mem_coeffCoboundaries hF hv

noncomputable def periodMap (n N : ℕ) [NeZero N] :
    CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ]
      HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) where
  toFun := periodClass n N
  map_add' f g := by
    have hEF := pm_chosenEI n N f
    have hEG := pm_chosenEI n N g
    have hF := pm_chosenHF n N f
    have hG := pm_chosenHF n N g
    have hpF := pm_chosenHpar n N f
    have hpG := pm_chosenHpar n N g
    have hEFG : IsEichlerIntegral n (⇑(f + g)) (pm_chosenF n N f + pm_chosenF n N g) := by
      rw [FunLike.coe_add]; exact hEF.add hEG
    have hFG : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (pm_chosenF n N f + pm_chosenF n N g) := IsEquivariantPrimitiveWith.add hF hG
    have hpFG : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        hFG.cocycle := by
      intro γ hγ
      rw [IsEquivariantPrimitiveWith.cocycle_add hF hG, Pi.add_apply]
      exact add_mem (hpF γ hγ) (hpG γ hγ)
    rw [periodClass_eq_coeffH1parMk n N (f + g) hEFG hFG hpFG,
      periodClass_eq_coeffH1parMk n N f hEF hF hpF,
      periodClass_eq_coeffH1parMk n N g hEG hG hpG, ← map_add]
    congr 1
    exact Subtype.ext (IsEquivariantPrimitiveWith.cocycle_add hF hG)
  map_smul' c f := by
    have hEF := pm_chosenEI n N f
    have hF := pm_chosenHF n N f
    have hpF := pm_chosenHpar n N f
    have hEcF : IsEichlerIntegral n (⇑(c • f)) (c • pm_chosenF n N f) := by
      rw [FunLike.coe_smul]; exact hEF.smul c
    have hcF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (c • pm_chosenF n N f) := IsEquivariantPrimitiveWith.smul hF c
    have hpcF : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        hcF.cocycle := by
      intro γ hγ
      rw [IsEquivariantPrimitiveWith.cocycle_smul hF c, Pi.smul_apply]
      exact Submodule.smul_mem _ c (hpF γ hγ)
    rw [periodClass_eq_coeffH1parMk n N (c • f) hEcF hcF hpcF,
      periodClass_eq_coeffH1parMk n N f hEF hF hpF, ← map_smul, RingHom.id_apply]
    congr 1
    exact Subtype.ext (IsEquivariantPrimitiveWith.cocycle_smul hF c)

theorem periodMap_eq_coeffH1parMk (n N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.periodMap n N f = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ :=
  periodClass_eq_coeffH1parMk n N f hEI hF hpar

/-! ### The injectivity proof's two analytic inputs -/

private theorem pm_mdifferentiable_eval {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}
    (hG : IsEichlerIntegral n g G) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have h := (hG.hasDerivAt_eval_iterate_pderiv (Nat.zero_le n) ⟨z, hz⟩).differentiableAt
  simp only [Function.iterate_zero, id_eq] at h
  refine (h.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hw]

private theorem pm_exists_eq_const_of_slash_invariant {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (hk : k ≤ 0)
    {F : ℍ → ℂ} (hinv : ∀ γ ∈ Γ, F ∣[k] γ = F) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty (F ∣[k] δ)) : ∃ c : ℂ, ∀ τ : ℍ, F τ = c := by
  let M : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := F
      slash_action_eq' := by
        intro g hg
        obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
        exact hinv γ hγ
      holo' := hhol
      bdd_at_cusps' := by
        intro c hc
        have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
          rintro g ⟨γ, -, rfl⟩
          exact ⟨γ, rfl⟩
        obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
        rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
        exact hbdd δ }
  have hMF : ∀ τ : ℍ, M τ = F τ := fun τ => rfl
  rcases hk.lt_or_eq with hlt | heq
  · refine ⟨0, fun τ => ?_⟩
    have hM : M = 0 := ModularForm.isZero_of_neg_weight hlt M
    rw [← hMF τ, hM]
    rfl
  · subst heq
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero M
    exact ⟨c, fun τ => by rw [← hMF τ, hc]; rfl⟩

private theorem pm_conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := by
  have hTN : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    simpa using this
  exact pm_Gamma_le_Gamma0 N ((CongruenceSubgroup.Gamma_normal N).conj_mem _ hTN δ)

/-! ### Injectivity — the tier's target

FLT `aa2d8b3`, `S_HeckeEis_eichlerShimuraMap_injective` (adapted to the linear
`periodMap`). -/

theorem periodMap_injective (n N : ℕ) [NeZero N] : Function.Injective (HeckeEis.periodMap n N) := by
  have : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (pm_Gamma_le_Gamma0 N)

  suffices hker : ∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2), periodMap n N f = 0 → f = 0 by
    intro f g hfg
    have h1 : periodMap n N (f - g) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hfg
    exact sub_eq_zero.mp (hker (f - g) h1)
  intro f hf0
  set R := binaryFormRepSL ℂ n with hR
  obtain ⟨F, hEI, hF, hpar⟩ := exists_isEichlerIntegral_isParabolicCocycle N n f
  rw [periodMap_eq_coeffH1parMk n N f hEI hF hpar, coeffH1parMk_eq_zero_iff] at hf0
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hf0

  set F₁ : ℍ → ↥(BinaryForm ℂ n) := fun τ => F τ + v with hF₁
  have hEI₁ : IsEichlerIntegral n f F₁ := by
    intro d τ
    have := (hEI d τ).add_const (((v : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)
    simpa [hF₁, Submodule.coe_add, pm_coeff_add] using this
  have hEq : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, F₁ (γ • τ) = R γ (F₁ τ) := by
    intro γ hγ τ
    have h1 := hF.sub_eq_cocycle ⟨γ, hγ⟩ τ
    have h2 := congrFun hv ⟨γ, hγ⟩
    simp only at h2
    rw [← h2] at h1

    simp only [hF₁, map_add]
    change F (γ • τ) + v = R γ (F τ) + R γ v
    have h3 : F (γ • τ) - R γ (F τ) = R γ v - v := h1
    rw [sub_eq_iff_eq_add.mp h3]
    abel

  set P : ℍ → ℂ := fun τ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((F₁ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
    with hP
  set Gδ : SL(2, ℤ) → ℍ → ↥(BinaryForm ℂ n) := fun δ τ => R δ⁻¹ (F₁ (δ • τ)) with hGδ
  have hGδEI : ∀ δ : SL(2, ℤ), IsEichlerIntegral n (⇑f ∣[((n : ℤ) + 2)] δ) (Gδ δ) := fun δ => hEI₁.slash δ
  have hRR : ∀ (δ : SL(2, ℤ)) (τ : ℍ), R δ (Gδ δ τ) = F₁ (δ • τ) := fun δ τ => by
    simp only [hGδ]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hslash : ∀ (δ : SL(2, ℤ)) (τ : ℍ), (P ∣[-(n : ℤ)] δ) τ
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((Gδ δ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := by
    intro δ τ
    rw [ModularForm.SL_slash_apply, hP, neg_neg]
    simp only []
    have key := jFactor_pow_mul_eval_binaryFormRepSL n δ τ (Gδ δ τ)
    rw [hRR, jFactor_eq_denom] at key
    rw [← key, mul_comm, zpow_natCast]
    rfl

  have hinv : ∀ γ ∈ Gamma0 N, P ∣[-(n : ℤ)] γ = P := by
    intro γ hγ
    funext τ
    rw [hslash γ τ, hP]
    simp only [hGδ]
    rw [hEq γ hγ τ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := pm_mdifferentiable_eval hEI₁
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty (P ∣[-(n : ℤ)] δ) := by
    intro δ
    have hfun : P ∣[-(n : ℤ)] δ
        = fun τ : ℍ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((Gδ δ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) :=
      funext (hslash δ)
    rw [hfun]
    have hσ : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := pm_conj_T_zpow_mem_Gamma0 N δ
    have hgper : Function.Periodic ((⇑f ∣[((n : ℤ) + 2)] δ) ∘ ofComplex) (((N : ℤ) : ℝ) : ℂ) :=
      pm_periodic_slash_comp_ofComplex_of_conj_T_zpow_mem f δ hσ
    have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[((n : ℤ) + 2)] δ) := (CuspFormClass.holo f).slash _ _
    have hgbdd : IsBoundedAtImInfty (⇑f ∣[((n : ℤ) + 2)] δ) := ModularFormClass.bdd_at_infty_slash f δ
    have hT : ∀ τ : ℍ, Gδ δ ((((N : ℤ) : ℝ)) +ᵥ τ) = R (ModularGroup.T ^ (N : ℤ)) (Gδ δ τ) := by
      intro τ
      simp only [hGδ]
      have h1 := hEq _ hσ (δ • τ)
      have hpt : ((δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ : SL(2, ℤ)) • δ • τ) = δ • ((((N : ℤ) : ℝ)) +ᵥ τ) := by
        rw [← UpperHalfPlane.modular_T_zpow_smul, smul_smul, smul_smul]
        congr 1
        group
      rw [hpt] at h1
      rw [h1, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    exact (hGδEI δ).isBoundedAtImInfty_eval hNpos hgper hghol hgbdd hT
  obtain ⟨c, hc⟩ := pm_exists_eq_const_of_slash_invariant (Γ := Gamma0 N) (k := -(n : ℤ)) (by omega) hinv hhol hbdd
  have hzero : (⇑f : ℍ → ℂ) = 0 := hEI₁.eq_zero_of_eval_eq_const hc
  exact DFunLike.ext f 0 fun τ => by rw [congrFun hzero τ]; rfl

end HeckeEis
