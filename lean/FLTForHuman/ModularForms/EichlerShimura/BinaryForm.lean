/-
Copyright (c) 2026 FLT-for-human contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT-for-human contributors
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RepresentationTheory.Basic

/-!
# Binary forms and the `SL(2, ℤ)`-representation on them

The weight-`n` binary forms over a commutative ring `K` are the degree-`n`
homogeneous polynomials in two variables, on which `SL(2, ℤ)` acts by
substitution of the linear forms `X i ↦ ∑ j M j i * X j`. This is the
coefficient module of the general-weight Eichler–Shimura period map
$`S_{n+2}(\Gamma_0(N)) \to H^1_{par}(\Gamma_0(N), \mathrm{Sym}^n)`; the
`SL(2, ℤ)`-representation is restricted to `Γ_0(N)` by the consumer.

## Subject

* `BinaryForm K n` — mathlib's `MvPolynomial.homogeneousSubmodule` in two
  variables, adopted as the port's interface (playbook §3.8), not a new type.
* `binarySubst K M` — the substitution `X i ↦ ∑ j M j i * X j` as a `K`-algebra
  endomorphism of `MvPolynomial (Fin 2) K`; it is functorial (`_one`, `_mul`)
  and preserves `BinaryForm K n` (`_mem`).
* `binaryFormRepSL K n` — the resulting representation of `SL(2, ℤ)` on
  `BinaryForm K n`.
* `binaryFormAlphaAdj K n ℓ` — the diagonal substitution `diag(ℓ, 1)`, the
  `α`-adjoint used by the Hecke-free cone.

## FLT source and pin

Pin `aa2d8b3`: `Definitions/Def_HeckeEis_BinaryFormRep.lean`, the
`BinaryForms` block (lines 9–91).
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeEis_BinaryFormRep.lean#L9-L91>.

Every declaration above is the pin's verbatim. The pin's `Eval` block
(`evalRow`, `evalRow_eq_of_unit_mul`, `binaryFormEval`, `binaryFormEval_mk`,
lines 93–138) is **deliberately omitted**: it needs the projective line
`ProjectiveLine`/`UnimodularRow` of `Def_ProjectiveLineMatrixAction`, which is
outside this cone (topic §6 stop condition). Likewise the pin's bare
`import Mathlib` and its `Def_ProjectiveLineMatrixAction` import are dropped.

## What this module assumes

Mathlib only: `MvPolynomial.homogeneousSubmodule` and `IsHomogeneous` for the
forms, `Mathlib.RepresentationTheory.Basic` for `Representation`,
`Matrix.SpecialLinearGroup` for `SL(2, ℤ)` and the `MatrixGroups` notation
scope. Nothing from other `FLTForHuman` modules.

## Adaptation notes (mathlib `v4.34.0`)

None in the statements. The proofs are the pin's, except that the pin's
`MvPolynomial.coeff` (a qualified name no longer present) does not occur here.
-/

open MvPolynomial
open scoped MatrixGroups

namespace HeckeEis

theorem eval_smul_of_isHomogeneous {σ : Type*} {R : Type*} [CommRing R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : R) (x : σ → R) :
    MvPolynomial.eval (c • x) φ = c ^ n * MvPolynomial.eval x φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

section BinaryForms

variable (K : Type*) [CommRing K]

abbrev BinaryForm (n : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K n

noncomputable def binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval fun j => ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i

theorem binarySubst_X (M : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) :
    binarySubst K M (X j) = ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i :=
  MvPolynomial.aeval_X _ _

theorem binarySubst_C (M : Matrix (Fin 2) (Fin 2) ℤ) (r : K) : binarySubst K M (C r) = C r := by
  rw [binarySubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem binarySubst_one : binarySubst K (1 : Matrix (Fin 2) (Fin 2) ℤ) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [binarySubst_X, AlgHom.id_apply, Fin.sum_univ_two]
  fin_cases j <;> simp [Matrix.one_apply]

theorem binarySubst_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) :
    binarySubst K (M * M') = (binarySubst K M).comp (binarySubst K M') := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, binarySubst_X, binarySubst_X]
  simp only [Fin.sum_univ_two, Matrix.mul_apply, map_add, map_mul, binarySubst_C, binarySubst_X,
    Int.cast_add, Int.cast_mul]
  ring

theorem binarySubst_mem {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) {F : MvPolynomial (Fin 2) K}
    (hF : F ∈ BinaryForm K n) : binarySubst K M F ∈ BinaryForm K n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF ⊢
  have h := hF.aeval (fun j => ∑ i : Fin 2, C ((M i j : ℤ) : K) * X i)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _)
  simpa only [binarySubst, one_mul] using h

variable (n : ℕ)

noncomputable def binaryFormRepSL : Representation K SL(2, ℤ) (BinaryForm K n) where
  toFun g := (binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap.restrict
    fun F hF => binarySubst_mem K _ hF
  map_one' := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) F.1 = F.1
    rw [Matrix.SpecialLinearGroup.coe_one, binarySubst_one]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun F => Subtype.ext ?_
    change binarySubst K ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) F.1
      = binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) (binarySubst K (h : Matrix (Fin 2) (Fin 2) ℤ) F.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, binarySubst_mul]
    rfl

@[simp]
theorem binaryFormRepSL_apply_coe (g : SL(2, ℤ)) (F : BinaryForm K n) :
    ((binaryFormRepSL K n g F : BinaryForm K n) : MvPolynomial (Fin 2) K)
      = binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) F :=
  rfl

noncomputable def binaryFormAlphaAdj (ℓ : ℕ) : BinaryForm K n →ₗ[K] BinaryForm K n :=
  (binarySubst K !![(ℓ : ℤ), 0; 0, 1]).toLinearMap.restrict fun _ hF => binarySubst_mem K _ hF

@[simp]
theorem binaryFormAlphaAdj_apply_coe (ℓ : ℕ) (F : BinaryForm K n) :
    ((binaryFormAlphaAdj K n ℓ F : BinaryForm K n) : MvPolynomial (Fin 2) K)
      = binarySubst K !![(ℓ : ℤ), 0; 0, 1] F :=
  rfl

end BinaryForms

/-! ## Tier 2 — the weight-`n` representation leaves

Three leaves of the general-weight Eichler–Shimura cone that live on the binary
forms themselves: the action of the central element `-1`, the identification of
the top coefficient with evaluation at the cusp `(1 : 0)`, and the fixed-vector
computation for the unipotent `T^h`. They are stated (and the first two proved)
directly on `binarySubst`, independent of the analysis.

The pin's `MvPolynomial.coeff d p` is written `p.coeff d` (mathlib `v4.34.0` no
longer exposes `coeff` as a qualified name; see the module header of
`EichlerIntegral.lean` for the same adaptation). -/

section Tier2

/-- The central element `-1 ∈ SL(2, ℤ)` acts on weight-`n` binary forms by the
scalar `(-1)^n`. FLT `aa2d8b3`,
`Thm_HeckeEis_binaryFormRepSL_neg_one_apply`. -/
theorem binaryFormRepSL_neg_one_apply (K : Type*) [CommRing K] (n : ℕ)
    (P : ↥(HeckeEis.BinaryForm K n)) :
    HeckeEis.binaryFormRepSL K n (-1) P = ((-1 : K) ^ n) • P := by
  classical
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Submodule.coe_smul]
  have hhom : (P : MvPolynomial (Fin 2) K).IsHomogeneous n := (mem_homogeneousSubmodule n _).mp P.2
  have h0 : binarySubst K ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (X 0) = -X 0 := by
    rw [binarySubst_X]; simp [Matrix.one_apply]
  have h1 : binarySubst K ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (X 1) = -X 1 := by
    rw [binarySubst_X]; simp [Matrix.one_apply]
  conv_lhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
  conv_rhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d.degree = n := by
    by_contra hc
    exact (mem_support_iff.mp hd) (hhom.coeff_eq_zero hc)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
  have hC : C ((-1 : K) ^ n) = (-1 : MvPolynomial (Fin 2) K) ^ (d 0) * (-1) ^ (d 1) := by
    rw [map_pow, map_neg, map_one, ← pow_add, hdn]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, map_mul, binarySubst_C,
    map_mul, map_pow, map_pow, h0, h1, smul_eq_C_mul, hC,
    neg_pow (X 0 : MvPolynomial (Fin 2) K), neg_pow (X 1 : MvPolynomial (Fin 2) K)]
  ring

/-- On a weight-`n` binary form the coefficient of `X 1 ^ n` is the evaluation
at the cusp `(1 : 0)`. FLT `aa2d8b3`,
`Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm`. -/
theorem coeff_single_one_eq_eval_of_mem_binaryForm {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    P.coeff (Finsupp.single 1 n) = MvPolynomial.eval ![0, 1] P := by
  classical
  have hhom : P.IsHomogeneous n := (mem_homogeneousSubmodule n P).mp hP
  rw [MvPolynomial.eval_eq]
  symm
  rw [Finset.sum_eq_single (Finsupp.single 1 n)]
  · simp [Finsupp.single_apply]
  · intro d hd hne

    have hdn : d.degree = n := by
      by_contra hc
      exact (mem_support_iff.mp hd) (hhom.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
    have hd0 : d 0 ≠ 0 := by
      intro h0
      apply hne
      ext i
      fin_cases i
      · simpa using h0
      · simp
        omega
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hd0) (by simp [zero_pow hd0]), mul_zero]
  · intro hn
    rw [MvPolynomial.notMem_support_iff.mp hn, zero_mul]

section RangeTzpow

/-- The monomial `X 0 ^ a * X 1 ^ b` is a binary form of weight `a + b`. -/
private theorem X_pow_mul_X_pow_mem (K : Type*) [CommRing K] (n : ℕ) {a b : ℕ} (h : a + b = n) :
    (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) K) ∈ HeckeEis.BinaryForm K n := by
  rw [mem_homogeneousSubmodule]
  have := ((isHomogeneous_X K (0 : Fin 2)).pow a).mul ((isHomogeneous_X K (1 : Fin 2)).pow b)
  convert this using 1
  omega

/-- The basis vector `X 0 ^ (n - b) * X 1 ^ b`, zero outside the range. -/
private noncomputable def mono (K : Type*) [CommRing K] (n : ℕ) (b : ℕ) : ↥(HeckeEis.BinaryForm K n) :=
  if hb : b ≤ n then ⟨X 0 ^ (n - b) * X 1 ^ b, X_pow_mul_X_pow_mem K n (by omega)⟩ else 0

private theorem coe_mono (K : Type*) [CommRing K] (n : ℕ) {b : ℕ} (hb : b ≤ n) :
    (mono K n b : MvPolynomial (Fin 2) K) = X 0 ^ (n - b) * X 1 ^ b := by
  rw [mono, dite_eq_left hb]

/-- `T^h` acts on the monomial basis by the truncated binomial expansion. -/
private theorem binaryFormRepSL_T_zpow_mono (K : Type*) [CommRing K] (n : ℕ) (h : ℤ) {b : ℕ}
    (hb : b ≤ n) :
    HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) (mono K n b)
      = ∑ i ∈ Finset.range (b + 1), ((b.choose i : K) * (h : K) ^ (b - i)) • mono K n i := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, coe_mono K n hb, Submodule.coe_sum, map_mul, map_pow, map_pow, binarySubst_X,
    binarySubst_X, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [ModularGroup.coe_T_zpow, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_one, Int.cast_zero, map_one, map_zero, one_mul, zero_mul,
    add_zero]
  rw [add_comm (C (h : K) * X 0) (X 1), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Submodule.coe_smul, coe_mono K n (by omega : i ≤ n), smul_eq_C_mul, mul_pow, ← C_pow,
    show n - i = (n - b) + (b - i) by omega, pow_add, map_mul, map_natCast]
  ring

/-- Every basis monomial of weight `< n` (i.e. every monomial but `X 1 ^ n`) is a
coboundary for the unipotent `T^h - 1` in characteristic zero. -/
private theorem mono_mem_range_T_zpow_sub_one {K : Type*} [Field K] [CharZero K]
    (n : ℕ) {h : ℤ} (hh : h ≠ 0) :
    ∀ b < n, mono K n b ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    have hexp := binaryFormRepSL_T_zpow_mono K n h (b := b + 1) (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul,
      one_smul, Nat.choose_succ_self_right, Nat.add_sub_cancel_left, pow_one] at hexp
    have hmem : (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) (mono K n (b + 1))
        ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := LinearMap.mem_range_self _ _
    rw [LinearMap.sub_apply, Module.End.one_apply, hexp, add_sub_cancel_right] at hmem
    have hsum : ∑ i ∈ Finset.range b, (((b + 1).choose i : K) * (h : K) ^ (b + 1 - i)) • mono K n i
        ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) :=
      Submodule.sum_mem _ fun i hi => by
        have hib := Finset.mem_range.mp hi
        exact Submodule.smul_mem _ _ (ih i hib (by omega))
    have hcb : (((b + 1 : ℕ) : K) * (h : K)) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b)) (Int.cast_ne_zero.mpr hh)
    have key := Submodule.sub_mem _ hmem hsum
    rw [add_sub_cancel_left] at key
    exact (Submodule.smul_mem_iff _ hcb).mp key

/-- A weight-`n` binary form whose `X 1 ^ n`-coefficient vanishes lies in the
range of `T^h - 1` for every `h ≠ 0`, over a characteristic-zero field. FLT
`aa2d8b3`, `Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one`. -/
theorem mem_range_binaryFormRepSL_T_zpow_sub_one {K : Type*} [Field K] [CharZero K] (n : ℕ) {h : ℤ}
    (hh : h ≠ 0) (P : ↥(HeckeEis.BinaryForm K n))
    (hP : (P : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 n) = 0) :
    P ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by
  classical
  have hhom : (P : MvPolynomial (Fin 2) K).IsHomogeneous n := (mem_homogeneousSubmodule n _).mp P.2
  have hdeg : ∀ d ∈ (P : MvPolynomial (Fin 2) K).support, d 0 + d 1 = n ∧ d 1 < n := by
    intro d hd
    have hne := mem_support_iff.mp hd
    have hdn : d.degree = n := by
      by_contra hc
      exact hne (hhom.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
    refine ⟨hdn, lt_of_le_of_ne (by omega) fun h1 => hne ?_⟩
    have : d = Finsupp.single 1 n := by
      ext i
      fin_cases i
      · simp
        omega
      · simpa using h1
    rw [this]
    exact hP
  have hrepr : P = ∑ d ∈ (P : MvPolynomial (Fin 2) K).support,
      (P : MvPolynomial (Fin 2) K).coeff d • mono K n (d 1) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdn, hd1⟩ := hdeg d hd
    rw [Submodule.coe_smul, coe_mono K n hd1.le, monomial_eq, smul_eq_C_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, show n - d 1 = d 0 by omega]
  rw [hrepr]
  exact Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ (mono_mem_range_T_zpow_sub_one n hh _ (hdeg d hd).2)

end RangeTzpow

end Tier2

end HeckeEis
