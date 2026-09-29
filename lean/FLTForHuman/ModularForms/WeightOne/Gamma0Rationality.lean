/-
  Γ₀-rationality of the `q`-expansion of a `Γ₁`-invariant form (SET-10 order 1).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean`,
  `Theorems/Thm_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean`,
  `Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean`
  and
  `Theorems/Thm_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean`;
  proofs transcribed from the matching `P2M/Sol/S_*` files (709 + 424 + 1,267 +
  583 lines) and adapted to mathlib `v4.34.0`.

  Each pin file's helpers stay `private` in the pin's own inner namespace
  (`FrickeIntegral` / `FrickeToInfinity` / `X1DiamondRational` /
  `GammaNDescent`), nested in this module's own `WLightS10.S_*` namespaces, so
  the four packages' repeated vocabulary (the `Width` helpers, `RatAt`, `cw`,
  `descent`, …) does not collide; the four headlines are the module's only
  public surface.  The package-to-package edges are the pin's own and consume
  the already-ported SET-7/8/9 headlines
  (`WLight.weierstrassP_qExpansion_package`,
  `WLight.frickeFunction_modularity_package`,
  `WLight.qExpansion_sigmaTransport_package`,
  `WLight.levelN_structure_package`,
  `WLight.exists_levelFraction_of_stable_family`,
  `WLight.exists_monicRel_j_of_mdifferentiable_levelFraction`,
  `WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient`,
  `WLight.frickeFunction_intBaseChange`,
  `WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction` and
  `WLight.linearIndependent_complex_of_qExpansion_rational`).

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean

  The pin's `set_option maxHeartbeats` bumps are **not** transcribed (the
  project's global `maxHeartbeats` cap is 4,000,000).
-/

import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
import FLTForHuman.ModularForms.WeightOne.LevelN
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.Unramified.Field
import FLTForHuman.ModularForms.WeightOne.Defs.PeriodPair
import FLTForHuman.ModularForms.WeightOne.Defs.PTorsion
import FLTForHuman.ModularForms.WeightOne.Defs.Gamma
import FLTForHuman.ModularForms.WeightOne.Fricke
import FLTForHuman.ModularForms.DiscPow
import FLTForHuman.ModularForms.QExpansionCoeff
import FLTForHuman.ModularForms.WeightOne.Defs.GammaRational
open X1DiamondRational
open UpperHalfPlaneAux
open WLight

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

open Complex Real UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real Manifold MatrixGroups ModularForm Topology UpperHalfPlane

namespace WLightS10.S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin

open Complex UpperHalfPlane ModularForm Function Filter Topology
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeIntegral

variable (N : ℕ) [NeZero N]

private def zeta : ℂ := cexp (2 * π * Complex.I / N)

private def AZ : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {zeta N}

private theorem zeta_mem : zeta N ∈ AZ N := Algebra.subset_adjoin (Set.mem_singleton _)

private theorem isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)

private theorem zeta_pow_N : zeta N ^ N = 1 := (isPrimitiveRoot_zeta N).pow_eq_one

private theorem zeta_ne_zero : zeta N ≠ 0 := by unfold zeta; exact exp_ne_zero _

private theorem norm_zeta : ‖zeta N‖ = 1 := (isPrimitiveRoot_zeta N).norm'_eq_one (NeZero.ne N)

private theorem zeta_inv_mem : (zeta N)⁻¹ ∈ AZ N := by
  have hN : 0 < N := NeZero.pos N
  have : (zeta N)⁻¹ = zeta N ^ (N - 1) := by
    rw [eq_comm, ← mul_inv_eq_one₀ (inv_ne_zero (zeta_ne_zero N)), inv_inv, ← pow_succ,
      Nat.sub_add_cancel hN, zeta_pow_N]
  rw [this]; exact pow_mem (zeta_mem N) _

private theorem intCast_mem (z : ℤ) : (z : ℂ) ∈ AZ N := by exact_mod_cast (AZ N).algebraMap_mem z

private theorem natCast_mem (n : ℕ) : (n : ℂ) ∈ AZ N := by exact_mod_cast intCast_mem N n

private theorem exists_mul_one_sub_eq {a : ℕ} (ha : 0 < a) (haN : a < N) :
    ∃ y ∈ AZ N, y * (1 - zeta N ^ a) = N := by
  set x : ℂ := zeta N ^ a with hx
  have hx1 : x ≠ 1 := by
    rw [hx]
    exact (isPrimitiveRoot_zeta N).pow_ne_one_of_pos_of_lt ha.ne' haN
  have hxN : x ^ N = 1 := by rw [hx, ← pow_mul, mul_comm, pow_mul, zeta_pow_N, one_pow]
  have hgeom : ∑ k ∈ Finset.range N, x ^ k = 0 := by
    rw [geom_sum_eq hx1, hxN, sub_self, zero_div]
  refine ⟨∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, x ^ j, ?_, ?_⟩
  · refine sum_mem fun k _ => sum_mem fun j _ => ?_
    rw [hx, ← pow_mul]; exact pow_mem (zeta_mem N) _
  · calc (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, x ^ j) * (1 - x)
        = ∑ k ∈ Finset.range N, (1 - x ^ k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm, mul_neg_geom_sum]
      _ = ∑ k ∈ Finset.range N, (1 : ℂ) - ∑ k ∈ Finset.range N, x ^ k := Finset.sum_sub_distrib _ _
      _ = N := by rw [hgeom, sub_zero]; simp

section Coeff

variable (a₁ a₂ : ℕ)

private abbrev Idx : Type := (ℕ+ × ℕ+) × Fin 3

private def expo (i : Idx) : ℕ :=
  ![((i.1.1 : ℕ) * N + a₁) * (i.1.2 : ℕ), ((i.1.1 : ℕ) * N - a₁) * (i.1.2 : ℕ), (i.1.1 : ℕ) * N * (i.1.2 : ℕ)] i.2

private def coef (i : Idx) : ℂ :=
  ![((i.1.2 : ℕ) : ℂ) * zeta N ^ (a₂ * (i.1.2 : ℕ)), ((i.1.2 : ℕ) : ℂ) * (zeta N)⁻¹ ^ (a₂ * (i.1.2 : ℕ)),
    -2 * ((i.1.2 : ℕ) : ℂ)] i.2

private theorem coef_mem (i : Idx) : coef N a₂ i ∈ AZ N := by
  rcases i with ⟨p, j⟩
  fin_cases j
  · exact mul_mem (natCast_mem N _) (pow_mem (zeta_mem N) _)
  · exact mul_mem (natCast_mem N _) (pow_mem (zeta_inv_mem N) _)
  · change -2 * ((p.2 : ℕ) : ℂ) ∈ AZ N
    exact mul_mem (by exact_mod_cast intCast_mem N (-2)) (natCast_mem N _)

private theorem norm_coef_le (i : Idx) : ‖coef N a₂ i‖ ≤ 2 * (i.1.2 : ℕ) := by
  rcases i with ⟨p, j⟩
  have h1 : (0 : ℝ) ≤ (p.2 : ℕ) := Nat.cast_nonneg _
  fin_cases j
  · change ‖((p.2 : ℕ) : ℂ) * zeta N ^ (a₂ * (p.2 : ℕ))‖ ≤ 2 * (p.2 : ℕ)
    rw [norm_mul, norm_pow, norm_zeta, one_pow, mul_one, Complex.norm_natCast]; linarith
  · change ‖((p.2 : ℕ) : ℂ) * (zeta N)⁻¹ ^ (a₂ * (p.2 : ℕ))‖ ≤ 2 * (p.2 : ℕ)
    rw [norm_mul, norm_pow, norm_inv, norm_zeta, inv_one, one_pow, mul_one, Complex.norm_natCast]; linarith
  · change ‖-2 * ((p.2 : ℕ) : ℂ)‖ ≤ 2 * (p.2 : ℕ)
    rw [norm_mul, norm_neg, Complex.norm_natCast]; norm_num

variable {N a₁} in

private theorem mul_le_expo (ha : a₁ < N) (i : Idx) : (i.1.1 : ℕ) * (i.1.2 : ℕ) ≤ expo N a₁ i := by
  rcases i with ⟨⟨c, k⟩, j⟩
  have hc : 1 ≤ (c : ℕ) := c.2
  have hcN : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
    have : (c : ℕ) * N ≥ (c : ℕ) + a₁ := by
      have h1 : (c : ℕ) * N = (c : ℕ) * (N - 1) + c := by
        rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (NeZero.pos N))]
      have h2 : a₁ ≤ (c : ℕ) * (N - 1) := le_trans (by omega) (Nat.le_mul_of_pos_left _ hc)
      omega
    omega
  fin_cases j
  · change (c : ℕ) * (k : ℕ) ≤ ((c : ℕ) * N + a₁) * (k : ℕ)
    exact Nat.mul_le_mul_right _ (le_trans (Nat.le_mul_of_pos_right _ (NeZero.pos N)) (Nat.le_add_right _ _))
  · change (c : ℕ) * (k : ℕ) ≤ ((c : ℕ) * N - a₁) * (k : ℕ)
    exact Nat.mul_le_mul_right _ hcN
  · change (c : ℕ) * (k : ℕ) ≤ (c : ℕ) * N * (k : ℕ)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (NeZero.pos N))

variable {N a₁} in
private theorem fst_le_expo (ha : a₁ < N) (i : Idx) : (i.1.1 : ℕ) ≤ expo N a₁ i :=
  le_trans (Nat.le_mul_of_pos_right _ i.1.2.2) (mul_le_expo ha i)

variable {N a₁} in
private theorem snd_le_expo (ha : a₁ < N) (i : Idx) : (i.1.2 : ℕ) ≤ expo N a₁ i :=
  le_trans (Nat.le_mul_of_pos_left _ i.1.1.2) (mul_le_expo ha i)

variable [Fact (a₁ < N)]

private def fibreMap (n : ℕ) : {i : Idx // expo N a₁ i = n} → (Fin (n + 1) × Fin (n + 1)) × Fin 3 := fun i =>
  ((⟨(i.1.1.1 : ℕ), Nat.lt_succ_of_le (le_trans (fst_le_expo (Fact.out : a₁ < N) i.1) i.2.le)⟩,
    ⟨(i.1.1.2 : ℕ), Nat.lt_succ_of_le (le_trans (snd_le_expo (Fact.out : a₁ < N) i.1) i.2.le)⟩), i.1.2)

private theorem fibreMap_injective (n : ℕ) : Function.Injective (fibreMap N a₁ n) := by
  rintro ⟨⟨⟨c, k⟩, j⟩, hi⟩ ⟨⟨⟨c', k'⟩, j'⟩, hi'⟩ h
  simp only [fibreMap, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hc : c = c' := PNat.coe_injective h1
  have hk : k = k' := PNat.coe_injective h2
  subst hc; subst hk; subst h3
  rfl

private scoped instance fintypeFibre (n : ℕ) : Fintype {i : Idx // expo N a₁ i = n} :=
  @Fintype.ofFinite _ (Finite.of_injective _ (fibreMap_injective N a₁ n))

private def cT (n : ℕ) : ℂ :=
  ∑ i : {i : Idx // expo N a₁ i = n}, coef N a₂ i.1

private theorem cT_mem (n : ℕ) : cT N a₁ a₂ n ∈ AZ N :=
  sum_mem fun i _ => coef_mem N a₂ i.1

private theorem card_fibre_le (n : ℕ) : Fintype.card {i : Idx // expo N a₁ i = n} ≤ (n + 1) * (n + 1) * 3 := by
  have := Fintype.card_le_of_injective _ (fibreMap_injective N a₁ n)
  simpa [Fintype.card_prod, Fintype.card_fin] using this

private theorem norm_cT_le (n : ℕ) : ‖cT N a₁ a₂ n‖ ≤ (n + 1) * (n + 1) * 3 * (2 * n) := by
  unfold cT
  calc ‖∑ i : {i : Idx // expo N a₁ i = n}, coef N a₂ i.1‖
      ≤ ∑ i : {i : Idx // expo N a₁ i = n}, ‖coef N a₂ i.1‖ := norm_sum_le _ _
    _ ≤ ∑ _i : {i : Idx // expo N a₁ i = n}, (2 * n : ℝ) := by
        refine Finset.sum_le_sum fun i _ => le_trans (norm_coef_le N a₂ i.1) ?_
        have h1 := snd_le_expo (Fact.out : a₁ < N) i.1
        rw [i.2] at h1
        have h2 : ((i.1.1.2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
        linarith
    _ = Fintype.card {i : Idx // expo N a₁ i = n} * (2 * n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (n + 1) * (n + 1) * 3 * (2 * n) := by
        have h1 : (Fintype.card {i : Idx // expo N a₁ i = n} : ℝ) ≤ (n + 1) * (n + 1) * 3 := by
          exact_mod_cast card_fibre_le N a₁ n
        have h2 : (0 : ℝ) ≤ 2 * n := by positivity
        exact mul_le_mul_of_nonneg_right h1 h2

private def cA (n : ℕ) : ℂ :=
  if a₁ = 0 then 0 else if a₁ ∣ n then ((n / a₁ : ℕ) : ℂ) * zeta N ^ (a₂ * (n / a₁)) else 0

private theorem cA_mem (n : ℕ) : cA N a₁ a₂ n ∈ AZ N := by
  unfold cA
  split_ifs
  · exact zero_mem _
  · exact mul_mem (natCast_mem N _) (pow_mem (zeta_mem N) _)
  · exact zero_mem _

private theorem norm_cA_le (n : ℕ) : ‖cA N a₁ a₂ n‖ ≤ n := by
  unfold cA
  split_ifs with h1 h2
  · simp
  · rw [norm_mul, norm_pow, norm_zeta, one_pow, mul_one, Complex.norm_natCast]
    exact_mod_cast Nat.div_le_self n a₁
  · simp

private def c0 : ℂ := 1 / 12 + if a₁ = 0 then zeta N ^ a₂ / (1 - zeta N ^ a₂) ^ 2 else 0

private theorem c0_mem (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : (12 * (N : ℂ) ^ 2) * c0 N a₁ a₂ ∈ AZ N := by
  unfold c0
  split_ifs with h1
  · have ha₂' : 0 < a₂ := by
      rcases h0 with h | h
      · exact absurd h1 h
      · exact Nat.pos_of_ne_zero h
    obtain ⟨y, hy, hyN⟩ := exists_mul_one_sub_eq N ha₂' ha₂
    have hne : (1 - zeta N ^ a₂) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm ((isPrimitiveRoot_zeta N).pow_ne_one_of_pos_of_lt ha₂'.ne' ha₂))
    have : (12 * (N : ℂ) ^ 2) * (1 / 12 + zeta N ^ a₂ / (1 - zeta N ^ a₂) ^ 2)
        = (N : ℂ) ^ 2 + 12 * zeta N ^ a₂ * y ^ 2 := by
      rw [← hyN]; field_simp
    rw [this]
    exact add_mem (pow_mem (natCast_mem N N) 2)
      (mul_mem (mul_mem (natCast_mem N 12) (pow_mem (zeta_mem N) _)) (pow_mem hy 2))
  · rw [add_zero]
    have : (12 * (N : ℂ) ^ 2) * (1 / 12) = (N : ℂ) ^ 2 := by ring
    rw [this]; exact pow_mem (natCast_mem N N) 2

private def cW (n : ℕ) : ℂ :=
  cA N a₁ a₂ n + (if n = 0 then c0 N a₁ a₂ else 0) + cT N a₁ a₂ n

private theorem cW_mem (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (12 * (N : ℂ) ^ 2) * cW N a₁ a₂ n ∈ AZ N := by
  unfold cW
  rw [mul_add, mul_add]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact mul_mem (mul_mem (natCast_mem N 12) (pow_mem (natCast_mem N N) 2)) (cA_mem N a₁ a₂ n)
  · split_ifs
    · exact c0_mem N a₁ a₂ ha₂ h0
    · rw [mul_zero]; exact zero_mem _
  · exact mul_mem (mul_mem (natCast_mem N 12) (pow_mem (natCast_mem N N) 2)) (cT_mem N a₁ a₂ n)

private theorem norm_cW_le (n : ℕ) : ‖cW N a₁ a₂ n‖ ≤ ‖c0 N a₁ a₂‖ + 8 * (n + 1) ^ 3 := by
  unfold cW
  have h1 := norm_cA_le N a₁ a₂ n
  have h3 := norm_cT_le N a₁ a₂ n
  have h2 : ‖(if n = 0 then c0 N a₁ a₂ else 0)‖ ≤ ‖c0 N a₁ a₂‖ := by split_ifs <;> simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ‖cA N a₁ a₂ n + (if n = 0 then c0 N a₁ a₂ else 0) + cT N a₁ a₂ n‖
      ≤ ‖cA N a₁ a₂ n‖ + ‖(if n = 0 then c0 N a₁ a₂ else 0)‖ + ‖cT N a₁ a₂ n‖ := norm_add₃_le
    _ ≤ n + ‖c0 N a₁ a₂‖ + (n + 1) * (n + 1) * 3 * (2 * n) := by linarith
    _ ≤ ‖c0 N a₁ a₂‖ + 8 * (n + 1) ^ 3 := by nlinarith

end Coeff

section Series

variable (a₁ a₂ : ℕ)

private def qq (τ : ℍ) : ℂ := cexp (2 * π * Complex.I * (τ : ℂ) / N)

private theorem qq_eq (τ : ℍ) : qq N τ = Periodic.qParam N τ := by
  unfold qq Periodic.qParam
  norm_cast

private theorem norm_qq (τ : ℍ) : ‖qq N τ‖ = Real.exp (-2 * π * τ.im / N) := by
  rw [qq_eq, Periodic.norm_qParam]; rfl

private theorem norm_qq_lt_one (τ : ℍ) : ‖qq N τ‖ < 1 := by
  rw [norm_qq, Real.exp_lt_one_iff]
  have h1 : 0 < 2 * π * τ.im / N := by
    have := τ.im_pos; have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N); positivity
  have h2 : -2 * π * τ.im / N = -(2 * π * τ.im / N) := by ring
  rw [h2]; linarith

private theorem norm_qq_pos (τ : ℍ) : 0 < ‖qq N τ‖ := by rw [norm_qq]; exact Real.exp_pos _

private def Gt (τ : ℍ) (i : Idx) : ℂ := coef N a₂ i * qq N τ ^ expo N a₁ i

private def Ft (τ : ℍ) (p : ℕ+ × ℕ+) : ℂ := ∑ j : Fin 3, Gt N a₁ a₂ τ (p, j)

private theorem coef_zero (p : ℕ+ × ℕ+) : coef N a₂ (p, 0) = ((p.2 : ℕ) : ℂ) * zeta N ^ (a₂ * (p.2 : ℕ)) := rfl
private theorem coef_one (p : ℕ+ × ℕ+) : coef N a₂ (p, 1) = ((p.2 : ℕ) : ℂ) * (zeta N)⁻¹ ^ (a₂ * (p.2 : ℕ)) := rfl
private theorem coef_two (p : ℕ+ × ℕ+) : coef N a₂ (p, 2) = -2 * ((p.2 : ℕ) : ℂ) := rfl
private theorem expo_zero (p : ℕ+ × ℕ+) : expo N a₁ (p, 0) = ((p.1 : ℕ) * N + a₁) * (p.2 : ℕ) := rfl
private theorem expo_one (p : ℕ+ × ℕ+) : expo N a₁ (p, 1) = ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ) := rfl
private theorem expo_two (p : ℕ+ × ℕ+) : expo N a₁ (p, 2) = (p.1 : ℕ) * N * (p.2 : ℕ) := rfl

private theorem Ft_eq (τ : ℍ) (p : ℕ+ × ℕ+) : Ft N a₁ a₂ τ p =
    ((p.2 : ℕ) : ℂ) * (zeta N ^ (a₂ * (p.2 : ℕ)) * qq N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zeta N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qq N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
      2 * qq N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))) := by
  rw [Ft, Fin.sum_univ_three, Gt, Gt, Gt, coef_zero, coef_one, coef_two, expo_zero, expo_one, expo_two]
  ring

private theorem summable_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ+ × ℕ+ => r ^ ((p.1 : ℕ) - 1) * (((p.2 : ℕ) : ℝ) * r ^ (p.2 : ℕ))) := by
  have hnr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h1 : Summable (fun k : ℕ+ => ((k : ℕ) : ℝ) * r ^ (k : ℕ)) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hnr).comp_injective PNat.coe_injective
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, pow_one]
  have h2 : Summable (fun c : ℕ+ => r ^ ((c : ℕ) - 1)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).comp_injective PNat.natPred_injective
    refine h.congr fun c => ?_
    simp only [Function.comp_apply, PNat.natPred]
  have h1' : Summable (fun k : ℕ+ => ‖((k : ℕ) : ℝ) * r ^ (k : ℕ)‖) := by
    refine h1.abs.congr fun k => ?_
    exact (Real.norm_eq_abs _).symm
  have h2' : Summable (fun c : ℕ+ => ‖r ^ ((c : ℕ) - 1)‖) := by
    refine h2.abs.congr fun c => ?_
    exact (Real.norm_eq_abs _).symm
  have key := summable_mul_of_summable_norm (R := ℝ) h2' h1'
  exact key

private theorem norm_Gt_le (ha : a₁ < N) (τ : ℍ) (i : Idx) :
    ‖Gt N a₁ a₂ τ i‖ ≤ 2 * (‖qq N τ‖ ^ ((i.1.1 : ℕ) - 1) * (((i.1.2 : ℕ) : ℝ) * ‖qq N τ‖ ^ (i.1.2 : ℕ))) := by
  set r : ℝ := ‖qq N τ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := (norm_qq_lt_one N τ).le
  have hc : 1 ≤ (i.1.1 : ℕ) := i.1.1.2
  have hk : 1 ≤ (i.1.2 : ℕ) := i.1.2.2
  have hexp : (i.1.2 : ℕ) + ((i.1.1 : ℕ) - 1) ≤ expo N a₁ i := by
    refine le_trans ?_ (mul_le_expo ha i)
    have : ((i.1.1 : ℕ) - 1) * ((i.1.2 : ℕ) - 1) + ((i.1.2 : ℕ) + ((i.1.1 : ℕ) - 1)) = (i.1.1 : ℕ) * (i.1.2 : ℕ) := by
      zify [hc, hk]; ring
    omega
  rw [Gt, norm_mul, norm_pow, ← hr]
  have hpow : r ^ expo N a₁ i ≤ r ^ ((i.1.2 : ℕ) + ((i.1.1 : ℕ) - 1)) := pow_le_pow_of_le_one hr0 hr1 hexp
  calc ‖coef N a₂ i‖ * r ^ expo N a₁ i ≤ (2 * (i.1.2 : ℕ)) * r ^ ((i.1.2 : ℕ) + ((i.1.1 : ℕ) - 1)) :=
        mul_le_mul (norm_coef_le N a₂ i) hpow (pow_nonneg hr0 _) (by positivity)
    _ = 2 * (r ^ ((i.1.1 : ℕ) - 1) * (((i.1.2 : ℕ) : ℝ) * r ^ (i.1.2 : ℕ))) := by rw [pow_add]; ring

private theorem summable_norm_Gt (ha : a₁ < N) (τ : ℍ) : Summable (fun i : Idx => ‖Gt N a₁ a₂ τ i‖) := by
  set r : ℝ := ‖qq N τ‖ with hr
  set M : ℕ+ × ℕ+ → ℝ := fun p => 2 * (r ^ ((p.1 : ℕ) - 1) * (((p.2 : ℕ) : ℝ) * r ^ (p.2 : ℕ))) with hM
  have hMs : Summable M := (summable_majorant (norm_nonneg _) (norm_qq_lt_one N τ)).mul_left 2
  have hM0 : ∀ p, 0 ≤ M p := fun p => by rw [hM]; positivity
  have hMaj : Summable (fun i : Idx => M i.1) := by
    rw [summable_prod_of_nonneg (fun i => hM0 i.1)]
    refine ⟨fun p => ?_, ?_⟩
    · exact (hasSum_fintype _).summable
    · simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact hMs.mul_left _
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hMaj
  exact norm_Gt_le N a₁ a₂ ha τ i

private theorem summable_Gt (ha : a₁ < N) (τ : ℍ) : Summable (Gt N a₁ a₂ τ) := (summable_norm_Gt N a₁ a₂ ha τ).of_norm

private theorem hasSum_Ft (ha : a₁ < N) (τ : ℍ) : HasSum (Ft N a₁ a₂ τ) (∑' i, Gt N a₁ a₂ τ i) :=
  (summable_Gt N a₁ a₂ ha τ).hasSum.prod_fiberwise fun _ => hasSum_fintype _

variable [Fact (a₁ < N)]

private theorem hasSum_cT (τ : ℍ) : HasSum (fun n => cT N a₁ a₂ n * qq N τ ^ n) (∑' i, Gt N a₁ a₂ τ i) := by
  have ha : a₁ < N := Fact.out
  have h1 : HasSum (Gt N a₁ a₂ τ ∘ Equiv.sigmaFiberEquiv (expo N a₁)) (∑' i, Gt N a₁ a₂ τ i) :=
    (Equiv.hasSum_iff _).mpr (summable_Gt N a₁ a₂ ha τ).hasSum
  refine h1.sigma fun n => ?_
  have h2 : (fun c : {i : Idx // expo N a₁ i = n} => (Gt N a₁ a₂ τ ∘ Equiv.sigmaFiberEquiv (expo N a₁)) ⟨n, c⟩)
      = fun c => coef N a₂ c.1 * qq N τ ^ n := by
    funext c
    simp only [comp_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, Gt]
    rw [c.2]
  rw [h2]
  have h3 : cT N a₁ a₂ n * qq N τ ^ n = ∑ c : {i : Idx // expo N a₁ i = n}, coef N a₂ c.1 * qq N τ ^ n := by
    rw [cT, Finset.sum_mul]
  rw [h3]
  exact hasSum_fintype _

private theorem hasSum_cA (τ : ℍ) (ha0 : a₁ ≠ 0) :
    HasSum (fun n => cA N a₁ a₂ n * qq N τ ^ n)
      (zeta N ^ a₂ * qq N τ ^ a₁ / (1 - zeta N ^ a₂ * qq N τ ^ a₁) ^ 2) := by
  set x : ℂ := zeta N ^ a₂ * qq N τ ^ a₁ with hx
  have hxn : ‖x‖ < 1 := by
    rw [hx, norm_mul, norm_pow, norm_zeta, one_pow, one_mul, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_qq_lt_one N τ) ha0
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hxn
  have hinj : Function.Injective fun k : ℕ => a₁ * k := mul_right_injective₀ ha0
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => a₁ * k), cA N a₁ a₂ n * qq N τ ^ n = 0 := by
    intro n hn
    have : ¬ a₁ ∣ n := by rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩
    simp [cA, ha0, this]
  refine (hinj.hasSum_iff hsupp).1 ?_
  convert h1 using 1; try rfl
  funext k
  simp only [comp_apply, cA, ha0, ↓reduceIte, dvd_mul_right, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0), hx]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  ring

private theorem hasSum_cW (X : ℍ → ℂ) (τ : ℍ)
    (hX : X τ = zeta N ^ a₂ * qq N τ ^ a₁ / (1 - zeta N ^ a₂ * qq N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, Ft N a₁ a₂ τ p) :
    HasSum (fun n => cW N a₁ a₂ n * qq N τ ^ n) (X τ) := by
  have ha : a₁ < N := Fact.out
  have hT := hasSum_cT N a₁ a₂ τ
  have htsum : ∑' p : ℕ+ × ℕ+, Ft N a₁ a₂ τ p = ∑' i, Gt N a₁ a₂ τ i := (hasSum_Ft N a₁ a₂ ha τ).tsum_eq
  have h0 : HasSum (fun n => (if n = 0 then c0 N a₁ a₂ else 0) * qq N τ ^ n) (c0 N a₁ a₂) := by
    have := hasSum_single (f := fun n => (if n = 0 then c0 N a₁ a₂ else 0) * qq N τ ^ n) 0
      (fun n hn => by simp [hn])
    simpa using this
  have hfun : (fun n => cW N a₁ a₂ n * qq N τ ^ n) = fun n =>
      cA N a₁ a₂ n * qq N τ ^ n + (if n = 0 then c0 N a₁ a₂ else 0) * qq N τ ^ n + cT N a₁ a₂ n * qq N τ ^ n := by
    funext n; rw [cW]; ring
  rw [hfun, hX, htsum]
  by_cases ha0 : a₁ = 0
  · have hA : HasSum (fun n => cA N a₁ a₂ n * qq N τ ^ n) 0 := by
      have : (fun n => cA N a₁ a₂ n * qq N τ ^ n) = 0 := by funext n; simp [cA, ha0]
      rw [this]; exact hasSum_zero
    have := (hA.add h0).add hT
    convert this using 1
    simp [c0, ha0]
    ring
  · have hA := hasSum_cA N a₁ a₂ τ ha0
    have := (hA.add h0).add hT
    convert this using 1
    simp [c0, ha0]

end Series

section QExp

variable (a₁ a₂ : ℕ) [Fact (a₁ < N)]


private theorem summable_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (‖c0 N a₁ a₂‖ + 8 * ((n : ℝ) + 1) ^ 3) * r ^ n) := by
  have hnr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h1 : Summable (fun n : ℕ => ‖c0 N a₁ a₂‖ * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have h2 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * r ^ n) := by
    have h3 := (summable_pow_mul_geometric_of_norm_lt_one 3 hnr).comp_injective Nat.succ_injective
    have h4 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 3 * r ^ (n + 1)) * r⁻¹) := h3.mul_right _
    by_cases hr : r = 0
    · subst hr
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this]
    · refine h4.congr fun n => ?_
      push_cast
      field_simp
      ring
  have := h1.add (h2.mul_left 8)
  refine this.congr fun n => ?_
  ring

private theorem qExpansion_eq_of_hasSum (X : ℍ → ℂ) (hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X)
    (hsum : ∀ τ : ℍ, HasSum (fun n => cW N a₁ a₂ n * qq N τ ^ n) (X τ)) :
    Periodic (X ∘ ofComplex) N ∧ IsBoundedAtImInfty X ∧
      ∀ n, (qExpansion N X).coeff n = cW N a₁ a₂ n := by

  have hper : Periodic (X ∘ ofComplex) N := by
    intro w
    by_cases hw : 0 < im w
    · have hw' : 0 < im (w + N) := by simp [hw]
      simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
      have hq : qq N ⟨w + N, hw'⟩ = qq N ⟨w, hw⟩ := by
        simp only [qq]
        have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        rw [show 2 * (π : ℂ) * Complex.I * (w + N) / N = 2 * π * Complex.I * w / N + 2 * π * Complex.I by
          field_simp, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      have h1 := hsum ⟨w + N, hw'⟩
      rw [hq] at h1
      exact h1.unique (hsum ⟨w, hw⟩)
    · push Not at hw
      have : im (w + N) ≤ 0 := by simpa using hw
      simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

  have hbd : IsBoundedAtImInfty X := by
    rw [isBoundedAtImInfty_iff]
    set r₀ : ℝ := Real.exp (-2 * π / N) with hr₀
    have hr₀0 : 0 ≤ r₀ := (Real.exp_pos _).le
    have hr₀1 : r₀ < 1 := by
      rw [hr₀, Real.exp_lt_one_iff]
      have : 0 < 2 * π / N := by have := natCast_pos N; positivity
      have h2 : -2 * π / N = -(2 * π / N) := by ring
      rw [h2]; linarith
    refine ⟨∑' n : ℕ, (‖c0 N a₁ a₂‖ + 8 * ((n : ℝ) + 1) ^ 3) * r₀ ^ n, 1, fun τ hτ => ?_⟩
    have hr : ‖qq N τ‖ ≤ r₀ := by
      rw [norm_qq, hr₀, Real.exp_le_exp]
      have hN := natCast_pos N
      have : 2 * π * 1 / N ≤ 2 * π * τ.im / N := by gcongr
      have h2 : -2 * π * τ.im / N = -(2 * π * τ.im / N) := by ring
      have h3 : -2 * π / N = -(2 * π * 1 / N) := by ring
      rw [h2, h3]; linarith
    have hs1 : Summable (fun n => ‖cW N a₁ a₂ n * qq N τ ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_bound N a₁ a₂ hr₀0 hr₀1)
      rw [norm_mul, norm_pow]
      exact mul_le_mul (norm_cW_le N a₁ a₂ n) (pow_le_pow_left₀ (norm_nonneg _) hr n) (pow_nonneg (norm_nonneg _) _)
        (by positivity)
    rw [← (hsum τ).tsum_eq]
    refine le_trans (norm_tsum_le_tsum_norm hs1) ?_
    refine Summable.tsum_le_tsum (fun n => ?_) hs1 (summable_bound N a₁ a₂ hr₀0 hr₀1)
    rw [norm_mul, norm_pow]
    exact mul_le_mul (norm_cW_le N a₁ a₂ n) (pow_le_pow_left₀ (norm_nonneg _) hr n) (pow_nonneg (norm_nonneg _) _)
      (by positivity)
  refine ⟨hper, hbd, fun n => ?_⟩
  symm
  refine qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N) hper hmd hbd)
    (fun τ => ?_) n
  have := hsum τ
  simpa only [smul_eq_mul, qq_eq] using this

end QExp

section Main

local notation "Δ" => ModularForm.discriminant


def spread (P : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if (N : ℕ) ∣ n then PowerSeries.coeff (n / N) P else 0

private theorem qExpansion_widthN_of_int {k : ℤ} (f : ModularForm 𝒮ℒ k) (P : PowerSeries ℤ)
    (hP : P.map (Int.castRingHom ℂ) = qExpansion 1 (⇑f : ℍ → ℂ)) :
    (spread N P).map (Int.castRingHom ℂ) = qExpansion N (⇑f : ℍ → ℂ) := by
  ext n
  have hw := qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo'
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty f) n
  rw [PowerSeries.coeff_map]
  refine Eq.trans ?_ hw.symm
  rw [spread, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [← hP, PowerSeries.coeff_map]
  · simp

private def P4 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

private def P6 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℤ)

theorem map_P4 : P4.map (Int.castRingHom ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P4, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]]
    push_cast
    ring

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, Nat.choose]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [h5]
  norm_num

theorem map_P6 : P6.map (Int.castRingHom ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P6, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]]
    push_cast
    ring

private def E46 : ModularForm 𝒮ℒ 10 := (E₄.mul E₆).mcast (by norm_num)

private theorem coe_E46 : (⇑E46 : ℍ → ℂ) = (E₄ : ℍ → ℂ) * E₆ := by rw [E46, coe_mcast, coe_mul]

private theorem map_E46 : (spread N (P4 * P6)).map (Int.castRingHom ℂ) = qExpansion N (⇑E46 : ℍ → ℂ) := by
  apply qExpansion_widthN_of_int
  rw [map_mul, map_P4, map_P6, E46, ModularForm.qExpansion_mcast, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL]

private structure FD where
  L : ℍ → PeriodPair
  hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1
  W : (Fin 2 → ZMod N) → ℍ → ℂ
  hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))
  fricke : (Fin 2 → ZMod N) → ℍ → ℂ
  hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ

variable {N}

private theorem main (X : FD N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ,
      (D : ℂ) * (qExpansion N (X.fricke v * Δ)).coeff n ∈ AZ N := by
  classical
  set a₁ : ℕ := (v 0).val with ha₁
  set a₂ : ℕ := (v 1).val with ha₂
  have ha₁N : a₁ < N := ZMod.val_lt _
  have ha₂N : a₂ < N := ZMod.val_lt _
  haveI : Fact (a₁ < N) := ⟨ha₁N⟩
  have h0 : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero (v 0)).mp h.1
    · exact (ZMod.val_eq_zero (v 1)).mp h.2

  obtain ⟨-, -, -, hpkg, -⟩ := WLight.weierstrassP_qExpansion_package
  obtain ⟨hseries, hmdP⟩ := hpkg X.L X.hL N a₁ a₂ ha₁N ha₂N h0

  set Wv : ℍ → ℂ := X.W v with hWv
  have h2pi : ((2 * (π : ℂ) * Complex.I) ^ 2) ≠ 0 := by
    apply pow_ne_zero; simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hWτ : ∀ τ : ℍ, Wv τ = zeta N ^ a₂ * qq N τ ^ a₁ / (1 - zeta N ^ a₂ * qq N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, Ft N a₁ a₂ τ p := by
    intro τ
    rw [hWv, X.hW v τ, ← ha₁, ← ha₂, hseries τ, inv_mul_cancel_left₀ h2pi]
    simp only [Ft_eq, zeta, qq]
  have hsum : ∀ τ, HasSum (fun n => cW N a₁ a₂ n * qq N τ ^ n) (Wv τ) := fun τ =>
    hasSum_cW N a₁ a₂ Wv τ (hWτ τ)
  have hmdW : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Wv := by
    have : Wv = fun τ => ((2 * (π : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (X.L τ) (((a₁ : ℂ) * τ + a₂) / N) := by
      funext τ; rw [hWv, X.hW v τ]
    rw [this]
    exact mdifferentiable_const.mul hmdP
  obtain ⟨hperW, hbdW, hcoefW⟩ := qExpansion_eq_of_hasSum N a₁ a₂ Wv hmdW hsum

  have hfun : X.fricke v * Δ = (-(1 / 2592 : ℂ)) • ((⇑E46 : ℍ → ℂ) * Wv) := by
    funext τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, coe_E46, hWv, X.hfricke v τ]
    field_simp [discriminant_ne_zero τ]

  have hE : (⇑E46 : ℍ → ℂ) = ⇑E46 := rfl
  have hperE : Periodic ((⇑E46 : ℍ → ℂ) ∘ ofComplex) N :=
    periodic_ofComplex_natCast (SlashInvariantFormClass.periodic_comp_ofComplex E46 one_mem_strictPeriods_SL) N
  have haE : AnalyticAt ℂ (cuspFunction N (⇑E46 : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperE E46.holo' (ModularFormClass.bdd_at_infty E46)
  have haW : AnalyticAt ℂ (cuspFunction N Wv) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperW hmdW hbdW
  have hperEW : Periodic (((⇑E46 : ℍ → ℂ) * Wv) ∘ ofComplex) N := by
    intro w; have h1 := hperE w; have h2 := hperW w
    simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢; rw [h1, h2]
  have haEW : AnalyticAt ℂ (cuspFunction N ((⇑E46 : ℍ → ℂ) * Wv)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperEW (E46.holo'.mul hmdW)
      ((ModularFormClass.bdd_at_infty E46).mul hbdW)
  have hq : qExpansion N (X.fricke v * Δ) =
      (-(1 / 2592 : ℂ)) • ((spread N (P4 * P6)).map (Int.castRingHom ℂ) * qExpansion N Wv) := by
    rw [hfun, qExpansion_smul haEW, qExpansion_mul haE haW, map_E46]

  refine ⟨2592 * 12 * N ^ 2, mul_ne_zero (by norm_num) (pow_ne_zero 2 (NeZero.ne N)), fun n => ?_⟩
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_mul, smul_eq_mul]
  have hc : ((2592 * 12 * N ^ 2 : ℕ) : ℂ) * (-(1 / 2592) *
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff ij.1 ((spread N (P4 * P6)).map (Int.castRingHom ℂ)) *
        PowerSeries.coeff ij.2 (qExpansion N Wv))
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, -(PowerSeries.coeff ij.1 ((spread N (P4 * P6)).map (Int.castRingHom ℂ)) *
        ((12 * (N : ℂ) ^ 2) * PowerSeries.coeff ij.2 (qExpansion N Wv))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    push_cast
    ring
  rw [hc]
  refine sum_mem fun ij _ => neg_mem (mul_mem ?_ ?_)
  · rw [PowerSeries.coeff_map]; exact intCast_mem N _
  · rw [hcoefW]; exact cW_mem N a₁ a₂ ha₂N h0 _

end Main
end FrickeIntegral

theorem _root_.ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
    (N : ℕ) [NeZero N]
    (L : UpperHalfPlane → PeriodPair)
    (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), W v τ =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ,
      (D : ℂ) * (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant)).coeff n ∈
        Algebra.adjoin ℤ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ) :=
  FrickeIntegral.main ⟨L, hL, W, hW, fricke, hfricke⟩ v hv

end WLightS10.S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin

namespace WLightS10.S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational

open Complex UpperHalfPlane ModularForm Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeToInfinity

local notation "Δ" => ModularForm.discriminant



variable (N : ℕ) [NeZero N]



private theorem qExpansion_coeff_one_eq_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion 1 g).coeff n = (qExpansion N g).coeff (N * n) := by
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)]

theorem ratCast_mem (K : IntermediateField ℚ ℂ) (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r





section PowerSeriesK

variable (K : IntermediateField ℚ ℂ)

private def CoeffIn (p : PowerSeries ℂ) : Prop := ∀ n, p.coeff n ∈ K

variable {K}

private theorem CoeffIn.exists_map {p : PowerSeries ℂ} (h : CoeffIn K p) :
    ∃ p₀ : PowerSeries K, p₀.map (algebraMap K ℂ) = p := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h n⟩, ?_⟩
  ext n
  simp

private theorem coeffIn_map (p₀ : PowerSeries K) : CoeffIn K (p₀.map (algebraMap K ℂ)) := fun n => by
  rw [PowerSeries.coeff_map]; exact (p₀.coeff n).2

private theorem CoeffIn.mul {p q : PowerSeries ℂ} (hp : CoeffIn K p) (hq : CoeffIn K q) : CoeffIn K (p * q) := by
  obtain ⟨p₀, rfl⟩ := hp.exists_map
  obtain ⟨q₀, rfl⟩ := hq.exists_map
  rw [← map_mul]; exact coeffIn_map q₀ |> fun _ => coeffIn_map (p₀ * q₀)

private theorem CoeffIn.pow {p : PowerSeries ℂ} (hp : CoeffIn K p) (n : ℕ) : CoeffIn K (p ^ n) := by
  obtain ⟨p₀, rfl⟩ := hp.exists_map
  rw [← map_pow]; exact coeffIn_map _

private theorem coeffIn_of_rat {p : PowerSeries ℂ} (h : ∀ n, ∃ r : ℚ, p.coeff n = (r : ℂ)) : CoeffIn K p := by
  intro n; obtain ⟨r, hr⟩ := h n; rw [hr]; exact ratCast_mem K r

private theorem CoeffIn.of_mul_X_pow {p : PowerSeries ℂ} {r : ℕ} (h : CoeffIn K (p * PowerSeries.X ^ r)) :
    CoeffIn K p := by
  intro n
  have := h (n + r)
  rwa [PowerSeries.coeff_mul_X_pow] at this

private theorem CoeffIn.of_mul_unit {p V : PowerSeries ℂ} (hpV : CoeffIn K (p * V)) (hV : CoeffIn K V)
    (hV0 : PowerSeries.constantCoeff V = 1) : CoeffIn K p := by
  obtain ⟨V₀, hV₀⟩ := hV.exists_map
  obtain ⟨T₀, hT₀⟩ := hpV.exists_map
  have hunit : IsUnit V₀ := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h1 : algebraMap K ℂ (PowerSeries.constantCoeff V₀) = 1 := by
      rw [← hV0, ← hV₀, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    have : PowerSeries.constantCoeff V₀ = 1 := by
      apply (algebraMap K ℂ).injective
      rw [h1, map_one]
    rw [this]; exact isUnit_one
  obtain ⟨u, hu⟩ := hunit
  have hVne : V ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [hV0, map_zero] at this
    exact one_ne_zero this
  have key : p = (T₀ * ↑u⁻¹).map (algebraMap K ℂ) := by
    apply mul_right_cancel₀ hVne
    rw [← hT₀]
    conv_rhs => rw [← hV₀, ← hu, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [key]; exact coeffIn_map _

end PowerSeriesK

private theorem exists_mvPolynomial_map {ι : Type*} (K : IntermediateField ℚ ℂ) (R : MvPolynomial ι ℂ)
    (h : ∀ mo, R.coeff mo ∈ K) : ∃ R₀ : MvPolynomial ι K, R₀.map (algebraMap K ℂ) = R := by
  classical
  refine ⟨∑ mo ∈ R.support, MvPolynomial.monomial mo ⟨R.coeff mo, h mo⟩, ?_⟩
  rw [map_sum]
  ext mo'
  simp only [MvPolynomial.map_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff] at hm; exact hm.symm

section Main

variable {N}
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})

local notation "Γ₁ℝ" M => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem one_mem_strictPeriods_Gamma1 (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private theorem step_up {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {M : ℕ}
    (h : Periodic ((G * Δ ^ M) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M)).coeff n ∈ K) :
    Periodic ((G * Δ ^ (M + 1)) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ (M + 1)) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ (M + 1))).coeff n ∈ K := by
  obtain ⟨hper, hbdd, hmem⟩ := h
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ M) := hG.mul (mdifferentiable_disc.pow M)
  have hΔN : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N := periodic_ofComplex_natCast periodic_disc_one N
  have heq : G * Δ ^ (M + 1) = (G * Δ ^ M) * Δ := by rw [pow_succ, ← mul_assoc]
  rw [heq]
  refine ⟨periodic_mul hper hΔN, hbdd.mul isBoundedAtImInfty_disc, fun n => ?_⟩
  rw [qExpansion_mul (analyticAt_cuspFunction_zero (natCast_pos N) hper hmd hbdd)
    (analyticAt_cuspFunction_zero (natCast_pos N) hΔN mdifferentiable_disc isBoundedAtImInfty_disc),
    PowerSeries.coeff_mul]
  refine sum_mem fun ij _ => mul_mem (hmem _) ?_
  obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
  rw [hr]; exact ratCast_mem K r

private theorem step_up_le {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {M M' : ℕ} (hMM' : M ≤ M')
    (h : Periodic ((G * Δ ^ M) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M)).coeff n ∈ K) :
    Periodic ((G * Δ ^ M') ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M') ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M')).coeff n ∈ K := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMM'
  induction d with
  | zero => simpa using h
  | succ d ih => exact step_up K hG (ih (Nat.le_add_right M d))

include hL hW hfricke hjf hK in
private theorem main (k : ℤ) (a b m : ℕ)
    (f : ModularForm (Γ₁ℝ N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ mo, P.coeff mo ∈ K) (hQK : ∀ mo, Q.coeff mo ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) P τ)
    (n : ℕ) :
    (qExpansion 1 ⇑f).coeff n ∈ K := by
  classical
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen

  let G : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    have hnum : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * (E₄ τ ^ a * E₆ τ ^ b)) :=
      f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))
    have hinv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (Δ τ ^ m)⁻¹) := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have h1 := UpperHalfPlane.mdifferentiable_iff.1 (mdifferentiable_disc.pow m)
      have h2 : DifferentiableOn ℂ (fun z : ℂ => ((((Δ : ℍ → ℂ) ^ m) ∘ ofComplex) z)⁻¹) {z | 0 < z.im} :=
        h1.inv fun z hz => by
          simp only [comp_apply, Pi.pow_apply]
          exact pow_ne_zero _ (discriminant_ne_zero _)
      exact h2.congr fun z _ => by simp [comp_apply]
    have : G = fun τ => (f τ * (E₄ τ ^ a * E₆ τ ^ b)) * (Δ τ ^ m)⁻¹ := by
      funext τ; simp only [G, div_eq_mul_inv]
    rw [this]
    exact hnum.mul hinv
  have hGQ : G * MvPolynomial.aeval gen Q = MvPolynomial.aeval gen P := by
    funext τ
    simp only [Pi.mul_apply, G]
    rw [div_mul_eq_mul_div, div_eq_iff (hΔm τ), hid τ, mul_comm]

  obtain ⟨P₀, hP₀⟩ := exists_mvPolynomial_map K P hPK
  obtain ⟨Q₀, hQ₀⟩ := exists_mvPolynomial_map K Q hQK
  have hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0 :=
    WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke jf hjf K hK
      G hGhol P₀ Q₀ (by rw [hQ₀]; exact hQ0) (by rw [hQ₀, hP₀]; exact hGQ)
  obtain ⟨M₀, hM₀⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL W hW
    fricke hfricke jf hjf K hK hGhol P Q hPK hQK hQ0 hGQ hint

  set M₁ : ℕ := M₀ + m with hM₁
  obtain ⟨hperN, hbddN, hmemN⟩ := step_up_le K hGhol (Nat.le_add_right M₀ m) hM₀

  let Emf : ModularForm 𝒮ℒ (a * 4 + b * 6 + M₀ * 12) :=
    ((E₄.pow a).mul (E₆.pow b)).mul ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow M₀)
  have hEmf : (⇑Emf : ℍ → ℂ) = fun τ => E₄ τ ^ a * E₆ τ ^ b * Δ τ ^ M₀ := by
    funext τ; simp [Emf]
  have hgeq : G * Δ ^ M₁ = (⇑f : ℍ → ℂ) * ⇑Emf := by
    funext τ
    have hΔ' := hΔm τ
    simp only [Pi.mul_apply, Pi.pow_apply, hEmf, G, hM₁, pow_add]
    field_simp
  have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) * ⇑Emf) := f.holo'.mul Emf.holo'
  have hgper : Periodic (((⇑f : ℍ → ℂ) * ⇑Emf) ∘ ofComplex) 1 :=
    periodic_mul (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma1 N))
      (SlashInvariantFormClass.periodic_comp_ofComplex Emf one_mem_strictPeriods_SL)
  have hgbdd : IsBoundedAtImInfty ((⇑f : ℍ → ℂ) * ⇑Emf) :=
    (ModularFormClass.bdd_at_infty f).mul (ModularFormClass.bdd_at_infty Emf)

  have hS : CoeffIn K (qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑Emf)) := by
    intro j
    rw [qExpansion_coeff_one_eq_widthN N hghol hgper hgbdd, ← hgeq]
    exact hmemN _

  have hprod : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑Emf) = qExpansion 1 ⇑f * qExpansion 1 ⇑Emf :=
    qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma1 N))
      (ModularFormClass.analyticAt_cuspFunction_zero Emf one_pos one_mem_strictPeriods_SL)

  set qΔ : PowerSeries ℂ := qExpansion 1 (Δ : ℍ → ℂ) with hqΔ
  set D₀ : PowerSeries ℂ := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) qΔ with hD₀
  have hqΔ0 : PowerSeries.constantCoeff qΔ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hqΔ]
    exact CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  have hqΔeq : qΔ = D₀ * PowerSeries.X := by
    conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const qΔ, hqΔ0, map_zero, add_zero]
  have hD₀0 : PowerSeries.constantCoeff D₀ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hD₀, PowerSeries.coeff_mk, zero_add, hqΔ]
    exact discriminant_qExpansion_coeff_one
  have hD₀K : CoeffIn K D₀ := by
    intro j
    rw [hD₀, PowerSeries.coeff_mk, hqΔ]
    obtain ⟨r, hr⟩ := qExpansion_disc_rat_one (j + 1)
    rw [hr]; exact ratCast_mem K r
  set V : PowerSeries ℂ := qExpansion 1 (E₄ : ℍ → ℂ) ^ a * qExpansion 1 (E₆ : ℍ → ℂ) ^ b * D₀ ^ M₀
    with hV
  have hEmf_q : qExpansion 1 ⇑Emf = V * PowerSeries.X ^ M₀ := by
    have h1 : qExpansion 1 ⇑Emf = qExpansion 1 (E₄ : ℍ → ℂ) ^ a * qExpansion 1 (E₆ : ℍ → ℂ) ^ b *
        qΔ ^ M₀ := by
      simp only [Emf, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hqΔ]
      rfl
    rw [h1, hqΔeq, mul_pow, hV]
    ring
  have hVK : CoeffIn K V := by
    rw [hV]
    exact ((coeffIn_of_rat qExpansion_E₄_rat).pow a).mul ((coeffIn_of_rat qExpansion_E₆_rat).pow b)
      |>.mul (hD₀K.pow M₀)
  have hV0 : PowerSeries.constantCoeff V = 1 := by
    have h4 : PowerSeries.constantCoeff (qExpansion 1 (E₄ : ℍ → ℂ)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₄]
      exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
    have h6 : PowerSeries.constantCoeff (qExpansion 1 (E₆ : ℍ → ℂ)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₆]
      exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩
    rw [hV, map_mul, map_mul, map_pow, map_pow, map_pow, h4, h6, hD₀0]
    simp

  have hT : CoeffIn K (qExpansion 1 ⇑f * V) := by
    apply CoeffIn.of_mul_X_pow (r := M₀)
    rw [mul_assoc, ← hEmf_q, ← hprod]
    exact hS
  exact CoeffIn.of_mul_unit hT hVK hV0 n

end Main
end FrickeToInfinity

theorem _root_.ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (k : ℤ) (a b m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ mo, P.coeff mo ∈ K) (hQK : ∀ mo, Q.coeff mo ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) P τ)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 ⇑f).coeff n ∈ K :=
  FrickeToInfinity.main L hL W hW fricke hfricke jf hjf K hK k a b m f P Q hPK hQK hQ0 hid n

end WLightS10.S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational

namespace WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace X1DiamondRational

variable (N : ℕ)

section Main

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem exists_discSeries (K : IntermediateField ℚ ℂ) :
    ∃ δ : PowerSeries K, (∀ n, ∃ r : ℚ, ((PowerSeries.coeff n δ : K) : ℂ) = (r : ℂ)) ∧
      δ.map (algebraMap K ℂ) = qExpansion N (Δ : ℍ → ℂ) := by
  choose r hr using qExpansion_disc_rat N
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem (r n)⟩, fun n => ⟨r n, by simp⟩, ?_⟩
  ext n
  simp [hr n]

variable (σ : (kN N) ≃ₐ[ℚ] (kN N))

private theorem map_phiOf_eq_of_rat {δ : PowerSeries (kN N)}
    (hδ : ∀ n, ∃ r : ℚ, ((PowerSeries.coeff n δ : kN N) : ℂ) = (r : ℂ)) :
    δ.map (phiOf N σ) = δ.map (algebraMap (kN N) ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  obtain ⟨r, hr⟩ := hδ n
  rw [phiOf_ratCast N σ r _ hr]
  exact hr.symm

private theorem tσ_lift {g g' : ℍ → ℂ} (h : Tσ σ g g') :
    ∃ m : ℕ, RatAt N (kN N) m g ∧ RatAt N (kN N) m g' ∧ ∀ M : ℕ, m ≤ M →
      ∃ p : PowerSeries (kN N), p.map (algebraMap (kN N) ℂ) = qExpansion N (g * Δ ^ M) ∧
        p.map (phiOf N σ) = qExpansion N (g' * Δ ^ M) := by
  obtain ⟨m, hg, hg', h4⟩ := h.exists
  refine ⟨m, hg, hg', ?_⟩
  intro M hM
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  obtain ⟨p₀, hp₀⟩ := hg.exists_map
  have hp₀' := TRel.map_eq (phiOf_mem N σ) h4 hp₀
  obtain ⟨δ, hδrat, hδ⟩ := exists_discSeries (N := N) (kN N)
  refine ⟨p₀ * δ ^ d, ?_, ?_⟩
  · induction d with
    | zero => simpa using hp₀
    | succ d ih =>
        have hR : RatAt N (kN N) (m + d) g := hg.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), hδ, ← add_assoc, pow_succ,
          ← mul_assoc, qExpansion_mul hR.analyticAt analyticAt_disc]
  · induction d with
    | zero => simpa using hp₀'
    | succ d ih =>
        have hR : RatAt N (kN N) (m + d) g' := hg'.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), map_phiOf_eq_of_rat σ hδrat, hδ,
          ← add_assoc, pow_succ, ← mul_assoc, qExpansion_mul hR.analyticAt analyticAt_disc]

variable {σ}

private theorem aeval_relPoly (φ : kN N →+* ℂ) (G : ℍ → ℂ) (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N))
    (P Q : MvPolynomial (Idx N) (kN N)) :
    MvPolynomial.aeval (fun o : Option (Idx N) => o.elim G (gen N t))
      (MvPolynomial.map φ (MvPolynomial.X none * MvPolynomial.rename some Q -
        MvPolynomial.rename some P)) = G * evφ N φ t Q - evφ N φ t P := by
  simp only [map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.map_rename,
    MvPolynomial.aeval_rename]
  rfl

private theorem evφ_algebraMap (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) :
    evφ N (algebraMap (kN N) ℂ) t R = ev N t R := rfl

theorem cw_ne_zero {b : ℍ → ℂ} (hb : b ≠ 0) (γ : SL(2, ℤ)) : cw b γ ≠ 0 := by
  intro h
  apply hb
  have : cw (cw b γ) γ⁻¹ = b := by rw [← cw_mul, mul_inv_cancel, cw_one]
  rw [← this, h]; rfl

private theorem exists_series_fixed {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (σ : (kN N) ≃ₐ[ℚ] (kN N)) :
    ∃ X : PowerSeries (kN N), X.map (algebraMap (kN N) ℂ) = qExpansion N (cw G γ * Δ ^ m) ∧
      X.map (phiOf N σ) = qExpansion N (cw G γ * Δ ^ m) := by
  classical

  have hperG : Periodic (G ∘ ofComplex) 1 := periodic_of_T_invariant fun τ => hinv _ (T_mem_Gamma1 N) τ
  have hinvγ : ∀ g ∈ Gamma1 N, ∀ τ : ℍ, cw G γ (g • τ) = cw G γ τ := by
    intro g hg τ
    simp only [cw_apply]
    have : γ • g • τ = (γ * g * γ⁻¹) • γ • τ := by simp only [mul_smul, inv_smul_smul]
    rw [this]; exact hinv _ (conj_mem_Gamma1 N hγ hg) _
  have hperγ : Periodic (cw G γ ∘ ofComplex) 1 :=
    periodic_of_T_invariant fun τ => hinvγ _ (T_mem_Gamma1 N) τ
  have hratG : RatAt N (kN N) m G :=
    ⟨hG, periodic_mul (periodic_ofComplex_natCast hperG N)
      (periodic_pow (periodic_ofComplex_natCast periodic_disc_one N) m),
      by simpa [cw_one] using hpb 1,
      fun n => by obtain ⟨r, hr⟩ := hrat n; rw [hr]; exact ratCast_mem r⟩

  obtain ⟨P, Q, hb0, hGb⟩ := descent hG (fun g hg => hinv g (Gamma_le_Gamma1 N hg)) hpb hratG

  obtain ⟨s, hs, hσ⟩ := exists_pow_of_aut N σ

  have hT0 : Tσ σ (G * evφ N (algebraMap (kN N) ℂ) id Q - evφ N (algebraMap (kN N) ℂ) id P)
      (G * evφ N (phiOf N σ) (ds N s ∘ id) Q - evφ N (phiOf N σ) (ds N s ∘ id) P) := by
    have hfam : ∀ o : Option (Idx N), Tσ σ ((fun o : Option (Idx N) => o.elim G (gen N id)) o)
        ((fun o : Option (Idx N) => o.elim G (gen N (ds N s ∘ id))) o) := by
      intro o
      cases o with
      | none =>
          exact tRel_self_of_rat hG hratG.periodic hratG.bdd hrat
      | some o => exact tσ_gen σ hs hσ id (fun v hv => hv) o
    have := tσ_aeval σ hfam (MvPolynomial.X none * MvPolynomial.rename some Q - MvPolynomial.rename some P)
    rwa [aeval_relPoly, aeval_relPoly] at this
  have hzero : G * evφ N (phiOf N σ) (ds N s) Q - evφ N (phiOf N σ) (ds N s) P = 0 := by
    have h0 : G * evφ N (algebraMap (kN N) ℂ) id Q - evφ N (algebraMap (kN N) ℂ) id P = 0 := by
      rw [evφ_algebraMap, evφ_algebraMap, hGb, sub_self]
    exact (tσ_zero_iff σ hT0).mp h0

  obtain ⟨γ', ⟨g₁, hg₁, rfl⟩, hvm⟩ := exists_twist_conj N hγ s
  have hvm' : (vm N (g₁ * γ) ∘ ds N s) = (ds N s ∘ vm N γ) := funext hvm
  have hcwG : cw G (g₁ * γ) = cw G γ := by
    rw [cw_mul]; congr 1; funext τ; exact hinv g₁ hg₁ τ

  have hE1 : cw G γ * ev N (vm N γ) Q = ev N (vm N γ) P := by
    have := congrArg (fun F => cw F γ) hGb
    simp only [cw_mul_fun, cw_ev] at this
    exact this
  have hE2 : cw G γ * evφ N (phiOf N σ) (ds N s ∘ vm N γ) Q = evφ N (phiOf N σ) (ds N s ∘ vm N γ) P := by
    have h := congrArg (fun F => cw F (g₁ * γ)) (sub_eq_zero.mp hzero)
    simp only [cw_mul_fun, cw_evφ, hcwG] at h
    rw [hvm'] at h
    exact h

  have hTQ : Tσ σ (ev N (vm N γ) Q) (evφ N (phiOf N σ) (ds N s ∘ vm N γ) Q) :=
    tσ_ev σ hs hσ (vm N γ) (fun v hv => vm_ne_zero N γ hv) Q
  have hTP : Tσ σ (ev N (vm N γ) P) (evφ N (phiOf N σ) (ds N s ∘ vm N γ) P) :=
    tσ_ev σ hs hσ (vm N γ) (fun v hv => vm_ne_zero N γ hv) P
  obtain ⟨mQ, hQr, hQr', hQlift⟩ := tσ_lift σ hTQ
  obtain ⟨mP, hPr, hPr', hPlift⟩ := tσ_lift σ hTP
  set MQ : ℕ := mQ + mP with hMQ
  obtain ⟨pB, hpB, hpB'⟩ := hQlift MQ (Nat.le_add_right _ _)
  obtain ⟨pA, hpA, hpA'⟩ := hPlift (m + MQ) (by omega)

  have hmdγ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G γ * Δ ^ m) := (mdifferentiable_cw hG γ).mul (mdifferentiable_disc.pow m)
  have hperγm : Periodic ((cw G γ * Δ ^ m) ∘ ofComplex) N :=
    periodic_mul (periodic_ofComplex_natCast hperγ N) (periodic_pow (periodic_ofComplex_natCast periodic_disc_one N) m)
  have hanγ : AnalyticAt ℂ (cuspFunction N (cw G γ * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperγm hmdγ (hpb γ)
  have hQR : RatAt N (kN N) MQ (ev N (vm N γ) Q) := hQr.of_le (Nat.le_add_right _ _)
  have hQR' : RatAt N (kN N) MQ (evφ N (phiOf N σ) (ds N s ∘ vm N γ) Q) := hQr'.of_le (Nat.le_add_right _ _)
  have hsplit : ∀ F : ℍ → ℂ, F * Δ ^ (m + MQ) = Δ ^ m * (F * Δ ^ MQ) := by
    intro F; rw [pow_add]; ring
  have h1 : qExpansion N (cw G γ * Δ ^ m) * pB.map (algebraMap (kN N) ℂ) = pA.map (algebraMap (kN N) ℂ) := by
    rw [hpB, hpA, ← hE1, ← qExpansion_mul hanγ hQR.analyticAt]
    congr 1; rw [pow_add]; ring
  have h2 : qExpansion N (cw G γ * Δ ^ m) * pB.map (phiOf N σ) = pA.map (phiOf N σ) := by
    rw [hpB', hpA', ← hE2, ← qExpansion_mul hanγ hQR'.analyticAt]
    congr 1; rw [pow_add]; ring
  have hpB0 : pB ≠ 0 := by
    intro h0
    have hne := hQR.qExpansion_ne_zero (by
      have : ev N (vm N γ) Q = cw (ev N id Q) γ := by rw [cw_ev]; rfl
      rw [this]; exact cw_ne_zero hb0 γ)
    rw [← hpB, h0, map_zero] at hne
    exact hne rfl
  exact exists_of_mul_eq (algebraMap (kN N) ℂ) (phiOf N σ) hpB0 h1 h2

private theorem rat_cw_of_mem_Gamma0 {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N (cw G γ * Δ ^ m)).coeff n = (r : ℂ) := by
  obtain ⟨X₀, hX₀, -⟩ := exists_series_fixed hG hinv hpb hrat hγ AlgEquiv.refl
  set x : kN N := PowerSeries.coeff n X₀ with hx
  have hxξ : (x : ℂ) = (qExpansion N (cw G γ * Δ ^ m)).coeff n := by
    rw [← hX₀, PowerSeries.coeff_map]; rfl
  obtain ⟨r, hr⟩ := exists_rat_of_fixed N x (fun σ => by
    obtain ⟨X, hX, hX'⟩ := exists_series_fixed hG hinv hpb hrat hγ σ
    have hy : ((PowerSeries.coeff n X : kN N) : ℂ) = (qExpansion N (cw G γ * Δ ^ m)).coeff n := by
      rw [← hX, PowerSeries.coeff_map]; rfl
    have hyx : PowerSeries.coeff n X = x := Subtype.ext (hy.trans hxξ.symm)
    have hφ : phiOf N σ (PowerSeries.coeff n X) = (qExpansion N (cw G γ * Δ ^ m)).coeff n := by
      rw [← hX', PowerSeries.coeff_map]
    rw [hyx, phiOf_apply, ← hxξ] at hφ
    exact Subtype.ext hφ)
  exact ⟨r, by rw [← hxξ, hr]⟩

private theorem cardK (N : ℕ) [NeZero N] (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 ((fun τ => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by

  have hperG : Periodic (G ∘ ofComplex) 1 := periodic_of_T_invariant fun τ => hinv _ (T_mem_Gamma1 N) τ
  have hinvγ : ∀ g ∈ Gamma1 N, ∀ τ : ℍ, cw G γ (g • τ) = cw G γ τ := by
    intro g hg τ
    simp only [cw_apply]
    have : γ • g • τ = (γ * g * γ⁻¹) • γ • τ := by simp only [mul_smul, inv_smul_smul]
    rw [this]; exact hinv _ (conj_mem_Gamma1 N hγ hg) _
  have hperγ : Periodic (cw G γ ∘ ofComplex) 1 :=
    periodic_of_T_invariant fun τ => hinvγ _ (T_mem_Gamma1 N) τ
  have hper1 : Periodic ((G * Δ ^ m) ∘ ofComplex) 1 :=
    periodic_mul hperG (periodic_pow periodic_disc_one m)
  have hper1γ : Periodic ((cw G γ * Δ ^ m) ∘ ofComplex) 1 :=
    periodic_mul hperγ (periodic_pow periodic_disc_one m)
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ m) := hG.mul (mdifferentiable_disc.pow m)
  have hmdγ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G γ * Δ ^ m) :=
    (mdifferentiable_cw hG γ).mul (mdifferentiable_disc.pow m)
  have hbd1 : IsBoundedAtImInfty (G * Δ ^ m) := by simpa [cw_one] using hbd 1
  have hratN : ∀ n, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ) :=
    qExpansion_widthN_rat N hmd hper1 hbd1 hrat
  have key := fun n => rat_cw_of_mem_Gamma0 (N := N) hG hinv hbd hratN hγ n
  exact qExpansion_widthOne_rat N hmdγ hper1γ (hbd γ) key n

end Main
end X1DiamondRational

theorem _root_.ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 (N : ℕ) [NeZero N] (m : ℕ)
    (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) :=
  X1DiamondRational.cardK N m G hG hinv hbd hrat γ hγ n

end WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0

namespace WLightS10.S_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaNDescent

private structure FD (N : ℕ) [NeZero N] where
  L : ℍ → PeriodPair
  hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1
  W : (Fin 2 → ZMod N) → ℍ → ℂ
  hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))
  fricke : (Fin 2 → ZMod N) → ℍ → ℂ
  hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ
  jf : ℍ → ℂ
  hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

variable (N : ℕ) [NeZero N]



variable {N}
variable (X : FD N)

private def genSet : Set (ℍ → ℂ) := insert X.jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = X.fricke v}


private def gen : Idx N → ℍ → ℂ := fun o => o.elim X.jf fun v => X.fricke v.1

private theorem gen_eq : gen X = fun o : Idx N => o.elim X.jf fun v => X.fricke v.1 := rfl

section Width

local notation "Δ" => ModularForm.discriminant








variable (N : ℕ) [NeZero N]







variable (K : IntermediateField ℚ ℂ)


variable {N K}









end Width

section Invariance

variable {N : ℕ}

local notation "Δ" => ModularForm.discriminant







private theorem conj_mem_Gamma (N : ℕ) (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  Subgroup.Normal.conj_mem (Gamma_normal N) g hg α

end Invariance

section Fricke

variable {N : ℕ} [NeZero N] (X : FD N)

local notation "Δ" => ModularForm.discriminant

private def ev (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen X) (MvPolynomial.map (algebraMap (kN N) ℂ) R)

private theorem gen_mem (o : Idx N) : gen X o ∈ genSet X := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩

private theorem aeval_mem_adjoin (R : MvPolynomial (Idx N) ℂ) :
    MvPolynomial.aeval (gen X) R ∈ Algebra.adjoin ℂ (genSet X) := by
  induction R using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_mem X o))

private theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev X R ∈ Algebra.adjoin ℂ (genSet X) :=
  aeval_mem_adjoin X _

private theorem adjoin_isDomain {a b : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ (genSet X))
    (hb : b ∈ Algebra.adjoin ℂ (genSet X)) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N X.L X.hL X.W X.hW
    X.fricke X.hfricke X.jf X.hjf
  exact h6 a b ha hb hab

private theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev X (Q i) ≠ 0) : ev X (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev X (Q a) * ev X (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain X (ev_mem_adjoin X _) (ev_mem_adjoin X _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

end Fricke

section Descent

variable {N : ℕ} [NeZero N] (X : FD N)

local notation "Δ" => ModularForm.discriminant



private theorem exists_ev_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin (kN N) (genSet X)) :
    ∃ R : MvPolynomial (Idx N) (kN N), ev X R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx

  have hsec : ∀ y : genSet X, ∃ o : Idx N, gen X o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  rw [ev, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen X ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl


private theorem descent {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : RatAt N (kN N) m G) :
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev X Q ≠ 0 ∧ G * ev X Q = ev X P := by
  classical

  set S : Set (ℍ → ℂ) := {F | ∃ α : SL(2, ℤ), F = cw G α} with hS
  have hGS : G ∈ S := ⟨1, (cw_one G).symm⟩
  have hhol : ∀ F ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rintro F ⟨α, rfl⟩; exact mdifferentiable_cw hG α
  have hpb' : ∀ F ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) := by
    rintro F ⟨α, rfl⟩; exact ⟨m, hpb α⟩
  have hst : ∀ γ : SL(2, ℤ), ∀ F ∈ S, (F ∘ (γ • ·)) ∈ S := by
    rintro γ F ⟨α, rfl⟩
    exact ⟨α * γ, by rw [cw_mul]; rfl⟩
  have hinvS : ∀ F ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    rintro F ⟨α, rfl⟩ γ hγ τ
    simp only [cw_apply]
    have : α • γ • τ = (α * γ * α⁻¹) • α • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (conj_mem_Gamma N α hγ) _
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N X.L X.hL
    X.W X.hW X.fricke X.hfricke X.jf X.hjf S hhol hpb' hst hinvS hGS

  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => ⟨m, hpb γ⟩
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N X.L X.hL
    X.W X.hW X.fricke X.hfricke X.jf X.hjf ha hb hb0 hG hGb hpbG

  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, hpiK, hGirel⟩ :=
    WLight.frickeFunction_intBaseChange N X.L X.hL X.W X.hW X.fricke
      X.hfricke X.jf X.hjf hG ha hb hb0 hGb p hprel

  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev X R = Pi i := fun i =>
    exists_ev_of_mem_adjoin X (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev X R = Qi i := fun i =>
    exists_ev_of_mem_adjoin X (hPQ i).2.1
  choose Ph hPh using hPi
  choose Qh hQh using hQi
  have hrati : ∀ i, ∃ mi : ℕ, RatAt N (kN N) mi (Gi i) := by
    intro i
    obtain ⟨mi, h1, h2, h3⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N
      X.L X.hL X.W X.hW X.fricke X.hfricke X.jf X.hjf (kN N) rfl
      (hGimd i) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i))
      (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh i)) (coeff_map_mem _) (coeff_map_mem _)
      (by
        have := (hPQ i).2.2.1
        rwa [← hQh i] at this)
      (by
        have := (hPQ i).2.2.2
        rw [← hQh i, ← hPh i] at this
        exact this)
      ⟨di i, pi i, hpiK i, hGirel i⟩
    exact ⟨mi, (hGimd i), h1, h2, h3⟩
  choose mi hmi using hrati

  set M : ℕ := m + ∑ i, mi i with hM
  have hGM : RatAt N (kN N) M G := hrat.of_le (Nat.le_add_right _ _)
  have hGiM : ∀ i, RatAt N (kN N) M (Gi i) := fun i =>
    (hmi i).of_le (le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i))
      (Nat.le_add_left _ _))

  have hmem : G ∈ Submodule.span ℂ (Set.range Gi) := by
    rw [hGsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨κ, hκ⟩ := exists_rat_combination (kN N) hGiM hGM hmem

  refine ⟨∑ i, MvPolynomial.C (κ i) * Ph i * ∏ j ∈ Finset.univ.erase i, Qh j, ∏ i, Qh i, ?_, ?_⟩
  · exact ev_prod_ne_zero X Finset.univ Qh fun i _ => by rw [hQh i]; exact (hPQ i).2.2.1
  · have hev_prod : ∀ (s : Finset (Fin n)), ev X (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
      intro s; simp only [ev, map_prod]; exact Finset.prod_congr rfl fun j _ => hQh j
    rw [hκ, hev_prod, Finset.sum_mul]
    simp only [ev, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C, map_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (MvPolynomial.aeval (gen X)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i)) = Pi i := hPh i
    have h2 : ∀ j, (MvPolynomial.aeval (gen X)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh j)) = Qi j :=
      hQh
    simp only [h1, h2]
    rw [← Finset.mul_prod_erase Finset.univ Qi (Finset.mem_univ i), ← (hPQ i).2.2.2]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [smul_one_smul, mul_assoc]
    rfl

end Descent

private theorem main (N : ℕ) [NeZero N] (X : FD N) (K : IntermediateField ℚ ℂ) (hK : K = kN N)
    (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * ModularForm.discriminant ^ m))
    (hcoeff : ∀ n : ℕ, (qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K) :
    ∃ P Q : MvPolynomial (Idx N) K,
      MvPolynomial.aeval (fun o : Idx N => o.elim X.jf fun v => X.fricke v.1) (Q.map (algebraMap K ℂ)) ≠ 0 ∧
      G * MvPolynomial.aeval (fun o : Idx N => o.elim X.jf fun v => X.fricke v.1) (Q.map (algebraMap K ℂ)) =
        MvPolynomial.aeval (fun o : Idx N => o.elim X.jf fun v => X.fricke v.1) (P.map (algebraMap K ℂ)) := by
  subst hK

  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    rw [Gamma_mem, ModularGroup.coe_T_zpow]
    simp
  have hperG : Periodic (G ∘ ofComplex) N := by
    intro w
    by_cases hw : 0 < im w
    · have this : 0 < im (w + N) := by simp [hw]
      simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
      have := hinv _ hT ⟨w, hw⟩
      convert this using 2
      ext
      rw [UpperHalfPlane.modular_T_zpow_smul]
      simp [add_comm, UpperHalfPlane.coe_vadd]
    · push Not at hw
      have : im (w + N) ≤ 0 := by simpa using hw
      simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]
  have hrat : RatAt N (kN N) m G :=
    { mdiff := hG
      periodic := periodic_mul hperG (periodic_pow (periodic_ofComplex_natCast periodic_disc_one N) m)
      bdd := by simpa [cw] using hbd 1
      mem := hcoeff }
  obtain ⟨P, Q, hQ, hGQ⟩ := descent X hG hinv (fun α => hbd α) hrat
  exact ⟨P, Q, hQ, hGQ⟩
end GammaNDescent

theorem _root_.ModularCurve.exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem
    (N : ℕ) [NeZero N]
    (L : UpperHalfPlane → PeriodPair)
    (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), W v τ =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : UpperHalfPlane → ℂ)
    (hjf : ∀ τ : UpperHalfPlane, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : UpperHalfPlane, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hcoeff : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K) :
    ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0 ∧
      G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) =
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) :=
  GammaNDescent.main N ⟨L, hL, W, hW, fricke, hfricke, jf, hjf⟩ K hK m G hG hinv hbd hcoeff

end WLightS10.S_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem

end
