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

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

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

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private def spread (P : PowerSeries ℤ) : PowerSeries ℤ :=
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

private theorem map_P4 : P4.map (Int.castRingHom ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P4, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]]
    push_cast
    ring

private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, Nat.choose]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [h5]
  norm_num

private theorem map_P6 : P6.map (Int.castRingHom ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
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

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty CuspForm.discriminant

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

variable (N : ℕ) [NeZero N]

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem qExpansion_coeff_one_eq_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion 1 g).coeff n = (qExpansion N g).coeff (N * n) := by
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)]

private theorem ratCast_mem (K : IntermediateField ℚ ℂ) (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private theorem qExpansion_E₄_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

private theorem qExpansion_E₆_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

private theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₄_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₆_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc n]
  split_ifs with h
  · exact qExpansion_disc_rat_one _
  · exact ⟨0, by simp⟩

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

private def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 τ.im_pos.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

private theorem tauPair_spec (τ : ℍ) : (tauPair τ).ω₁ = (τ : ℂ) ∧ (tauPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

variable (N : ℕ)

private def WW (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

private def fricke (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ

private def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private theorem WW_spec (v : Fin 2 → ZMod N) (τ : ℍ) : WW N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) :=
  rfl

private theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

private theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

private def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

private def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

private abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke N (t v.1)

private theorem gen_none (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : gen N t none = jf := rfl

private theorem gen_some (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (v : {v : Fin 2 → ZMod N // v ≠ 0}) :
    gen N t (some v) = fricke N (t v.1) := rfl

section Cyclo

variable [NeZero N]

private theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

private scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

private scoped instance instIsGalois : IsGalois ℚ (kN N) := IsCyclotomicExtension.isGalois {N} ℚ (kN N)

private scoped instance instFiniteDimensional : FiniteDimensional ℚ (kN N) :=
  IsCyclotomicExtension.finiteDimensional {N} ℚ (kN N)

private def zetaK : kN N := ⟨zetaN N, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

@[scoped simp] private theorem coe_zetaK : ((zetaK N : kN N) : ℂ) = zetaN N := rfl

private theorem isPrimitiveRoot_zetaK : IsPrimitiveRoot (zetaK N) N := by
  have h := isPrimitiveRoot_zetaN N
  rw [← coe_zetaK] at h
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h

private theorem exists_pow_of_aut (σ : (kN N) ≃ₐ[ℚ] (kN N)) :
    ∃ s : ℕ, s.Coprime N ∧ σ (zetaK N) = zetaK N ^ s := by
  have hμ := isPrimitiveRoot_zetaK N
  refine ⟨((hμ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N).val, ZMod.val_coe_unit_coprime _, ?_⟩
  rw [hμ.autToPow_spec ℚ σ]

private theorem exists_rat_of_fixed (x : kN N) (hx : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), σ x = x) :
    ∃ r : ℚ, (x : ℂ) = (r : ℂ) := by
  have := (IsGalois.mem_bot_iff_fixed x).2 hx
  rw [IntermediateField.mem_bot] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨r, ?_⟩
  rw [← hr]
  rfl

private def phiOf (σ : (kN N) ≃ₐ[ℚ] (kN N)) : kN N →+* ℂ :=
  (algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom

private theorem phiOf_apply (σ : (kN N) ≃ₐ[ℚ] (kN N)) (z : kN N) : phiOf N σ z = ((σ z : kN N) : ℂ) := rfl

private theorem phiOf_mem (σ : (kN N) ≃ₐ[ℚ] (kN N)) (z : kN N) : phiOf N σ z ∈ kN N := (σ z).2

private theorem phiOf_zeta (σ : (kN N) ≃ₐ[ℚ] (kN N)) {s : ℕ} (hs : σ (zetaK N) = zetaK N ^ s)
    (z : kN N) (hz : (z : ℂ) = zetaN N) : phiOf N σ z = zetaN N ^ s := by
  have : z = zetaK N := Subtype.ext hz
  rw [phiOf_apply, this, hs]
  rfl

private theorem phiOf_ratCast (σ : (kN N) ≃ₐ[ℚ] (kN N)) (r : ℚ) (z : kN N) (hz : (z : ℂ) = (r : ℂ)) :
    phiOf N σ z = r := by
  have : z = algebraMap ℚ (kN N) r := by
    apply Subtype.ext; rw [hz]; rfl
  rw [phiOf_apply, this, AlgEquiv.commutes]
  rfl

end Cyclo

section Width

local notation "Δ" => ModularForm.discriminant

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem disc_ne_zero_fun : (Δ : ℍ → ℂ) ≠ 0 := fun h => by
  have := congrFun h UpperHalfPlane.I
  exact discriminant_ne_zero _ this

private theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem periodic_pow {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (m : ℕ) :
    Periodic ((g ^ m) ∘ ofComplex) c := by
  induction m with
  | zero => intro z; simp
  | succ m ih => rw [pow_succ]; exact periodic_mul ih h

private theorem periodic_smul {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) :
    Periodic ((a • g) ∘ ofComplex) c := by
  intro z; have h1 := h z; simp only [comp_apply, Pi.smul_apply] at h1 ⊢; rw [h1]

private theorem periodic_add {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g + g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

variable (N : ℕ) [NeZero N]

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem qExpansion_widthN_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N hg hper hbd n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

private theorem qExpansion_widthOne_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := hrat (N * n)
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)] at hr
  exact ⟨r, hr⟩

private theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by

  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  have h4 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩
  have h6 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using h4
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using h6
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) :=
  qExpansion_widthN_rat N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc
    qExpansion_disc_rat_one n

variable (K : IntermediateField ℚ ℂ)

private structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

private theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

private theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

private theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem r

private theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  simp

private theorem RatAt.qExpansion_ne_zero {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) (hg : g ≠ 0) :
    qExpansion N (g * Δ ^ m) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) h.periodic h.mdiff_mul h.bdd]
  intro h0
  apply hg
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (disc_pow_ne_zero m τ)

end Width

section Transport

variable (N : ℕ) [NeZero N] (K : IntermediateField ℚ ℂ) (φ : K →+* ℂ)

local notation "Δ" => ModularForm.discriminant

private def TRel (g g' : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
    ∃ m : ℕ,
      (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      ∀ (n : ℕ) (z : K),
        (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
        (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z

variable {N K φ}

private theorem TRel.exists {g g' : ℍ → ℂ} (h : TRel N K φ g g') :
    ∃ m : ℕ, RatAt N K m g ∧ RatAt N K m g' ∧
      ∀ (n : ℕ) (z : K), (z : ℂ) = (qExpansion N (g * Δ ^ m)).coeff n →
        (qExpansion N (g' * Δ ^ m)).coeff n = φ z := by
  obtain ⟨hg, hg', m, ⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, h4⟩ := h
  exact ⟨m, ⟨hg, h1, h2, h3⟩, ⟨hg', h1', h2', h3'⟩, h4⟩

private theorem TRel.map_eq {g g' : ℍ → ℂ} {m : ℕ} (_hφK : ∀ z : K, φ z ∈ K)
    (h4 : ∀ (n : ℕ) (z : K), (z : ℂ) = (qExpansion N (g * Δ ^ m)).coeff n →
        (qExpansion N (g' * Δ ^ m)).coeff n = φ z)
    {p : PowerSeries K} (hp : p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m)) :
    p.map φ = qExpansion N (g' * Δ ^ m) := by
  ext n
  rw [PowerSeries.coeff_map]
  symm
  apply h4
  rw [← hp, PowerSeries.coeff_map]
  rfl

private theorem tRel_self_of_rat {g : ℍ → ℂ} {m : ℕ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic ((g * Δ ^ m) ∘ ofComplex) N) (hbd : IsBoundedAtImInfty (g * Δ ^ m))
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N (g * Δ ^ m)).coeff n = (r : ℂ)) : TRel N K φ g g := by
  have hmem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K := by
    intro n; obtain ⟨r, hr⟩ := hrat n; rw [hr]; exact ratCast_mem r
  refine ⟨hg, hg, m, ⟨hper, hbd, hmem⟩, ⟨hper, hbd, hmem⟩, ?_⟩
  intro n z hz
  obtain ⟨r, hr⟩ := hrat n
  rw [hr] at hz ⊢
  have : z = algebraMap ℚ K r := by
    apply Subtype.ext; rw [hz]; rfl
  rw [this]
  simp

end Transport

section Group

variable (N : ℕ)

private def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

private def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN N γ)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem redN_eq (γ : SL(2, ℤ)) : redN N γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) :=
  rfl

private theorem redN_mul (γ γ' : SL(2, ℤ)) : redN N (γ * γ') = redN N γ * redN N γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

private theorem redN_one : redN N 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

private theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm N (γ * γ') v = vm N γ' (vm N γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

private theorem vm_one (v : Fin 2 → ZMod N) : vm N 1 v = v := by simp [vm, redN_one]

private theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm N γ v ≠ 0 := by
  intro h
  apply hv
  have : vm N γ⁻¹ (vm N γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

private theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : ds N s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

private theorem T_pow_mem_Gamma1 (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

private theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 N := by
  simp

private theorem conj_mem_Gamma1 {γ g : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (hg : g ∈ Gamma1 N) :
    γ * g * γ⁻¹ ∈ Gamma1 N := by
  have hA0 : g ∈ Gamma0 N := Gamma1_in_Gamma0 N hg
  set A₀ : Gamma0 N := ⟨g, hA0⟩
  set γ₀ : Gamma0 N := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem N g).mp hg
  haveI : (Gamma1' N).Normal := by
    change ((Gamma0Map N).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' N := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

private theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  Subgroup.Normal.conj_mem (Gamma_normal N) g hg α

private theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

private theorem exists_twist_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (s : ℕ) :
    ∃ γ' : SL(2, ℤ), (∃ g ∈ Gamma1 N, γ' = g * γ) ∧
      ∀ v : Fin 2 → ZMod N, vm N γ' (ds N s v) = ds N s (vm N γ v) := by
  set t : ℤ := γ 1 1 * γ 0 1 * ((s : ℤ) - 1) with ht
  refine ⟨γ * ModularGroup.T ^ t, ⟨γ * ModularGroup.T ^ t * γ⁻¹, conj_mem_Gamma1 N hγ
    (T_pow_mem_Gamma1 N t), by rw [inv_mul_cancel_right]⟩, ?_⟩
  intro v
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod N) h1
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hT : redN N (ModularGroup.T ^ t) = !![1, (t : ZMod N); 0, 1] := by
    rw [redN, ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hγm : redN N γ = !![((γ 0 0 : ℤ) : ZMod N), ((γ 0 1 : ℤ) : ZMod N); 0, ((γ 1 1 : ℤ) : ZMod N)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [redN, hc]
  funext i
  simp only [vm, redN_mul, hT, hγm, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ht]
    linear_combination (v 0 * ((γ 0 1 : ℤ) : ZMod N) * ((s : ZMod N) - 1)) * hdet

end Group

section Invariance

variable {N : ℕ}

local notation "Δ" => ModularForm.discriminant

private def cw (G : ℍ → ℂ) (α : SL(2, ℤ)) : ℍ → ℂ := fun τ => G (α • τ)

private theorem cw_apply (G : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) : cw G α τ = G (α • τ) := rfl

private theorem cw_mul (G : ℍ → ℂ) (α β : SL(2, ℤ)) : cw G (α * β) = cw (cw G α) β := by
  funext τ; simp [cw, mul_smul]

private theorem cw_one (G : ℍ → ℂ) : cw G 1 = G := by funext τ; simp [cw]

private theorem cw_eq_slash (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw G α = G ∣[(0 : ℤ)] α := by
  funext τ
  rw [ModularForm.SL_slash_apply, cw_apply, neg_zero, zpow_zero, mul_one]

private theorem mdifferentiable_cw {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G α) := by
  rw [cw_eq_slash, ModularForm.SL_slash]; exact hG.slash _ _

private def cwAlgHom (α : SL(2, ℤ)) : (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun G := cw G α
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] private theorem cwAlgHom_apply (α : SL(2, ℤ)) (G : ℍ → ℂ) : cwAlgHom α G = cw G α := rfl

private theorem cw_mul_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G * G') α = cw G α * cw G' α := rfl

private theorem periodic_of_T_invariant {G : ℍ → ℂ} (h : ∀ τ : ℍ, G (ModularGroup.T • τ) = G τ) :
    Periodic (G ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := h ⟨w, hw⟩
    rw [modular_T_smul] at this
    convert this using 2
    ext
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + 1) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

private theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem E₄_smul (α : SL(2, ℤ)) (τ : ℍ) :
    E₄ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [jf, jf, disc_smul, E₄_smul]
  field_simp

private theorem cw_jf (α : SL(2, ℤ)) : cw jf α = jf := funext (jf_smul α)

end Invariance

section Fricke

variable (N : ℕ) [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    fricke N v (γ • τ) = fricke N (vm N γ v) τ := by
  obtain ⟨h1, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h1 v γ τ

private theorem cw_fricke (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : cw (fricke N v) γ = fricke N (vm N γ v) :=
  funext (fricke_smul N v γ)

private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke N v) := by
  obtain ⟨-, -, h3, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h3 v hv

private theorem isBoundedAtImInfty_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    IsBoundedAtImInfty (fricke N v * Δ) := by
  obtain ⟨-, -, -, h4, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h4 v hv

private theorem periodic_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    Periodic ((fricke N v * Δ) ∘ ofComplex) N := by
  obtain ⟨-, -, -, -, h5, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact (h5 v hv).1

private theorem coeff_fricke_mem {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ) :
    (qExpansion N (fricke N v * Δ)).coeff n ∈ kN N := by
  obtain ⟨-, -, -, -, h5, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact (h5 v hv).2 n

private theorem coeff_fricke_ds {s : ℕ} (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : ∀ z : kN N, (z : ℂ) = zetaN N → φ z = zetaN N ^ s)
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ) (z : kN N)
    (hz : (z : ℂ) = (qExpansion N (fricke N v * Δ)).coeff n) :
    (qExpansion N (fricke N (ds N s v) * Δ)).coeff n = φ z := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h8 s hs φ hφ v hv n z hz

private theorem ratAt_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : RatAt N (kN N) 1 (fricke N v) where
  mdiff := mdifferentiable_fricke N hv
  periodic := by rw [pow_one]; exact periodic_fricke N hv
  bdd := by rw [pow_one]; exact isBoundedAtImInfty_fricke N hv
  mem := by rw [pow_one]; exact coeff_fricke_mem N hv

private theorem qExpansion_E₄_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

private theorem qExpansion_E₆_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

private theorem exists_map_of_rat {q : PowerSeries ℂ} (h : ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)) :
    ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  choose r hr using h
  exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩

private theorem rat_of_exists_map {q : PowerSeries ℂ} (h : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q)
    (n : ℕ) : ∃ r : ℚ, q.coeff n = (r : ℂ) := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

private def E4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

private theorem coe_E4cube : (⇑E4cube : ℍ → ℂ) = (E₄ : ℍ → ℂ) ^ 3 := by
  rw [E4cube, coe_mcast, coe_pow]

private theorem qExpansion_E4cube_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (⇑E4cube : ℍ → ℂ)).coeff n = (r : ℂ) := by
  obtain ⟨p, hp⟩ := exists_map_of_rat qExpansion_E₄_rat
  refine rat_of_exists_map ⟨p ^ 3, ?_⟩ n
  rw [E4cube, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    map_pow, hp]

private theorem ratAt_jf (K : IntermediateField ℚ ℂ) : RatAt N K 1 jf := by
  have hj : jf * Δ ^ 1 = ⇑E4cube := by
    funext τ
    rw [coe_E4cube]
    simp only [Pi.mul_apply, Pi.pow_apply, pow_one, jf]
    field_simp [discriminant_ne_zero τ]
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
    intro τ
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => E₄ τ ^ 3) τ := (E₄.holo' τ).pow 3
    exact h1.div (mdifferentiable_disc τ) (discriminant_ne_zero τ)
  refine ⟨hmd, ?_, ?_, ?_⟩
  · rw [hj]; exact periodic_ofComplex_natCast (SlashInvariantFormClass.periodic_comp_ofComplex E4cube
      one_mem_strictPeriods_SL) N
  · rw [hj]; exact ModularFormClass.bdd_at_infty E4cube
  · intro n
    rw [hj]
    obtain ⟨r, hr⟩ := qExpansion_widthN_rat N (g := (⇑E4cube : ℍ → ℂ)) E4cube.holo'
      (SlashInvariantFormClass.periodic_comp_ofComplex E4cube one_mem_strictPeriods_SL)
      (ModularFormClass.bdd_at_infty E4cube) qExpansion_E4cube_rat n
    rw [hr]; exact ratCast_mem r

variable {N}
variable (σ : (kN N) ≃ₐ[ℚ] (kN N)) {s : ℕ} (hs : s.Coprime N) (hσ : σ (zetaK N) = zetaK N ^ s)

private abbrev Tσ (σ : (kN N) ≃ₐ[ℚ] (kN N)) : (ℍ → ℂ) → (ℍ → ℂ) → Prop := TRel N (kN N) (phiOf N σ)

include hs hσ in
private theorem tσ_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : Tσ σ (fricke N v) (fricke N (ds N s v)) := by
  have h1 := ratAt_fricke N hv
  have h2 := ratAt_fricke N (ds_ne_zero N hs hv)
  refine ⟨h1.mdiff, h2.mdiff, 1, ⟨h1.periodic, h1.bdd, h1.mem⟩, ⟨h2.periodic, h2.bdd, h2.mem⟩, ?_⟩
  intro n z hz
  rw [pow_one] at hz ⊢
  exact coeff_fricke_ds N hs (phiOf N σ) (fun z hz => phiOf_zeta N σ hσ z hz) hv n z hz

private theorem transportPkg :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, Tσ σ (g i) (g' i)) →
      ∀ R : MvPolynomial ι (kN N),
        Tσ σ (MvPolynomial.aeval g (MvPolynomial.map (algebraMap (kN N) ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map (phiOf N σ) R))) ∧
    (∀ g g' : ℍ → ℂ, Tσ σ g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf' : ℍ → ℂ, (∀ τ : ℍ, jf' τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) → Tσ σ jf' jf' :=
  WLight.qExpansion_sigmaTransport_package N (kN N) (phiOf N σ) (phiOf_mem N σ) (Tσ σ)
    (fun _ _ => Iff.rfl)

private theorem tσ_jf : Tσ σ jf jf := (transportPkg σ).2.2 jf (jf_spec)

private theorem tσ_zero_iff {g g' : ℍ → ℂ} (h : Tσ σ g g') : g = 0 ↔ g' = 0 := (transportPkg σ).2.1 g g' h

private theorem tσ_aeval {ι : Type} {g g' : ι → ℍ → ℂ} (h : ∀ i, Tσ σ (g i) (g' i))
    (R : MvPolynomial ι (kN N)) :
    Tσ σ (MvPolynomial.aeval g (MvPolynomial.map (algebraMap (kN N) ℂ) R))
      (MvPolynomial.aeval g' (MvPolynomial.map (phiOf N σ) R)) :=
  (transportPkg σ).1 g g' h R

variable (N) in

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map (algebraMap (kN N) ℂ) R)

variable (N) in

private def evφ (φ : kN N →+* ℂ) (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) :
    ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map φ R)

include hs hσ in
private theorem tσ_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0) (o : Idx N) :
    Tσ σ (gen N t o) (gen N (ds N s ∘ t) o) := by
  cases o with
  | none => exact tσ_jf σ
  | some v => exact tσ_fricke σ hs hσ (ht v.1 v.2)

include hs hσ in
private theorem tσ_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (R : MvPolynomial (Idx N) (kN N)) : Tσ σ (ev N t R) (evφ N (phiOf N σ) (ds N s ∘ t) R) :=
  tσ_aeval σ (tσ_gen σ hs hσ t ht) R

private theorem cw_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (α : SL(2, ℤ)) (o : Idx N) :
    cw (gen N t o) α = gen N (vm N α ∘ t) o := by
  cases o with
  | none => exact cw_jf α
  | some v => exact cw_fricke N (t v.1) α

private theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  have h := congrArg (fun F => F R) this
  simpa using h

private theorem gen_cw_eq (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (α : SL(2, ℤ)) :
    (fun o => cw (gen N t o) α) = gen N (vm N α ∘ t) :=
  funext (cw_gen t α)

private theorem cw_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N))
    (α : SL(2, ℤ)) : cw (ev N t R) α = ev N (vm N α ∘ t) R := by
  unfold ev
  rw [cw_aeval, gen_cw_eq]

private theorem cw_evφ (φ : kN N →+* ℂ) (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N))
    (R : MvPolynomial (Idx N) (kN N)) (α : SL(2, ℤ)) :
    cw (evφ N φ t R) α = evφ N φ (vm N α ∘ t) R := by
  unfold evφ
  rw [cw_aeval, gen_cw_eq]

private theorem gen_id_mem (o : Idx N) : gen N id o ∈ genSet N := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩

private theorem aeval_mem_adjoin (R : MvPolynomial (Idx N) ℂ) :
    MvPolynomial.aeval (gen N id) R ∈ Algebra.adjoin ℂ (genSet N) := by
  induction R using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_id_mem o))

private theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev N id R ∈ Algebra.adjoin ℂ (genSet N) :=
  aeval_mem_adjoin _

private theorem adjoin_isDomain {a b : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ (genSet N))
    (hb : b ∈ Algebra.adjoin ℂ (genSet N)) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N tauPair tauPair_spec (WW N) (WW_spec N)
    (fricke N) (fricke_spec N) jf jf_spec
  exact h6 a b ha hb hab

private theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev N id (Q i) ≠ 0) : ev N id (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev N id (Q a) * ev N id (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain (ev_mem_adjoin _) (ev_mem_adjoin _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

end Fricke

section Descent

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem smul_eq_coe_smul (K : IntermediateField ℚ ℂ) (κ : K) (f : ℍ → ℂ) : κ • f = (κ : ℂ) • f := rfl

private theorem exists_rat_combination (K : IntermediateField ℚ ℂ) {n M : ℕ} {Gi : Fin n → ℍ → ℂ}
    {G : ℍ → ℂ} (hGi : ∀ i, RatAt N K M (Gi i)) (hG : RatAt N K M G)
    (hmem : G ∈ Submodule.span ℂ (Set.range Gi)) :
    ∃ κ : Fin n → K, G = ∑ i, (κ i : ℂ) • Gi i := by
  classical
  by_cases hW : G ∈ Submodule.span K (Set.range Gi)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hW
    exact ⟨c, by rw [← hc]; rfl⟩
  exfalso
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (Set.range Gi)
  have hbfin : b.Finite := (Set.finite_range Gi).subset hb_sub
  have hGb : G ∉ b := fun h => hW (hb_span ▸ Submodule.subset_span h)
  have hGspan : G ∉ Submodule.span K b := by rwa [hb_span]
  have hins : LinearIndepOn K id (insert G b) := LinearIndepOn.id_insert hb_ind hGspan
  set sF : Finset (ℍ → ℂ) := (hbfin.insert G).toFinset with hsF
  have hcoe : (↑sF : Set (ℍ → ℂ)) = insert G b := Set.Finite.coe_toFinset _
  have hdata : ∀ f ∈ sF, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ M) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ M)).coeff n ∈ K := by
    intro f hf
    have hf' : f ∈ insert G b := by rwa [← hcoe, Finset.mem_coe]
    rcases hf' with rfl | hf'
    · exact ⟨hG.mdiff, hG.periodic, hG.bdd, hG.mem⟩
    · obtain ⟨i, rfl⟩ := hb_sub hf'
      exact ⟨(hGi i).mdiff, (hGi i).periodic, (hGi i).bdd, (hGi i).mem⟩
  have hind : LinearIndependent K (fun w : ↥(↑sF : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
    rw [hcoe]; exact hins
  have hC := WLight.linearIndependent_complex_of_qExpansion_rational N K sF M hdata hind
  rw [hcoe] at hC
  have hC' : LinearIndepOn ℂ id (insert G b) := hC
  have hnot := hC'.notMem_span_of_insert hGb
  rw [Set.image_id] at hnot
  apply hnot
  have hle : Submodule.span ℂ (Set.range Gi) ≤ Submodule.span ℂ b := by
    rw [Submodule.span_le]
    intro x hx
    have hxK : x ∈ Submodule.span K b := by rw [hb_span]; exact Submodule.subset_span hx
    exact Submodule.span_subset_span K ℂ b hxK
  exact hle hmem

private theorem exists_ev_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin (kN N) (genSet N)) :
    ∃ R : MvPolynomial (Idx N) (kN N), ev N id R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx

  have hsec : ∀ y : genSet N, ∃ o : Idx N, gen N id o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  rw [ev, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen N id ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl

private theorem coeff_map_mem (R : MvPolynomial (Idx N) (kN N)) (m : Idx N →₀ ℕ) :
    (MvPolynomial.map (algebraMap (kN N) ℂ) R).coeff m ∈ kN N := by
  rw [MvPolynomial.coeff_map]; exact (R.coeff m).2

private theorem descent {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : RatAt N (kN N) m G) :
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev N id Q ≠ 0 ∧ G * ev N id Q = ev N id P := by
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
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec S hhol hpb' hst hinvS hGS

  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => ⟨m, hpb γ⟩
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec ha hb hb0 hG hGb hpbG

  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, hpiK, hGirel⟩ :=
    WLight.frickeFunction_intBaseChange N tauPair tauPair_spec (WW N) (WW_spec N) (fricke N)
      (fricke_spec N) jf jf_spec hG ha hb hb0 hGb p hprel

  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev N id R = Pi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev N id R = Qi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).2.1
  choose Ph hPh using hPi
  choose Qh hQh using hQi
  have hrati : ∀ i, ∃ mi : ℕ, RatAt N (kN N) mi (Gi i) := by
    intro i
    obtain ⟨mi, h1, h2, h3⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N
      tauPair tauPair_spec (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) rfl
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
  · exact ev_prod_ne_zero Finset.univ Qh fun i _ => by rw [hQh i]; exact (hPQ i).2.2.1
  · have hev_prod : ∀ (s : Finset (Fin n)), ev N id (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
      intro s; simp only [ev, map_prod]; exact Finset.prod_congr rfl fun j _ => hQh j
    rw [hκ, hev_prod, Finset.sum_mul]
    simp only [ev, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C, map_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i)) = Pi i := hPh i
    have h2 : ∀ j, (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh j)) = Qi j :=
      hQh
    simp only [h1, h2]
    rw [← Finset.mul_prod_erase Finset.univ Qi (Finset.mem_univ i), ← (hPQ i).2.2.2]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [smul_one_smul, mul_assoc]
    rfl

end Descent

section Algebra

private theorem exists_of_mul_eq {K : Type*} [Field K] (ι φ : K →+* ℂ)
    {B A : PowerSeries K} (hB : B ≠ 0) {ξ : PowerSeries ℂ}
    (h1 : ξ * B.map ι = A.map ι) (h2 : ξ * B.map φ = A.map φ) :
    ∃ X : PowerSeries K, X.map ι = ξ ∧ X.map φ = ξ := by
  classical
  set v : ℕ := B.order.toNat with hv
  set U : PowerSeries K := B.divXPowOrder with hU
  have hBU : PowerSeries.X ^ v * U = B := PowerSeries.X_pow_order_mul_divXPowOrder
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU, PowerSeries.constantCoeff_divXPowOrder]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.coeff_order hB)
  obtain ⟨u, hu⟩ := hUunit

  have hAι : A.map ι = PowerSeries.X ^ v * (ξ * U.map ι) := by
    rw [← h1, ← hBU]
    simp only [map_mul, map_pow, PowerSeries.map_X]
    ring
  have hAdvd : PowerSeries.X ^ v ∣ A := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hcoef : PowerSeries.coeff n (A.map ι) = 0 := by
      rw [hAι, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hn)]
    rw [PowerSeries.coeff_map] at hcoef
    exact ι.injective (by rw [hcoef, map_zero])
  obtain ⟨A', hA'⟩ := hAdvd
  have hXv : (PowerSeries.X : PowerSeries ℂ) ^ v ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero

  have key : ∀ ψ : K →+* ℂ, ξ * B.map ψ = A.map ψ → ξ * U.map ψ = A'.map ψ := by
    intro ψ h
    rw [← hBU, hA'] at h
    simp only [map_mul, map_pow, PowerSeries.map_X] at h
    have : (PowerSeries.X : PowerSeries ℂ) ^ v * (ξ * U.map ψ) = PowerSeries.X ^ v * A'.map ψ := by
      rw [← h]; ring
    exact mul_left_cancel₀ hXv this
  refine ⟨A' * ↑u⁻¹, ?_, ?_⟩
  · have hk := key ι h1
    have hUι : U.map ι ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map ι).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUι
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]
  · have hk := key φ h2
    have hUφ : U.map φ ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map φ).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUφ
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]

end Algebra

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

private theorem cw_ne_zero {b : ℍ → ℂ} (hb : b ≠ 0) (γ : SL(2, ℤ)) : cw b γ ≠ 0 := by
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

private def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

private def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

variable {N}
variable (X : FD N)

private def genSet : Set (ℍ → ℂ) := insert X.jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = X.fricke v}

variable (N) in

private abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen : Idx N → ℍ → ℂ := fun o => o.elim X.jf fun v => X.fricke v.1

private theorem gen_eq : gen X = fun o : Idx N => o.elim X.jf fun v => X.fricke v.1 := rfl

section Width

local notation "Δ" => ModularForm.discriminant

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem disc_ne_zero_fun : (Δ : ℍ → ℂ) ≠ 0 := fun h => by
  have := congrFun h UpperHalfPlane.I
  exact discriminant_ne_zero _ this

private theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem periodic_pow {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (m : ℕ) :
    Periodic ((g ^ m) ∘ ofComplex) c := by
  induction m with
  | zero => intro z; simp
  | succ m ih => rw [pow_succ]; exact periodic_mul ih h

private theorem periodic_smul {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) :
    Periodic ((a • g) ∘ ofComplex) c := by
  intro z; have h1 := h z; simp only [comp_apply, Pi.smul_apply] at h1 ⊢; rw [h1]

private theorem periodic_add {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g + g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

variable (N : ℕ) [NeZero N]

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem qExpansion_widthN_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N hg hper hbd n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

private theorem qExpansion_widthOne_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := hrat (N * n)
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)] at hr
  exact ⟨r, hr⟩

private theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by

  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  have h4 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩
  have h6 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using h4
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using h6
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) :=
  qExpansion_widthN_rat N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc
    qExpansion_disc_rat_one n

variable (K : IntermediateField ℚ ℂ)

private structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

private theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

private theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

private theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem r

private theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  simp

private theorem RatAt.qExpansion_ne_zero {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) (hg : g ≠ 0) :
    qExpansion N (g * Δ ^ m) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) h.periodic h.mdiff_mul h.bdd]
  intro h0
  apply hg
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (disc_pow_ne_zero m τ)

end Width

section Invariance

variable {N : ℕ}

local notation "Δ" => ModularForm.discriminant

private def cw (G : ℍ → ℂ) (α : SL(2, ℤ)) : ℍ → ℂ := fun τ => G (α • τ)

private theorem cw_apply (G : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) : cw G α τ = G (α • τ) := rfl

private theorem cw_mul (G : ℍ → ℂ) (α β : SL(2, ℤ)) : cw G (α * β) = cw (cw G α) β := by
  funext τ; simp [cw, mul_smul]

private theorem cw_one (G : ℍ → ℂ) : cw G 1 = G := by funext τ; simp [cw]

private theorem cw_eq_slash (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw G α = G ∣[(0 : ℤ)] α := by
  funext τ
  rw [ModularForm.SL_slash_apply, cw_apply, neg_zero, zpow_zero, mul_one]

private theorem mdifferentiable_cw {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G α) := by
  rw [cw_eq_slash, ModularForm.SL_slash]; exact hG.slash _ _

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

private theorem smul_eq_coe_smul (K : IntermediateField ℚ ℂ) (κ : K) (f : ℍ → ℂ) : κ • f = (κ : ℂ) • f := rfl

private theorem exists_rat_combination (K : IntermediateField ℚ ℂ) {n M : ℕ} {Gi : Fin n → ℍ → ℂ}
    {G : ℍ → ℂ} (hGi : ∀ i, RatAt N K M (Gi i)) (hG : RatAt N K M G)
    (hmem : G ∈ Submodule.span ℂ (Set.range Gi)) :
    ∃ κ : Fin n → K, G = ∑ i, (κ i : ℂ) • Gi i := by
  classical
  by_cases hW : G ∈ Submodule.span K (Set.range Gi)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hW
    exact ⟨c, by rw [← hc]; rfl⟩
  exfalso
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (Set.range Gi)
  have hbfin : b.Finite := (Set.finite_range Gi).subset hb_sub
  have hGb : G ∉ b := fun h => hW (hb_span ▸ Submodule.subset_span h)
  have hGspan : G ∉ Submodule.span K b := by rwa [hb_span]
  have hins : LinearIndepOn K id (insert G b) := LinearIndepOn.id_insert hb_ind hGspan
  set sF : Finset (ℍ → ℂ) := (hbfin.insert G).toFinset with hsF
  have hcoe : (↑sF : Set (ℍ → ℂ)) = insert G b := Set.Finite.coe_toFinset _
  have hdata : ∀ f ∈ sF, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ M) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ M)).coeff n ∈ K := by
    intro f hf
    have hf' : f ∈ insert G b := by rwa [← hcoe, Finset.mem_coe]
    rcases hf' with rfl | hf'
    · exact ⟨hG.mdiff, hG.periodic, hG.bdd, hG.mem⟩
    · obtain ⟨i, rfl⟩ := hb_sub hf'
      exact ⟨(hGi i).mdiff, (hGi i).periodic, (hGi i).bdd, (hGi i).mem⟩
  have hind : LinearIndependent K (fun w : ↥(↑sF : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
    rw [hcoe]; exact hins
  have hC := WLight.linearIndependent_complex_of_qExpansion_rational N K sF M hdata hind
  rw [hcoe] at hC
  have hC' : LinearIndepOn ℂ id (insert G b) := hC
  have hnot := hC'.notMem_span_of_insert hGb
  rw [Set.image_id] at hnot
  apply hnot
  have hle : Submodule.span ℂ (Set.range Gi) ≤ Submodule.span ℂ b := by
    rw [Submodule.span_le]
    intro x hx
    have hxK : x ∈ Submodule.span K b := by rw [hb_span]; exact Submodule.subset_span hx
    exact Submodule.span_subset_span K ℂ b hxK
  exact hle hmem

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

private theorem coeff_map_mem (R : MvPolynomial (Idx N) (kN N)) (m : Idx N →₀ ℕ) :
    (MvPolynomial.map (algebraMap (kN N) ℂ) R).coeff m ∈ kN N := by
  rw [MvPolynomial.coeff_map]; exact (R.coeff m).2

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
