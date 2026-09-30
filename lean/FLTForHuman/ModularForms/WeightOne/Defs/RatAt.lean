/-
  The `RatAt` vocabulary: the discriminant/width lemmas and the `RatAt` structure
  (`MDifferentiable`/periodic/pole-bounded with `K`-rational width-`m` coefficients)
  that the Γ-rationality arguments share. Lifted out of `Defs/GammaRational` so that
  `LevelN` (which `Defs/GammaRational` imports, and therefore cannot import it) can
  use the same structure instead of re-declaring it.
-/
import FLTForHuman.ModularForms.DiscPow
import FLTForHuman.ModularForms.QExpansionCoeff
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

set_option linter.unusedSectionVars false

noncomputable section

open Complex Real UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology
open UpperHalfPlaneAux

namespace X1DiamondRational

variable (N : ℕ)

section Width

local notation "Δ" => ModularForm.discriminant

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

theorem disc_ne_zero_fun : (Δ : ℍ → ℂ) ≠ 0 := fun h => by
  have := congrFun h UpperHalfPlane.I
  exact discriminant_ne_zero _ this

theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

theorem periodic_pow {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (m : ℕ) :
    Periodic ((g ^ m) ∘ ofComplex) c := by
  induction m with
  | zero => intro z; simp
  | succ m ih => rw [pow_succ]; exact periodic_mul ih h

theorem periodic_smul {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) :
    Periodic ((a • g) ∘ ofComplex) c := by
  intro z; have h1 := h z; simp only [comp_apply, Pi.smul_apply] at h1 ⊢; rw [h1]

/- H2 reconciliation of the specialised-vs-general clash: the pin's unit-period
copy of `periodic_smul`, derived from the general lemma above. It lives in a
sub-namespace so both public statements verify. -/
namespace PeriodOne

/-- The pin's unit-period `periodic_smul`. -/
theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 :=
  X1DiamondRational.periodic_smul hG c

end PeriodOne

theorem periodic_add {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g + g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

variable (N : ℕ) [NeZero N]

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

theorem qExpansion_widthN_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N hg hper hbd n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

theorem qExpansion_widthOne_rat {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion N g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := hrat (N * n)
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)] at hr
  exact ⟨r, hr⟩

theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by

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

theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) :=
  qExpansion_widthN_rat N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc
    qExpansion_disc_rat_one n

variable (K : IntermediateField ℚ ℂ)

structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
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

theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  simp

theorem RatAt.qExpansion_ne_zero {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) (hg : g ≠ 0) :
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
