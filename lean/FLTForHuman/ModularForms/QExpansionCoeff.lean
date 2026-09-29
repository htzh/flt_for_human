/-
  Generic q-expansion coefficient analysis for modular forms.

  `qParam_one_eq_pow` (the level-`1` and level-`N` `q`-parameters agree up to the
  `N`-th power), `qExpansion_coeff_width_fn` and its bundled form
  `UpperHalfPlaneAux.ModularFormClass.qExpansion_coeff_width`: the coefficient of
  `qExpansion N f` at `n` is the level-one coefficient at `n / N` when `N ∣ n`,
  and `0` otherwise.

  Generic modular-forms analysis, not weight-one material, so it lives outside
  `WeightOne/`.  Lifted from the repeated `private` prelude of the weight-one
  packages (`P2M/Sol/S_WLight_*`, pinned `aa2d8b3`).  The declarations keep the
  pin/port namespace `UpperHalfPlaneAux`, so call sites do not change spelling.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

open Complex Real

namespace UpperHalfPlaneAux

section Width

open scoped UpperHalfPlane Manifold
open UpperHalfPlane hiding I

lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

theorem qExpansion_coeff_width_fn (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm


end Width

section WidthMF

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open SlashInvariantFormClass ModularFormClass

namespace ModularFormClass
theorem qExpansion_coeff_width {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    (qExpansion N f).coeff n = if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact qExpansion_coeff_width_fn f hN (by simpa using periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

end ModularFormClass

end WidthMF

section WidthN

open Function
open scoped UpperHalfPlane Manifold
open UpperHalfPlane hiding I

variable (N : ℕ) [NeZero N]

/-- The Γ-module spelling of the width formula: `N` is a section variable and the
`NeZero` instance supplies the non-vanishing hypothesis.  Same content as
`qExpansion_coeff_width_fn`, kept because the Γ consumers state it this way. -/
theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 :=
  qExpansion_coeff_width_fn g (NeZero.ne N) hper hg hbd n

/-- The weight-one packages' spelling of `qExpansion_coeff_width_fn` (argument order
`(f) (hN) (hper) (hhol) (hbd)`); kept as the name they use. -/
theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 :=
  qExpansion_coeff_width_fn f hN hper hhol hbd n

/-- Uniqueness of a `q`-expansion from its coefficients at the cusp. -/
theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

end WidthN

end UpperHalfPlaneAux
