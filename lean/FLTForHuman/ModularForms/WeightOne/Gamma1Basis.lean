/-
  The Γ₁-basis packages from Galois rationality to the spectral side (SET-11 order 1).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean`,
  `Theorems/Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean`,
  `Theorems/Thm_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean`,
  `Theorems/Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean`,
  `Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean`
  and `Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean`;
  proofs transcribed from the matching `P2M/Sol/S_*` files (422 + 333 + 784 +
  1,390 + 913 + 352 lines) and adapted to mathlib `v4.34.0`.

  Each pin file's helpers stay `private` in the pin's own inner namespace
  (`WeightLoweringCriterion` / `Gamma1Eisenstein` / `FrickeCuspTransport` /
  `FrickeSpan` / `GammaOneGaloisEven` / `GammaOneGaloisAllWeights`), nested in
  this module's own `WLightS11.S_*` namespaces, so the packages' repeated
  vocabulary (`redN`, `vm`, `cw`, `RatAt`, …) does not collide; the six
  headlines are the module's only public surface.  `ModularCurve.IsIntegralQExp`
  (the pin's `Definitions/Def_ModularCurve_X1.lean` definition) is consumed from
  SET-10's `Gamma0Integral`.  The package-to-package edges are the pin's own and
  consume the already-ported SET-7/8/9 headlines.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean

  The pin's `set_option maxHeartbeats` bumps are **not** transcribed (the
  project's global `maxHeartbeats` cap is 4,000,000).
-/

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
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
import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
import FLTForHuman.ModularForms.WeightOne.LevelN
import FLTForHuman.ModularForms.WeightOne.EisensteinSeries
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.WeightOne.Gamma0Rationality
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularCurve.Defs.Jq

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

open Complex Real UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real Manifold MatrixGroups ModularForm Topology UpperHalfPlane

namespace WLightS11.S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm Filter Topology
open scoped Manifold MatrixGroups ModularForm

namespace WeightLoweringCriterion

local notation "Δ" => ModularForm.discriminant

private theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem analyticOnNhd_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) :
    AnalyticOnNhd ℂ (u ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd isOpen_upperHalfPlaneSet

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by

  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (v ∘ ofComplex) z ≠ 0 := hvc.eventually_ne hv0'
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hne] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := (analyticOnNhd_comp_ofComplex hu).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  have := hEq τ.im_pos
  simpa [Function.comp, ofComplex_apply] using this

private theorem mdifferentiableAt_of_eventuallyEq {f g : ℍ → ℂ} {τ : ℍ}
    (hfg : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] (g ∘ ofComplex))
    (hg : DifferentiableAt ℂ (g ∘ ofComplex) (τ : ℂ)) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ :=
  UpperHalfPlane.mdifferentiableAt_iff.2 (hfg.differentiableAt_iff.2 hg)

private theorem exists_mul_eq_of_coprime {P b c H₁ H₂ : ℍ → ℂ}
    (hb : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b) (hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c)
    (hH₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₁) (hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂)
    (hcop : ∀ τ : ℍ, b τ ≠ 0 ∨ c τ ≠ 0)
    (h₁ : ∀ τ : ℍ, H₁ τ * b τ = P τ) (h₂ : ∀ τ : ℍ, H₂ τ * c τ = P τ) :
    ∃ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∀ τ : ℍ, f τ * (b τ * c τ) = P τ := by
  classical
  let f : ℍ → ℂ := fun τ => if c τ = 0 then H₂ τ / b τ else H₁ τ / c τ
  refine ⟨f, fun τ₀ => ?_, fun τ => ?_⟩
  ·
    by_cases hc0 : c τ₀ = 0
    ·
      have hb0 : b τ₀ ≠ 0 := (hcop τ₀).resolve_right (by simpa using hc0)
      have hbc : ContinuousAt (b ∘ ofComplex) (τ₀ : ℂ) :=
        (differentiableAt_comp_ofComplex hb τ₀).continuousAt
      have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (b ∘ ofComplex) z ≠ 0 :=
        hbc.eventually_ne (by simpa [Function.comp, ofComplex_apply] using hb0)
      refine mdifferentiableAt_of_eventuallyEq (g := fun τ => H₂ τ / b τ) ?_ ?_
      · filter_upwards [hne] with z hz
        simp only [Function.comp_apply] at hz ⊢
        by_cases hcz : c (ofComplex z) = 0
        · simp [f, hcz]
        · simp only [f, hcz, ite_false]
          have e1 := h₁ (ofComplex z)
          have e2 := h₂ (ofComplex z)
          field_simp
          rw [← e2] at e1
          linear_combination e1
      · exact ((differentiableAt_comp_ofComplex hH₂ τ₀).div (differentiableAt_comp_ofComplex hb τ₀)
          (by simpa [Function.comp, ofComplex_apply] using hb0))
    ·
      have hcc : ContinuousAt (c ∘ ofComplex) (τ₀ : ℂ) :=
        (differentiableAt_comp_ofComplex hc τ₀).continuousAt
      have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (c ∘ ofComplex) z ≠ 0 :=
        hcc.eventually_ne (by simpa [Function.comp, ofComplex_apply] using hc0)
      refine mdifferentiableAt_of_eventuallyEq (g := fun τ => H₁ τ / c τ) ?_ ?_
      · filter_upwards [hne] with z hz
        simp only [Function.comp_apply] at hz ⊢
        simp [f, hz]
      · exact ((differentiableAt_comp_ofComplex hH₁ τ₀).div (differentiableAt_comp_ofComplex hc τ₀)
          (by simpa [Function.comp, ofComplex_apply] using hc0))
  ·
    by_cases hcz : c τ = 0
    · simp only [f, hcz, ite_true, mul_zero]
      rw [← h₂ τ, hcz, mul_zero]
    · simp only [f, hcz, ite_false]
      rw [← h₁ τ]
      field_simp

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) :=
  CuspForm.discriminant.holo'

private theorem mdifferentiable_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄ : ℍ → ℂ) := E₄.holo'

private theorem mdifferentiable_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆ : ℍ → ℂ) := E₆.holo'

private theorem E₄_ne_zero_or_E₆_ne_zero (τ : ℍ) : E₄ τ ≠ 0 ∨ E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [h.1, h.2] at hΔ
  exact disc_ne_zero τ (by rw [hΔ]; norm_num)

private theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

private theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

private theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

private theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem E₆_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₆ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (6 : ℤ) * E₆ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₆ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

variable (a b m : ℕ)

private def Efun : ℍ → ℂ := fun τ => E₄ τ ^ a * E₆ τ ^ b

private theorem Efun_apply (τ : ℍ) : Efun a b τ = E₄ τ ^ a * E₆ τ ^ b := rfl

private theorem mdifferentiable_Efun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Efun a b) :=
  (mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b)

private theorem exists_Efun_ne_zero : ∃ τ : ℍ, Efun a b τ ≠ 0 := by

  obtain ⟨τ₄, h₄⟩ := exists_E₄_ne_zero
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero

  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero mdifferentiable_E₆ mdifferentiable_E₄ hmul h₄
  obtain ⟨τ₆, h₆⟩ := exists_E₆_ne_zero
  exact h₆ (by simpa using congrFun this τ₆)

private theorem Efun_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Efun a b (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) * Efun a b τ := by
  simp only [Efun, E₄_smul, E₆_smul, zpow_natCast, zpow_ofNat]
  ring

private theorem disc_pow_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) ^ m = denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ) * Δ τ ^ m := by
  rw [disc_smul, zpow_natCast, zpow_ofNat]
  ring

private theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos
    one_mem_strictPeriods_SL
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

private theorem tendsto_Efun : Tendsto (Efun a b) atImInfty (𝓝 1) := by
  have h4 := (tendsto_E (by norm_num : 3 ≤ 4) ⟨2, rfl⟩).pow a
  have h6 := (tendsto_E (by norm_num : 3 ≤ 6) ⟨3, rfl⟩).pow b
  have h__af := h4.mul h6
  simp at h__af
  exact h__af

private theorem isBoundedAtImInfty_Efun : IsBoundedAtImInfty (Efun a b) :=
  (tendsto_Efun a b).isBigO_one ℝ

section Forward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m}
variable (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ}

include hk in

private theorem slash_mul_Efun {f : ℍ → ℂ} (hf : ∀ τ : ℍ, f τ * Efun a b τ = F τ * Δ τ ^ m)
    (A : SL(2, ℤ)) (τ : ℍ) : (f ∣[k] A) τ * Efun a b τ = F (A • τ) * Δ τ ^ m := by
  have hd : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ≠ 0 := denom_ne_zero _ _
  have h1 := hf (A • τ)
  rw [Efun_smul, disc_pow_smul] at h1
  rw [ModularForm.SL_slash_apply]

  have hexp : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ (-k) =
      denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) *
        (denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ))⁻¹ := by
    rw [← zpow_neg, ← zpow_add₀ hd]
    congr 1
    push_cast
    linarith
  rw [hexp]
  have h12 : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ ((12 * m : ℕ) : ℤ) ≠ 0 := zpow_ne_zero _ hd
  field_simp
  linear_combination h1

include hk in
private theorem forward (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) :
    ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
      (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
      (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) := by
  have hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := f.holo'
  refine ⟨⟨fun τ => f τ ^ 3 * E₆ τ ^ (3 * b), (hfhol.pow 3).mul (mdifferentiable_E₆.pow _), fun τ => ?_⟩,
    ⟨fun τ => f τ ^ 2 * E₄ τ ^ (2 * a), (hfhol.pow 2).mul (mdifferentiable_E₄.pow _), fun τ => ?_⟩,
    fun A => ?_, fun γ hγ τ => ?_⟩
  · rw [← hf τ]; ring
  · rw [← hf τ]; ring
  ·
    have hfA : IsZeroAtImInfty ((⇑f : ℍ → ℂ) ∣[k] A) := CuspFormClass.zero_at_infty_slash f A
    have hEq : ((F ∘ (A • ·)) * Δ ^ m : ℍ → ℂ) = fun τ => ((⇑f : ℍ → ℂ) ∣[k] A) τ * Efun a b τ := by
      funext τ
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply]
      exact (slash_mul_Efun hk hf A τ).symm
    rw [hEq]
    exact hfA.mul_boundedAtFilter (isBoundedAtImInfty_Efun a b)
  ·
    have h := slash_mul_Efun hk hf γ τ
    have hinv : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
      have := SlashInvariantForm.slash_action_eqn f (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    rw [hinv] at h
    rw [Efun_apply, hf τ] at h
    have hΔ : Δ τ ^ m ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
    exact (mul_left_injective₀ hΔ h).symm

end Forward

section Backward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m}
variable (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)

include hF in

private theorem exists_div_E₄ (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₄ τ ^ a = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₄ τ ^ a
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (mdifferentiable_disc.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := mdifferentiable_E₄.pow a
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
    intro hB0
    exact pow_ne_zero a hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 3, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [c, hi] at h__af ⊢
      exact h__af
  have hmonic : P ^ 3 + ∑ i ∈ Finset.range 3, c i * B ^ (3 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 from two_ne_zero, ite_false,
      Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := WLight.exists_mdifferentiable_div_of_monicRel hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

include hF in

private theorem exists_div_E₆ (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₆ τ ^ b = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₆ τ ^ b
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (mdifferentiable_disc.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := mdifferentiable_E₆.pow b
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
    intro hB0
    exact pow_ne_zero b hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [c, hi] at h__af ⊢
      exact h__af
  have hmonic : P ^ 2 + ∑ i ∈ Finset.range 2, c i * B ^ (2 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, ite_false, Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := WLight.exists_mdifferentiable_div_of_monicRel hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

include hk hF in

private theorem backward
    (h₁ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ)
    (h₂ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ)
    (h₃ : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m))
    (h₄ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k,
      ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m := by

  obtain ⟨H₁, hH₁, hH₁E⟩ := exists_div_E₄ hF h₁
  obtain ⟨H₂, hH₂, hH₂E⟩ := exists_div_E₆ hF h₂
  have hcop : ∀ τ : ℍ, E₄ τ ^ a ≠ 0 ∨ E₆ τ ^ b ≠ 0 := fun τ =>
    (E₄_ne_zero_or_E₆_ne_zero τ).imp (pow_ne_zero a) (pow_ne_zero b)
  obtain ⟨f, hfhol, hfE⟩ := exists_mul_eq_of_coprime (mdifferentiable_E₄.pow a) (mdifferentiable_E₆.pow b)
    hH₁ hH₂ hcop hH₁E hH₂E
  have hfE' : ∀ τ : ℍ, f τ * Efun a b τ = F τ * Δ τ ^ m := hfE

  have hinv : ∀ γ ∈ Γ, f ∣[k] γ = f := by
    intro γ hγ
    have hzero : ∀ τ : ℍ, ((f ∣[k] γ) τ - f τ) * Efun a b τ = 0 := by
      intro τ
      rw [sub_mul, slash_mul_Efun hk hfE' γ τ, hfE' τ, h₄ γ hγ τ, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_Efun_ne_zero a b
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (f ∣[k] γ) τ - f τ) := by
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hfhol.slash k _
      exact h1.sub hfhol
    have := eq_zero_of_mul_eq_zero hdiff (mdifferentiable_Efun a b) hzero hτ₀
    funext τ
    exact sub_eq_zero.1 (by simpa using congrFun this τ)

  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] A) := by
    intro A
    have hE1 : Tendsto (Efun a b) atImInfty (𝓝 1) := tendsto_Efun a b
    have hne : ∀ᶠ τ in atImInfty, Efun a b τ ≠ 0 := hE1.eventually_ne one_ne_zero
    have hq : Tendsto (fun τ => ((F ∘ (A • ·)) * Δ ^ m) τ / Efun a b τ) atImInfty (𝓝 0) := by
      have h__af := (h₃ A).div hE1 one_ne_zero
      simp at h__af
      exact h__af
    refine (hq.congr' ?_)
    filter_upwards [hne] with τ hτ
    rw [div_eq_iff hτ]
    simpa [Pi.mul_apply, Function.comp_apply, Pi.pow_apply] using (slash_mul_Efun hk hfE' A τ).symm

  let fC : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := f
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hfhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  exact ⟨fC, fun τ => hfE τ⟩

end Backward

private theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : ℍ,
        f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) ↔
      ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :=
  ⟨fun ⟨f, hf⟩ => forward hk f hf, fun ⟨h₁, h₂, h₃, h₄⟩ => backward hk hF h₁ h₂ h₃ h₄⟩

end WeightLoweringCriterion

end

open scoped Manifold MatrixGroups ModularForm

theorem _root_.CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : UpperHalfPlane,
        f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) =
          F τ * ModularForm.discriminant τ ^ m) ↔
      ((∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 3 = ModularForm.E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 2 = ModularForm.E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty
          ((F ∘ (A • ·)) * ModularForm.discriminant ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) :=
  WeightLoweringCriterion.main Γ k a b m hk F hF

end WLightS11.S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff

namespace WLightS11.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function Matrix Complex Function.Complex Real ModularCurve
open scoped MatrixGroups ModularForm Manifold Nat

namespace Gamma1Eisenstein

local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) [NeZero M] (k : ℕ)

private abbrev ent (γ : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((γ i j : ℤ) : ZMod M)

private theorem vecMul_eq (c b : ZMod M) (γ : SL(2, ℤ)) :
    (![c, b] ᵥ* γ : Fin 2 → ZMod M) =
      ![c * ent M γ 0 0 + b * ent M γ 1 0, c * ent M γ 0 1 + b * ent M γ 1 1] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ent]

variable {M} in
private theorem ent_one_zero_eq_zero {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : ent M γ 1 0 = 0 := Gamma0_mem.mp hγ

variable {M} in

private theorem isUnit_ent_one_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsUnit (ent M γ 1 1) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  have hc : ent M γ 1 0 = 0 := ent_one_zero_eq_zero hγ
  simp only [ent] at hc ⊢
  rw [hc, mul_zero, sub_zero, mul_comm] at h
  exact IsUnit.of_mul_eq_one _ h

variable {M} in

private theorem bijective_affine (c : ZMod M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Function.Bijective fun b : ZMod M => c * ent M γ 0 1 + b * ent M γ 1 1 := by
  obtain ⟨u, hu⟩ := isUnit_ent_one_one hγ
  refine (Finite.injective_iff_bijective).mp fun b b' h => ?_
  have h' : b * ent M γ 1 1 = b' * ent M γ 1 1 := add_left_cancel h
  rw [← hu] at h'
  exact (Units.mul_left_inj u).mp h'

private def gsum (c : ZMod M) : ℍ → ℂ := ∑ b : ZMod M, EisensteinSeries.eisensteinG M k ![c, b]

private theorem finset_sum_slash {kk : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, F i) ∣[kk] γ = ∑ i ∈ s, (F i ∣[kk] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

variable {k} in
private theorem hk' (hk : 3 ≤ k) : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk

private theorem gsum_slash (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    gsum M k c ∣[(k : ℤ)] γ = gsum M k (c * ent M γ 0 0) := by
  rw [gsum, gsum, finset_sum_slash]
  have hsl : ∀ b : ZMod M, EisensteinSeries.eisensteinG M k ![c, b] ∣[(k : ℤ)] γ
      = EisensteinSeries.eisensteinG M k ![c * ent M γ 0 0, c * ent M γ 0 1 + b * ent M γ 1 1] := by
    intro b
    rw [(EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).2 γ,
      vecMul_eq, ent_one_zero_eq_zero hγ, mul_zero, add_zero]
  simp_rw [hsl]
  exact Fintype.sum_bijective _ (bijective_affine c hγ) _ _ fun b => rfl

private theorem gsum_slash_of_mem_Gamma1 (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 M) :
    gsum M k c ∣[(k : ℤ)] γ = gsum M k c := by
  have h := (Gamma1_mem M γ).mp hγ
  rw [gsum_slash M k hk c γ (Gamma1_in_Gamma0 M hγ)]
  simp only [ent, h.1, mul_one]

private def Fform (hk : 3 ≤ k) (c b : ZMod M) : ModularForm Γ(M) (k : ℤ) :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).1.choose

private theorem coe_Fform (hk : 3 ≤ k) (c b : ZMod M) : (⇑(Fform M k hk c b) : ℍ → ℂ) = EisensteinSeries.eisensteinG M k ![c, b] :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).1.choose_spec

private theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {kk : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ kk) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

private def Sform (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ(M) (k : ℤ) := ∑ b : ZMod M, Fform M k hk c b

private theorem coe_Sform (hk : 3 ≤ k) (c : ZMod M) : (⇑(Sform M k hk c) : ℍ → ℂ) = gsum M k c := by
  rw [Sform, coe_finset_sum, gsum]
  exact Finset.sum_congr rfl fun b _ => coe_Fform M k hk c b

private def Sform1 (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ₁ᴳ(M) (k : ℤ) where
  toFun := gsum M k c
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := gsum_slash_of_mem_Gamma1 M k hk c γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := by
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gsum M k c)
    rw [← coe_Sform M k hk c]; exact (Sform M k hk c).holo'
  bdd_at_cusps' {cu} hcu := by
    have hcu' : IsCusp cu Γ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu ⊢
      exact hcu
    change cu.IsBoundedAt (gsum M k c) (k : ℤ)
    rw [← coe_Sform M k hk c]
    exact (Sform M k hk c).bdd_at_cusps' hcu'

private theorem coe_Sform1 (hk : 3 ≤ k) (c : ZMod M) : (⇑(Sform1 M k hk c) : ℍ → ℂ) = gsum M k c := rfl

private def kappa : ℂ := (-2 * π * Complex.I) ^ k / (k - 1)!

private theorem kappa_ne_zero : kappa k ≠ 0 := by
  rw [kappa]
  refine div_ne_zero (pow_ne_zero _ ?_) (by exact_mod_cast (Nat.factorial_ne_zero _))
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

private def Gform (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ₁ᴳ(M) (k : ℤ) := (kappa k)⁻¹ • Sform1 M k hk c

private theorem coe_Gform (hk : 3 ≤ k) (c : ZMod M) : (⇑(Gform M k hk c) : ℍ → ℂ) = (kappa k)⁻¹ • gsum M k c := by
  rw [Gform, FunLike.coe_smul, coe_Sform1]

private theorem Gform_slash (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(Gform M k hk c) : ℍ → ℂ) ∣[(k : ℤ)] γ = ⇑(Gform M k hk (c * ent M γ 0 0)) := by
  rw [coe_Gform, coe_Gform, ModularForm.SL_smul_slash, gsum_slash M k hk c γ hγ]

section QExp

private def acoef (c : ZMod M) (n : ℕ) : ℤ :=
  (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
    (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1)

private theorem acoef_eq (c : ZMod M) (n : ℕ) :
    ((acoef M k c n : ℤ) : ℂ) = ∑ m ∈ n.divisors,
      ((if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) +
        (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0)) * (m : ℂ) ^ (k - 1) := by
  classical
  rw [acoef, Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

private theorem sum_stdAddChar_mul (t : ZMod M) :
    ∑ b : ZMod M, ZMod.stdAddChar (b * t) = if t = 0 then (M : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar M)]
  split_ifs <;> simp [ZMod.card]

private theorem sum_divisors_filter_dvd (n' : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ (M * n').divisors with M ∣ m, f m = ∑ m' ∈ n'.divisors, f (M * m') := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have e : (M * n').divisors.filter (M ∣ ·) = n'.divisors.map ⟨fun m' => M * m', mul_right_injective₀ hM⟩ := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hmn, hn0⟩, m', rfl⟩
      refine ⟨m', ⟨(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM)).mp hmn, ?_⟩, rfl⟩
      exact right_ne_zero_of_mul hn0
    · rintro ⟨m', ⟨hm', hn'0⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left M hm', mul_ne_zero hM hn'0⟩, dvd_mul_right M m'⟩
  rw [e, Finset.sum_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem sum_coeff_eq (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (n : ℕ) :
    ∑ b : ZMod M, (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n =
      if M ∣ n then kappa k * ((acoef M k c (n / M) : ℤ) : ℂ) else 0 := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  simp_rw [EisensteinSeries.qExpansion_eisensteinG_coeff M k hk _ n]
  by_cases hn : n = 0
  ·
    subst hn
    simp only [ite_true, Matrix.cons_val_zero, ite_eq_right hc, Finset.sum_const_zero]
    rw [ite_eq_left (dvd_zero M), Nat.zero_div, acoef]
    simp
  simp only [ite_eq_right hn, Matrix.cons_val_zero, Matrix.cons_val_one]

  rw [← Finset.mul_sum, Finset.sum_comm]
  have hchar : ∀ m ∈ n.divisors,
      ∑ b : ZMod M, ((if ((n / m : ℕ) : ZMod M) = c then ZMod.stdAddChar (b * (m : ZMod M)) else 0) +
          (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then ZMod.stdAddChar (-(b * (m : ZMod M))) else 0)) *
            (m : ℂ) ^ (k - 1)
        = (if (M ∣ m) then (M : ℂ) * (((if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) +
            (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0)) * (m : ℂ) ^ (k - 1)) else 0) := by
    intro m _
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ b : ZMod M, (if ((n / m : ℕ) : ZMod M) = c then ZMod.stdAddChar (b * (m : ZMod M)) else 0)
        = (if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) * (if ((m : ℕ) : ZMod M) = 0 then (M : ℂ) else 0) := by
      by_cases h1 : ((n / m : ℕ) : ZMod M) = c
      · simp only [ite_eq_left h1, one_mul]; exact sum_stdAddChar_mul M _
      · simp only [ite_eq_right h1, Finset.sum_const_zero, zero_mul]
    have e2 : ∑ b : ZMod M, (if ((n / m : ℕ) : ZMod M) = -c then ZMod.stdAddChar (-(b * (m : ZMod M))) else 0)
        = (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0) * (if ((m : ℕ) : ZMod M) = 0 then (M : ℂ) else 0) := by
      by_cases h1 : ((n / m : ℕ) : ZMod M) = -c
      · simp only [ite_eq_left h1, one_mul]
        have : ∀ b : ZMod M, -(b * (m : ZMod M)) = b * (-(m : ZMod M)) := fun b => by ring
        simp_rw [this]
        rw [sum_stdAddChar_mul M _]
        simp only [neg_eq_zero]
      · simp only [ite_eq_right h1, Finset.sum_const_zero, zero_mul]
    rw [e1, e2]
    by_cases hMm : M ∣ m
    · have h0 : ((m : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff m M).mpr hMm
      simp only [ite_eq_left h0, ite_eq_left hMm]; ring
    · have h0 : ((m : ℕ) : ZMod M) ≠ 0 := fun h => hMm ((ZMod.natCast_eq_zero_iff m M).mp h)
      simp only [ite_eq_right h0, ite_eq_right hMm]; ring
  rw [Finset.sum_congr rfl hchar, ← Finset.sum_filter]
  split_ifs with hMn
  · obtain ⟨n', rfl⟩ := hMn
    rw [sum_divisors_filter_dvd, Nat.mul_div_cancel_left n' (Nat.pos_of_ne_zero hM), acoef_eq, kappa,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' hm' => ?_
    have hm'0 : m' ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hm')
    rw [Nat.mul_div_mul_left n' m' (Nat.pos_of_ne_zero hM)]
    push_cast
    have hk1 : 1 ≤ k := by omega
    have epow : ((M : ℂ) * (m' : ℂ)) ^ (k - 1) = (M : ℂ) ^ (k - 1) * (m' : ℂ) ^ (k - 1) := mul_pow _ _ _
    rw [epow]
    have eM : (M : ℂ) ^ k = (M : ℂ) * (M : ℂ) ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
    rw [eM]
    field_simp
  ·
    rw [Finset.sum_eq_zero, mul_zero]
    intro m hm
    rw [Finset.mem_filter, Nat.mem_divisors] at hm
    exact absurd (hm.2.trans hm.1.1) hMn

private theorem qParam_pow (τ : ℍ) : Periodic.qParam (M : ℝ) τ ^ M = Periodic.qParam 1 τ := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem M_mem_strictPeriods : ((M : ℕ) : ℝ) ∈ (Γ(M) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

private theorem one_mem_strictPeriods_one : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

private theorem hasSum_gsum (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (τ : ℍ) :
    HasSum (fun n' : ℕ => (kappa k * ((acoef M k c n' : ℤ) : ℂ)) • Periodic.qParam 1 τ ^ n') (gsum M k c τ) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM

  have hb : ∀ b : ZMod M, HasSum (fun n : ℕ =>
      (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n • Periodic.qParam M τ ^ n)
      (EisensteinSeries.eisensteinG M k ![c, b] τ) := by
    intro b
    have h := hasSum_qExpansion hMpos
      (SlashInvariantFormClass.periodic_comp_ofComplex (Fform M k hk c b) (M_mem_strictPeriods M))
      (Fform M k hk c b).holo' (ModularFormClass.bdd_at_infty (Fform M k hk c b)) τ
    rwa [coe_Fform] at h

  have hs : HasSum (fun n : ℕ => (∑ b : ZMod M,
      (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n) • Periodic.qParam M τ ^ n)
      (gsum M k c τ) := by
    have h := hasSum_sum (s := (Finset.univ : Finset (ZMod M))) (fun b _ => hb b)
    rw [gsum, Finset.sum_apply]
    convert h using 1
    funext n
    rw [Finset.sum_smul]

  simp_rw [sum_coeff_eq M k hk c hc] at hs
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun n' : ℕ => M * n') →
      (if M ∣ n then kappa k * ((acoef M k c (n / M) : ℤ) : ℂ) else 0) • Periodic.qParam M τ ^ n = 0 := by
    intro n hn
    rw [ite_eq_right, zero_smul]
    rintro ⟨n', rfl⟩
    exact hn ⟨n', rfl⟩
  have hinj : Function.Injective (fun n' : ℕ => M * n') := mul_right_injective₀ hM
  rw [← hinj.hasSum_iff hzero] at hs
  refine hs.congr_fun fun n' => ?_
  simp only [Function.comp_apply]
  rw [ite_eq_left (dvd_mul_right M n'), Nat.mul_div_cancel_left n' (Nat.pos_of_ne_zero hM), pow_mul, qParam_pow]

private theorem qExpansion_Gform_coeff (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (n : ℕ) :
    (qExpansion 1 (⇑(Gform M k hk c))).coeff n = ((acoef M k c n : ℤ) : ℂ) := by
  have hsum : ∀ τ : ℍ, HasSum (fun n' : ℕ => (((acoef M k c n' : ℤ) : ℂ)) • Periodic.qParam 1 τ ^ n')
      (Gform M k hk c τ) := by
    intro τ
    have h := (hasSum_gsum M k hk c hc τ).const_smul ((kappa k)⁻¹)
    rw [coe_Gform, Pi.smul_apply]
    refine h.congr_fun fun n' => ?_
    rw [smul_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (kappa_ne_zero k), one_mul]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_one M)
    (f := Gform M k hk c) hsum n).symm

private theorem isIntegralQExp_coeff {f : ℍ → ℂ} {p : PowerSeries ℤ}
    (h : ModularCurve.IsIntegralQExp f p) (n : ℕ) :
    ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  rw [← h, PowerSeries.coeff_map, eq_intCast]

private theorem isIntegralQExp_iff {f : ℍ → ℂ} {p : PowerSeries ℤ} :
    ModularCurve.IsIntegralQExp f p ↔
      ∀ n : ℕ, ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  refine ⟨fun h n => isIntegralQExp_coeff h n, fun h => ?_⟩
  ext n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact h n
private theorem isIntegralQExp_Gform (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) :
    IsIntegralQExp (⇑(Gform M k hk c)) (PowerSeries.mk (acoef M k c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_Gform_coeff M k hk c hc n]

end QExp

end Gamma1Eisenstein

open Gamma1Eisenstein in

theorem _root_.ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (M : ℕ) [NeZero M]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ c : ZMod M, c ≠ 0 →
        ModularCurve.IsIntegralQExp (G c)
          (PowerSeries.mk fun n : ℕ =>
            (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
              (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1))) ∧
      ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        ((⇑(G c) : UpperHalfPlane → ℂ) ∣[(k : ℤ)] γ) =
          (⇑(G (c * ((γ 0 0 : ℤ) : ZMod M))) : UpperHalfPlane → ℂ) :=
  ⟨Gform M k hk, fun c hc => isIntegralQExp_Gform M k hk c hc, fun c γ hγ => Gform_slash M k hk c γ hγ⟩
end

end WLightS11.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq

namespace WLightS11.S_CuspForm_exists_gamma1_frickeRational_sigmaTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeCuspTransport

local notation "Δ" => ModularForm.discriminant

section Analytic

private theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem exists_ne_zero {v : ℍ → ℂ} (hv : v ≠ 0) : ∃ τ, v τ ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext h)

private theorem pow_ne_zero_fun {v : ℍ → ℂ} (hv : v ≠ 0) (p : ℕ) : v ^ p ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_ne_zero hv
  intro h
  have := congrFun h τ
  simp only [Pi.pow_apply, Pi.zero_apply] at this
  exact pow_ne_zero p hτ this

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_disc (N : ℕ) : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N := periodic_ofComplex_natCast periodic_disc_one N

private theorem periodic_sub {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g - g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem periodic_div_disc_pow {N : ℕ} {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) N) (e : ℕ) :
    Periodic ((fun τ => g τ / Δ τ ^ e) ∘ ofComplex) N := by
  intro z; have h1 := h z; have h2 := periodic_disc N z
  simp only [comp_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem mdifferentiable_inv {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (h0 : ∀ τ : ℍ, g τ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (g τ)⁻¹) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 := UpperHalfPlane.mdifferentiable_iff.1 hg
  exact (h1.inv fun z _ => h0 _).congr fun z _ => by simp [comp_apply]

private theorem mdifferentiable_div_disc_pow {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => g τ / Δ τ ^ r) := by
  have := hg.mul (mdifferentiable_inv (mdifferentiable_disc.pow r) fun τ => pow_ne_zero _ (disc_ne_zero τ))
  exact this

private theorem tendsto_E {k : ℕ} (hk3 : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk3) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk3) one_pos
    one_mem_strictPeriods_SL
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk3) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk3)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk3)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk3 hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

private theorem tendsto_E₄ : Tendsto (⇑E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨2, rfl⟩
private theorem tendsto_E₆ : Tendsto (⇑E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨3, rfl⟩

private theorem bdd_of_mul_tendsto_one {h e : ℍ → ℂ} (hhe : IsBoundedAtImInfty (h * e))
    (he : Tendsto e atImInfty (𝓝 1)) : IsBoundedAtImInfty h := by
  have hne : ∀ᶠ τ in atImInfty, e τ ≠ 0 := he.eventually_ne one_ne_zero
  have hinv : Tendsto (fun τ => (e τ)⁻¹) atImInfty (𝓝 1) := by simpa using he.inv₀ one_ne_zero
  have hb : IsBoundedAtImInfty ((h * e) * fun τ => (e τ)⁻¹) := hhe.mul (hinv.isBigO_one ℝ)
  refine (hb.congr' ?_ EventuallyEq.rfl)
  filter_upwards [hne] with τ hτ
  simp only [Pi.mul_apply]
  field_simp

private theorem bdd_pow {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero => (simp only [pow_zero]; exact Filter.const_boundedAtFilter atImInfty (1 : ℂ))
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

private theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

private theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

end Analytic

section Params

variable {N : ℕ} [NeZero N]
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)

private abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke (t v.1)

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf t) (MvPolynomial.map ψ R)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : ds s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

private theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R * S) = ev fricke jf K t ψ R * ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_pow (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) (n : ℕ) :
    ev fricke jf K t ψ (R ^ n) = ev fricke jf K t ψ R ^ n := by
  simp [ev]

private theorem ev_sub (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R - S) = ev fricke jf K t ψ R - ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_X (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (o : Idx N) :
    ev fricke jf K t ψ (MvPolynomial.X o) = gen fricke jf t o := by
  simp [ev, MvPolynomial.map_X]

private theorem ev_C (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (c : K) :
    ev fricke jf K t ψ (MvPolynomial.C c) = fun _ => ψ c := by
  funext τ
  simp only [ev, MvPolynomial.map_C, MvPolynomial.aeval_C, Pi.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

include hW hfricke in
private theorem fricke_eq : fricke = fun (a : Fin 2 → ZMod N) (τ : ℍ) =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext a τ; rw [hfricke, hW]

include hL hW hfricke in
private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.1 v hv

include hjf in
private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ := funext hjf
  rw [this]
  intro τ
  exact ((E₄.holo' τ).pow 3).div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

include hL hW hfricke hjf in
private theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf t o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke (ht v.1 v.2)

include hL hW hfricke hjf in
private theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev fricke jf K t ψ R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf t ht o)

include hjf in
private theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [hjf, hjf, disc_smul, E₄_smul]
  field_simp

include hjf in

private theorem E₄_cube_eq (τ : ℍ) : E₄ τ ^ 3 = jf τ * Δ τ := by
  rw [hjf]; field_simp [disc_ne_zero τ]

include hjf in

private theorem E₆_sq_eq (τ : ℍ) : E₆ τ ^ 2 = (jf τ - 1728) * Δ τ := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [hjf, sub_mul, div_mul_cancel₀ _ (disc_ne_zero τ)]
  linear_combination (1728 : ℂ) * h

include hjf in
private theorem exists_jf_ne_zero : ∃ τ : ℍ, jf τ ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 3 hτ (by rw [E₄_cube_eq jf hjf, h, zero_mul])⟩

include hjf in
private theorem exists_jf_sub_ne_zero : ∃ τ : ℍ, jf τ - 1728 ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 2 hτ (by rw [E₆_sq_eq jf hjf, h, zero_mul])⟩

private def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

private def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN γ)

private theorem redN_eq (γ : SL(2, ℤ)) :
    redN (N := N) γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

private theorem redN_mul (γ γ' : SL(2, ℤ)) : redN (N := N) (γ * γ') = redN γ * redN γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

private theorem redN_one : redN (N := N) 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

private theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm (γ * γ') v = vm γ' (vm γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

private theorem vm_one (v : Fin 2 → ZMod N) : vm (N := N) 1 v = v := by simp [vm, redN_one]

private theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm γ v ≠ 0 := by
  intro h
  apply hv
  have : vm γ⁻¹ (vm γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

private def idxMap (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm α v.1, vm_ne_zero α v.2⟩

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

private theorem cw_mul_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G * G') α = cw G α * cw G' α := rfl

private theorem cw_ne_zero {b : ℍ → ℂ} (hb : b ≠ 0) (γ : SL(2, ℤ)) : cw b γ ≠ 0 := by
  intro h
  apply hb
  have : cw (cw b γ) γ⁻¹ = b := by rw [← cw_mul, mul_inv_cancel, cw_one]
  rw [← this, h]; rfl

private theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  exact congrArg (fun F => F R) this

include hL hW hfricke in
private theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) : fricke v (γ • τ) = fricke (vm γ v) τ := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.1 v γ τ

include hL hW hfricke hjf in

private theorem cw_gen {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm α (t v) = t (vm α' v)) (o : Idx N) :
    cw (gen fricke jf t o) α = gen fricke jf t (idxMap α' o) := by
  cases o with
  | none => funext τ; exact jf_smul jf hjf α τ
  | some v => funext τ; rw [cw_apply, gen, gen, Option.elim, fricke_smul L hL W hW fricke hfricke, h]; rfl

include hL hW hfricke hjf in

private theorem cw_ev {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm α (t v) = t (vm α' v)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    cw (ev fricke jf K t ψ R) α = ev fricke jf K t ψ (MvPolynomial.rename (idxMap α') R) := by
  rw [ev, ev, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen fricke jf t i) α) = gen fricke jf t ∘ idxMap α' :=
    funext fun o => cw_gen L hL W hW fricke hfricke jf hjf h o
  rw [this]

private theorem T_zpow_mem_Gamma1 (n : ℤ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

include hs in

private theorem exists_gamma1_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ γ' ∈ Gamma1 N, ∀ v : Fin 2 → ZMod N, vm γ (ds s v) = ds s (vm γ' v) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs with hu
  set t : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) with ht
  have hst : (s : ZMod N) * (t : ZMod N) = 1 := by
    have h1 : ((u : ZMod N)) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact h1
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem N γ).1 hγ
  refine ⟨ModularGroup.T ^ ((γ 0 1 : ℤ) * t), T_zpow_mem_Gamma1 _, fun v => ?_⟩
  have hT : redN (N := N) (ModularGroup.T ^ ((γ 0 1 : ℤ) * t)) = !![1, ((γ 0 1 : ℤ) : ZMod N) * t; 0, 1] := by
    rw [redN, ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hγm : redN (N := N) γ = !![1, ((γ 0 1 : ℤ) : ZMod N); 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [redN, h00, h11, h10]
  funext i
  simp only [vm, hT, hγm, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination (-(v 0 * ((γ 0 1 : ℤ) : ZMod N))) * hst

include hs in

private theorem exists_SL2_conj (A : SL(2, ℤ)) :
    ∃ A' : SL(2, ℤ), ∀ v : Fin 2 → ZMod N, vm A (ds s v) = ds s (vm A' v) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs with hu
  set tN : ZMod N := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) with htN
  have hst : (s : ZMod N) * tN = 1 := Units.mul_inv u
  have hts : tN * (s : ZMod N) = 1 := Units.inv_mul u
  let D : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, (s : ZMod N)]
  let Di : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, tN]
  have hDDi : Di * D = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [D, Di, Matrix.mul_apply, Fin.sum_univ_two, hts]
  have hds : ∀ v : Fin 2 → ZMod N, ds s v = Matrix.vecMul v D := by
    intro v; funext i; fin_cases i <;> simp [ds, D, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  set M' : Matrix (Fin 2) (Fin 2) (ZMod N) := D * redN A * Di with hM'
  have hdetA : (redN (N := N) A).det = 1 := by
    rw [redN_eq, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
  have hdet : M'.det = 1 := by
    rw [hM', Matrix.det_mul, Matrix.det_mul, hdetA]
    simp [D, Di, Matrix.det_fin_two, hst]
  obtain ⟨A', hA'⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod N ⟨M', hdet⟩
  have hred : redN (N := N) A' = M' := by
    have := congrArg (fun y : SL(2, ZMod N) => (y : Matrix (Fin 2) (Fin 2) (ZMod N))) hA'
    simpa [redN_eq] using this
  refine ⟨A', fun v => ?_⟩
  rw [vm, vm, hds, hds, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hred, hM', Matrix.mul_assoc,
    Matrix.mul_assoc, hDDi, Matrix.mul_one]

private def TD (m₀ : ℕ) (u u' : ℍ → ℂ) : Prop := ∀ M : ℕ, m₀ ≤ M →
  (Function.Periodic ((u * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
  (Function.Periodic ((u' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u' * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
  ∀ (n : ℕ) (z : ↥K),
    (z : ℂ) = (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n →
    (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n = φ z

include hL hW hfricke hjf hK hs hφ in

private theorem transportT {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P Q : MvPolynomial (Idx N) K)
    (hQ0 : ev fricke jf K id (algebraMap K ℂ) Q ≠ 0)
    (huQ : u * ev fricke jf K id (algebraMap K ℂ) Q = ev fricke jf K id (algebraMap K ℂ) P) :
    ev fricke jf K (ds s) φ Q ≠ 0 ∧ ∃ u' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u' ∧
      u' * ev fricke jf K (ds s) φ Q = ev fricke jf K (ds s) φ P ∧ ∃ m₀ : ℕ, TD (N := N) K φ m₀ u u' :=
  ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N L hL W hW fricke hfricke jf hjf K hK
    s hs φ hφ u hu P Q hQ0 huQ

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem eq_of_TD {u F₁ F₂ : ℍ → ℂ} (h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₁) (h₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₂)
    {m₁ m₂ : ℕ} (hT₁ : TD (N := N) K φ m₁ u F₁) (hT₂ : TD (N := N) K φ m₂ u F₂) : F₁ = F₂ := by
  set M : ℕ := m₁ + m₂ with hM
  obtain ⟨⟨-, -, hmem⟩, ⟨hper₁, hbd₁, -⟩, hco₁⟩ := hT₁ M (Nat.le_add_right _ _)
  obtain ⟨-, ⟨hper₂, hbd₂, -⟩, hco₂⟩ := hT₂ M (Nat.le_add_left _ _)
  have hexp : qExpansion N (F₁ * Δ ^ M) = qExpansion N (F₂ * Δ ^ M) := by
    ext n
    obtain ⟨z, hz⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
    rw [hco₁ n z hz, hco₂ n z hz]
  have hmd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₁ * Δ ^ M) := h₁.mul (mdifferentiable_disc.pow M)
  have hmd₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₂ * Δ ^ M) := h₂.mul (mdifferentiable_disc.pow M)
  have han₁ := analyticAt_cuspFunction_zero (natCast_pos (N := N)) hper₁ hmd₁ hbd₁
  have han₂ := analyticAt_cuspFunction_zero (natCast_pos (N := N)) hper₂ hmd₂ hbd₂
  have hzero : qExpansion N (F₁ * Δ ^ M - F₂ * Δ ^ M) = 0 := by
    rw [qExpansion_sub han₁ han₂, hexp, sub_self]
  rw [qExpansion_eq_zero_iff (natCast_pos (N := N)) (periodic_sub hper₁ hper₂) (hmd₁.sub hmd₂) (hbd₁.sub hbd₂)]
    at hzero
  funext τ
  have := congrFun hzero τ
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  have hΔ : Δ τ ^ M ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
  have : (F₁ τ - F₂ τ) * Δ τ ^ M = 0 := by rw [sub_mul]; exact this
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hΔ)

private theorem isZero_of_TD {u u' : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hu' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u')
    {m₀ : ℕ} (hT : TD (N := N) K φ m₀ u u') (r : ℕ) (hz : IsZeroAtImInfty (u * Δ ^ r)) :
    IsZeroAtImInfty (u' * Δ ^ r) := by
  set M : ℕ := m₀ + 1 + r with hM
  obtain ⟨⟨hper, hbd, hmem⟩, ⟨hper', hbd', -⟩, hco⟩ := hT M (by omega)
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero

  have gen_facts : ∀ (w : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) w → Periodic ((w * Δ ^ M) ∘ ofComplex) N →
      let F : ℍ → ℂ := fun τ => w τ * Δ τ ^ r / Δ τ
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ Periodic (F ∘ ofComplex) N ∧
        F * Δ = w * Δ ^ r ∧ F * Δ ^ (m₀ + 2) = w * Δ ^ M := by
    intro w hw hwper F
    have hF1 : F * Δ = w * Δ ^ r := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply]; field_simp
    have hF2 : F * Δ ^ (m₀ + 2) = w * Δ ^ M := by
      funext τ; have hΔτ := hΔ τ
      simp only [F, Pi.mul_apply, Pi.pow_apply]
      rw [div_mul_eq_mul_div, div_eq_iff hΔτ, hM]
      ring
    have hFeq : F = fun τ => (w * Δ ^ M) τ / Δ τ ^ (m₀ + 2) := by
      funext τ
      have := congrFun hF2 τ
      simp only [Pi.mul_apply, Pi.pow_apply] at this ⊢
      rw [← this, mul_div_assoc, div_self (pow_ne_zero _ (hΔ τ)), mul_one]
    refine ⟨?_, ?_, hF1, hF2⟩
    · have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Δ τ ^ r / Δ τ) := by
        have h' : (fun τ : ℍ => Δ τ ^ r / Δ τ) = (fun τ => (Δ ^ r : ℍ → ℂ) τ / Δ τ ^ 1) := by
          funext τ; simp
        rw [h']; exact mdifferentiable_div_disc_pow (mdifferentiable_disc.pow r) 1
      have : F = w * fun τ => Δ τ ^ r / Δ τ := by funext τ; simp only [F, Pi.mul_apply]; ring
      rw [this]; exact hw.mul hq
    · rw [hFeq]; exact periodic_div_disc_pow hwper (m₀ + 2)
  have hM1 : 1 ≤ m₀ + 2 := by omega
  obtain ⟨hFhol, hFper, hF1, hF2⟩ := gen_facts u hu hper
  have hcoef := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol hFper (by rw [hF2]; exact hbd)).1
    (by rw [hF1]; exact hz)
  rw [hF2] at hcoef
  obtain ⟨hFhol', hFper', hF1', hF2'⟩ := gen_facts u' hu' hper'
  have := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol' hFper' (by rw [hF2']; exact hbd')).2
  rw [hF1', hF2'] at this
  refine this fun n hn => ?_
  obtain ⟨z, hz'⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
  have hz0 : z = 0 := by
    apply Subtype.val_injective
    rw [hz', hcoef n hn]; rfl
  rw [hco n z hz', hz0, map_zero]

section Main

local notation "𝔢" => ev fricke jf K id (algebraMap K ℂ)
local notation "𝔢'" => ev fricke jf K (ds s) φ
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ))

include hL hW hfricke hjf hK hs hφ in

private theorem transport_pow_div (p q : ℕ) (E : ℍ → ℂ) (J₀ : MvPolynomial (Idx N) K)
    (hEJ : ∀ τ : ℍ, E τ ^ p = 𝔢 J₀ τ * Δ τ) (hJ' : 𝔢' J₀ = 𝔢 J₀) (hJ0 : ∃ τ : ℍ, 𝔢 J₀ τ ≠ 0)
    {u : ℍ → ℂ} (_hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) {P Q : MvPolynomial (Idx N) K} (hQ0 : 𝔢 Q ≠ 0)
    (huQ : u * 𝔢 Q = 𝔢 P) {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hQ'0 : 𝔢' Q ≠ 0)
    (hFQ : F * 𝔢' Q = 𝔢' P)
    (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (u τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
  obtain ⟨G, hG, hGrel⟩ := h
  set J : ℍ → ℂ := 𝔢 J₀ with hJdef
  have hJhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) J := mdifferentiable_ev L hL W hW fricke hfricke jf hjf K id (fun v hv => hv) _ J₀
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (hΔ τ)

  let W₁ : ℍ → ℂ := fun τ => G τ * Δ τ ^ q / (Δ τ ^ m) ^ p
  have hW₁hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) W₁ := by
    have := mdifferentiable_div_disc_pow (hG.mul (mdifferentiable_disc.pow q)) (m * p)
    convert this using 1; try with_reducible_and_instances rfl
    funext τ; simp only [W₁, pow_mul, Pi.mul_apply, Pi.pow_apply]
  have huW : ∀ τ : ℍ, u τ ^ p = J τ ^ q * W₁ τ := by
    intro τ
    have e1 : u τ ^ p * (Δ τ ^ m) ^ p = J τ ^ q * Δ τ ^ q * G τ := by
      rw [← mul_pow, hGrel τ, pow_mul, hEJ τ, mul_pow]
    have hp : (Δ τ ^ m) ^ p ≠ 0 := pow_ne_zero _ (hΔm τ)
    simp only [W₁]
    field_simp
    linear_combination e1

  have hden : 𝔢 (J₀ ^ q * Q ^ p) ≠ 0 := by
    rw [ev_mul, ev_pow, ev_pow]
    intro h0
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero (pow_ne_zero_fun hQ0 p)
    have hz := eq_zero_of_mul_eq_zero (hJhol.pow q)
      ((mdifferentiable_ev L hL W hW fricke hfricke jf hjf K id (fun v hv => hv) _ Q).pow p)
      (fun τ => by simpa using congrFun h0 τ) hτ₀
    obtain ⟨τ₁, hτ₁⟩ := hJ0
    exact pow_ne_zero q hτ₁ (by simpa using congrFun hz τ₁)
  have hW₁Q : W₁ * 𝔢 (J₀ ^ q * Q ^ p) = 𝔢 (P ^ p) := by
    rw [ev_mul, ev_pow, ev_pow, ev_pow, ← huQ, mul_pow]
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [huW τ]; ring

  obtain ⟨-, W₁', hW₁', hW₁'Q, -⟩ := transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hW₁hol _ _ hden hW₁Q

  have hFW : F ^ p = J ^ q * W₁' := by
    have hrel : ∀ τ : ℍ, (F ^ p - J ^ q * W₁') τ * (𝔢' Q ^ p) τ = 0 := by
      intro τ
      have e1 := congrFun hW₁'Q τ
      have e2 := congrFun hFQ τ
      rw [ev_mul, ev_pow, ev_pow, ev_pow, hJ'] at e1
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [← e2, mul_pow] at e1
      linear_combination -e1
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero (pow_ne_zero_fun hQ'0 p)
    have := eq_zero_of_mul_eq_zero ((hF.pow p).sub ((hJhol.pow q).mul hW₁'))
      ((mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ Q).pow p)
      hrel hτ₀
    exact sub_eq_zero.1 this
  refine ⟨fun τ => W₁' τ * (Δ τ ^ m) ^ p / Δ τ ^ q, ?_, fun τ => ?_⟩
  · have := mdifferentiable_div_disc_pow (hW₁'.mul ((mdifferentiable_disc.pow m).pow p)) q
    convert this using 1
  · have h1 := congrFun hFW τ
    simp only [Pi.pow_apply, Pi.mul_apply] at h1
    have hq0 : Δ τ ^ q ≠ 0 := pow_ne_zero _ (hΔ τ)
    rw [mul_pow, h1, pow_mul, hEJ τ, mul_pow]
    field_simp

variable {k a b m}

private def Φ (f : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m

private theorem Φ_apply (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) : Φ (a := a) (b := b) (m := m) f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

private theorem Φ_mul_disc (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ (a := a) (b := b) (m := m) f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (disc_ne_zero τ))]

private theorem mdifferentiable_Φ (f : CuspForm (Γ₁ℝ N) k) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ (a := a) (b := b) (m := m) f) :=
  mdifferentiable_div_disc_pow (f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))) m

include hL hW hfricke hjf hK hs hφ hk in

private theorem main (f : CuspForm (Γ₁ℝ N) k) (P Q : MvPolynomial (Idx N) K) (hQ0 : 𝔢 Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * 𝔢 Q τ = Δ τ ^ m * 𝔢 P τ) :
    ∃ f' : CuspForm (Γ₁ℝ N) k, 𝔢' Q ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (E₄ τ ^ a * E₆ τ ^ b) * 𝔢' Q τ = Δ τ ^ m * 𝔢' P τ := by
  set G : ℍ → ℂ := Φ (a := a) (b := b) (m := m) f with hGdef
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := mdifferentiable_Φ f
  have hGQ : G * 𝔢 Q = 𝔢 P := by
    funext τ
    have h1 := hid τ
    simp only [Pi.mul_apply]
    apply mul_left_cancel₀ (pow_ne_zero m (disc_ne_zero τ))
    rw [← h1, Φ_mul_disc f τ]
    ring

  obtain ⟨h₁, h₂, h₃, h₄⟩ := (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk G hG).1
    ⟨f, Φ_mul_disc f⟩

  obtain ⟨hQ'0, F, hF, hFQ, mF, hTF⟩ := transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hG P Q hQ0 hGQ

  have h₄' : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    intro γ hγ
    obtain ⟨γ', hγ', hconj⟩ := exists_gamma1_conj s hs hγ

    have hGinv : cw G γ' = G := funext fun τ => h₄ γ' hγ' τ
    have hQγ : 𝔢 (MvPolynomial.rename (idxMap γ') Q) ≠ 0 := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' := γ') (fun v => rfl)]
      exact cw_ne_zero hQ0 γ'
    have hGQγ : G * 𝔢 (MvPolynomial.rename (idxMap γ') Q) = 𝔢 (MvPolynomial.rename (idxMap γ') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' := γ') (fun v => rfl),
        ← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' := γ') (fun v => rfl), ← hGinv,
        ← cw_mul_fun, hGQ]
    obtain ⟨hQ'γ, F₂, hF₂, hF₂Q, m₂, hT₂⟩ := transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hG _ _ hQγ hGQγ

    have hFF₂ : F = F₂ := eq_of_TD K φ hF hF₂ hTF hT₂

    have hcwF : cw F γ * 𝔢' (MvPolynomial.rename (idxMap γ') Q) = 𝔢' (MvPolynomial.rename (idxMap γ') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K hconj, ← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
        ← cw_mul_fun, hFQ]
    have hdiff : ∀ τ : ℍ, (cw F γ - F₂) τ * 𝔢' (MvPolynomial.rename (idxMap γ') Q) τ = 0 := by
      intro τ
      have e1 := congrFun hcwF τ
      have e2 := congrFun hF₂Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ'γ
    have hz := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hF γ).sub hF₂)
      (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ _) hdiff hτ₀
    intro τ
    have := congrFun hz τ
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, cw_apply] at this
    rw [this, ← hFF₂]

  have hJ₄ : 𝔢 (MvPolynomial.X none) = jf := by rw [ev_X]; rfl
  have hJ₄' : 𝔢' (MvPolynomial.X none) = 𝔢 (MvPolynomial.X none) := by rw [ev_X, ev_X]; rfl
  have h₁' := transport_pow_div L hL W hW fricke hfricke jf hjf K hK s hs φ hφ m 3 a (E₄ : ℍ → ℂ) (MvPolynomial.X none)
    (fun τ => by rw [hJ₄]; exact E₄_cube_eq jf hjf τ) hJ₄' (by rw [hJ₄]; exact exists_jf_ne_zero jf hjf)
    hG hQ0 hGQ hF hQ'0 hFQ h₁
  set c1728 : K := algebraMap ℚ K 1728 with hc
  have hc' : ((c1728 : K) : ℂ) = 1728 := by
    rw [hc, eq_ratCast, SubfieldClass.coe_ratCast]; norm_num
  have hcφ : φ c1728 = 1728 := by
    rw [hc, ← RingHom.comp_apply, eq_ratCast]; norm_num
  have hJ₆ : 𝔢 (MvPolynomial.X none - MvPolynomial.C c1728) = fun τ => jf τ - 1728 := by
    rw [ev_sub, ev_X, ev_C]; funext τ; simp only [Pi.sub_apply, gen, Option.elim]; rw [← hc']; rfl
  have hJ₆' : 𝔢' (MvPolynomial.X none - MvPolynomial.C c1728) = 𝔢 (MvPolynomial.X none - MvPolynomial.C c1728) := by
    rw [hJ₆, ev_sub, ev_X, ev_C, hcφ]; rfl
  have h₂' := transport_pow_div L hL W hW fricke hfricke jf hjf K hK s hs φ hφ m 2 b (E₆ : ℍ → ℂ)
    (MvPolynomial.X none - MvPolynomial.C c1728)
    (fun τ => by rw [hJ₆]; exact E₆_sq_eq jf hjf τ) hJ₆' (by rw [hJ₆]; exact exists_jf_sub_ne_zero jf hjf)
    hG hQ0 hGQ hF hQ'0 hFQ h₂

  have h₃' : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m) := by
    intro A
    obtain ⟨A', hconj⟩ := exists_SL2_conj s hs A

    have hQA : 𝔢 (MvPolynomial.rename (idxMap A') Q) ≠ 0 := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' := A') (fun v => rfl)]
      exact cw_ne_zero hQ0 A'
    have hGQA : cw G A' * 𝔢 (MvPolynomial.rename (idxMap A') Q) = 𝔢 (MvPolynomial.rename (idxMap A') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' := A') (fun v => rfl),
        ← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' := A') (fun v => rfl), ← cw_mul_fun, hGQ]
    obtain ⟨hQ'A, F₂, hF₂, hF₂Q, m₂, hT₂⟩ := transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ
      (mdifferentiable_cw hG A') _ _ hQA hGQA

    have hcwF : cw F A * 𝔢' (MvPolynomial.rename (idxMap A') Q) = 𝔢' (MvPolynomial.rename (idxMap A') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K hconj, ← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
        ← cw_mul_fun, hFQ]
    have hdiff : ∀ τ : ℍ, (cw F A - F₂) τ * 𝔢' (MvPolynomial.rename (idxMap A') Q) τ = 0 := by
      intro τ
      have e1 := congrFun hcwF τ
      have e2 := congrFun hF₂Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ'A
    have hz := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hF A).sub hF₂)
      (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ _) hdiff hτ₀
    have hcwF₂ : cw F A = F₂ := sub_eq_zero.1 hz
    have : (F ∘ (A • ·)) = cw F A := rfl
    rw [this, hcwF₂]
    exact isZero_of_TD K φ (mdifferentiable_cw hG A') hF₂ hT₂ m (h₃ A')

  obtain ⟨f', hf'⟩ := (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk F hF).2 ⟨h₁', h₂', h₃', h₄'⟩
  refine ⟨f', hQ'0, fun τ => ?_⟩
  have e1 := congrFun hFQ τ
  simp only [Pi.mul_apply] at e1
  rw [hf' τ, mul_comm (F τ), mul_assoc, e1]

end Main

end Params

end FrickeCuspTransport

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem _root_.CuspForm.exists_gamma1_frickeRational_sigmaTransport
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) τ) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) τ =
        ModularForm.discriminant τ ^ m *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) τ :=
  FrickeCuspTransport.main L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hk f P Q hQ0 hid

end WLightS11.S_CuspForm_exists_gamma1_frickeRational_sigmaTransport

namespace WLightS11.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeSpan

local notation "Δ" => ModularForm.discriminant

section Analytic

private theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty CuspForm.discriminant

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem periodic_add {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g + g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem periodic_smul {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (a : ℂ) :
    Periodic ((a • g) ∘ ofComplex) c := by
  intro z; have h1 := h z; simp only [comp_apply, Pi.smul_apply] at h1 ⊢; rw [h1]

private theorem mdifferentiable_inv {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (h0 : ∀ τ : ℍ, g τ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (g τ)⁻¹) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 := UpperHalfPlane.mdifferentiable_iff.1 hg
  exact (h1.inv fun z _ => h0 _).congr fun z _ => by simp [comp_apply]

private theorem mdifferentiable_div_disc_pow {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => g τ / Δ τ ^ r) := by
  have := hg.mul (mdifferentiable_inv (mdifferentiable_disc.pow r) fun τ => pow_ne_zero _ (disc_ne_zero τ))
  exact this

end Analytic

section Params

variable {N : ℕ} [NeZero N]
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

private abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen : Idx N → ℍ → ℂ := fun o => o.elim jf fun v => fricke v.1

private def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}

private def evK (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf) (MvPolynomial.map (algebraMap K ℂ) R)

private theorem evK_def (R : MvPolynomial (Idx N) K) :
    evK fricke jf K R = MvPolynomial.aeval (gen fricke jf) (MvPolynomial.map (algebraMap K ℂ) R) := rfl

private theorem evK_add (R S : MvPolynomial (Idx N) K) : evK fricke jf K (R + S) = evK fricke jf K R + evK fricke jf K S := by
  simp [evK]

private theorem evK_mul (R S : MvPolynomial (Idx N) K) : evK fricke jf K (R * S) = evK fricke jf K R * evK fricke jf K S := by
  simp [evK]

private theorem evK_C (c : K) : evK fricke jf K (MvPolynomial.C c) = fun _ => (c : ℂ) := by
  funext τ
  simp only [evK, MvPolynomial.map_C, MvPolynomial.aeval_C, Pi.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  rfl

private theorem evK_one : evK fricke jf K 1 = 1 := by simp [evK]

private theorem evK_zero : evK fricke jf K 0 = 0 := by simp [evK]

private theorem evK_X (o : Idx N) : evK fricke jf K (MvPolynomial.X o) = gen fricke jf o := by
  simp [evK, MvPolynomial.map_X]

private def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

private def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN γ)

private theorem redN_eq (γ : SL(2, ℤ)) :
    redN (N := N) γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

private theorem redN_mul (γ γ' : SL(2, ℤ)) : redN (N := N) (γ * γ') = redN γ * redN γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

private theorem redN_one : redN (N := N) 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

private theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm (γ * γ') v = vm γ' (vm γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

private theorem vm_one (v : Fin 2 → ZMod N) : vm (N := N) 1 v = v := by simp [vm, redN_one]

private theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm γ v ≠ 0 := by
  intro h
  apply hv
  have : vm γ⁻¹ (vm γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

private def idxMap (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm α v.1, vm_ne_zero α v.2⟩

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
private theorem cw_add_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G + G') α = cw G α + cw G' α := rfl
private theorem cw_smul_fun (c : ℂ) (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw (c • G) α = c • cw G α := rfl
private theorem cw_sub_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G - G') α = cw G α - cw G' α := rfl

private theorem cw_sum {ι : Type*} (s : Finset ι) (G : ι → ℍ → ℂ) (α : SL(2, ℤ)) :
    cw (∑ i ∈ s, G i) α = ∑ i ∈ s, cw (G i) α := map_sum (cwAlgHom α) G s

private theorem mdifferentiable_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄ : ℍ → ℂ) := E₄.holo'
private theorem mdifferentiable_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆ : ℍ → ℂ) := E₆.holo'

private theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

private theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem E₆_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₆ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (6 : ℤ) * E₆ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₆ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

private theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

include hjf in
private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ ^ 1 := by funext τ; rw [hjf, pow_one]
  rw [this]; exact mdifferentiable_div_disc_pow (mdifferentiable_E₄.pow 3) 1

include hjf in
private theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [hjf, hjf, disc_smul, E₄_smul]
  field_simp

include hjf in
private theorem cw_jf (α : SL(2, ℤ)) : cw jf α = jf := funext (jf_smul jf hjf α)

include hjf in

private theorem E₄_cube_eq (τ : ℍ) : E₄ τ ^ 3 = jf τ * Δ τ := by
  rw [hjf]; field_simp [disc_ne_zero τ]

include hjf in

private theorem E₆_sq_eq (τ : ℍ) : E₆ τ ^ 2 = (jf τ - 1728) * Δ τ := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [hjf, sub_mul, div_mul_cancel₀ _ (disc_ne_zero τ)]
  linear_combination (1728 : ℂ) * h

include hjf in
private theorem exists_jf_ne_zero : ∃ τ : ℍ, jf τ ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 3 hτ (by rw [E₄_cube_eq jf hjf, h, zero_mul])⟩

include hjf in
private theorem exists_jf_sub_ne_zero : ∃ τ : ℍ, jf τ - 1728 ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 2 hτ (by rw [E₆_sq_eq jf hjf, h, zero_mul])⟩

include hW hfricke in

private theorem fricke_eq : fricke = fun (a : Fin 2 → ZMod N) (τ : ℍ) =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext a τ; rw [hfricke, hW]

include hL hW hfricke in
private theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) : fricke v (γ • τ) = fricke (vm γ v) τ := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.1 v γ τ

include hL hW hfricke in
private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.1 v hv

include hL hW hfricke in
private theorem fricke_Gamma_smul (v : Fin 2 → ZMod N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N)
    (τ : ℍ) : fricke v (γ • τ) = fricke v τ := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.2.2.2.2.1 v γ hγ τ

include hL hW hfricke hjf in
private theorem cw_gen (α : SL(2, ℤ)) (o : Idx N) : cw (gen fricke jf o) α = gen fricke jf (idxMap α o) := by
  cases o with
  | none => exact cw_jf jf hjf α
  | some v => funext τ; exact fricke_smul L hL W hW fricke hfricke v.1 α τ

include hL hW hfricke hjf in
private theorem mdifferentiable_gen (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke v.2

private theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  simpa using congrArg (fun F => F R) this

include hL hW hfricke hjf in

private theorem cw_evK (R : MvPolynomial (Idx N) K) (α : SL(2, ℤ)) :
    cw (evK fricke jf K R) α = evK fricke jf K (MvPolynomial.rename (idxMap α) R) := by
  rw [evK, evK, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen fricke jf i) α) = gen fricke jf ∘ idxMap α :=
    funext fun o => cw_gen L hL W hW fricke hfricke jf hjf α o
  rw [this]

include hL hW hfricke hjf in
private theorem mdifferentiable_evK (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (evK fricke jf K R) := by
  rw [evK]
  induction (MvPolynomial.map (algebraMap K ℂ) R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp => rw [map_mul, MvPolynomial.aeval_X]; exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf o)

include hL hW hfricke hjf in
private theorem evK_Gamma_smul (R : MvPolynomial (Idx N) K) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    cw (evK fricke jf K R) γ = evK fricke jf K R := by
  rw [evK, cw_aeval]
  have : (fun i => cw (gen fricke jf i) γ) = gen fricke jf := by
    funext o
    cases o with
    | none => exact cw_jf jf hjf γ
    | some v => funext τ; exact fricke_Gamma_smul L hL W hW fricke hfricke v.1 hγ τ
  rw [this]

private theorem gen_mem_genSet (o : Idx N) : gen fricke jf o ∈ genSet (N := N) fricke jf := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩

private theorem aeval_mem_adjoin (R : MvPolynomial (Idx N) ℂ) :
    MvPolynomial.aeval (gen fricke jf) R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := by
  induction R using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_mem_genSet fricke jf o))

private theorem evK_mem_adjoin (R : MvPolynomial (Idx N) K) :
    evK fricke jf K R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := aeval_mem_adjoin fricke jf _

include hL hW hfricke hjf in

private theorem adjoin_isDomain {x y : ℍ → ℂ} (hx : x ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf))
    (hy : y ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf)) (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N L hL W hW fricke hfricke jf hjf
  exact h6 x y hx hy hxy

include hL hW hfricke hjf in
private theorem evK_mul_ne_zero {R S : MvPolynomial (Idx N) K} (hR : evK fricke jf K R ≠ 0) (hS : evK fricke jf K S ≠ 0) :
    evK fricke jf K (R * S) ≠ 0 := by
  rw [evK_mul]
  intro h
  rcases adjoin_isDomain L hL W hW fricke hfricke jf hjf (evK_mem_adjoin fricke jf K R)
    (evK_mem_adjoin fricke jf K S) h with h | h
  · exact hR h
  · exact hS h

private theorem exists_evK_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin K (genSet (N := N) fricke jf)) :
    ∃ R : MvPolynomial (Idx N) K, evK fricke jf K R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx
  have hsec : ∀ y : genSet (N := N) fricke jf, ∃ o : Idx N, gen fricke jf o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  rw [evK, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen fricke jf ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl

private def IsFQ (G : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∃ P Q : MvPolynomial (Idx N) K,
    evK fricke jf K Q ≠ 0 ∧ G * evK fricke jf K Q = evK fricke jf K P

include hL hW hfricke hjf in
private theorem IsFQ.add {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G + G') := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  obtain ⟨hG', P', Q', hQ', hGQ'⟩ := h'
  refine ⟨hG.add hG', P * Q' + P' * Q, Q * Q', evK_mul_ne_zero L hL W hW fricke hfricke jf hjf K hQ hQ', ?_⟩
  rw [evK_add, evK_mul, evK_mul, evK_mul, add_mul, ← hGQ, ← hGQ']
  ring

private theorem IsFQ.smul {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (c : K) : IsFQ fricke jf K ((c : ℂ) • G) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  refine ⟨hG.const_smul _, MvPolynomial.C c * P, Q, hQ, ?_⟩
  rw [evK_mul, evK_C, smul_mul_assoc, hGQ]
  funext τ; simp [smul_eq_mul]

private theorem isFQ_zero : IsFQ fricke jf K (0 : ℍ → ℂ) :=
  ⟨mdifferentiable_const, 0, 1, by rw [evK_one]; exact one_ne_zero, by rw [evK_zero, zero_mul]⟩

include hL hW hfricke hjf in
private theorem IsFQ.mul {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G * G') := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  obtain ⟨hG', P', Q', hQ', hGQ'⟩ := h'
  refine ⟨hG.mul hG', P * P', Q * Q', evK_mul_ne_zero L hL W hW fricke hfricke jf hjf K hQ hQ', ?_⟩
  rw [evK_mul, evK_mul, ← hGQ, ← hGQ']; ring

include hL hW hfricke hjf in
private theorem isFQ_evK (R : MvPolynomial (Idx N) K) : IsFQ fricke jf K (evK fricke jf K R) :=
  ⟨mdifferentiable_evK L hL W hW fricke hfricke jf hjf K R, R, 1, by rw [evK_one]; exact one_ne_zero,
    by rw [evK_one, mul_one]⟩

include hL hW hfricke hjf in
private theorem isFQ_jf : IsFQ fricke jf K jf := by
  have := isFQ_evK L hL W hW fricke hfricke jf hjf K (MvPolynomial.X none)
  rwa [evK_X] at this

include hL hW hfricke hjf in
private theorem isFQ_const (c : K) : IsFQ fricke jf K (fun _ : ℍ => (c : ℂ)) := by
  have := isFQ_evK L hL W hW fricke hfricke jf hjf K (MvPolynomial.C c)
  rwa [evK_C] at this

include hL hW hfricke hjf in
private theorem isFQ_one : IsFQ fricke jf K (1 : ℍ → ℂ) := by
  have h1 : (fun _ : ℍ => ((1 : K) : ℂ)) = 1 := by funext τ; simp
  exact h1 ▸ isFQ_const L hL W hW fricke hfricke jf hjf K 1

private theorem evK_neg (R : MvPolynomial (Idx N) K) : evK fricke jf K (-R) = -evK fricke jf K R := by
  simp [evK]

private theorem IsFQ.neg {G : ℍ → ℂ} (h : IsFQ fricke jf K G) : IsFQ fricke jf K (-G) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  exact ⟨hG.neg, -P, Q, hQ, by rw [evK_neg, neg_mul, hGQ]⟩

include hL hW hfricke hjf in
private theorem IsFQ.sub {G G' : ℍ → ℂ} (h : IsFQ fricke jf K G) (h' : IsFQ fricke jf K G') :
    IsFQ fricke jf K (G - G') := by
  rw [sub_eq_add_neg]
  exact h.add L hL W hW fricke hfricke jf hjf K h'.neg

include hL hW hfricke hjf in
private theorem IsFQ.pow {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (n : ℕ) : IsFQ fricke jf K (G ^ n) := by
  induction n with
  | zero => simpa using isFQ_one L hL W hW fricke hfricke jf hjf K
  | succ n ih => rw [pow_succ]; exact ih.mul L hL W hW fricke hfricke jf hjf K h

include hL hW hfricke hjf in

private theorem isFQ_cw {G : ℍ → ℂ} (h : IsFQ fricke jf K G) (α : SL(2, ℤ)) : IsFQ fricke jf K (cw G α) := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  refine ⟨mdifferentiable_cw hG α, MvPolynomial.rename (idxMap α) P, MvPolynomial.rename (idxMap α) Q, ?_, ?_⟩
  · rw [← cw_evK L hL W hW fricke hfricke jf hjf]
    intro h0
    apply hQ
    have : cw (cw (evK fricke jf K Q) α) α⁻¹ = 0 := by rw [h0]; rfl
    rwa [← cw_mul, mul_inv_cancel, cw_one] at this
  · rw [← cw_evK L hL W hW fricke hfricke jf hjf, ← cw_evK L hL W hW fricke hfricke jf hjf, ← cw_mul_fun, hGQ]

include hL hW hfricke hjf in

private theorem isFQ_Gamma_smul {G : ℍ → ℂ} (h : IsFQ fricke jf K G) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : cw G γ = G := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  have h1 : cw G γ * evK fricke jf K Q = evK fricke jf K P := by
    have := congrArg (fun F => cw F γ) hGQ
    simp only [cw_mul_fun, evK_Gamma_smul L hL W hW fricke hfricke jf hjf K _ hγ] at this
    exact this
  have h2 : ∀ τ, (cw G γ - G) τ * evK fricke jf K Q τ = 0 := by
    intro τ
    have := congrFun h1 τ
    have h' := congrFun hGQ τ
    simp only [Pi.mul_apply, Pi.sub_apply] at this h' ⊢
    rw [sub_mul, this, h', sub_self]
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, evK fricke jf K Q τ₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hQ (funext hall)
  have := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hG γ).sub hG)
    (mdifferentiable_evK L hL W hW fricke hfricke jf hjf K Q) h2 hτ₀
  exact sub_eq_zero.1 this

include hL hW hfricke hjf in

private def M : Submodule K (ℍ → ℂ) where
  carrier := {G | IsFQ fricke jf K G}
  add_mem' hG hG' := IsFQ.add L hL W hW fricke hfricke jf hjf K hG hG'
  zero_mem' := isFQ_zero fricke jf K
  smul_mem' c _ hG := IsFQ.smul fricke jf K hG c

private theorem mem_M {G : ℍ → ℂ} : G ∈ M L hL W hW fricke hfricke jf hjf K ↔ IsFQ fricke jf K G := Iff.rfl

section Width

variable (N)

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
    convert h1 using 1; try with_reducible_and_instances rfl
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

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

private theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private structure Nice (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)

private structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop extends Nice N m g where
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

private theorem Nice.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem Nice.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

private theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

private theorem Nice.succ {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) : Nice N (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc

private theorem Nice.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : Nice N m g) : Nice N m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem Nice.add {m : ℕ} {g g' : ℍ → ℂ} (h : Nice N m g) (h' : Nice N m g') : Nice N m (g + g') where
  mdiff := h.mdiff.add h'.mdiff
  periodic := by rw [add_mul]; exact periodic_add h.periodic h'.periodic
  bdd := by rw [add_mul]; exact h.bdd.add h'.bdd

private theorem Nice.smul {m : ℕ} {g : ℍ → ℂ} (h : Nice N m g) (c : ℂ) : Nice N m (c • g) where
  mdiff := h.mdiff.const_smul c
  periodic := by rw [smul_mul_assoc]; exact periodic_smul h.periodic c
  bdd := by
    rw [smul_mul_assoc]
    have := h.bdd.const_mul_left c
    exact this

private theorem nice_zero (m : ℕ) : Nice N m (0 : ℍ → ℂ) where
  mdiff := mdifferentiable_const
  periodic := by intro z; simp
  bdd := by rw [zero_mul]; exact UpperHalfPlane.zero_form_isBoundedAtImInfty

private theorem Nice.sum {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℂ} (h : ∀ i ∈ s, Nice N m (g i))
    (c : ι → ℂ) : Nice N m (∑ i ∈ s, c i • g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nice_zero m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact ((h a (Finset.mem_insert_self a s)).smul (c a)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem qExpansion_sum {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℂ} (h : ∀ i ∈ s, Nice N m (g i))
    (c : ι → ℂ) (n : ℕ) :
    (qExpansion N ((∑ i ∈ s, c i • g i) * Δ ^ m)).coeff n = ∑ i ∈ s, c i * (qExpansion N (g i * Δ ^ m)).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mul,
        qExpansion_add ((h a (Finset.mem_insert_self a s)).smul (c a)).analyticAt
          (Nice.sum s (fun i hi => h i (Finset.mem_insert_of_mem hi)) c).analyticAt,
        map_add, ih fun i hi => h i (Finset.mem_insert_of_mem hi), smul_mul_assoc,
        qExpansion_smul (h a (Finset.mem_insert_self a s)).analyticAt, map_smul, smul_eq_mul]

private theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  toNice := h.toNice.succ
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem K r

private theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem coeff_map_mem (R : MvPolynomial (Idx N) K) (mo : Idx N →₀ ℕ) :
    (MvPolynomial.map (algebraMap K ℂ) R).coeff mo ∈ K := by
  rw [MvPolynomial.coeff_map]; exact (R.coeff mo).2

include hL hW hfricke hjf hK in

private theorem IsFQ.exists_ratAt {G : ℍ → ℂ} (h : IsFQ fricke jf K G) : ∃ m, RatAt N K m G := by
  obtain ⟨hG, P, Q, hQ, hGQ⟩ := h
  have hint := WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke jf hjf
    K hK G hG P Q hQ hGQ
  obtain ⟨m, hper, hbdd, hmem⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL
    W hW fricke hfricke jf hjf K hK hG (MvPolynomial.map (algebraMap K ℂ) P)
    (MvPolynomial.map (algebraMap K ℂ) Q) (coeff_map_mem P) (coeff_map_mem Q) hQ hGQ hint
  exact ⟨m, ⟨⟨hG, hper, hbdd⟩, hmem⟩⟩

include hL hW hfricke hjf hK in

private theorem M_flat (s : Finset (ℍ → ℂ)) (hs : (↑s : Set (ℍ → ℂ)) ⊆ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ)))
    (hind : LinearIndependent K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ))) :
    LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
  classical
  have hrat : ∀ f : ↥s, ∃ m, RatAt N K m (f : ℍ → ℂ) := fun f =>
    IsFQ.exists_ratAt L hL W hW fricke hfricke jf hjf hK (hs (by simp))
  choose mf hmf using hrat
  set M₀ : ℕ := ∑ f : ↥s, mf f
  have hM₀ : ∀ f : ↥s, RatAt N K M₀ (f : ℍ → ℂ) := fun f =>
    (hmf f).of_le (Finset.single_le_sum (fun g _ => Nat.zero_le (mf g)) (Finset.mem_univ f))
  refine WLight.linearIndependent_complex_of_qExpansion_rational N K s M₀ (fun f hf => ?_) hind
  have h := hM₀ ⟨f, hf⟩
  exact ⟨h.mdiff, h.periodic, h.bdd, h.mem⟩

end Width

section Key

include hL hW hfricke hjf hK in

private theorem mem_span_M {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty (cw G α * Δ ^ m)) :
    G ∈ Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ)) := by
  classical

  set S : Set (ℍ → ℂ) := {F | ∃ α : SL(2, ℤ), F = cw G α} with hS
  have hGS : G ∈ S := ⟨1, (cw_one G).symm⟩
  have hhol : ∀ F ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rintro F ⟨α, rfl⟩; exact mdifferentiable_cw hG α
  have hpb' : ∀ F ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) := by
    rintro F ⟨α, rfl⟩; exact hpb α
  have hst : ∀ γ : SL(2, ℤ), ∀ F ∈ S, (F ∘ (γ • ·)) ∈ S := by
    rintro γ F ⟨α, rfl⟩
    exact ⟨α * γ, by rw [cw_mul]; rfl⟩
  have hinvS : ∀ F ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    rintro F ⟨α, rfl⟩ γ hγ τ
    simp only [cw_apply]
    have : α • γ • τ = (α * γ * α⁻¹) • α • τ := by simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (Subgroup.Normal.conj_mem (CongruenceSubgroup.Gamma_normal N) γ hγ α) _
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N L hL W hW fricke hfricke
    jf hjf S hhol hpb' hst hinvS hGS

  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => hpb γ
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N L hL W hW fricke hfricke
    jf hjf ha hb hb0 hG hGb hpbG

  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, -, -⟩ :=
    WLight.frickeFunction_intBaseChange N L hL W hW fricke hfricke jf hjf hG ha hb hb0 hGb p hprel

  subst hK
  have hGiM : ∀ i, Gi i ∈ M L hL W hW fricke hfricke jf hjf
      (IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}) := by
    intro i
    obtain ⟨hPi, hQi, hQi0, hrel⟩ := hPQ i
    obtain ⟨RP, hRP⟩ := exists_evK_of_mem_adjoin fricke jf _ hPi
    obtain ⟨RQ, hRQ⟩ := exists_evK_of_mem_adjoin fricke jf _ hQi
    exact ⟨hGimd i, RP, RQ, by rw [hRQ]; exact hQi0, by rw [hRQ, hRP]; exact hrel⟩
  rw [hGsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hGiM i))

end Key

section Twist

variable (σ : ℂ ≃ₐ[K] ℂ)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K

include hK in
private theorem exists_twist : ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
    (∀ i, e i ∈ 𝕄) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
  WLight.exists_twist_of_flat K 𝕄 (M_flat L hL W hW fricke hfricke jf hjf hK) σ

include hK in

private def Tw : (ℍ → ℂ) → (ℍ → ℂ) := (exists_twist L hL W hW fricke hfricke jf hjf K hK σ).choose

variable {L hL W hW fricke hfricke jf hjf K}

local notation "𝕋" => Tw L hL W hW fricke hfricke jf hjf K hK σ

private theorem Tw_rep {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    𝕋 (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
  (exists_twist L hL W hW fricke hfricke jf hjf K hK σ).choose_spec ι c e he

private theorem exists_rep {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (e : Fin n → ℍ → ℂ), (∀ i, e i ∈ 𝕄) ∧ u = ∑ i, c i • e i := by
  obtain ⟨n, c, g, hu⟩ := Submodule.mem_span_set'.1 hu
  exact ⟨n, c, fun i => (g i : ℍ → ℂ), fun i => (g i).2, hu.symm⟩

private theorem sum_smul_mem_span {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    ∑ i, c i • e i ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (he i))

private theorem Tw_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [Tw_rep hK σ c e he]
  exact sum_smul_mem_span _ e he

private theorem Tw_add {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (u + v) =
      𝕋 u + 𝕋 v := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  have hsum : (∑ i, c i • e i) + (∑ i, c' i • e' i) =
      ∑ i : Fin n ⊕ Fin n', Sum.elim c c' i • Sum.elim e e' i := by
    rw [Fintype.sum_sum_type]; rfl
  rw [hsum, Tw_rep hK σ _ _ (fun i => by cases i <;> simp [he, he']),
    Tw_rep hK σ c e he, Tw_rep hK σ c' e' he',
    Fintype.sum_sum_type]
  rfl

private theorem Tw_smul (a : ℂ) {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (a • u) = σ a • 𝕋 u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have hsum : a • (∑ i, c i • e i) = ∑ i, (a * c i) • e i := by
    rw [Finset.smul_sum]; simp_rw [smul_smul]
  rw [hsum, Tw_rep hK σ _ e he, Tw_rep hK σ c e he,
    Finset.smul_sum]
  simp_rw [map_mul, smul_smul]

private theorem Tw_mul {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    𝕋 (u * v) =
      𝕋 u * 𝕋 v := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  have hprod : ∀ (x : Fin n → ℂ) (y : Fin n' → ℂ), (∑ i, x i • e i) * (∑ j, y j • e' j) =
      ∑ ij : Fin n × Fin n', (x ij.1 * y ij.2) • (e ij.1 * e' ij.2) := by
    intro x y
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [smul_mul_smul_comm]
  have hee : ∀ ij : Fin n × Fin n', e ij.1 * e' ij.2 ∈ 𝕄 := fun ij =>
    IsFQ.mul L hL W hW fricke hfricke jf hjf K (he ij.1) (he' ij.2)
  rw [hprod, Tw_rep hK σ _ _ hee, Tw_rep hK σ c e he,
    Tw_rep hK σ c' e' he', hprod]
  simp_rw [map_mul]

private theorem Tw_of_mem {e : ℍ → ℂ} (he : e ∈ 𝕄) : 𝕋 e = e := by
  have h1 : e = ∑ _i : Fin 1, (1 : ℂ) • e := by simp
  conv_lhs => rw [h1]
  rw [Tw_rep hK σ _ _ (fun _ => he)]
  simp

private theorem mem_span_of_mem {e : ℍ → ℂ} (he : e ∈ 𝕄) : e ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  Submodule.subset_span he

private theorem one_mem_span : (1 : ℍ → ℂ) ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) :=
  mem_span_of_mem (isFQ_one L hL W hW fricke hfricke jf hjf K)

private theorem mul_mem_span {u v : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    (hv : v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) : u * v ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨n', c', e', he', rfl⟩ := exists_rep hv
  rw [Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (IsFQ.mul L hL W hW fricke hfricke jf hjf K (he i) (he' j)))

private theorem pow_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (n : ℕ) :
    u ^ n ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_span
  | succ n ih => rw [pow_succ]; exact mul_mem_span ih hu

private theorem Tw_pow {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (n : ℕ) :
    𝕋 (u ^ n) = (𝕋 u) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Tw_of_mem hK σ (isFQ_one L hL W hW fricke hfricke jf hjf K)
  | succ n ih =>
      rw [pow_succ, pow_succ, Tw_mul hK σ (pow_mem_span hu n) hu, ih]

private theorem cw_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (α : SL(2, ℤ)) :
    cw u α ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [cw_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [cw_smul_fun]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (isFQ_cw L hL W hW fricke hfricke jf hjf K (he i) α))

private theorem Tw_cw {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) (α : SL(2, ℤ)) :
    𝕋 (cw u α) = cw (𝕋 u) α := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have h1 : cw (∑ i, c i • e i) α = ∑ i, c i • cw (e i) α := by rw [cw_sum]; rfl
  rw [h1, Tw_rep hK σ _ _ (fun i => isFQ_cw L hL W hW fricke hfricke jf hjf K (he i) α),
    Tw_rep hK σ c e he, cw_sum]
  rfl

private theorem mdifferentiable_of_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i • e i) :=
    fun i _ => ((he i).1).const_smul (c i)
  exact MDifferentiable.sum (t := Finset.univ) this

private theorem Tw_mdifferentiable {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (𝕋 u) :=
  mdifferentiable_of_mem_span (Tw_mem_span hK σ hu)

private theorem Gamma_smul_of_mem_span {u : ℍ → ℂ} (hu : u ∈ Submodule.span ℂ (𝕄 : Set (ℍ → ℂ)))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) : cw u γ = u := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  rw [cw_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cw_smul_fun, isFQ_Gamma_smul L hL W hW fricke hfricke jf hjf K (he i) hγ]

include hK in

private theorem exists_common_ratAt {ι : Type} [Fintype ι] (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ i, RatAt N K m (e i) := by
  classical
  have : ∀ i, ∃ m, RatAt N K m (e i) := fun i => IsFQ.exists_ratAt L hL W hW fricke hfricke jf hjf hK (he i)
  choose mf hmf using this
  refine ⟨∑ i, mf i, fun m hm i => (hmf i).of_le (le_trans ?_ hm)⟩
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (mf j)) (Finset.mem_univ i)

private theorem Tw_coeff {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) (n : ℕ) :
    (qExpansion N (𝕋 (∑ i, c i • e i) * Δ ^ m)).coeff n =
      σ ((qExpansion N ((∑ i, c i • e i) * Δ ^ m)).coeff n) := by
  rw [Tw_rep hK σ c e he,
    qExpansion_sum Finset.univ (fun i _ => (hm i).toNice) (fun i => σ (c i)) n,
    qExpansion_sum Finset.univ (fun i _ => (hm i).toNice) c n, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  obtain ⟨z, hz⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (e i * Δ ^ m)).coeff n := ⟨⟨_, (hm i).mem n⟩, rfl⟩
  rw [← hz]
  exact (σ.commutes z).symm

private theorem nice_Tw {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) (he : ∀ i, e i ∈ 𝕄) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) : Nice N m (𝕋 (∑ i, c i • e i)) := by
  rw [Tw_rep hK σ c e he]
  exact Nice.sum Finset.univ (fun i _ => (hm i).toNice) _

private theorem nice_sum {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ) {m : ℕ}
    (hm : ∀ i, RatAt N K m (e i)) : Nice N m (∑ i, c i • e i) :=
  Nice.sum Finset.univ (fun i _ => (hm i).toNice) _

end Twist

section Stability

private theorem tendsto_E {k : ℕ} (hk3 : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk3) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk3) one_pos
    one_mem_strictPeriods_SL
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk3) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk3)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk3)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk3 hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

private theorem tendsto_E₄ : Tendsto (⇑E₄ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨2, rfl⟩
private theorem tendsto_E₆ : Tendsto (⇑E₆ : ℍ → ℂ) atImInfty (𝓝 1) := tendsto_E (by norm_num) ⟨3, rfl⟩

private theorem bdd_of_mul_tendsto_one {h e : ℍ → ℂ} (hhe : IsBoundedAtImInfty (h * e))
    (he : Tendsto e atImInfty (𝓝 1)) : IsBoundedAtImInfty h := by
  have hne : ∀ᶠ τ in atImInfty, e τ ≠ 0 := he.eventually_ne one_ne_zero
  have hinv : Tendsto (fun τ => (e τ)⁻¹) atImInfty (𝓝 1) := by simpa using he.inv₀ one_ne_zero
  have hb : IsBoundedAtImInfty ((h * e) * fun τ => (e τ)⁻¹) := hhe.mul (hinv.isBigO_one ℝ)
  refine (hb.congr' ?_ EventuallyEq.rfl)
  filter_upwards [hne] with τ hτ
  simp only [Pi.mul_apply]
  field_simp

private theorem bdd_pow {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero => (simp only [pow_zero]; exact Filter.const_boundedAtFilter atImInfty (1 : ℂ))
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private theorem periodic_of_Gamma_invariant {N : ℕ} [NeZero N] {u : ℍ → ℂ}
    (h : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw u γ = u) : Periodic (u ∘ ofComplex) N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    rwa [Int.natAbs_natCast] at this
  have hu : ∀ τ : ℍ, u ((ModularGroup.T ^ (N : ℤ)) • τ) = u τ := fun τ => congrFun (h _ hT) τ
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := hu ⟨w, hw⟩
    rw [modular_T_zpow_smul] at this
    convert this using 2; try with_reducible_and_instances rfl
    ext
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + N) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

private theorem periodic_disc_fun (φ : ℂ → ℂ) : Periodic ((fun τ : ℍ => φ (Δ τ)) ∘ ofComplex) 1 := by
  intro z
  have := periodic_disc_one z
  simp only [comp_apply] at this ⊢
  rw [this]

variable {L hL W hW fricke hfricke jf hjf K}
variable (σ : ℂ ≃ₐ[K] ℂ)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K
local notation "𝕊" => Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ))
local notation "𝕋" => Tw L hL W hW fricke hfricke jf hjf K hK σ

include hK in

private theorem transport_pow_div (m p q : ℕ) (E J : ℍ → ℂ) (_hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E)
    (hEJ : ∀ τ : ℍ, E τ ^ p = J τ * Δ τ) (hJM : J ∈ 𝕄) (hJ0 : ∃ τ : ℍ, J τ ≠ 0)
    (hJinv : ∀ α : SL(2, ℤ), cw J α = J) (hE1 : Tendsto E atImInfty (𝓝 1))
    {v : ℍ → ℂ} (hv : v ∈ 𝕊) (hvinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw v γ = v)
    (hvpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw v α * Δ ^ m))
    (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (v τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      ∀ τ : ℍ, (𝕋 v τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
  obtain ⟨G, hG, hGrel⟩ := h
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (hΔ τ)

  let W₁ : ℍ → ℂ := fun τ => G τ * Δ τ ^ q / (Δ τ ^ m) ^ p
  have hW₁hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) W₁ := by
    have := mdifferentiable_div_disc_pow (hG.mul (mdifferentiable_disc.pow q)) (m * p)
    convert this using 1; try with_reducible_and_instances rfl
    funext τ; simp only [W₁, pow_mul, Pi.mul_apply, Pi.pow_apply]
  have hvW : ∀ τ : ℍ, v τ ^ p = J τ ^ q * W₁ τ := by
    intro τ
    have e1 : v τ ^ p * (Δ τ ^ m) ^ p = J τ ^ q * Δ τ ^ q * G τ := by
      rw [← mul_pow, hGrel τ, pow_mul, hEJ τ, mul_pow]
    have hp : (Δ τ ^ m) ^ p ≠ 0 := pow_ne_zero _ (hΔm τ)
    simp only [W₁]
    field_simp
    linear_combination e1
  have hvWfun : v ^ p = J ^ q * W₁ := funext fun τ => by simp [hvW τ]

  have hW₁inv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, W₁ (γ • τ) = W₁ τ := by
    intro γ hγ
    have hzero : ∀ τ : ℍ, (cw W₁ γ - W₁) τ * (J ^ q) τ = 0 := by
      intro τ
      have h1 := congrArg (fun F => cw F γ) hvWfun
      try simp only at h1
      rw [show cw (v ^ p) γ = (cw v γ) ^ p from rfl, hvinv γ hγ, cw_mul_fun,
        show cw (J ^ q) γ = (cw J γ) ^ q from rfl, isFQ_Gamma_smul L hL W hW fricke hfricke jf hjf K hJM hγ] at h1
      have := congrFun h1 τ
      have h2 := congrFun hvWfun τ
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, cw_apply] at this h2 ⊢
      linear_combination h2 - this
    obtain ⟨τ₀, hτ₀⟩ := hJ0
    have hJq : (J ^ q) τ₀ ≠ 0 := by simpa using pow_ne_zero q hτ₀
    have := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hW₁hol γ).sub hW₁hol) (hJM.1.pow q) hzero hJq
    intro τ
    have := congrFun this τ
    simpa [sub_eq_zero, cw_apply] using this
  have hW₁pb : ∀ α : SL(2, ℤ), ∃ r : ℕ, IsBoundedAtImInfty (cw W₁ α * Δ ^ r) := by
    intro α
    refine ⟨m * p, ?_⟩
    have hid : ∀ τ : ℍ, (cw W₁ α τ * (Δ τ ^ m) ^ p) * E τ ^ (p * q) =
        (cw v α τ * Δ τ ^ m) ^ p * Δ τ ^ q := by
      intro τ
      have h1 : (cw v α τ) ^ p = (cw J α τ) ^ q * cw W₁ α τ :=
        congrFun (congrArg (fun F => cw F α) hvWfun) τ
      rw [show cw J α τ = J τ from congrFun (hJinv α) τ] at h1
      rw [pow_mul, hEJ τ, mul_pow, mul_pow, h1]
      ring
    have hb : IsBoundedAtImInfty ((fun τ => cw W₁ α τ * (Δ τ ^ m) ^ p) * fun τ => E τ ^ (p * q)) := by
      have h3 : IsBoundedAtImInfty (fun τ => (cw v α τ * Δ τ ^ m) ^ p * Δ τ ^ q) :=
        (bdd_pow (hvpb α) p).mul (bdd_pow isBoundedAtImInfty_disc q)
      refine h3.congr' ?_ EventuallyEq.rfl
      exact Eventually.of_forall fun τ => (hid τ).symm
    have hE' : Tendsto (fun τ => E τ ^ (p * q)) atImInfty (𝓝 1) := by simpa using hE1.pow (p * q)
    have := bdd_of_mul_tendsto_one hb hE'
    convert this using 1; try with_reducible_and_instances rfl
    funext τ; simp [pow_mul, cw_apply]
  have hW₁span : W₁ ∈ 𝕊 := mem_span_M L hL W hW fricke hfricke jf hjf K hK hW₁hol hW₁inv hW₁pb

  have hJq_mem : J ^ q ∈ 𝕄 := IsFQ.pow L hL W hW fricke hfricke jf hjf K hJM q
  have hTv : (𝕋 v) ^ p = J ^ q * 𝕋 W₁ := by
    rw [← Tw_pow hK σ hv p, hvWfun, Tw_mul hK σ (Submodule.subset_span hJq_mem) hW₁span, Tw_of_mem hK σ hJq_mem]
  refine ⟨fun τ => 𝕋 W₁ τ * (Δ τ ^ m) ^ p / Δ τ ^ q, ?_, fun τ => ?_⟩
  · have := mdifferentiable_div_disc_pow ((Tw_mdifferentiable hK σ hW₁span).mul ((mdifferentiable_disc.pow m).pow p)) q
    convert this using 1
  · have h1 := congrFun hTv τ
    simp only [Pi.pow_apply, Pi.mul_apply] at h1
    have hq0 : Δ τ ^ q ≠ 0 := pow_ne_zero _ (hΔ τ)
    rw [mul_pow, h1, pow_mul, hEJ τ, mul_pow]
    field_simp

include hK in

private theorem isZero_Tw {u : ℍ → ℂ} (hu : u ∈ 𝕊) (r : ℕ) (hz : IsZeroAtImInfty (u * Δ ^ r)) :
    IsZeroAtImInfty (𝕋 u * Δ ^ r) := by
  obtain ⟨n, c, e, he, rfl⟩ := exists_rep hu
  obtain ⟨m₀, hm₀⟩ := exists_common_ratAt hK e he
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero

  have gen_facts : ∀ (w : ℍ → ℂ), Nice N (r + m₀) w → (∀ γ ∈ CongruenceSubgroup.Gamma N, cw w γ = w) →
      let F : ℍ → ℂ := fun τ => w τ * Δ τ ^ r / Δ τ
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ Periodic (F ∘ ofComplex) N ∧
        IsBoundedAtImInfty (F * Δ ^ (m₀ + 1)) ∧ F * Δ = w * Δ ^ r ∧ F * Δ ^ (m₀ + 1) = w * Δ ^ (r + m₀) := by
    intro w hw hwinv F
    have hFeq : F = w * fun τ => Δ τ ^ r / Δ τ := by funext τ; simp only [F, Pi.mul_apply]; ring
    have hF1 : F * Δ = w * Δ ^ r := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply]; field_simp
    have hF2 : F * Δ ^ (m₀ + 1) = w * Δ ^ (r + m₀) := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply, pow_add, pow_one]; field_simp
    refine ⟨?_, ?_, ?_, hF1, hF2⟩
    · have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Δ τ ^ r / Δ τ) := by
        have h' : (fun τ : ℍ => Δ τ ^ r / Δ τ) = (fun τ => (Δ ^ r : ℍ → ℂ) τ / Δ τ ^ 1) := by
          funext τ; simp
        rw [h']; exact mdifferentiable_div_disc_pow (mdifferentiable_disc.pow r) 1
      rw [hFeq]; exact hw.mdiff.mul hq
    · rw [hFeq]
      exact periodic_mul (periodic_of_Gamma_invariant hwinv)
        (periodic_ofComplex_natCast (periodic_disc_fun fun x => x ^ r / x) N)
    · rw [hF2]; exact hw.bdd
  have hM1 : 1 ≤ m₀ + 1 := Nat.le_add_left 1 m₀
  have hrat : ∀ i, RatAt N K (r + m₀) (e i) := hm₀ _ (Nat.le_add_left m₀ r)

  have huN : Nice N (r + m₀) (∑ i, c i • e i) := nice_sum c e hrat
  have huinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw (∑ i, c i • e i) γ = ∑ i, c i • e i := fun γ hγ =>
    Gamma_smul_of_mem_span (sum_smul_mem_span c e he) hγ
  obtain ⟨hFhol, hFper, hFbd, hF1, hF2⟩ := gen_facts _ huN huinv
  have hcoef := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol hFper hFbd).1
    (by rw [hF1]; exact hz)
  rw [hF2] at hcoef

  have hTuN : Nice N (r + m₀) (𝕋 (∑ i, c i • e i)) := nice_Tw hK σ c e he hrat
  have hTuinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw (𝕋 (∑ i, c i • e i)) γ = 𝕋 (∑ i, c i • e i) :=
    fun γ hγ => Gamma_smul_of_mem_span (Tw_mem_span hK σ (sum_smul_mem_span c e he)) hγ
  obtain ⟨hFhol', hFper', hFbd', hF1', hF2'⟩ := gen_facts _ hTuN hTuinv
  have := (WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol' hFper' hFbd').2
  rw [hF1', hF2'] at this
  refine this fun n' hn' => ?_
  rw [Tw_coeff hK σ c e he hrat, hcoef n' hn', map_zero]

variable (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)

private def Φ : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m
  map_add' f g := by funext τ; simp only [add_apply, Pi.add_apply]; ring
  map_smul' c f := by funext τ; simp only [smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem Φ_apply (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    Φ Γ k a b m f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

private theorem Φ_mul_disc (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ Γ k a b m f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (disc_ne_zero τ))]

private theorem mdifferentiable_Φ (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ Γ k a b m f) :=
  mdifferentiable_div_disc_pow (f.holo'.mul ((mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b))) m

include hΓ hk in

private theorem crit_Φ (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (Φ Γ k a b m f τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
      (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (Φ Γ k a b m f τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
      (∀ A : SL(2, ℤ), IsZeroAtImInfty (((Φ Γ k a b m f) ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, Φ Γ k a b m f (γ • τ) = Φ Γ k a b m f τ) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  exact (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff Γ k a b m hk (Φ Γ k a b m f)
    (mdifferentiable_Φ Γ k a b m f)).1 ⟨f, Φ_mul_disc Γ k a b m f⟩

include hΓ hk hK in
private theorem Φ_mem_span (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Φ Γ k a b m f ∈ 𝕊 := by
  obtain ⟨-, -, h₃, h₄⟩ := crit_Φ Γ hΓ k a b m hk f
  refine mem_span_M L hL W hW fricke hfricke jf hjf K hK (mdifferentiable_Φ Γ k a b m f)
    (fun γ hγ τ => h₄ γ (hΓ hγ) τ) fun α => ⟨m, (h₃ α).isBoundedAtImInfty⟩

include hΓ hk hK in

private theorem exists_Φ_eq_Tw (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ f' : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, Φ Γ k a b m f' = 𝕋 (Φ Γ k a b m f) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  set v := Φ Γ k a b m f with hvdef
  obtain ⟨h₁, h₂, h₃, h₄⟩ := crit_Φ Γ hΓ k a b m hk f
  have hv : v ∈ 𝕊 := Φ_mem_span hK Γ hΓ k a b m hk f
  have hvinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, cw v γ = v := fun γ hγ => funext fun τ => h₄ γ (hΓ hγ) τ
  have hvpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw v α * Δ ^ m) := fun α => (h₃ α).isBoundedAtImInfty

  have h₁' := transport_pow_div hK σ m 3 a (E₄ : ℍ → ℂ) jf mdifferentiable_E₄ (E₄_cube_eq jf hjf)
    (isFQ_jf L hL W hW fricke hfricke jf hjf K) (exists_jf_ne_zero jf hjf) (cw_jf jf hjf) tendsto_E₄ hv hvinv hvpb h₁
  have hJ : (fun τ : ℍ => jf τ - 1728) ∈ 𝕄 := by
    have h1 := (isFQ_jf L hL W hW fricke hfricke jf hjf K).sub L hL W hW fricke hfricke jf hjf K
      (isFQ_const L hL W hW fricke hfricke jf hjf K (algebraMap ℚ K 1728))
    have h1728 : ((algebraMap ℚ K 1728 : K) : ℂ) = 1728 := by
      rw [eq_ratCast, SubfieldClass.coe_ratCast]; norm_num
    have h2 : (jf - fun _ : ℍ => ((algebraMap ℚ K 1728 : K) : ℂ)) = fun τ => jf τ - 1728 := by
      funext τ; simp only [Pi.sub_apply, h1728]
    rw [h2] at h1
    exact h1
  have h₂' := transport_pow_div hK σ m 2 b (E₆ : ℍ → ℂ) (fun τ => jf τ - 1728) mdifferentiable_E₆
    (E₆_sq_eq jf hjf) hJ (exists_jf_sub_ne_zero jf hjf)
    (fun α => funext fun τ => by simp only [cw_apply]; rw [jf_smul jf hjf]) tendsto_E₆ hv hvinv hvpb h₂

  have h₃' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (((𝕋 v) ∘ (A • ·)) * Δ ^ m) := by
    intro A
    have : ((𝕋 v) ∘ (A • ·)) = cw (𝕋 v) A := rfl
    rw [this, ← Tw_cw hK σ hv A]
    exact isZero_Tw hK σ (cw_mem_span hv A) m (h₃ A)

  have h₄' : ∀ γ ∈ Γ, ∀ τ : ℍ, 𝕋 v (γ • τ) = 𝕋 v τ := by
    intro γ hγ τ
    have hinv : cw v γ = v := funext fun τ => h₄ γ hγ τ
    have := Tw_cw hK σ hv γ
    rw [hinv] at this
    have := congrFun this τ
    simpa [cw_apply] using this.symm
  obtain ⟨f', hf'⟩ := (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff Γ k a b m hk (𝕋 v)
    (Tw_mdifferentiable hK σ hv)).2 ⟨h₁', h₂', h₃', h₄'⟩
  refine ⟨f', funext fun τ => ?_⟩
  rw [Φ_apply, hf' τ, mul_div_assoc, div_self (pow_ne_zero _ (disc_ne_zero τ)), mul_one]

end Stability

section Final

variable {L hL W hW fricke hfricke jf hjf K}
variable (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)

local notation "𝕄" => M L hL W hW fricke hfricke jf hjf K
local notation "𝕊" => Submodule.span ℂ (M L hL W hW fricke hfricke jf hjf K : Set (ℍ → ℂ))

private theorem exists_Efun_ne_zero : ∃ τ : ℍ, E₄ τ ^ a * E₆ τ ^ b ≠ 0 := by
  obtain ⟨τ₄, h₄⟩ := exists_E₄_ne_zero
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero
  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero mdifferentiable_E₆ mdifferentiable_E₄ hmul h₄
  obtain ⟨τ₆, h₆⟩ := exists_E₆_ne_zero
  exact h₆ (by simpa using congrFun this τ₆)

private theorem Φ_injective : Function.Injective (Φ Γ k a b m) := by
  intro f g hfg
  have h : ∀ τ : ℍ, (⇑(f - g) : ℍ → ℂ) τ * (E₄ τ ^ a * E₆ τ ^ b) = 0 := by
    intro τ
    have := congrFun hfg τ
    rw [Φ_apply, Φ_apply, div_left_inj' (pow_ne_zero _ (disc_ne_zero τ))] at this
    simp only [sub_apply, sub_mul, this, sub_self]
  obtain ⟨τ₀, hτ₀⟩ := exists_Efun_ne_zero a b
  have hz := eq_zero_of_mul_eq_zero (f - g).holo' ((mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b))
    (fun τ => by simpa using h τ) (τ₀ := τ₀) (by simpa using hτ₀)
  have : f - g = 0 := DFunLike.ext _ _ fun τ => by simpa using congrFun hz τ
  exact sub_eq_zero.1 this

include L hL W hW hfricke hjf hΓ hk hK in

private theorem main :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Idx N) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (gen fricke jf) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * MvPolynomial.aeval (gen fricke jf) Q τ =
          Δ τ ^ m * MvPolynomial.aeval (gen fricke jf) P τ} = ⊤ := by
  classical
  set S : Set (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) := {f |
      ∃ P Q : MvPolynomial (Idx N) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (gen fricke jf) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * MvPolynomial.aeval (gen fricke jf) Q τ =
          Δ τ ^ m * MvPolynomial.aeval (gen fricke jf) P τ} with hSdef
  rw [eq_top_iff]
  rintro f -

  let V : Submodule ℂ (ℍ → ℂ) := LinearMap.range (Φ Γ k a b m)
  have hVle : V ≤ 𝕊 := by
    rintro _ ⟨g, rfl⟩; exact Φ_mem_span hK Γ hΓ k a b m hk g
  have hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (𝕄 : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V := by
    rintro σ _ ⟨g, rfl⟩
    obtain ⟨cf, hsupp, hsum⟩ := Submodule.mem_span_set.1 (hVle ⟨g, rfl⟩)
    refine ⟨cf.support, cf, hsupp, ?_, ?_⟩
    · rw [← hsum]; rfl
    · have hrep : (Φ Γ k a b m g : ℍ → ℂ) = ∑ i : ↥cf.support, cf i • (i : ℍ → ℂ) := by
        rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort]
      have hT : Tw L hL W hW fricke hfricke jf hjf K hK σ (Φ Γ k a b m g) = ∑ w ∈ cf.support, σ (cf w) • w := by
        rw [hrep, Tw_rep hK σ (fun i : ↥cf.support => cf i) (fun i => (i : ℍ → ℂ)) (fun i => hsupp i.2),
          Finset.sum_coe_sort cf.support (fun w => σ (cf w) • w)]
      obtain ⟨g', hg'⟩ := exists_Φ_eq_Tw hK σ Γ hΓ k a b m hk g
      rw [← hT, ← hg']
      exact ⟨g', rfl⟩
  have G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[K] ℂ, σ c = c) → ∃ x : K, algebraMap K ℂ x = c := by
    intro c hc
    by_contra hnot
    have hc' : c ∉ Set.range (algebraMap K ℂ) := fun ⟨x, hx⟩ => hnot ⟨x, hx⟩
    obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range (F := K) (E := ℂ) hc'
    exact hσ (hc σ)
  have hdesc := WLight.span_inter_rational_of_twist_stable K 𝕄 (M_flat L hL W hW fricke hfricke jf hjf hK)
    V hVle hstab G1 (v := Φ Γ k a b m f) ⟨f, rfl⟩

  have hsub : {y : ℍ → ℂ | y ∈ V ∧ y ∈ 𝕄} ⊆ (Φ Γ k a b m) '' S := by
    rintro y ⟨⟨g, rfl⟩, hyM⟩
    refine ⟨g, ?_, rfl⟩
    obtain ⟨-, P, Q, hQ, hGQ⟩ := hyM
    refine ⟨MvPolynomial.map (algebraMap K ℂ) P, MvPolynomial.map (algebraMap K ℂ) Q, coeff_map_mem P,
      coeff_map_mem Q, hQ, fun τ => ?_⟩
    have h1 := congrFun hGQ τ
    simp only [Pi.mul_apply] at h1
    change g τ * (E₄ τ ^ a * E₆ τ ^ b) * evK fricke jf K Q τ = Δ τ ^ m * evK fricke jf K P τ
    rw [Φ_mul_disc Γ k a b m g τ, ← h1]
    ring
  have h1 : (Φ Γ k a b m f : ℍ → ℂ) ∈ (Submodule.span ℂ S).map (Φ Γ k a b m) := by
    rw [Submodule.map_span]; exact Submodule.span_mono hsub hdesc
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 h1
  rw [← Φ_injective Γ k a b m hgf]
  exact hg

end Final

end Params

end FrickeSpan

end

open Complex Real UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem _root_.CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top
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
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) P τ} = ⊤ :=
  FrickeSpan.main (L := L) (hL := hL) (W := W) (hW := hW) (hfricke := hfricke) (hjf := hjf) hK Γ hΓ k a b m hk

end WLightS11.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top

namespace WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaOneGaloisEven

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
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) := rfl

private theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

private theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

private def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

private def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := rfl

private def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

private abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke N (t v.1)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem gen_id_eq : gen N id = fun o : Idx N => o.elim jf fun v => fricke N v.1 := rfl

private theorem gen_ds_eq (s : ℕ) :
    gen N (ds N s) = fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1] := rfl

section Cyclo

variable [NeZero N]

private theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

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

private def phiOf (σ : (kN N) ≃ₐ[ℚ] (kN N)) : kN N →+* ℂ :=
  (algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom

private theorem phiOf_apply (σ : (kN N) ≃ₐ[ℚ] (kN N)) (z : kN N) : phiOf N σ z = ((σ z : kN N) : ℂ) := rfl

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

private theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

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

private theorem qExpansion_widthN_rat_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N (g := (⇑F : ℍ → ℂ)) F.holo' (SlashInvariantFormClass.periodic_comp_ofComplex F
    one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty F) n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

private def E4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

private def E6sq : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)

private def discForm : ModularForm 𝒮ℒ 12 := (1728 : ℂ)⁻¹ • (E4cube - E6sq)

@[scoped simp] private theorem coe_discForm : (⇑discForm : ℍ → ℂ) = Δ := by
  funext z
  rw [discForm, smul_apply, sub_apply, discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [E4cube, E6sq, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
  ring

private theorem qExpansion_disc_rat_one (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑discForm : ℍ → ℂ)).coeff n = (r : ℂ) := by
  obtain ⟨p4, hp4⟩ := exists_map_of_rat qExpansion_E₄_rat
  obtain ⟨p6, hp6⟩ := exists_map_of_rat qExpansion_E₆_rat
  refine rat_of_exists_map ⟨PowerSeries.C (1728 : ℚ)⁻¹ * (p4 ^ 3 - p6 ^ 2), ?_⟩ n
  rw [discForm, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  simp only [E4cube, E6sq, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub, map_pow, map_pow, hp4, hp6]
  congr 1
  simp

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [← coe_discForm]
  exact qExpansion_widthN_rat_of_levelOne N _ qExpansion_disc_rat_one n

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

private theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
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

end Width

section Group

variable (N : ℕ)

local notation "Δ" => ModularForm.discriminant

private def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

private def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN N γ)

private theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  Subgroup.Normal.conj_mem (Gamma_normal N) g hg α

private theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

variable {N}

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

end Group

section Fricke

variable (N : ℕ) [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke N v) := by
  obtain ⟨-, -, h3, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h3 v hv

private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  intro τ
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => E₄ τ ^ 3) τ := (E₄.holo' τ).pow 3
  exact h1.div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

variable {N}

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map (algebraMap (kN N) ℂ) R)

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

private theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev id R ∈ Algebra.adjoin ℂ (genSet N) :=
  aeval_mem_adjoin _

private theorem adjoin_isDomain {a b : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ (genSet N))
    (hb : b ∈ Algebra.adjoin ℂ (genSet N)) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N tauPair tauPair_spec (WW N) (WW_spec N)
    (fricke N) (fricke_spec N) jf jf_spec
  exact h6 a b ha hb hab

private theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev id (Q i) ≠ 0) : ev id (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev id (Q a) * ev (N := N) id (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain (ev_mem_adjoin _) (ev_mem_adjoin _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

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
    ∃ R : MvPolynomial (Idx N) (kN N), ev id R = x := by
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
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev id Q ≠ 0 ∧ G * ev id Q = ev id P := by
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
  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev id R = Pi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev id R = Qi i := fun i =>
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
  · have hev_prod : ∀ (s : Finset (Fin n)), ev id (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
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

end Fricke

section Companion

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private theorem exists_abm {k : ℤ} (hk : Even k) :
    ∃ a b m : ℕ, k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ) := by
  obtain ⟨r, rfl⟩ := hk
  rcases le_or_gt 0 r with hr | hr
  · refine ⟨r.toNat, r.toNat, r.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hr]; ring
  · refine ⟨2 * (-r).toNat, (-r).toNat, (-r).toNat, ?_⟩
    have h : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [h]; ring

variable (a b : ℕ)

private def Ek : ModularForm 𝒮ℒ ((a : ℤ) * 4 + (b : ℤ) * 6) := (E₄.pow a).mul (E₆.pow b)

private theorem Ek_apply (τ : ℍ) : Ek a b τ = E₄ τ ^ a * E₆ τ ^ b := by
  simp [Ek, coe_mul, coe_pow]

private theorem qExpansion_Ek_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (⇑(Ek a b) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  obtain ⟨p4, hp4⟩ := exists_map_of_rat qExpansion_E₄_rat
  obtain ⟨p6, hp6⟩ := exists_map_of_rat qExpansion_E₆_rat
  refine rat_of_exists_map ⟨p4 ^ a * p6 ^ b, ?_⟩ n
  rw [Ek, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_mul, map_pow, map_pow, hp4, hp6]

private theorem exists_Ek_ne_zero : ∃ τ : ℍ, E₄ τ ^ a * E₆ τ ^ b ≠ 0 := by
  have h4 : ∃ τ : ℍ, E₄ τ ≠ 0 := by
    by_contra h
    push Not at h
    have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
    exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this
  have h6 : ∃ τ : ℍ, E₆ τ ≠ 0 := by
    by_contra h
    push Not at h
    have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
    exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this
  obtain ⟨τ₄, hτ₄⟩ := h4
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero
  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero E₆.holo' E₄.holo' hmul hτ₄
  obtain ⟨τ₆, hτ₆⟩ := h6
  exact hτ₆ (by simpa using congrFun this τ₆)

variable {a b} (k : ℤ) (m : ℕ)

private def Φ (f : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m

private theorem Φ_apply (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) : Φ (a := a) (b := b) k m f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

private theorem Φ_mul_disc (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ (a := a) (b := b) k m f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (discriminant_ne_zero τ))]

private theorem Φ_mul_disc_fun (f : CuspForm (Γ₁ℝ N) k) :
    Φ (a := a) (b := b) k m f * Δ ^ m = ⇑f * ⇑(Ek a b) := by
  funext τ; simp only [Pi.mul_apply, Pi.pow_apply, ← Φ_mul_disc, Ek_apply]

private theorem mdifferentiable_Φ (f : CuspForm (Γ₁ℝ N) k) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ (a := a) (b := b) k m f) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * (E₄ τ ^ a * E₆ τ ^ b)) :=
    f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))
  intro τ
  exact (h1 τ).div ((mdifferentiable_disc τ).pow m) (pow_ne_zero _ (discriminant_ne_zero τ))

variable (hk : k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ))
include hk

private theorem crit_Φ (f : CuspForm (Γ₁ℝ N) k) :
    (∀ A : SL(2, ℤ), IsZeroAtImInfty ((Φ (a := a) (b := b) k m f ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, Φ (a := a) (b := b) k m f (γ • τ) = Φ (a := a) (b := b) k m f τ := by
  obtain ⟨-, -, h₃, h₄⟩ := (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk
    (Φ (a := a) (b := b) k m f) (mdifferentiable_Φ k m f)).1 ⟨f, Φ_mul_disc k m f⟩
  exact ⟨h₃, h₄⟩

omit hk in

private theorem ratAt_Φ (f : CuspForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ n : ℕ, (qExpansion 1 (⇑f)).coeff n = (c n : ℂ)) :
    RatAt N (kN N) m (Φ (a := a) (b := b) k m f) := by
  have hperf : Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N)
  have hperE : Periodic ((⇑(Ek a b) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (Ek a b) one_mem_strictPeriods_SL
  have hbdf : IsBoundedAtImInfty (⇑f : ℍ → ℂ) := ModularFormClass.bdd_at_infty f
  have hbdE : IsBoundedAtImInfty (⇑(Ek a b) : ℍ → ℂ) := ModularFormClass.bdd_at_infty (Ek a b)
  refine ⟨mdifferentiable_Φ k m f, ?_, ?_, ?_⟩
  · rw [Φ_mul_disc_fun]
    exact periodic_mul (periodic_ofComplex_natCast hperf N) (periodic_ofComplex_natCast hperE N)
  · rw [Φ_mul_disc_fun]; exact hbdf.mul hbdE
  · intro n
    rw [Φ_mul_disc_fun, qExpansion_mul (analyticAt_cuspFunction_zero (natCast_pos N)
      (periodic_ofComplex_natCast hperf N) f.holo' hbdf) (analyticAt_cuspFunction_zero (natCast_pos N)
      (periodic_ofComplex_natCast hperE N) (Ek a b).holo' hbdE), PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem ?_ ?_
    · rw [qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo' hperf hbdf]
      split_ifs
      · rw [hf]; exact SetLike.coe_mem _
      · exact zero_mem _
    · obtain ⟨r, hr⟩ := qExpansion_widthN_rat_of_levelOne N (Ek a b) (qExpansion_Ek_rat a b) ij.2
      rw [hr]; exact ratCast_mem r

end Companion

section Main

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem exists_multSeries (σ : (kN N) ≃ₐ[ℚ] (kN N)) (a b d : ℕ) :
    ∃ e : PowerSeries (kN N),
      e.map (algebraMap (kN N) ℂ) = qExpansion N (⇑(Ek a b) * Δ ^ d) ∧
      e.map (phiOf N σ) = qExpansion N (⇑(Ek a b) * Δ ^ d) ∧
      qExpansion N (⇑(Ek a b) * Δ ^ d) ≠ 0 := by

  let F : ModularForm 𝒮ℒ (((a : ℤ) * 4 + (b : ℤ) * 6) + (d : ℤ) * 12) := (Ek a b).mul (discForm.pow d)
  have hF : (⇑F : ℍ → ℂ) = ⇑(Ek a b) * Δ ^ d := by
    simp only [F, coe_mul, coe_pow, coe_discForm]
  have hrat1 : ∀ n, ∃ r : ℚ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) := by
    obtain ⟨p, hp⟩ := exists_map_of_rat (qExpansion_Ek_rat a b)
    obtain ⟨q, hq⟩ := exists_map_of_rat qExpansion_disc_rat_one
    refine rat_of_exists_map ⟨p * q ^ d, ?_⟩
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_mul, map_pow, hp, hq]
  have hratN : ∀ n, ∃ r : ℚ, (qExpansion N (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) :=
    qExpansion_widthN_rat_of_levelOne N F hrat1
  choose r hr using hratN
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem (r n)⟩, ?_, ?_, ?_⟩
  · rw [← hF]; ext n; simp [hr n]
  · rw [← hF]; ext n
    rw [PowerSeries.coeff_map, hr n, PowerSeries.coeff_mk, phiOf_ratCast N σ (r n) _ rfl]
  · rw [← hF]
    have hperN : Periodic ((⇑F : ℍ → ℂ) ∘ ofComplex) N :=
      periodic_ofComplex_natCast (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) N
    rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) hperN (f := (⇑F : ℍ → ℂ)) F.holo'
      (ModularFormClass.bdd_at_infty F)]
    intro h0
    obtain ⟨τ, hτ⟩ := exists_Ek_ne_zero a b
    have := congrFun h0 τ
    rw [hF] at this
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hτ (by rw [← Ek_apply]; exact h)
    · exact pow_ne_zero _ (discriminant_ne_zero τ) h

private theorem main (k : ℤ) (hk : Even k) (σ : (kN N) ≃ₐ[ℚ] (kN N)) (f : CuspForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n = (c n : ℂ)) :
    ∃ f' : CuspForm (Γ₁ℝ N) k, ∀ n : ℕ, ModularFormClass.qCoeff f' n = ((σ (c n) : kN N) : ℂ) := by
  classical
  have hf' : ∀ n : ℕ, (qExpansion 1 (⇑f)).coeff n = (c n : ℂ) := hf
  obtain ⟨a, b, m, habm⟩ := exists_abm hk

  set G : ℍ → ℂ := Φ (a := a) (b := b) k m f with hGdef
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := mdifferentiable_Φ k m f
  obtain ⟨h₃, h₄⟩ := crit_Φ k m habm f
  have hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ :=
    fun g hg τ => h₄ g (Gamma_le_Gamma1 N hg) τ
  have hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m) := fun α => (h₃ α).isBoundedAtImInfty
  have hrat : RatAt N (kN N) m G := ratAt_Φ k m f c hf'

  obtain ⟨P, Q, hQ0, hGQ⟩ := descent hG hinv hpb hrat

  obtain ⟨s, hs, hσ⟩ := exists_pow_of_aut N σ
  have hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      phiOf N σ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s :=
    fun z hz => phiOf_zeta N σ hσ z hz

  have hQ0' : MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1)
      (Q.map (algebraMap (kN N) ℂ)) ≠ 0 := hQ0
  have hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
      MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1) (Q.map (algebraMap (kN N) ℂ)) τ =
      Δ τ ^ m * MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1)
        (P.map (algebraMap (kN N) ℂ)) τ := by
    intro τ
    have h1 := congrFun hGQ τ
    simp only [Pi.mul_apply] at h1
    change f τ * (E₄ τ ^ a * E₆ τ ^ b) * ev id Q τ = Δ τ ^ m * ev id P τ
    rw [Φ_mul_disc k m f τ, ← h1]
    ring

  obtain ⟨f', hQ'0, hid'⟩ := CuspForm.exists_gamma1_frickeRational_sigmaTransport N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs (phiOf N σ) hφ k a b m
    habm f P Q hQ0' hid

  obtain ⟨-, G', hG', hG'Q, m₁, hTdata⟩ :=
    ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N tauPair tauPair_spec (WW N)
      (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs (phiOf N σ) hφ G hG P Q hQ0'
      hGQ
  obtain ⟨⟨hper, hbd, hmem⟩, ⟨hper', hbd', hmem'⟩, hcoef⟩ := hTdata (m₁ + m) (Nat.le_add_right _ _)

  set Q' : ℍ → ℂ := MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1])
    (Q.map (phiOf N σ)) with hQ'def
  set P' : ℍ → ℂ := MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1])
    (P.map (phiOf N σ)) with hP'def
  have hQ'hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q' := by
    rw [hQ'def]
    induction (Q.map (phiOf N σ)) using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p o hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        refine hp.mul ?_
        cases o with
        | none => exact mdifferentiable_jf
        | some v =>
            refine mdifferentiable_fricke N ?_
            intro h
            apply v.2
            have h0 : v.1 0 = 0 := by simpa using congrFun h 0
            have h1 : (s : ZMod N) * v.1 1 = 0 := by simpa using congrFun h 1
            have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
            have h1' : v.1 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
            funext i; fin_cases i <;> simp [h0, h1']
  have hG₁Q : Φ (a := a) (b := b) k m f' * Q' = P' := by
    funext τ
    have h1 := hid' τ
    simp only [Pi.mul_apply]
    apply mul_left_cancel₀ (pow_ne_zero m (discriminant_ne_zero τ))
    rw [← h1, Φ_mul_disc k m f' τ]
    ring
  have hG₁eq : Φ (a := a) (b := b) k m f' = G' := by
    have hdiff : ∀ τ : ℍ, (Φ (a := a) (b := b) k m f' - G') τ * Q' τ = 0 := by
      intro τ
      have e1 := congrFun hG₁Q τ
      have e2 := congrFun hG'Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, Q' τ₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hQ'0 (funext hall)
    have := eq_zero_of_mul_eq_zero ((mdifferentiable_Φ k m f').sub hG') hQ'hol hdiff hτ₀
    exact sub_eq_zero.1 this

  have hRGM : RatAt N (kN N) (m₁ + m) G := ⟨hG, hper, hbd, hmem⟩
  have hRG'M : RatAt N (kN N) (m₁ + m) G' := ⟨hG', hper', hbd', hmem'⟩
  obtain ⟨p₁, hpι⟩ := hRGM.exists_map
  have hpφ : p₁.map (phiOf N σ) = qExpansion N (G' * Δ ^ (m₁ + m)) := by
    ext n
    rw [PowerSeries.coeff_map]
    symm
    apply hcoef
    rw [← hpι, PowerSeries.coeff_map]
    rfl

  have hsplit : ∀ (g : CuspForm (Γ₁ℝ N) k), Φ (a := a) (b := b) k m g * Δ ^ (m₁ + m) =
      ⇑g * (⇑(Ek a b) * Δ ^ m₁) := by
    intro g
    rw [add_comm, pow_add, ← mul_assoc, Φ_mul_disc_fun]; ring
  obtain ⟨e, heι, heφ, he0⟩ := exists_multSeries (N := N) σ a b m₁

  have hperf : ∀ g : CuspForm (Γ₁ℝ N) k, Periodic ((⇑g : ℍ → ℂ) ∘ ofComplex) 1 := fun g =>
    SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods N)
  have hanf : ∀ g : CuspForm (Γ₁ℝ N) k, AnalyticAt ℂ (cuspFunction N (⇑g)) 0 := fun g =>
    analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast (hperf g) N) g.holo'
      (ModularFormClass.bdd_at_infty g)
  let F : ModularForm 𝒮ℒ (((a : ℤ) * 4 + (b : ℤ) * 6) + (m₁ : ℤ) * 12) := (Ek a b).mul (discForm.pow m₁)
  have hFcoe : (⇑F : ℍ → ℂ) = ⇑(Ek a b) * Δ ^ m₁ := by
    simp only [F, coe_mul, coe_pow, coe_discForm]
  have hanE : AnalyticAt ℂ (cuspFunction N (⇑(Ek a b) * Δ ^ m₁)) 0 := by
    rw [← hFcoe]
    exact analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast
      (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) N) (f := (⇑F : ℍ → ℂ))
      F.holo' (ModularFormClass.bdd_at_infty F)

  set Sf : PowerSeries (kN N) := PowerSeries.mk fun n => if (N : ℕ) ∣ n then c (n / N) else 0 with hSf
  have hSfι : Sf.map (algebraMap (kN N) ℂ) = qExpansion N (⇑f) := by
    ext n
    rw [PowerSeries.coeff_map, hSf, PowerSeries.coeff_mk,
      qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo' (hperf f) (ModularFormClass.bdd_at_infty f)]
    split_ifs with h
    · rw [hf']; rfl
    · simp

  have hprod : Sf * e = p₁ := by
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [map_mul, hSfι, heι, hpι, hsplit f, qExpansion_mul (hanf f) hanE]

  have hf'exp : qExpansion N (⇑f') = Sf.map (phiOf N σ) := by
    have h1 : qExpansion N (⇑f') * qExpansion N (⇑(Ek a b) * Δ ^ m₁) =
        Sf.map (phiOf N σ) * qExpansion N (⇑(Ek a b) * Δ ^ m₁) := by
      rw [← qExpansion_mul (hanf f') hanE, ← hsplit f', hG₁eq, ← hpφ, ← heφ, ← map_mul, hprod]
    exact mul_right_cancel₀ he0 h1
  refine ⟨f', fun n => ?_⟩
  have hw := qExpansion_coeff_widthN N (g := (⇑f' : ℍ → ℂ)) f'.holo' (hperf f')
    (ModularFormClass.bdd_at_infty f') (N * n)
  rw [ite_eq_left (dvd_mul_right N n), Nat.mul_div_cancel_left _ (NeZero.pos N)] at hw
  change (qExpansion 1 (⇑f')).coeff n = _
  rw [← hw, hf'exp, PowerSeries.coeff_map, hSf, PowerSeries.coeff_mk,
    ite_eq_left (dvd_mul_right N n), Nat.mul_div_cancel_left _ (NeZero.pos N), phiOf_apply]

end Main

end GammaOneGaloisEven

end

theorem _root_.CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  subst hK
  exact GammaOneGaloisEven.main (N := N) k hk σ f c hf

end WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even

namespace WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneGaloisAllWeights

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {N : ℕ} {k : ℤ}

private theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private theorem coe_eq_of_qExpansion_eq [NeZero N] {F G : Type*} [FunLike F ℍ ℂ] [FunLike G ℍ ℂ] {a b : ℤ}
    [ModularFormClass F (Γ₁ℝ N) a] [ModularFormClass G (Γ₁ℝ N) b] (f : F) (g : G)
    (h : qExpansion 1 (⇑f) = qExpansion 1 (⇑g)) : (⇑f : ℍ → ℂ) = ⇑g := by
  funext τ
  have hf := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  have hg := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods N))
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) τ
  rw [h] at hf
  exact hf.unique hg

private theorem coe_modularForm (f : CuspForm (Γ₁ℝ N) k) :
    (⇑(ModularFormClass.modularForm f : ModularForm (Γ₁ℝ N) k) : ℍ → ℂ) = ⇑f := rfl

private theorem coe_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    (⇑(f.mulModularForm g) : ℍ → ℂ) = ⇑f * ⇑g := rfl

private theorem qExpansion_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    qExpansion 1 (⇑(f.mulModularForm g)) = qExpansion 1 (⇑f) * qExpansion 1 (⇑g) := by
  rw [coe_mulModularForm]
  exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N) f g

end QExp

section Transport

variable (K : IntermediateField ℚ ℂ) (N : ℕ) (k : ℤ)

private abbrev ι : ↥K →+* ℂ := algebraMap ↥K ℂ

private def Stab : Prop :=
  ∀ (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (Γ₁ℝ N) k) (p : PowerSeries ↥K),
    qExpansion 1 (⇑f) = p.map (ι K) →
      ∃ f' : CuspForm (Γ₁ℝ N) k, qExpansion 1 (⇑f') = (p.map (σ : ↥K →+* ↥K)).map (ι K)

variable {K N k}

private theorem stab_of_forall_eq_zero (h : ∀ f : CuspForm (Γ₁ℝ N) k, f = 0) : Stab K N k := by
  intro σ f p hp
  refine ⟨0, ?_⟩
  have hp0 : p = 0 := by
    apply PowerSeries.map_injective (ι K) (algebraMap ↥K ℂ).injective
    rw [← hp, h f, FunLike.coe_zero, qExpansion_zero, map_zero]
  rw [FunLike.coe_zero, qExpansion_zero, hp0, map_zero, map_zero]

private theorem stab_of_even [NeZero N]
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (hk : Even k) : Stab K N k := by
  intro σ f p hp
  obtain ⟨f', hf'⟩ := CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even N k hk K hK σ f
    (fun m => PowerSeries.coeff m p) (fun m => by
      show PowerSeries.coeff m (qExpansion 1 (⇑f)) = _
      rw [hp, PowerSeries.coeff_map]; rfl)
  refine ⟨f', ?_⟩
  ext m
  have := hf' m
  simp only [ModularFormClass.qCoeff] at this
  rw [this, PowerSeries.coeff_map, PowerSeries.coeff_map, RingHom.coe_coe]
  rfl

end Transport

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.1 (hv τ₀)).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (v ∘ ofComplex) z ≠ 0 := hvc.eventually_ne hv0'
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hne] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hana : AnalyticOnNhd ℂ (u ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd isOpen_upperHalfPlaneSet
  have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  have := hEq τ.im_pos
  simpa [Function.comp, ofComplex_apply] using this

private theorem isZeroAtImInfty_of_mul_self {g : ℍ → ℂ} (h : IsZeroAtImInfty (g * g)) :
    IsZeroAtImInfty g := by
  rw [UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter] at h ⊢
  have h₁ : Tendsto (fun τ => ‖g τ‖ * ‖g τ‖) atImInfty (𝓝 0) := by
    have := tendsto_zero_iff_norm_tendsto_zero.mp h
    simpa [norm_mul] using this
  have h₂ : Tendsto (fun τ => Real.sqrt (‖g τ‖ * ‖g τ‖)) atImInfty (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h₁
    simpa [Function.comp_def] using this
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (h₂.congr fun τ => ?_)
  exact Real.sqrt_mul_self (norm_nonneg _)

section OddStep

variable (K : IntermediateField ℚ ℂ) {N : ℕ} {k : ℤ} [NeZero N]

private theorem stab_of_anchor {w : ℤ} (E : ModularForm (Γ₁ℝ N) w) (hE : E ≠ 0)
    (e : PowerSeries ℤ) (hEe : ModularCurve.IsIntegralQExp (⇑E) e)
    (h1 : Stab K N (k + w)) (h2 : Stab K N (k + k)) : Stab K N k := by
  classical
  intro σ f p hp

  set eK : PowerSeries ↥K := e.map (Int.castRingHom ↥K) with heK
  have hEe' : e.map (Int.castRingHom ℂ) = qExpansion 1 (⇑E) := hEe
  have heKι : eK.map (ι K) = qExpansion 1 (⇑E) := by
    rw [← hEe']
    ext n
    simp [heK, PowerSeries.coeff_map]
  have heKσ : eK.map (σ : ↥K →+* ↥K) = eK := by
    ext n
    simp [heK, PowerSeries.coeff_map]
  set φh : PowerSeries ℂ := (p.map (σ : ↥K →+* ↥K)).map (ι K) with hφh

  have hfE : qExpansion 1 (⇑(f.mulModularForm E)) = (p * eK).map (ι K) := by
    rw [qExpansion_mulModularForm, map_mul, hp, heKι]
  have hff : qExpansion 1 (⇑(f.mulModularForm (ModularFormClass.modularForm f))) =
      (p * p).map (ι K) := by
    rw [qExpansion_mulModularForm, coe_modularForm, map_mul, hp]
  obtain ⟨G, hG⟩ := h1 σ (f.mulModularForm E) (p * eK) hfE
  obtain ⟨H, hH⟩ := h2 σ (f.mulModularForm (ModularFormClass.modularForm f)) (p * p) hff
  have hQE : qExpansion 1 (⇑E) ≠ 0 := fun h =>
    hE ((ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N) E).mp h)
  have hG' : qExpansion 1 (⇑G) = φh * qExpansion 1 (⇑E) := by
    rw [hG, map_mul, map_mul, heKσ, heKι]
  have hH' : qExpansion 1 (⇑H) = φh * φh := by
    rw [hH, map_mul, map_mul]

  have hval : ∀ τ : ℍ, G τ * G τ = H τ * E τ * E τ := by
    have hq : qExpansion 1 (⇑(G.mulModularForm (ModularFormClass.modularForm G))) =
        qExpansion 1 (⇑((H.mulModularForm E).mulModularForm E)) := by
      rw [qExpansion_mulModularForm, qExpansion_mulModularForm, qExpansion_mulModularForm,
        coe_modularForm, hG', hH']
      ring
    have hfun := coe_eq_of_qExpansion_eq _ _ hq
    intro τ
    have hτ := congrFun hfun τ
    simpa [coe_mulModularForm, coe_modularForm, mul_assoc] using hτ

  have hEfun : (⇑E : ℍ → ℂ) ≠ 0 := by
    intro h0
    exact hE ((FunLike.coe_zero_iff E).mp h0)
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, E τ₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hEfun (funext hcon)
  have hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑E) := ModularFormClass.holo E
  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑G) := ModularFormClass.holo G
  have hHhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑H) := ModularFormClass.holo H
  let cc : ℕ → ℍ → ℂ := fun i => if i = 0 then -⇑H else 0
  have hcc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cc i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [cc, hi] using hHhol.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [cc, hi] at h__af ⊢
      exact h__af
  have hrel : (⇑G) ^ 2 + ∑ i ∈ Finset.range 2, cc i * (⇑E) ^ (2 - i) * (⇑G) ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, cc, ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, ite_false, Pi.neg_apply]
    rw [pow_two, hval τ]; ring
  obtain ⟨φ, hφhol, hφE⟩ := WLight.exists_mdifferentiable_div_of_monicRel hGhol hEhol hEfun hcc hrel
  have hφE' : ∀ τ : ℍ, φ τ * E τ = G τ := fun τ => congrFun hφE τ

  have hφsq : ∀ τ : ℍ, φ τ * φ τ = H τ := by
    have hzero : ∀ τ : ℍ, (φ τ * φ τ - H τ) * (E τ * E τ) = 0 := by
      intro τ
      have h := hval τ
      rw [← hφE' τ] at h
      linear_combination h
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => φ τ * φ τ - H τ) := (hφhol.mul hφhol).sub hHhol
    have hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => E τ * E τ) := hEhol.mul hEhol
    have := eq_zero_of_mul_eq_zero hdiff hv hzero (τ₀ := τ₀) (mul_ne_zero hτ₀ hτ₀)
    intro τ
    exact sub_eq_zero.mp (congrFun this τ)

  have hinv : ∀ γ ∈ Gamma1 N, φ ∣[k] γ = φ := by
    intro γ hγ
    have hGγ : (⇑G : ℍ → ℂ) ∣[k + w] γ = ⇑G := by
      have := SlashInvariantForm.slash_action_eqn G (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hEγ : (⇑E : ℍ → ℂ) ∣[w] γ = ⇑E := by
      have := SlashInvariantForm.slash_action_eqn E (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hprod : (φ ∣[k] γ) * ⇑E = φ * ⇑E := by
      have h := ModularForm.mul_slash_SL2 k w γ φ ⇑E
      rw [hEγ, hφE, hGγ] at h
      rw [hφE]; exact h.symm
    have hzero : ∀ τ : ℍ, ((φ ∣[k] γ) τ - φ τ) * E τ = 0 := by
      intro τ
      have := congrFun hprod τ
      simp only [Pi.mul_apply] at this
      linear_combination this
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (φ ∣[k] γ) τ - φ τ) := by
      have h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hφhol.slash k _
      exact h₁.sub hφhol
    have := eq_zero_of_mul_eq_zero hdiff hEhol hzero hτ₀
    funext τ
    exact sub_eq_zero.mp (by simpa using congrFun this τ)

  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (φ ∣[k] A) := by
    intro A
    apply isZeroAtImInfty_of_mul_self
    have hφφ : φ * φ = ⇑H := funext fun τ => hφsq τ
    have h := ModularForm.mul_slash_SL2 k k A φ φ
    rw [hφφ] at h
    rw [← h]
    exact CuspFormClass.zero_at_infty_slash H A

  let φC : CuspForm (Γ₁ℝ N) k :=
    { toFun := φ
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hφhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  refine ⟨φC, ?_⟩
  have hprod : qExpansion 1 (⇑φC) * qExpansion 1 (⇑E) = φh * qExpansion 1 (⇑E) := by
    rw [← hG', ← qExpansion_mulModularForm, coe_mulModularForm]
    exact congrArg (qExpansion 1) hφE
  exact mul_right_cancel₀ hQE hprod

end OddStep

section Assembly

variable (N : ℕ)

private def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

private theorem anchor [NeZero N] (h10 : (1 : ZMod N) ≠ 0) (h11 : (1 : ZMod N) ≠ -1) :
    ∃ (E : ModularForm (Γ₁ℝ N) ((3 : ℕ) : ℤ)) (e : PowerSeries ℤ), E ≠ 0 ∧
      ModularCurve.IsIntegralQExp (⇑E) e := by
  classical
  obtain ⟨G, hG, -⟩ := ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq N 3 le_rfl
  have hint := hG 1 h10
  refine ⟨G 1, _, ?_, hint⟩
  rw [ModularCurve.IsIntegralQExp] at hint
  intro h0
  have h1 := congrArg (PowerSeries.coeff 1) hint
  rw [h0, FunLike.coe_zero, qExpansion_zero, map_zero, PowerSeries.coeff_map,
    PowerSeries.coeff_mk] at h1
  simp [Nat.divisors_one, Finset.filter_singleton, h11] at h1

private theorem neg_one_mem_Gamma1 (hN : N ∣ 2) : (-1 : SL(2, ℤ)) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h2 : ((2 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff 2 N).mpr hN
  have hneg : ((-1 : ℤ) : ZMod N) = 1 := by
    have h11 : (1 : ZMod N) + 1 = 0 := by simpa [one_add_one_eq_two] using h2
    push_cast
    linear_combination -h11
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_neg, hneg]

private theorem neg_one_mem_Gamma1GL (hN : N ∣ 2) : (-1 : GL (Fin 2) ℝ) ∈ Γ₁ℝ N := by
  refine Subgroup.mem_map.mpr ⟨-1, neg_one_mem_Gamma1 N hN, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> simp [Units.val_neg]

private theorem stab_all [NeZero N] (k : ℤ) : Stab (kN N) N k := by
  rcases Int.even_or_odd k with hk | hk
  · exact stab_of_even rfl hk
  by_cases hN : N ∣ 2
  ·
    refine stab_of_forall_eq_zero fun f => ?_
    have h := ModularForm.eq_zero_of_neg_one_mem (neg_one_mem_Gamma1GL N hN) hk
      (ModularFormClass.modularForm f)
    have hcoe : (⇑f : ℍ → ℂ) = 0 := by
      rw [← coe_modularForm f, h, FunLike.coe_zero]
    exact DFunLike.ext' (by rw [hcoe, FunLike.coe_zero])
  ·
    have h10 : (1 : ZMod N) ≠ 0 := by
      intro h
      have hN1 : N ∣ 1 := (ZMod.natCast_eq_zero_iff 1 N).mp (by simpa using h)
      exact hN ((Nat.dvd_one.mp hN1).symm ▸ one_dvd 2)
    have h11 : (1 : ZMod N) ≠ -1 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_two, ← one_add_one_eq_two]
        nth_rewrite 2 [h]
        exact add_neg_cancel 1
      exact hN ((ZMod.natCast_eq_zero_iff 2 N).mp h2)
    obtain ⟨E, e, hE0, hEe⟩ := anchor N h10 h11
    have hk3 : Even (k + ((3 : ℕ) : ℤ)) := by
      push_cast
      exact hk.add_odd ⟨1, by norm_num⟩
    exact stab_of_anchor (kN N) E hE0 e hEe (stab_of_even rfl hk3) (stab_of_even rfl ⟨k, rfl⟩)

private theorem main [NeZero N] (k : ℤ) (σ : ↥(kN N) ≃ₐ[ℚ] ↥(kN N)) (f : CuspForm (Γ₁ℝ N) k)
    (c : ℕ → ↥(kN N)) (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (Γ₁ℝ N) k, ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  have hp : qExpansion 1 (⇑f) = (PowerSeries.mk c).map (ι (kN N)) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact hf m
  obtain ⟨f', hf'⟩ := stab_all N k σ f (PowerSeries.mk c) hp
  refine ⟨f', fun m => ?_⟩
  show PowerSeries.coeff m (qExpansion 1 (⇑f')) = _
  rw [hf', PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk, RingHom.coe_coe]
  rfl

end Assembly

end GammaOneGaloisAllWeights

end

theorem _root_.CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply (N : ℕ) [NeZero N] (k : ℤ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  subst hK
  exact GammaOneGaloisAllWeights.main N k σ f c hf

end WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply

