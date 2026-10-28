/-
  Consumer specification for **SET MC-5** (M4 + M7): the Siegel unit and the semisimple descent.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed across modules.  It is a deliverable
  measure, not a proof obligation, and it is **not part of any library** (`lake build` does not see
  `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveMC5Consumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [siegel]    ZONE A — the `SL(2, ℤ)`-multiplier of `siegelFun` is a non-zero root of unity: the
                row's `μ` fed to `pow_ne_zero`/`zero_pow`, and the transformation law specialised.
    [diff]      ZONE B — the differentiability pair consumed as `DifferentiableAt` at a point of the
                upper half plane (through `DifferentiableOn.differentiableAt` and the openness of
                `{0 < im}`), then fed to `UpperHalfPlane`'s coercion.
    [eisenstein] ZONE C — the weight-3 Eisenstein form's existential unpacked into its five clauses;
                the constant term's non-vanishing and the integrality of its `N^a`-multiple.
    [descent]   ZONE D — the semisimple descent's `ρ₀` compared with `ρ` through the trace and
                determinant conjuncts, and its invariant-subspace complement applied.
-/

import FLTForHuman.ModularCurve.SiegelUnit.Basic
import FLTForHuman.ModularCurve.SiegelUnit.Eisenstein
import FLTForHuman.ModularCurve.ResidualDescent

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace MC5Consumer

/-! ## Zone A — `[siegel]` the multiplier is a non-zero twelfth root of unity -/

theorem exists_mu_ne_zero_and_law (N : ℕ) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      ModularCurve.siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * ModularCurve.siegelFun N
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) := by
  obtain ⟨μ, hμ, hlaw⟩ := ModularCurve.siegelFun_specialLinearGroup_smul N α
  refine ⟨μ, ?_, hlaw⟩
  intro hzero
  rw [hzero, zero_pow (by norm_num : 12 ≠ 0)] at hμ
  exact zero_ne_one hμ

/-- The law at the identity matrix: the multiplier is `1`. -/
theorem siegelFun_one_smul (N : ℕ) (r s : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N r s (((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ) =
      ModularCurve.siegelFun N r s (τ : ℂ) := by
  obtain ⟨μ, hμ, hlaw⟩ := exists_mu_ne_zero_and_law N 1
  have h := hlaw r s τ
  simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, mul_one, mul_zero, add_zero,
    zero_add, one_smul] using h

/-! ## Zone B — `[diff]` differentiability at a point of the upper half plane -/

theorem differentiableAt_siegelFun (N : ℕ) (r s : ℤ) (τ : UpperHalfPlane) :
    DifferentiableAt ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) (τ : ℂ) := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : (τ : ℂ) ∈ {z : ℂ | 0 < z.im} := τ.2
  exact (ModularCurve.SiegelUnit.differentiableOn_siegelFun N r s).1.differentiableAt
    (hopen.mem_nhds hmem)

/-! ## Zone C — `[eisenstein]` the weight-3 Eisenstein form, unpacked -/

theorem eisenstein_coeff_zero_ne_zero {N : ℕ} (hN : 3 ≤ N) :
    ∃ (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 3) (a : ℕ),
      (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) := by
  obtain ⟨E, a, -, h0, hinv, -⟩ :=
    ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion N hN
  exact ⟨E, a, h0, hinv⟩

/-! ## Zone D — `[descent]` the descended representation keeps the trace -/

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem exists_rep_k_same_trace (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) =
        LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) := by
  obtain ⟨V₀, hAdd, hMod, ρ₀, -, -, -, htr₀, hdet₀, -⟩ :=
    ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite M p Ω k ι V ρ
      hp hV hfin hirr htr hdet hcyc
  exact ⟨V₀, hAdd, hMod, ρ₀, htr₀, hdet₀⟩

end MC5Consumer
