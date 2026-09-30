/-
  Shared Galois-representation prelude.

  FLT repeats the finiteness of the image of a Galois representation that factors
  through a finite level in every `S_` file that needs it. The block is
  byte-identical in its two copies and is written once here, under
  `GaloisRep`:

  - `finite_range_of_factorsThroughFiniteLevel`, from
    `P2M/Sol/S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean:21`
    (also `S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean:18`),
    pinned `aa2d8b3`.

  It assumes `GaloisFactorsThroughFiniteLevel` from
  `FLTForHuman/GaloisRep/Defs/Residual.lean`.
-/
import FLTForHuman.GaloisRep.Defs.Residual

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GaloisRep

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem finite_range_of_factorsThroughFiniteLevel {M : Type} [Group M] (ρ : Γℚ →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite (MonoidHom.range ρ) := by
  classical
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  let F : Γℚ → (L →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => σ.toAlgHom.comp L.val
  have hF : ∀ σ τ : Γℚ, F σ = F τ → ρ σ = ρ τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hx' := congrArg (fun φ : L →ₐ[ℚ] AlgebraicClosure ℚ => φ ⟨x, hx⟩) h
      simp only [F, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom] at hx'
      change σ x = τ x at hx'
      rw [AlgEquiv.mul_apply, hx']
      exact τ.symm_apply_apply x
    have h1 : ρ (τ⁻¹ * σ) = 1 := hker _ hfix
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  let g : (L →ₐ[ℚ] AlgebraicClosure ℚ) → M := fun v =>
    if h : ∃ σ : Γℚ, F σ = v then ρ h.choose else 1
  have hsub : (MonoidHom.range ρ : Set M) ⊆ Set.range g := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨F σ, ?_⟩
    have h : ∃ σ' : Γℚ, F σ' = F σ := ⟨σ, rfl⟩
    simp only [g, dite_eq_left h]
    exact hF _ _ h.choose_spec
  exact Set.Finite.subset (Set.finite_range g) hsub |>.to_subtype

end GaloisRep
