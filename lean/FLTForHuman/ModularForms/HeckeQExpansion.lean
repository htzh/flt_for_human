/-
  The two Hecke translates of a realized `q`-expansion on `ℍ`.

  `τ ↦ (τ + b)/ℓ` twists the coefficients by `exp(2πibm/ℓ)` and changes the
  period `1 ↦ ℓ`; `τ ↦ ℓτ` replaces the coefficients by `qExpand ℂ (ℓ*ℓ)` and
  also changes the period to `ℓ`. These are base/013 §5.2's "analytic face of the
  Hecke action", and they are what makes the descended coefficients level-one
  invariant in T8's `hasSum_coeff_of_phiGenDescends`.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean` (54) and
  `P2M/Sol/S_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean` (55). Both
  statements are verbatim from their `Theorems/` wrappers (so they use the
  wrappers' spelling, per T7's log §7.3).

  Assumes the Hecke matrices from `FLTForHuman.ModularForms.Defs.HeckeOperator`
  and `qExpand`/`qExpand_coeff_*` from `FLTForHuman.ModularCurve.Defs.Laurent`.
-/
import Mathlib.RingTheory.LaurentSeries
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularCurve.Defs.Laurent

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

/-- The `τ ↦ (τ + b)/ℓ` Hecke translate of a realized `q`-expansion at period
`1`. Stated verbatim from
`Theorems/Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean`. -/
theorem hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ)
    (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ =>
      A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeMatrix ℓ b • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have e : 𝕢 1 ((ModularForm.heckeMatrix ℓ b • τ : ℍ) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * b / ℓ) * 𝕢 ℓ (τ : ℂ) := by
    rw [ModularForm.coe_heckeMatrix_smul hℓ, Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have e2 : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * b / ℓ) ^ m
      = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
    intro m
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  have hfg : (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) *
        𝕢 ℓ (τ : ℂ) ^ m)
      = fun m : ℤ => A.coeff m * 𝕢 1 ((ModularForm.heckeMatrix ℓ b • τ : ℍ) : ℂ) ^ m := by
    funext m
    rw [e, mul_zpow, e2]
    ring
  rw [hfg]
  exact hA _

/-- The `τ ↦ ℓτ` Hecke translate of a realized `q`-expansion at period `1`.
Stated verbatim from
`Theorems/Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean`. -/
theorem hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ] (A : LaurentSeries ℂ)
    (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ =>
      A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (qExpand ℂ (ℓ * ℓ) A).coeff m *
      Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hN : ((ℓ * ℓ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne (ℓ * ℓ))
  have e : 𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) =
      𝕢 ℓ (τ : ℂ) ^ ((ℓ * ℓ : ℕ) : ℤ) := by
    rw [ModularForm.coe_heckeDiagMatrix_smul hℓ, Periodic.qParam, Periodic.qParam, zpow_natCast,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hinj : Function.Injective (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m) := mul_right_injective₀ hN
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (qExpand ℂ (ℓ * ℓ) A).coeff m * 𝕢 ℓ (τ : ℂ) ^ m) ∘
        (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m)
        = fun m : ℤ => A.coeff m * 𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [qExpand_coeff_mul, e, ← zpow_mul]
    rw [hfg]
    exact hA _
  · intro m hm
    rw [qExpand_coeff_of_not_dvd (ℓ * ℓ) A (fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩), zero_mul]

end ModularCurve

end
