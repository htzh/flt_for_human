/-
  There are no nonzero `Γ₀(N)` cusp forms of weight `k ≤ 1`.

  Three cases: negative weight (`ModularForm.isZero_of_neg_weight`), weight `0` (a
  constant cusp form vanishes at the cusp `∞`), and weight `1` with `-1 ∈ Γ₀(N)`
  (`ModularForm.eq_zero_of_neg_one_mem`). The consequences used below are that the
  cusp-form space is a subsingleton and that the Hecke algebra acting on it is.

  The pin states some of its finiteness results only for `1 ≤ k`; this module is what
  removes that restriction, since for `k ≤ 1` the algebra is a subsingleton.

  FLT provenance, pinned `aa2d8b3`: the pin has no wrapper for these — its `k ≤ 1`
  branches are inline in the `S_` files.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.NormTrace

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace CuspForm

variable {N : ℕ} {k : ℤ}

/-- `-1` lies in `Γ₀(N)` (it lies in every `Gamma0`). -/
private theorem neg_one_mem_gamma0 (N : ℕ) :
    (-1 : GL (Fin 2) ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) := by
  refine Subgroup.mem_map.mpr ⟨-1, ?_, ?_⟩
  · simp [CongruenceSubgroup.Gamma0_mem]
  · ext i j
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.one_apply]

/-- For `k ≤ 1` there are no nonzero `Γ₀(N)` cusp forms: negative weight, weight
`0` cusp forms (constant, hence zero at the cusp `∞`), or weight `1` with
`-1 ∈ Γ₀(N)`. -/
theorem eq_zero_of_weight_le_one (N : ℕ) [NeZero N] (k : ℤ) (hk : k ≤ 1)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  apply CuspForm.toModularFormₗ_injective
  rw [map_zero]
  set F : ModularForm (CongruenceSubgroup.Gamma0 N) k := CuspForm.toModularFormₗ f with hF
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · exact ModularForm.isZero_of_neg_weight hk0 F
  · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
    have hz : UpperHalfPlane.IsZeroAtImInfty (F : UpperHalfPlane → ℂ) := by
      have hcusp : IsCusp OnePoint.infty
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
        Subgroup.isCusp_of_mem_strictPeriods one_pos
          (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
      simpa [hF, CuspForm.toModularFormₗ_eq_coe] using
        (OnePoint.isZeroAt_infty_iff.mp (f.zero_at_cusps' hcusp))
    have hc0 : c = 0 := by
      rw [hc] at hz
      exact tendsto_nhds_unique tendsto_const_nhds hz
    ext τ
    have hτ := congrFun hc τ
    simp only [hc0, Function.const_zero, Pi.zero_apply] at hτ
    simp [hτ]
  · obtain rfl : k = 1 := le_antisymm hk hk0
    exact ModularForm.eq_zero_of_neg_one_mem (neg_one_mem_gamma0 N) odd_one F

theorem subsingleton_of_weight_le_one (N : ℕ) [NeZero N] (k : ℤ) (hk : k ≤ 1) :
    Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  ⟨fun f g ↦ by rw [eq_zero_of_weight_le_one N k hk f, eq_zero_of_weight_le_one N k hk g]⟩

end CuspForm

end
