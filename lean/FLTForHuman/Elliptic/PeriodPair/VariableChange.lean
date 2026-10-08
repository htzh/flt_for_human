/-
  `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq`: every elliptic curve over `ℂ`
  is a change of variables of the Weierstrass curve attached to a period lattice.

  Statement authority:
  `Theorems/Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean`; proof from the
  pin's `P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean` (`:9–17`),
  pinned `anthropics/fermats-last-theorem@aa2d8b3`.

  One of SC's two leaves (row S, `topics/velu/WORKORDER-SC-capstone.md`); it is a two-step
  consequence of the ported `PeriodPair.jLattice_surjective`,
  `PeriodPair.jLattice_eq_c₄_pow_three_div_Δ` and mathlib's
  `WeierstrassCurve.exists_variableChange_of_j_eq`.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean>
-/
import FLTForHuman.Elliptic.PeriodPair.JLine
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve

namespace PeriodPair

theorem exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by
  obtain ⟨L, hΔ, hj⟩ := PeriodPair.jLattice_surjective E.j
  haveI : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ.weierstrassCurve_Δ_ne_zero⟩
  have hjE : L.weierstrassCurve.j = E.j := by
    rw [← hj, L.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, div_eq_mul_inv, mul_comm,
      Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact ⟨L, WeierstrassCurve.exists_variableChange_of_j_eq L.weierstrassCurve E hjE⟩

end PeriodPair
