/-
  The Petersson product on cusp forms for a congruence subgroup, as an integral
  over the standard fundamental domain `𝒟` of `SL(2, ℤ)`.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_CuspForm_PeterssonOn.lean`,
  the whole 31-line module. Mathlib `v4.34.0` already has the pointwise density
  `UpperHalfPlane.petersson` (`Mathlib/NumberTheory/ModularForms/Petersson.lean`);
  what this module adds is the coset sum over `SL(2, ℤ) ⧸ Γ` and its integral
  against `volume.restrict 𝒟`.
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

/-- The pointwise Petersson density of `f` and `g` summed over the cosets of `Γ`
in `SL(2, ℤ)`. -/
def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

/-- The Petersson product on `Γ`-cusp forms: integrate the coset-summed density
over the standard fundamental domain. -/
def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)

theorem peterssonOn_def (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonOn Γ k f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonOnIntegrand Γ k f g) := rfl

end CuspForm

end
