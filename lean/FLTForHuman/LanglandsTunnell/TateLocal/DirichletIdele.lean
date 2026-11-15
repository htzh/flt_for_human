/-
  The Dirichlet character read on the idèle class character at an unramified place: the value at the
  uniformizer is `χ (|𝔭|) * |𝔭|⁻¹`.

  spec-pin: P2M/Sol/S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen.lean
-/
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.HeckeCharacter.Dirichlet
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell

theorem dirichletIdeleChar_mul_modulus_det_gen
    {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  sorry

end LanglandsTunnell

end
