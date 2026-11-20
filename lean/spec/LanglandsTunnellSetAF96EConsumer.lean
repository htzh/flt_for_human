/-
  SET-AF96 consumer (E): the two central-character rows agree at the pin.

  `LanglandsTunnell/WeightOneLiftCentralScalar.lean` (SET-AF95) carries the centre law of the lift:
  `weightOneLift n f (centralScalar u * g) = (ω_χ u) * weightOneLift n f g` for the idèle-class
  character `ω_χ = dirichletIdeleChar χ · ‖·‖`. `LanglandsTunnell/WeightOneLiftCentralDet.lean`
  (SET-AF96) carries its determinant companion: at a place `v ∉ S` the lift transforms by the
  eigenvalue `Φ.b v` through the *determinant* of the production pin `gen v`.

  Composing them reads the eigenvalue as the character's value at a determinant, which is the form
  the Euler product consumes; the composition also exercises the `Z`-subtype coercion that
  `det_gen_mem_Z` establishes (`Z = ⊤` for the compact pins, so `det (gen v)` is central).

  `spec/` is outside every Lake library: this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF96EConsumer.lean` and never enters the build.
-/

import FLTForHuman.LanglandsTunnell.WeightOneLiftCentralDet

set_option autoImplicit false
noncomputable section

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain
open scoped ModularForm MatrixGroups

namespace LanglandsTunnellSetAF96EConsumer

/-- At a place outside `S`, the central-character law holds at the *determinant* of the pin. -/
theorem weightOneLift_centralScalar_det_eq_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
        (centralScalar (𝓞 ℚ) ℚ
          (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
      = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g :=
  LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul hn f hf χ hχ Φ S hb v hv g

/-- The eigenvalue is multiplicative across two places, through the two centre laws. -/
theorem weightOneLift_centralScalar_det_mul_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ))
    {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) (hw : w ∉ S)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
        (centralScalar (𝓞 ℚ) ℚ
          (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v) *
            Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen w)) * g)
      = (Φ.b v * Φ.b w) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  rw [map_mul, mul_assoc,
    LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul hn f hf χ hχ Φ S hb v hv,
    LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul hn f hf χ hχ Φ S hb w hw]
  ring

end LanglandsTunnellSetAF96EConsumer
