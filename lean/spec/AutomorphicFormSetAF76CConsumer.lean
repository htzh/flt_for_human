/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/BesselInequality.lean` (`AF76C`).

  A `spec/` probe, not a library module. The zone is read at `F = ℚ`, where the pin's abstract
  character `ψ` has a concrete instance: the trivial character `1` is *not* global
  (`AutomorphicForm.not_isGlobalAddChar_one`), so the standard character `psiQ` is the one to use, and
  its globality is the port's `isGlobalAddChar_psiQ`.

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in it)
  breaks this file:

  * `phiRat` is the `‖·‖`-type coefficient function the headline is read at: the modulus of the
    standard character at the difference of the upper-right and lower-left matrix entries. On the
    unipotent line `u ↦ unipotentGL2 u * 1` that is `‖psiQ (u - 0)‖`, so its continuity needs the
    matrix coefficients of `unipotentGL2` (`Continuous.matrix_elem` off `Units.continuous_val`), the
    continuity inside `isGlobalAddChar_psiQ`, and the norm of `ℂ`;
  * `inner_ech_zero_one` reads `orthonormal_ech` through `orthonormal_iff_ite` at `α = 0`, `β = 1`:
    the two characters `ech psiQ 0 = 1` and `ech psiQ 1 = psiQ` are orthogonal, which is the
    character-integral vanishing of `integral_addChar_mul_eq_zero` in `L²`;
  * `bessel_at_zero` is the headline at `A = {0}` and `g = 1`, on those pins.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF76CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.BesselInequality
import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddCharRat

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicBox MeasureTheory
open AutomorphicForm AutomorphicForm.BesselInequality NumberField.StandardAddChar

open scoped ENNReal ComplexConjugate

namespace AutomorphicFormSetAF76CConsumer

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

/-- The pins the headline is read at, at `F = ℚ`. -/
abbrev pinsQ : CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (adelicBox ℚ)

/-- The `‖·‖`-type coefficient function: the modulus of the standard character at the difference of
the upper-right and lower-left matrix entries. -/
def phiRat (x : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  ((‖psiQ ((x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 -
      (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0)‖ : ℝ) : ℂ)

/-- On the unipotent line at `g = 1` the coefficient function is continuous: the matrix entries of
`unipotentGL2 u` are `u` and `0`, so the datum is `‖psiQ u‖` read through a continuous character. -/
theorem continuous_phiRat_unipotent :
    Continuous fun u : AdeleRing (𝓞 ℚ) ℚ =>
      phiRat (unipotentGL2 u * (1 : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  have hmat : Continuous fun u : AdeleRing (𝓞 ℚ) ℚ =>
      ((unipotentGL2 u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    Units.continuous_val.comp continuous_unipotentGL2
  have h01 := hmat.matrix_elem 0 1
  have h10 := hmat.matrix_elem 1 0
  have hchar : Continuous fun u : AdeleRing (𝓞 ℚ) ℚ =>
      psiQ (((unipotentGL2 u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1 -
        ((unipotentGL2 u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0) :=
    isGlobalAddChar_psiQ.continuous.comp (h01.sub h10)
  have h := Complex.continuous_ofReal.comp hchar.norm
  simpa only [phiRat, mul_one, Function.comp_def] using h

/-- `orthonormal_ech` at `α = 0` and `β = 1`, read through `orthonormal_iff_ite`: the characters
`ech psiQ 0` and `ech psiQ 1` are orthogonal in `L²` of the box-normalized adèle ring. -/
theorem inner_ech_zero_one :
    inner ℂ ((memLp_ech isGlobalAddChar_psiQ 0).toLp (ech psiQ 0))
      ((memLp_ech isGlobalAddChar_psiQ 1).toLp (ech psiQ 1)) = 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_ech isGlobalAddChar_psiQ)) 0 1
  simpa using h

/-- The headline at `A = {0}`, `g = 1`, on the concrete `‖·‖`-type coefficient function. -/
theorem bessel_at_zero :
    ∑ α ∈ ({0} : Finset ℚ),
        ‖whittakerCoefficient ℚ pinsQ psiQ phiRat α (1 : AdelicGL2 (𝓞 ℚ) ℚ)‖ ^ 2 ≤
      ∫ u, ‖phiRat (unipotentGL2 u * (1 : AdelicGL2 (𝓞 ℚ) ℚ))‖ ^ 2 ∂pinsQ.ν :=
  sum_norm_whittakerCoefficient_sq_le_integral_norm_sq ℚ ∅ (fun _ => ⊥) (fun _ => 1) psiQ
    isGlobalAddChar_psiQ phiRat 1 continuous_phiRat_unipotent ({0} : Finset ℚ)

end AutomorphicFormSetAF76CConsumer
