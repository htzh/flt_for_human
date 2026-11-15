/-
  The box normalization in Fourier form: the inverse box measure times the adelic Fourier transform of a
  pure tensor equals the discriminant factor times the product of the two one-variable transforms.

  This is the Fourier-integral form of `NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq`
  (the two transforms differ by the character twist and the `w`-argument).

  spec-pin: P2M/Sol/S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.lean
-/
import FLTForHuman.NumberTheory.AdelicBox.Normalization
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
open NumberField.InfiniteAdeleRing NumberField.AdelicFourier IsDedekindDomain
open scoped ENNReal NNReal Classical

namespace EisensteinGeneral.Factorization

section Places

variable (F : Type) [Field F] [NumberField F]

-- pin: countable_heightOneSpectrum
-- (S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.lean:32)
private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have hF : Countable F := by
    have e := (Module.finBasis ℚ F).equivFun.toEquiv
    exact (Equiv.countable_iff e).mpr inferInstance
  have hO : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  have hL : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  have hI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

end Places

attribute [local instance] countable_heightOneSpectrum

variable (F : Type) [Field F] [NumberField F]

namespace FiniteAdelicFactorization

open scoped Classical in

-- pin: inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
-- (S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.lean:93)
private theorem inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by
  have key := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq F μ ν
    (fun y => (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          (-(y * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)) * f y)
    (fun z => (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) (-(z * w.2)) * g z)
  have hpt : (fun x : AdeleRing (𝓞 F) F =>
        ψ (-(x * w)) * (f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2))
      = fun x : AdeleRing (𝓞 F) F =>
        (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            (-(InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
                * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1))
          * f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
          * ((ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) (-(x.2 * w.2)) * g x.2) := by
    funext x
    have hsplit : -(x * w)
        = (((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)) :
              AdeleRing (𝓞 F) F)
            + ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)) :
              AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F) :=
      Prod.ext (show -(x.1 * w.1) = -(x.1 * w.1) + 0 from (add_zero _).symm)
        (show -(x.2 * w.2) = 0 + -(x.2 * w.2) from (zero_add _).symm)
    have hmul : ψ (((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)) :
              AdeleRing (𝓞 F) F)
            + ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)) :
              AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F)
        = ψ ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)))
            * ψ ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2))) :=
      AddChar.map_add_eq_mul ψ _ _
    show ψ (-(x * w)) * (f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2)
        = ψ ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
              ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
                (-(InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
                    * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1))))
            * f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
            * (ψ ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)))
                * g x.2)
    rw [map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm,
      map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply, hsplit, hmul]
    ring
  simp only [fourierIntegral_def]
  rw [hpt]
  exact key

end FiniteAdelicFactorization

theorem inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by
  exact FiniteAdelicFactorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq F μ ν ψ f g w

end EisensteinGeneral.Factorization

end
