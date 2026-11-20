/-
  SET-AF91C consumer: the fundamental domain at a prescribed growth rate.

  **The row.** `FLTForHuman/NumberTheory/NumberField/TateGlobal/FundamentalDomain.lean` carries
  `exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow`: a
  measurable fundamental domain `D` for the principal idèles such that, for every `r`, some power
  `k` of the min-idèle-norm factor makes `min ‖a‖ ‖a‖⁻¹ ^ k · ‖a‖ ^ r` integrable on `D`.

  **The reading.** The row is read at a prescribed `r` rather than as a `∀ r`: the witness domain is
  fixed first and then the exponent is chosen, which is the order the unfolding argument needs (the
  `r` comes from the zeta integral's exponent, the `k` from the shell estimate).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF91CConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FundamentalDomain

set_option autoImplicit false

noncomputable section

open NumberField NumberField.TateGlobal MeasureTheory IsDedekindDomain
open scoped ENNReal BigOperators

namespace NumberFieldSetAF91CConsumer

/-- **The reading.** A single fundamental domain works for every growth rate `r`, after choosing
the shell exponent `k`. -/
theorem exists_fundamentalDomain_integrableOn_min_ideleNorm_pow
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] (r : ℝ) :
    ∃ D : Set (AdeleRing (𝓞 F) F)ˣ, MeasurableSet D ∧
      IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D ν ∧
      ∃ k : ℕ, IntegrableOn
        (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r) D ν := by
  obtain ⟨D, hD, hfd, hint⟩ :=
    exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F ν
  exact ⟨D, hD, hfd, hint r⟩

end NumberFieldSetAF91CConsumer
