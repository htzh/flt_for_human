/-
  SET-AF85A consumer: the archimedean `K`-types, the Bruhat series at one summand, and the Weyl
  integral applied twice.

  **The rows.** `FLTForHuman/EisensteinGeneral/ArchKType.lean` carries
  `Arch.exists_complexKType` and `Arch.exists_realKType` (an integral `J`, holomorphic in the spectral
  variable, with a uniform exponential decay in the family parameter);
  `FLTForHuman/EisensteinGeneral/ArchIntegralBound.lean` carries
  `Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum` (the Whittaker coefficient of a Bruhat series
  of a finite sum of induced sections is that finite sum of coefficients) and
  `AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral` (the Weyl integral of
  an induced section is an induced section with the two characters exchanged and `s ↦ -s`).

  **The readings.** Each row is stated with parameters that the uses specialise, and these are the
  forms the consumers read:

  * Zone 1 — **`(a, b) = (0, 0)`**: the two `GL₂(ℂ)`-type weights vanish, so the integrand loses its
    `z ^ a * conj z ^ b` factor and the half-plane threshold is `1 < Re w`;
  * Zone 2 — **`k = 0`**: the `GL₂(ℝ)`-type weight vanishes, and the integral is
    `∫ x, (1 + x²) ^ (-w) exp (-2πi t x)` on `Re w > 1/2`;
  * Zone 3 — **one summand**: the Bruhat-series row at `n = 1` with `Φ = c • Ψ` is the scalar rule
    `W(Φ) = c * W(Ψ)` for the coefficient of a single induced section;
  * Zone 4 — **the Weyl integral twice**: applying the row to its own output returns the original
    character pair and the original `s` (the involution `(μ, ν, s) ↦ (ν, μ, -s)`).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/EisensteinGeneralSetAF85AConsumer.lean` and never enters the build.
-/
import FLTForHuman.EisensteinGeneral.ArchKType
import FLTForHuman.EisensteinGeneral.ArchIntegralBound

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal

namespace EisensteinGeneralSetAF85AConsumer

/-! ### Zone 1 — the `GL₂(ℂ)`-type at vanishing weights -/

/-- **Zone 1.** At `a = b = 0` the `z ^ a * conj z ^ b` factor is `1`, so `J` is the plain
`(1 + ‖z‖²) ^ (-w)` integral against `exp (-4πi Re (ζ z))`, on `Re w > 1`. -/
theorem exists_complexKType_zero_weight :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  obtain ⟨J, h1, h2, h3⟩ := EisensteinGeneral.Arch.exists_complexKType 0 0
  refine ⟨J, h1, ?_, h3⟩
  intro w ζ hw hζ
  have hw' : ((0 + 0 : ℕ) : ℝ) / 2 + 1 < w.re := by
    norm_num
    exact hw
  simpa using h2 w ζ hw' hζ

/-! ### Zone 2 — the `GL₂(ℝ)`-type at vanishing weight -/

/-- **Zone 2.** At `k = 0` the weight `((x - i) / √(1 + x²)) ^ k` is `1`, so `J` is the plain
`(1 + x²) ^ (-w)` integral against `exp (-2πi t x)`, on `Re w > 1/2`. -/
theorem exists_realKType_zero_weight :
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 →
        J w t = ∫ x : ℝ, (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w : ℂ) (t : ℝ), ‖w‖ ≤ R → t ≠ 0 →
        ‖J w t‖ ≤ C * max 1 (|t| ^ (-(N : ℝ))) * Real.exp (-c' * |t|)) := by
  obtain ⟨J, h1, h2, h3⟩ := EisensteinGeneral.Arch.exists_realKType 0
  exact ⟨J, h1, fun w t hw ht => by simpa using h2 w t hw ht, h3⟩

/-! ### Zone 3 — the Bruhat-series coefficient at one summand -/

/-- **Zone 3.** With a single summand and `Φ = c • Ψ`, the row is the scalar rule: the Whittaker
coefficient of the Bruhat series of `c • Ψ` is `c` times that of `Ψ`. -/
theorem whittakerCoefficient_bruhatSeries_single (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (c : ℂ) (Ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ Ψ)
    (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => Ψ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => c * Ψ g' + ∑' ξ' : F,
          c * Ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g
      = c * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ g' + ∑' ξ' : F,
            Ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g := by
  have h := EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum F ψ hψc hψ 1
    (fun _ => c) (fun _ => Ψ) (fun g' => c * Ψ g')
    (by intro i; exact hΨ) (by intro g'; simp) ξ g (by intro i; simpa using hint)
  simpa using h

/-! ### Zone 4 — the Weyl intertwining integral is an involution on induced sections -/

/-- **Zone 4.** Applying the Weyl integral to its own output returns the original character pair and
the original spectral parameter: the substitution `(μ, ν, s) ↦ (ν, μ, -s)` has order two. -/
theorem isInducedSection_weylIntertwiningIntegral_twice (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s)
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ)) := by
  refine fun hα μ ν s φ hφ => ?_
  have h := AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα μ ν s φ hφ
  simpa using (AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hα ν μ (-s) _
    (by simpa using h))

end EisensteinGeneralSetAF85AConsumer
