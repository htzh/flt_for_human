/-
  SET-AF13 consumer zone — the flat Eisenstein series of a section family and its constant term.

  The dictionary row `exists_flat_isInducedSection_family_eq_of_isInducedSection` turns one
  induced section `φ₀` at `s₀` that is archimedean-`K`-finite, `K_f`-smooth and continuous into a
  whole family `ψ` of induced sections (continuous in `(s, g)`, holomorphic in `s`). The two other
  rows then read off, at every `ψ s` in the half-plane `re s > 1/2`:

  * `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` — the flat Eisenstein
    series `E (ψ) (s) = ψ s + ∑' ξ, ψ s (w n(ξ) ·)` is holomorphic in `s` there;
  * `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` — its constant term is
    the section plus the Weyl-intertwining integral,
    `constantTerm E (ψ s) g = ψ s g + (vol box)⁻¹ * weylIntertwiningIntegral (ψ s) g`.

  No consumer-side hypothesis beyond the dictionary row's own inputs is needed: the only
  ingredient the constant-term row asks for that the dictionary does not hand over verbatim is
  continuity of the single section `ψ s`, and joint continuity gives that by `Continuous.comp`
  with `g ↦ (s, g)`.
-/
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisenstein

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicLevel
open NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace AutomorphicForm

/-- From one archimedean-`K`-finite, `K_f`-smooth, continuous induced section at `s₀`, the
dictionary row's family `ψ` has a flat Eisenstein series that is holomorphic in the half-plane
`re s > 1/2`, and its constant term is the section plus the Weyl-intertwining integral. -/
theorem exists_flatEisenstein_holomorphic_and_constantTerm_eq_section_add_weyl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀) (_hφ₀f : IsKfSmooth F φ₀) (_hφ₀c : Continuous φ₀),
    ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ s₀ = φ₀
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ (∀ g : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ
          (fun s : ℂ => ψ s g + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
          {z : ℂ | 1 / 2 < z.re})
      ∧ ∀ (s : ℂ), 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          letI := adeleBorel (𝓞 F) F
          constantTerm
            (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F)
              (adelicBox F))
            unipotentGL2 (fun g' => ψ s g' + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')) g
            = ψ s g
              + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
                * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ s) g := by
  intro α hα μ ν hμ hν s₀ φ₀ hφ₀ hφ₀K hφ₀f hφ₀c
  obtain ⟨ψ, hψ₀, hψind, -, -, hψjc, hψhol, -⟩ :=
    exists_flat_isInducedSection_family_eq_of_isInducedSection F hα μ ν s₀ φ₀ hφ₀ hφ₀K hφ₀f hφ₀c
  have hψc : ∀ s : ℂ, Continuous (ψ s) := fun s =>
    hψjc.comp (continuous_const.prodMk continuous_id)
  refine ⟨ψ, hψ₀, hψind, hψjc, hψhol, fun g => ?_, ?_⟩
  · exact bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family F hα μ ν hμ hν ψ hψind
      hψjc hψhol g
  · intro s hs g
    exact constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα μ ν hμ hν
      s hs (ψ s) (hψind s) (hψc s) g

end AutomorphicForm

end
