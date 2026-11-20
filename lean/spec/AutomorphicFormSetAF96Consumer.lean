/-
  SET-AF96 consumer: the two independent definition layers read together.

  **The rows.** `AutomorphicForm/Adelic/IwasawaShellIndex.lean` carries the shell index
  `iwasawaShellIndex K v g` (twice the log-valuation of the bottom row minus the log-valuation of
  the determinant) with its invariance lemmas; `AutomorphicForm/Adelic/IwasawaShellInvariance.lean`
  carries the two rows that the index is locally constant and invariant under the rational centre
  times the unipotent radical. `LanglandsTunnell/TateLocal/ArchPlace.lean` carries the archimedean
  local data (the additive characters, the characters of `ℂˣ`/`ℝˣ`, the test functions, the zeta
  integrals and the Gamma factors); `LanglandsTunnell/TateLocalZetaComparison.lean` carries the two
  rows that the real and complex zeta integrals agree with `localZeta`.

  **The reading.** The first theorem multiplies an invariant element by the Hecke generator at the
  place `v`: the rational-centre-unipotent invariance of the row leaves the index alone, and the
  hecke-generator lemma adds exactly one. The second reads the archimedean Gamma factor as a ratio of
  *local* zeta functions, which is the form the global functional equation consumes.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF96Consumer.lean` and never enters the build.
-/

import FLTForHuman.AutomorphicForm.Adelic.IwasawaShellInvariance
import FLTForHuman.LanglandsTunnell.TateLocalZetaComparison

set_option autoImplicit false
noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm MeasureTheory
open LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal NNReal

namespace AutomorphicFormSetAF96Consumer

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

/-- A rational-centre-unipotent element shifts the shell index by the hecke generator's `1`. -/
theorem iwasawaShellIndex_mul_centreUnipotent_mul_heckeGen
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalCentreUnipotent K)
    (g : AdelicGL2 (𝓞 K) K) :
    iwasawaShellIndex K v (x * heckeGen (𝓞 K) K v * g) =
      iwasawaShellIndex K v g + 1 := by
  rw [mul_assoc, iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent K v x hx,
    iwasawaShellIndex_heckeGen_mul]

/-- The archimedean Gamma factor is a ratio of local zeta functions. -/
theorem complexGammaAt_eq_localZeta_ratio
    (μ : Measure ℂ) (ψ : AddChar ℂ ℂ) (f₀ : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexGammaAt μ ψ f₀ χ s =
      localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s := by
  rw [complexGammaAt, complexZeta_eq_localZeta, complexZeta_eq_localZeta]

/-- The real archimedean Gamma factor, the same reading. -/
theorem realGammaAt_eq_localZeta_ratio
    (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) :
    realGammaAt μ ψ f₀ χ s =
      localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s := by
  rw [realGammaAt, realZeta_eq_localZeta, realZeta_eq_localZeta]

end AutomorphicFormSetAF96Consumer
