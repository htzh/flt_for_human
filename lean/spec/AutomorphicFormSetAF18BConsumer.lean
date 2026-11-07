/-
  SET-AF18B consumer: the right-translation zone of the cuspidal-spectrum carrier.

  **The zone.** Row 1 (`exists_isLift_rightTranslate`) produces, for a central character `ξ` of
  modulus `σ` and every `y : GL₂(𝔸_F)`, bounded operators `T`, `T'` on the carrier
  `Carrier F Φ₀ σ` lifting `rightTranslate y` and `rightTranslate y⁻¹` with `T† = |det y|^σ • T'`
  and `‖T‖ ≤ |det y|^(σ/2)`. Row 2 (`rightTranslate_mem_cuspMemberSubmodule`) is the membership
  that `IsCuspLift` is parametrised by — it is precisely the `op φ ∈ cuspMemberSubmodule` side
  condition of `IsCuspLift`'s defining equation. Row 3
  (`exists_isCuspLift_rightTranslate_and_norm_le`) transports row 1 to the cuspidal subcarrier
  `cuspSubcarrier F hΦ₀ σ ξ`, with the same `|det y|^(σ/2)` bound.

  Composed, the adjoint identity is read at a pair `x`, `v` of carrier elements (the character
  factor `|det y|^σ` moved to the left of the inner product by conj-reality), the two norm
  bounds are the row-1 and row-3 halves, and the subcarrier lift `S` is applied to the cusp
  projection `toCuspSubcarrier φ` of a cusp member `φ`: row 2 makes `rightTranslate y φ` a cusp
  member, so `IsCuspLift`'s defining equation fires and `S (toCuspSubcarrier φ)` is
  `toCuspSubcarrier` of the right translate. The exponent bookkeeping is visible in the
  statement: `σ` is the exponent of the adjoint twist, `σ / 2` the exponent of both norm
  bounds, and `y` versus `y⁻¹` the pair of lifts.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace CuspidalSpectrum

/-- **The zone.** For a central character `ξ` of modulus `σ` and every `y : GL₂(𝔸_F)` there are
bounded operators `T`, `T'` on the carrier and a bounded operator `S` on the cuspidal
subcarrier such that

* the adjoint identity holds at every pair `x`, `v` of carrier elements, with the character
  factor `|det y|^σ` explicit (`T† = |det y|^σ • T'`),
* `‖T‖ ≤ |det y|^(σ/2)` and `‖S‖ ≤ |det y|^(σ/2)`,
* `S` is the cuspidal lift of `rightTranslate y` (`IsCuspLift`), and
* at a cusp member `φ` the lift is computable: `S` of the cusp projection of `φ` is the cusp
  projection of the right translate of `φ` — the membership of row 2 supplying the side
  condition of `IsCuspLift`. -/
theorem consumer_zoneA_carrier_rightTranslate
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (y : AdelicGL2 (𝓞 F) F) :
    ∃ (T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
      (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ x v : Carrier F Φ₀ σ, ⟪T x, v⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
          ⟪x, T' v⟫_ℂ) ∧
      ‖T‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) ∧
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) S ∧
      ‖S‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) =
          toCuspSubcarrier F hΦ₀ σ ξ
            ⟨rightTranslate F y φ,
              rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ y φ φ.2⟩ := by
  obtain ⟨T, T', _, _, hadj, hTn⟩ := exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y
  obtain ⟨S, hS, hSn⟩ := exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ y
  refine ⟨T, T', S, ?_, hTn, hS, hSn, fun φ => hS φ _⟩
  intro x v
  rw [← ContinuousLinearMap.adjoint_inner_right T x v, hadj, smul_apply, inner_smul_right]

end CuspidalSpectrum

end AutomorphicForm
