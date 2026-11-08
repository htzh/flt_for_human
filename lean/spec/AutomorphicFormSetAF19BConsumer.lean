/-
  SET-AF19B consumer: the four rows of `Cusp/SpectrumConvAction.lean` composed into one chain.

  The module proves that right convolution by a factorisable `f` is an operator on the cuspidal
  carrier. The four rows are, in order, (1) the `L²` norm bound
  `‖φ * g‖ ≤ sqrt (N1 * N2) · ‖φ‖` on the continuous member submodule, (2) `cuspMemberSubmodule`
  is preserved by `φ ↦ φ * f`, (3) a bounded operator `T` lifting `φ ↦ φ * f` maps
  `cuspSubcarrier` into itself, and (4) if `f` is bi-invariant under the level-`N` subgroup
  `(fdPins F Φ₀).U N` then the image lands in the smaller `cuspLevelSubcarrier … N`.

  **This zone.** One chain, in the order the module proves the rows. Row 1 is read *at a cusp
  member* `ψ` — the bound is extracted as `C` together with its value on `ψ`, whose continuity
  hypothesis is the cusp member's own second conjunct. Row 2 then supplies the membership
  `ψ * f ∈ cuspMemberSubmodule` that makes `toCuspSubcarrier` applicable, and the resulting
  cusp-subcarrier vector `u` is written out through `toCuspSubcarrier_apply_coe`: it is the `Lp`
  class of `ψ * f` in the weighted measure. Rows 3 and 4 are then read on that same `u` — the
  cuspidal membership from row 3, and, at a bi-invariant `f`, the level-`N` membership from row 4.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConvAction

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

-- the pin's wrappers register the adelic Borel structures as local instances for these statements
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
namespace SetAF19B

/-- **The zone.** In one statement, from a cusp member `ψ`, a factorisable `f` bi-invariant under
`(fdPins F Φ₀).U N`, and a bounded operator `T` lifting `φ ↦ rightConv F φ f`:

* row 1's `C` with its bound read at `ψ` (`hψc` is `ψ`'s membership in the continuous member
  submodule, assembled from the cusp member's own conjuncts);
* row 2's membership `ψ * f ∈ cuspMemberSubmodule`, fed into `toCuspSubcarrier` to produce a
  cusp-subcarrier vector `u` whose underlying `Lp` class is spelled out by
  `toCuspSubcarrier_apply_coe`;
* row 3 at `u`: `T u` is again in `cuspSubcarrier`;
* row 4 at `u`: since `f` is `(fdPins F Φ₀).U N`-bi-invariant, `T u` is in `cuspLevelSubcarrier … N`. -/
theorem consumer_zone_norm_and_subcarrier_closure
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g f : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hf : IsFactorizableTestFn F f) (N : Ideal (𝓞 F))
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (u * x) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
    (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T)
    (ψ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ hψc : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ,
        ∃ hψg : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) g ∈ memberSubmodule F Φ₀ ξ,
          ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) g, hψg⟩‖ ≤
            C * ‖toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hψc.1⟩‖) ∧
      ∃ hm : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ,
        ∃ u : ↥(cuspSubcarrier F hΦ₀ σ ξ),
          (u : Carrier F Φ₀ σ) =
              toCarrier F hΦ₀ σ ξ ⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f, hm.1.1.1⟩ ∧
            T (u : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ ∧
            T (u : Carrier F Φ₀ σ) ∈ cuspLevelSubcarrier F hΦ₀ σ ξ N := by
  classical
  -- row 1, with its bound read at the cusp member
  obtain ⟨C, hC, hbound⟩ := exists_norm_toCarrier_rightConv_le F hΦ₀ σ ξ hσ g hg hgc
  -- row 2, giving the cusp-member membership that `toCuspSubcarrier` consumes
  have hm := rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf _ ψ.2
  refine ⟨C, hC, fun hψc => hbound _ hψc, hm, ?_⟩
  -- the cusp-subcarrier vector is the row-2 membership fed through `toCuspSubcarrier`
  refine ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨_, hm⟩,
    toCuspSubcarrier_apply_coe F hΦ₀ σ ξ ⟨_, hm⟩, ?_, ?_⟩
  -- row 3 at that vector
  · exact apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ f hf T hT _
      (toCuspSubcarrier F hΦ₀ σ ξ ⟨_, hm⟩).2
  -- row 4 at the same vector, at a `(fdPins F Φ₀).U N`-bi-invariant `f`
  · exact map_cuspSubcarrier_le_cuspLevelSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ N f hf hfU T hT
      (Submodule.mem_map.mpr ⟨_, (toCuspSubcarrier F hΦ₀ σ ξ ⟨_, hm⟩).2, rfl⟩)

end SetAF19B
end AutomorphicForm
