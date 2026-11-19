/-
  SET-AF85C consumer: the slab's volume, the cuspidal exhaustion, and the `ℚ` production cover.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Siegel/SlabVolume.lean` carries
  `AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain` (a
  fundamental domain of the determinant-norm slab has finite Haar measure) with its two engine lemmas;
  `FLTForHuman/AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` carries
  `AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul`
  (an eigenvector of a compact cusp operator is a finite sum of eigenvectors in pairwise orthogonal
  irreducible cusp subrepresentations); `FLTForHuman/AutomorphicForm/Adelic/Siegel/FiniteCover.lean`
  carries `AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat`.

  **The readings.**

  * Zone 1 — **a concrete window**: the volume row read at `α = 1`, `β = 2`, i.e. a fundamental domain
    of the annulus `1 ≤ ‖det‖ ≤ 2` (the window the Rankin–Selberg and Petersson slabs use);
  * Zone 2 — **a singleton covering set**: the two engine lemmas at `T = {1}` are the same statement,
    one through the translate and one through the union — the consistency the cover needs when the
    covering set has one element;
  * Zone 3 — **the exhaustion is nontrivial**: `v ≠ 0` forces some component `vs i` to be nonzero, so
    the decomposition produces a nonzero irreducible cusp subrepresentation and the sum is not empty;
  * Zone 4 — **the `ℚ` cover, unfolded**: `CoversModCentre` at the production pinning's `D`, read as
    the statement it is — every `g` is a rational point times a central scalar into `D`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF85CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabVolume
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IrreducibleSpine
import FLTForHuman.AutomorphicForm.Adelic.Siegel.FiniteCover

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalSpectrum
open scoped Classical ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF85CConsumer

/-! ### Zone 1 — the volume row in a concrete window -/

/-- **Zone 1.** A fundamental domain of the annulus `1 ≤ ‖det g‖ ≤ 2` over `ℚ` has finite
`adelicGLHaar`-measure: the row at `α = 1`, `β = 2`. -/
theorem adelicGLHaar_inter_slab_one_two_lt_top (Φ₀ : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2})) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        (Φ₀ ∩ {g | NumberField.TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2}) < ⊤ :=
  AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    ℚ 1 2 one_pos one_lt_two Φ₀ hΦ₀

/-! ### Zone 2 — the two engine lemmas at a singleton covering set -/

/-- **Zone 2.** The union lemma at `T = {1}` and the single-translate lemma are the same statement:
the translate of the centre-cut Siegel set is what the union of one element is. -/
theorem measure_image_mul_right_eq_biUnion_singleton {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ}
    (hd₁ : 0 < d₁) (d₂ : ℝ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        (⋃ y ∈ ({x} : Finset (AdelicGL2 (𝓞 ℚ) ℚ)),
          (· * y) '' centreCutSiegelSet ℚ c u d₁ d₂) < ⊤
      ∧ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        ((· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) < ⊤ := by
  refine ⟨AutomorphicForm.SlabVolume.measure_biUnion_lt_top ℚ hc u hd₁ d₂ {x}, ?_⟩
  exact AutomorphicForm.SlabVolume.measure_image_mul_right_centreCutSiegelSet_lt_top ℚ hc u hd₁ d₂ x

/-! ### Zone 3 — the exhaustion produces a nonzero irreducible piece -/

/-- **Zone 3.** If the eigenvector `v` is nonzero, at least one of the finitely many pairwise
orthogonal irreducible cusp subrepresentations it decomposes into carries a nonzero component — the
decomposition is not the empty sum. -/
theorem exists_nonzero_component_of_decomposition (F : Type) [Field F] [NumberField F] {α β : ℝ}
    {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hft : IsArchBiFinite F tys f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hTc : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc) (hcpt : IsCompactOperator Tc)
    (lam : ℂ) (hlam : lam ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = lam • v)
    (hvne : v ≠ 0) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
      (vs : Fin n → ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ i, IsIrreducibleCuspSubrep F hΦ₀ σ ξ (M i)) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ∧ Tc (vs i) = lam • vs i) ∧
      v = ∑ i, vs i ∧ ∃ i, vs i ≠ 0 := by
  obtain ⟨n, M, vs, hM, hMo, hvs, hsum⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
      F hΦ₀ σ ξ hσ f hf tys hft Tc hTc hcpt lam hlam v hv
  refine ⟨n, M, vs, hM, hMo, hvs, hsum, ?_⟩
  by_contra hzero
  simp only [not_exists, not_not] at hzero
  exact hvne (by rw [hsum]; exact Finset.sum_eq_zero fun i _ => hzero i)

/-! ### Zone 4 — the `ℚ` production cover, unfolded -/

/-- **Zone 4.** `CoversModCentre` at the production pinning's `D` says what it means: every `g` is a
rational point times `g` times a central scalar landing in `D`. -/
theorem exists_globalPoints_mul_centralScalar_mem_productionPinsGeneral_D_rat
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ γ : GL (Fin 2) ℚ, ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      globalPoints (𝓞 ℚ) ℚ γ * g * centralScalar (𝓞 ℚ) ℚ z
        ∈ (productionPinsGeneral ℚ).D :=
  AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat g

end AutomorphicFormSetAF85CConsumer
