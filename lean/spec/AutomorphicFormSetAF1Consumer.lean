/-
  Cross-module wire test for the cuspidal-spectrum carrier (SET-AF1's definition gate) and for
  the eight headlines of WORKORDER-AF1-proofs.

  A `spec/` probe, not a library module. Zone A composes the carrier with the centre-cut
  trio's determinant-norm fundamental domain: the slab fundamental domain at `(1, 2)`, the
  weighted-`L²` transfer of a cusp member, and `toCarrier`'s linearity read on it. Zone B
  composes the subrepresentation datum: `IsCuspLift` from its `∀ ∃` form, and two closed
  subrepresentation conditions meeting. Zones C–J each consume one landed headline:

  * C — `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (B1): the norm exponent,
    paired with the positivity of the idèle norm at every idèle;
  * D — `exists_isSlabFundamentalDomain` (C1): the produced slab fundamental domain carries the
    weighted-`L²` transfer;
  * E — `isotypicCuspSubmodule_le_cuspMemberSubmodule` (C2): a Hecke-isotypic cusp form is in
    the carrier's weighted space on any slab fundamental domain;
  * F — `cuspKFiniteSubmodule_le_cuspMemberSubmodule` (C3): the same for a `K`-finite cusp form;
  * G — `eq_zero_of_toCarrier_eq_zero` (C4): a continuous member killed by `toCarrier` is the
    zero function;
  * H — `exists_hasModulus_of_isAutomorphicFnAt_of_continuous` (C5): the modulus exponent, read
    back on the unit group through the gate's `hasModulus_iff_units`;
  * I — `rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one` (D1): a
    unit-norm right translate stays in the weighted space and is unitary for the pairing;
  * J — `exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample`
    (D2): the slab bound against an ample centre-cut cover.

  Every zone is a real composition — no `#check` — so deleting any one module it imports
  makes the probe fail.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumSubrep
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumPairing
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormExponent

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped ENNReal

namespace AutomorphicFormSetAF1Consumer

variable (F : Type) [Field F] [NumberField F]

-- Zone A: the slab fundamental domain and the carrier's weighted-`L²` transfer.
--
-- `IsSlabFundamentalDomain F 1 2 S` is read off the determinant-norm fundamental domain the
-- centre-cut trio landed, and `memLp_weightedMeasure_of_mem` then puts every element of the
-- carrier's cusp member submodule into the weighted space; `toCarrier` is its linear map.
example (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
      (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F (1 : ℝ) 2 Φ₀),
      (∀ φ : ↥(AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule F Φ₀ ξ),
          MemLp (φ : AdelicGL2 (𝓞 F) F → ℂ) 2
            (AutomorphicForm.CuspidalSpectrum.weightedMeasure F Φ₀ σ)) ∧
      (∀ φ ψ : ↥(AutomorphicForm.CuspidalSpectrum.memberSubmodule F Φ₀ ξ),
          AutomorphicForm.CuspidalSpectrum.toCarrier F hΦ₀ σ ξ (φ + ψ) =
            AutomorphicForm.CuspidalSpectrum.toCarrier F hΦ₀ σ ξ φ +
              AutomorphicForm.CuspidalSpectrum.toCarrier F hΦ₀ σ ξ ψ) ∧
      (∀ z : (AdeleRing (𝓞 F) F)ˣ,
          AutomorphicForm.CuspidalSpectrum.HasModulus F ξ 1 →
          0 < NumberField.TateGlobal.ideleNorm F z) := by
  obtain ⟨S, hS, hFD⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2
  have hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F (1 : ℝ) 2 S :=
    ⟨one_pos, one_lt_two, hS, hFD⟩
  refine ⟨S, hΦ₀, fun φ => ?_, fun φ ψ => map_add _ φ ψ, fun z _ =>
    NumberField.TateGlobal.ideleNorm_pos z⟩
  exact AutomorphicForm.CuspidalSpectrum.memLp_weightedMeasure_of_mem F hΦ₀ σ φ.2.1.1.1

-- Zone B: the subrepresentation datum.
--
-- A lift whose agreement is only known `∀ ∃` is a lift; the top and bottom conditions are
-- closed subrepresentations; and two closed conditions meet.
example {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(AutomorphicForm.CuspidalSpectrum.cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ]
      ↥(AutomorphicForm.CuspidalSpectrum.cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ φ : ↥(AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule F Φ₀ ξ),
      ∃ h : op φ ∈ AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule F Φ₀ ξ,
        S (AutomorphicForm.CuspidalSpectrum.toCuspSubcarrier F hΦ₀ σ ξ φ) =
          AutomorphicForm.CuspidalSpectrum.toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩) :
    AutomorphicForm.CuspidalSpectrum.IsCuspLift F hΦ₀ σ ξ op S ∧
      AutomorphicForm.CuspidalSpectrum.IsClosedCuspSubrep F hΦ₀ σ ξ
        (⊤ ⊓ ⊤ : Submodule ℂ
          ↥(AutomorphicForm.CuspidalSpectrum.cuspSubcarrier F hΦ₀ σ ξ)) :=
  ⟨AutomorphicForm.CuspidalSpectrum.isCuspLift_of_forall_exists F hΦ₀ σ ξ op S hS,
    AutomorphicForm.CuspidalSpectrum.IsClosedCuspSubrep.inf F
      (AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_top F hΦ₀ σ ξ)
      (AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_top F hΦ₀ σ ξ)⟩

-- Zone C: B1, the modulus of an idèle-class character is a power of the idèle norm.
--
-- The exponent the norm-exponent theorem produces is read together with the strict positivity
-- of the idèle norm, which is what every later `rpow` comparison needs.
example (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 F) F μ)
    (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 F) F)ˣ,
      ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F x ^ σ ∧
        0 < NumberField.TateGlobal.ideleNorm F x := by
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F μ hμ hc
  exact ⟨σ, fun x => ⟨hσ x, NumberField.TateGlobal.ideleNorm_pos x⟩⟩

-- Zone D: C1, a slab fundamental domain exists, and it carries the weighted-`L²` transfer.
--
-- The domain `C1` produces is fed straight into `memLp_weightedMeasure_of_mem`, at the very
-- `α`, `β` it was produced for.
example (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
      (_ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀),
      ∀ φ ∈ AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule F Φ₀ ξ,
        MemLp φ 2 (AutomorphicForm.CuspidalSpectrum.weightedMeasure F Φ₀ σ) := by
  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  exact ⟨α, β, Φ₀, hΦ₀, fun φ hφ =>
    AutomorphicForm.CuspidalSpectrum.memLp_weightedMeasure_of_mem F hΦ₀ σ hφ.1.1.1⟩

-- Zone E: C2, a Hecke-isotypic cusp form is a weighted-`L²` member on any slab domain.
--
-- The inclusion at the production pins of a centre-cut cover is composed with the carrier's
-- bounded-weight transfer, so the isotypic submodule lands in the weighted space.
example (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : AutomorphicForm.SiegelCovering.CoversModCentre F
      (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : AutomorphicForm.HeckeEigensystem F ℂ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) :
    ∀ φ ∈ AutomorphicForm.isotypicCuspSubmodule F
        (AutomorphicForm.productionPinsOf F
          (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
          (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓
            AutomorphicForm.finiteAdelicGL2Subgroup F)
          (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v)
          (NumberField.AdelicBox.adelicBox F)) ξ N S Ψ,
      MemLp φ 2 (AutomorphicForm.CuspidalSpectrum.weightedMeasure F Φ₀ σ) := by
  intro φ hφ
  exact AutomorphicForm.CuspidalSpectrum.memLp_weightedMeasure_of_mem F hΦ₀ σ
    (AutomorphicForm.CuspidalSpectrum.isotypicCuspSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T
      hd hcov ξ N S Ψ hΦ₀ hφ).1.1.1

-- Zone F: C3, the same for the `K`-finite cuspidal submodule.
--
-- The `K`-finite row keeps the wrapper's `0 < c` and `0 < d₁`; both are supplied here and the
-- resulting inclusion is again composed with the weighted-`L²` transfer.
example (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : AutomorphicForm.SiegelCovering.CoversModCentre F
      (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) :
    ∀ φ ∈ AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule F
        (AutomorphicForm.productionPinsOf F
          (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
          (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓
            AutomorphicForm.finiteAdelicGL2Subgroup F)
          (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v)
          (NumberField.AdelicBox.adelicBox F)) ξ,
      MemLp φ 2 (AutomorphicForm.CuspidalSpectrum.weightedMeasure F Φ₀ σ) := by
  intro φ hφ
  exact AutomorphicForm.CuspidalSpectrum.memLp_weightedMeasure_of_mem F hΦ₀ σ
    (AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T
      hc hd₁ hd hcov ξ hΦ₀ hφ).1.1.1

-- Zone G: C4, `toCarrier` is injective on continuous members.
--
-- A continuous member killed in the carrier is the zero *function*, so its value at every point
-- vanishes — the form the almost-everywhere statements are upgraded to.
example {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ AutomorphicForm.CuspidalSpectrum.contMemberSubmodule F Φ₀ ξ)
    (h0 : AutomorphicForm.CuspidalSpectrum.toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = 0) :
    ∀ x, φ x = 0 := by
  have h := AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ φ hφ h0
  simpa using congrFun h

-- Zone H: C5, the modulus exponent of a continuous automorphic form.
--
-- The exponent `C5` produces is read back on the unit group through the gate's
-- `hasModulus_iff_units`, which is the form the carrier's rows consume it in.
example (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (AutomorphicForm.productionPinsOf F D
      (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup F)
      (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v)
      (NumberField.AdelicBox.adelicBox F)) ξ φ)
    (hφc : Continuous φ) (hφ0 : φ ≠ 0) :
    ∃ σ : ℝ, ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F z ^ σ := by
  obtain ⟨σ, hσ⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous F D ξ φ
      hφ hφc hφ0
  exact ⟨σ, (AutomorphicForm.CuspidalSpectrum.hasModulus_iff_units F ξ σ).mp hσ⟩

-- Zone I: D1, unit-norm right translation on the carrier.
--
-- Right translation by an idèle-norm-one `y` keeps a continuous member in the submodule and is
-- unitary for the weighted pairing against the inverse translate; the translate's weighted-`L²`
-- membership is read off through the carrier's bounded-weight transfer.
example {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ AutomorphicForm.CuspidalSpectrum.contMemberSubmodule F Φ₀ ξ)
    (hψ : ψ ∈ AutomorphicForm.CuspidalSpectrum.contMemberSubmodule F Φ₀ ξ)
    (y : AdelicGL2 (𝓞 F) F)
    (hy : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) = 1) :
    MemLp (AutomorphicForm.CuspidalConstituent.rightTranslate F y φ) 2
        (AutomorphicForm.CuspidalSpectrum.weightedMeasure F Φ₀ σ) ∧
      AutomorphicForm.CuspidalSpectrum.pairing F Φ₀ σ
          (AutomorphicForm.CuspidalConstituent.rightTranslate F y φ) ψ =
        AutomorphicForm.CuspidalSpectrum.pairing F Φ₀ σ φ
          (AutomorphicForm.CuspidalConstituent.rightTranslate F y⁻¹ ψ) := by
  obtain ⟨h1, -, h3⟩ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
      F hΦ₀ σ ξ φ ψ hφ hψ y hy
  exact ⟨AutomorphicForm.CuspidalSpectrum.memLp_weightedMeasure_of_mem F hΦ₀ σ h1.1, h3⟩

-- Zone J: D2, the slab bound over an ample centre-cut cover.
--
-- The carry-forward headline, applied at the wrapper's binders to a continuous member of the
-- carrier: the same constant `C` bounds the weighted `L²` mass on the slab fundamental domain by
-- its mass on the finite union of centre-cut Siegel translates.
example (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ)
    (hcov : AutomorphicForm.SiegelCovering.CoversModCentre F
      (⋃ x ∈ T, (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain F α β Φ₀)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ AutomorphicForm.CuspidalSpectrum.contMemberSubmodule F Φ₀ ξ) :
    ∃ C : ℝ,
      ∫⁻ x in Φ₀, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ENNReal.ofReal C *
          ∫⁻ x in ⋃ x ∈ T,
              (· * x) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
      F c u d₁ d₂ κ T hd hκ hcov ξ hΦ₀
  exact ⟨C, hC φ
    ((AutomorphicForm.CuspidalSpectrum.mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1).1 hφ.2⟩

end AutomorphicFormSetAF1Consumer
