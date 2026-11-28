import FLTForHuman.AutomorphicForm.Adelic.WhittakerSmoothSummability
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisensteinWhittakerSummability
import FLTForHuman.AutomorphicForm.Adelic.PolyDecay
import FLTForHuman.NumberTheory.AdelicFourier.FourierInversion
import FLTForHuman.NumberTheory.AdelicFourier.PoissonNormalized
import FLTForHuman.AlgebraicCurve.Differential.FreeAlgebraLift
import FLTForHuman.AutomorphicForm.Adelic.AddCharLocalComponents

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicFourier
  NumberField.AdelicHaar MeasureTheory AutomorphicForm
open scoped Classical NNReal nonZeroDivisors

namespace SetAF112Consumer

/-! ## Zone 1 — the two Kf-smooth Whittaker rows are one statement (order A)

Order A's second row gives integrability of every coefficient *and* summability of the series; its first
row states absolute summability. The first is the stronger form: a summable family of complex numbers is
absolutely summable (`Summable.norm`). So a consumer that has the pair's hypotheses gets the norm form
from the integrability form, without a second application of the archimedean engine. -/

theorem summable_norm_of_integrable_and_summable
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ)
    (harch : ∀ g : AdelicGL2 (𝓞 K) K, ContDiff ℝ (Module.finrank ℚ K + 1)
      (fun z : mixedEmbedding.mixedSpace K =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))) :
    ∀ g : AdelicGL2 (𝓞 K) K,
      Summable (fun α : K => ‖whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g‖) :=
  fun g => (whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
    K D U gen ψ hψ φ hleft hsm harch).2 g |>.norm

/-! ## Zone 2 — the Bruhat–Eisenstein hypotheses feed the polynomial-decay engine (orders B, AF111A)

Order B's row assumes `1 < s.re` among its hypotheses; the pin's polynomial-decay estimate
(`PolyDecay.lean`, SET-AF111A) needs only `1/2 < s.re` and the same induced section and continuity.
Composed, the two give the decay estimate *at order B's hypothesis bundle*: the input the summability
proof consumes, available to any consumer that has B's hypotheses. -/

theorem exists_polyDecay_of_bruhatEisenstein_hypotheses
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by
  intro α hα μc νc hμ hν ψ hψ s hs φ hφ hφK hφf hφc g N
  exact norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary F
    hα μc νc hμ hν ψ hψ s (lt_trans (by norm_num) hs) φ hφ hφK hφc g N

/-! ## Zone 3 — the double transform has order four (order C, both rows)

The inversion row and the Schwartz row compose: applying the inversion to a locally constant compactly
supported `h` gives the second transform; applying the Schwartz row twice keeps `h` in that space through
two transforms; applying the inversion twice more gives `𝓕⁴ h = c² • h`, the four-fold form a
Poisson-summation consumer uses. -/

theorem fourierIntegral_four_fold
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (y : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
          (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
            (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h))) y
      = (((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
            * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2) *
          ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
            * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2)) • h y := by
  set ψf := ψ.compAddMonoidHom
    (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf
  set c : ℂ := ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ)
    * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2) with hc
  have e1 : ∀ z, fourierIntegral ψf ν (fourierIntegral ψf ν h) z = c • h (-z) := fun z =>
    fourierIntegral_fourierIntegral_finiteAdeleRing_eq (F := F) ν hψ hψ_inf hlc hcs z
  have h2 : IsLocallyConstant (fourierIntegral ψf ν h) ∧ HasCompactSupport (fourierIntegral ψf ν h) :=
    isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing (F := F) ν hψ hψ_inf hlc hcs
  have h3 : IsLocallyConstant (fourierIntegral ψf ν (fourierIntegral ψf ν h)) ∧
      HasCompactSupport (fourierIntegral ψf ν (fourierIntegral ψf ν h)) :=
    isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing (F := F) ν hψ hψ_inf h2.1 h2.2
  have e3 : ∀ z, fourierIntegral ψf ν (fourierIntegral ψf ν (fourierIntegral ψf ν
      (fourierIntegral ψf ν h))) z = c • (fourierIntegral ψf ν (fourierIntegral ψf ν h)) (-z) := fun z =>
    fourierIntegral_fourierIntegral_finiteAdeleRing_eq (F := F) ν hψ hψ_inf h3.1 h3.2 z
  calc fourierIntegral ψf ν (fourierIntegral ψf ν (fourierIntegral ψf ν
        (fourierIntegral ψf ν h))) y
      = c • (fourierIntegral ψf ν (fourierIntegral ψf ν h)) (-y) := e3 y
    _ = c • (c • h (-(-y))) := by rw [e1 (-y)]
    _ = (c * c) • h y := by rw [neg_neg, smul_smul]

/-! ## Zone 4 — the differential lift's contrapositive (order E)

Order E's row says a vanishing `Pic0` free-algebra lift kills every regular differential. Read
contrapositively: a regular differential the differential lift does not kill certifies that the `Pic0`
lift does not vanish — the form a consumer uses to *produce* nonzero correspondence classes. -/

section DifferentialLift

open AlgebraicCurve

theorem lift_correspondence_ne_zero_of_exists_differential_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    {ω : regularDifferentials K F}
    (h : MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω ≠ 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p ≠ 0 := by
  intro hp
  exact h (Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero
    K F hfg F' φ ψ hφ hψ hFI hfin hN p hp ω ω.property)

end DifferentialLift

end SetAF112Consumer
