/-
  The Fourier inversion formula for the vector Fourier integral on a finite
  dimensional real vector space `V` with a Haar measure `μ` and a nondegenerate
  bilinear form `B`:

      `𝓕_B.flip (𝓕_B f) x = (μ (fundamentalDomain b)) ^ 2 / |det (B (b i) (b j))| * f (-x)`

  and the companion fact that `𝓕_B f` is again the coercion of a Schwartz function.

  The pin's `PiFourier` block is folded into the object's own `VectorFourier` namespace here
  (its declarations are `VectorFourier.piFourierIntegral*`); no pin label is left.

  The ports of the pin leaves `VectorFourier.fourierIntegral_flip_fourierIntegral_eq`
  (235 pin lines) and `SchwartzMap.exists_coe_eq_vectorFourierIntegral` (180 pin
  lines), together with the statements of their `Theorems/` wrappers. They are one
  module because the second's proof consumes the first's private prelude verbatim:
  both pin `S_` files carry the identical `PiFourier` block (the coordinate-space
  integral `piFourierIntegral`, the Euclidean identification, and the change of
  variables `vectorFourierIntegral_eq_smul_piFourierIntegral`), and a transcription
  keeps one copy.

  It also carries the third Fourier-family leaf, `AddChar.exists_continuousLinearMap_fourierChar_eq`
  (45 pin lines): a continuous character `E → Circle` of a real normed space is
  `x ↦ 𝐞 (l x)` for a continuous linear functional `l`. That is the character-side
  converse of the `𝐞`-integral used above, and it is a sub-80-line entry, so it
  rides with this module under order §5. Its mathematics: `Circle.exp` is a
  covering map, so `χ` lifts to a continuous `F : E → ℝ`; the lift is additive
  (uniqueness of lifts applied to `z ↦ F (z + y) - F y`), hence a continuous
  additive functional, and `𝐞 = exp ∘ (2π)⁻¹ ·`.

  The mathematics: in a basis `b` of `V` the vector Fourier integral of `f` at `y`
  is `μ (fundamentalDomain b)` times the coordinate integral of `f ∘ b.equivFun.symm`
  against `∑ i, v i * B (b i) y`; so `𝓕_B.flip 𝓕_B` is a coordinate-space Fourier
  inversion conjugated by the matrix `M = (B (b i) (b j))`, and the change of
  volume under `M` contributes `|det M|⁻¹`, whence the stated constant.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has Fourier inversion on
  `EuclideanSpace` (`MeasureTheory.Integral.FourierTransform.fourierInv_fourier_eq`,
  `Real.fourierInv_eq_fourier_neg`) and on general finite-dimensional inner product
  spaces, but not this statement — `rg -n "fourierIntegral_flip"`,
  `rg -n "exists_coe_eq_vectorFourierIntegral"` and `rg -n
  "exists_schwartz_piFourierIntegral"` over `Mathlib/` find nothing, and
  `VectorFourier.fourierIntegral` has no inversion theorem at all. The ingredients
  (`Real.map_linearMap_volume_pi_eq_smul_volume_pi`, `Measure.addHaarScalarFactor`,
  `ZSpan.map_fundamentalDomain`, `ZSpan.fundamentalDomain_pi_basisFun`,
  `SchwartzMap.compCLMOfContinuousLinearEquiv`, `PiLp.volume_preserving_ofLp`) are
  imported, not restated.

  The third leaf's mathlib-first check: no equivalent statement in mathlib
  (`rg -n "exists_continuousLinearMap_fourierChar_eq|forall.*fourierChar_eq"` over
  `Mathlib/` finds nothing; mathlib has the forward direction only, that `𝐞 ∘ l` is
  a continuous character). Ingredients imported: `Circle.isCoveringMap_exp`,
  `IsCoveringMap.existsUnique_continuousMap_lifts`, `AddMonoidHom.toRealLinearMap`,
  `Real.fourierChar_apply'`.

  Drift:
  * the pin's three file-wide options (`linter.unusedSectionVars false`,
    `linter.unusedVariables false`, `maxHeartbeats 3200000`) are all dropped: the
    two headlines elaborate inside the 200,000 edit-loop budget here, and the one
    residual unused-variable warning — the pin's `hB : B.Nondegenerate` binder of
    the helper `vectorFourierIntegral_eq_smul_piFourierIntegral`, which is in the
    checked statement but not used by its proof — is handled with a
    **declaration-scoped** `set_option linter.unusedVariables false in` (renaming
    the binder would rewrite a checked statement);
  * the two headlines are written with the wrappers' explicit `{V} [ … ]` binder
    block instead of the pin's section variables, because the wrapper's text is the
    statement authority;
  * `SchwartzMap.smul_apply` → `_root_.smul_apply` and
    `ContinuousLinearMap.smul_apply` → `smul_apply` (both deprecated spellings);
  * `haveI : ν.IsAddHaarMeasure` → `have` (linter).

  spec-pin: Theorems/Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.lean
  spec-pin: P2M/Sol/S_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.lean
  spec-pin: Theorems/Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral.lean
  spec-pin: P2M/Sol/S_SchwartzMap_exists_coe_eq_vectorFourierIntegral.lean
  spec-pin: Theorems/Thm_AddChar_exists_continuousLinearMap_fourierChar_eq.lean
  spec-pin: P2M/Sol/S_AddChar_exists_continuousLinearMap_fourierChar_eq.lean
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.RealVectorSpace

set_option autoImplicit false

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace SchwartzMap

noncomputable section

namespace VectorFourier

variable {d : Type*} [Fintype d]

def piFourierIntegral (f : (d → ℝ) → ℂ) (ξ : d → ℝ) : ℂ :=
  ∫ v, f v * (𝐞 (-∑ i, v i * ξ i) : ℂ) ∂(volume : Measure (d → ℝ))

abbrev euclideanToPi : EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)

theorem piFourierIntegral_eq_fourier_euclidean (g : (d → ℝ) → ℂ) (ξ : d → ℝ) :
    piFourierIntegral g ξ
      = 𝓕 (fun v : EuclideanSpace ℝ d => g (ofLp v)) (toLp 2 ξ) := by
  unfold piFourierIntegral
  rw [Real.fourier_eq]
  rw [← MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp d)
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  have hinner : ∑ i, (ofLp v) i * ξ i = ⟪v, toLp 2 ξ⟫_ℝ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [← hinner, mul_comm]

theorem exists_schwartz_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) :
    ∃ g : SchwartzMap (d → ℝ) ℂ, ∀ ξ, piFourierIntegral (⇑h) ξ = g ξ := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  let g' : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕 h'
  let g : SchwartzMap (d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)).symm g'
  refine ⟨g, fun ξ => ?_⟩
  rw [piFourierIntegral_eq_fourier_euclidean]
  simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rfl

theorem piFourierIntegral_piFourierIntegral (h : SchwartzMap (d → ℝ) ℂ) (u : d → ℝ) :
    piFourierIntegral (piFourierIntegral (⇑h)) u = h (-u) := by
  let h' : SchwartzMap (EuclideanSpace ℝ d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := d)) h
  have hh' : ∀ v, h' v = h (ofLp v) := fun v => by
    simp only [h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl

  have h1 : (fun v : EuclideanSpace ℝ d => piFourierIntegral (⇑h) (ofLp v)) = 𝓕 (⇑h') := by
    funext v
    rw [piFourierIntegral_eq_fourier_euclidean, WithLp.toLp_ofLp]
    congr 1
  rw [piFourierIntegral_eq_fourier_euclidean, h1]

  have h2 := Real.fourierInv_eq_fourier_neg (𝓕 (⇑h')) (-(toLp 2 u))
  rw [neg_neg] at h2
  rw [← h2, h'.continuous.fourierInv_fourier_eq h'.integrable]
  · rw [hh', ← WithLp.toLp_neg]
  · exact SchwartzMap.integrable (𝓕 h' : SchwartzMap (EuclideanSpace ℝ d) ℂ)

end VectorFourier

section BFourier

open VectorFourier LinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

set_option linter.unusedVariables false in
theorem vectorFourierIntegral_eq_smul_piFourierIntegral
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) (f : V → ℂ) (y : V) :
    VectorFourier.fourierIntegral 𝐞 μ B f y
      = ((μ.real (ZSpan.fundamentalDomain b) : ℝ) : ℂ)
        * piFourierIntegral (fun v => f (b.equivFun.symm v)) (fun i => B (b i) y) := by
  classical
  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]
  have hA' : ∀ v, b.equivFun.symm v = A v := fun v => rfl

  set ν : MeasureTheory.Measure V := Measure.map A volume with hν_def
  have : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  set c : NNReal := Measure.addHaarScalarFactor μ ν with hc_def
  have hμν : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hνF : ν (ZSpan.fundamentalDomain b) = 1 := by
    rw [hν_def, Measure.map_apply A.continuous.measurable (ZSpan.fundamentalDomain_measurableSet b),
      ← A.image_symm_eq_preimage]
    have : (A.symm : V → ι → ℝ) '' ZSpan.fundamentalDomain b
        = ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) := by
      rw [show ((A.symm : V → ι → ℝ)) = ⇑(b.equivFun : V ≃ₗ[ℝ] ι → ℝ) from rfl,
        ZSpan.map_fundamentalDomain]
      congr 1
      ext i j
      simp [Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [this, ZSpan.fundamentalDomain_pi_basisFun]
    simp [volume_pi, Measure.pi_pi, Real.volume_Ico]
  have hμF : μ.real (ZSpan.fundamentalDomain b) = c := by
    rw [Measure.real, hμν, Measure.smul_apply, hνF, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_toReal]

  have hpair : ∀ v : ι → ℝ, B (A v) y = ∑ i, v i * B (b i) y := fun v => by
    rw [hA, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

  have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w y)) : ℂ)) (A v)
      = ∫ w, f w * (𝐞 (-(B w y)) : ℂ) ∂ν := by
    have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun w : V => f w * (𝐞 (-(B w y)) : ℂ)) (μ := volume)
    simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
    rw [hν_def, this]
  rw [hμF, VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  congr 1
  have h3 : ∫ x, 𝐞 (-(B x y)) • f x ∂ν = ∫ w, f w * (𝐞 (-(B w y)) : ℂ) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp only [Circle.smul_def, smul_eq_mul, mul_comm])
  rw [h3, ← h2]
  unfold piFourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [hA', hpair]

end BFourier

section Flip

open VectorFourier LinearMap

theorem VectorFourier.fourierIntegral_flip_fourierIntegral_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (f : 𝓢(V, ℂ)) (x : V) :
    VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = ((μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| : ℝ)
        * f (-x) := by
  classical
  set cR : ℝ := μ.real (ZSpan.fundamentalDomain b) with hcR
  set M : Matrix ι ι ℝ := Matrix.of fun i j => B (b i) (b j) with hM
  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]
  have hA' : ∀ v, b.equivFun.symm v = A v := fun v => rfl

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (A v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

  have hMdet : M.det ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
    convert this using 2
    ext i j
    rw [hM, Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply]

  have hinner : ∀ w : ι → ℝ, VectorFourier.fourierIntegral 𝐞 μ B f (A w)
      = (cR : ℂ) * piFourierIntegral (⇑h) (M.mulVec w) := by
    intro w
    have e1 : (fun v => f (b.equivFun.symm v)) = ⇑h := funext fun v => by rw [hh, hA']
    have e2 : (fun i => B (b i) (A w)) = M.mulVec w := funext fun i => by
      simp only [hA, map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, hM, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [vectorFourierIntegral_eq_smul_piFourierIntegral μ B hB b (⇑f) (A w), e1, e2]

  set u : ι → ℝ := A.symm x with hu
  have hx : x = A u := (A.apply_symm_apply x).symm
  have houter : VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = (cR : ℂ) * piFourierIntegral
          (fun w => VectorFourier.fourierIntegral 𝐞 μ B f (A w)) (fun i => B.flip (b i) x) := by
    rw [vectorFourierIntegral_eq_smul_piFourierIntegral μ B.flip hB.flip b _ x]
    rfl
  have hflipcoord : (fun i => B.flip (b i) x) = M.transpose.mulVec u := by
    funext i
    show B x (b i) = _
    rw [hx, hA, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, hM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  let Φ : (ι → ℝ) → ℂ := fun ξ => piFourierIntegral (⇑h) ξ * (𝐞 (-∑ i, ξ i * u i) : ℂ)
  have hΦ : ∀ w : ι → ℝ, (VectorFourier.fourierIntegral 𝐞 μ B f (A w))
        * (𝐞 (-∑ i, w i * (M.transpose.mulVec u) i) : ℂ) = (cR : ℂ) * Φ (M.mulVec w) := by
    intro w
    have hsum : ∑ i, w i * (M.transpose.mulVec u) i = ∑ i, (M.mulVec w) i * u i := by
      show w ⬝ᵥ (M.transpose.mulVec u) = (M.mulVec w) ⬝ᵥ u
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hinner, mul_assoc, hsum]

  have hcov : ∫ w : ι → ℝ, Φ (M.mulVec w) = |M.det|⁻¹ • ∫ ξ, Φ ξ := by
    have hdet : LinearMap.det (Matrix.toLin' M) ≠ 0 := by rwa [LinearMap.det_toLin']
    have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
    have hmeas : AEMeasurable (⇑(Matrix.toLin' M)) (volume : Measure (ι → ℝ)) :=
      (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable

    obtain ⟨g₀, hg₀⟩ := exists_schwartz_piFourierIntegral h
    have hΦc : Continuous Φ := by
      have : Φ = fun ξ => g₀ ξ * (𝐞 (-∑ i, ξ i * u i) : ℂ) := by
        funext ξ; simp only [Φ, hg₀]
      rw [this]
      fun_prop
    have : ∫ w : ι → ℝ, Φ (M.mulVec w) = ∫ w, Φ (Matrix.toLin' M w) := by
      simp only [Matrix.toLin'_apply]
    rw [this, ← integral_map hmeas hΦc.aestronglyMeasurable, hmap, integral_smul_measure,
      LinearMap.det_toLin', ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

  rw [houter, hflipcoord]
  unfold piFourierIntegral
  simp_rw [hΦ]
  rw [integral_const_mul, hcov]
  change (cR : ℂ) * ((cR : ℂ) * (|M.det|⁻¹ • piFourierIntegral (piFourierIntegral (⇑h)) u)) = _
  rw [piFourierIntegral_piFourierIntegral h u, hh, map_neg, ← hx, Complex.real_smul]
  push_cast
  ring

namespace SchwartzMap

theorem exists_coe_eq_vectorFourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f := by
  classical

  let ι := Module.Free.ChooseBasisIndex ℝ V
  let b : Module.Basis ι ℝ V := Module.Free.chooseBasis ℝ V
  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  let T : V ≃L[ℝ] (ι → ℝ) := bd.equivFun.toContinuousLinearEquiv
  have hT : ∀ y i, T y i = B (b i) y := fun y i => by
    show bd.repr y i = B (b i) y
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (b.equivFun.symm v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_schwartz_piFourierIntegral h
  refine ⟨((μ.real (ZSpan.fundamentalDomain b) : ℝ) : ℂ)
      • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T g₀, ?_⟩
  funext y
  have e1 : (fun v => f (b.equivFun.symm v)) = ⇑h := funext fun v => (hh v).symm
  have e2 : (fun i => B (b i) y) = T y := funext fun i => (hT y i).symm
  rw [vectorFourierIntegral_eq_smul_piFourierIntegral μ B hB b (⇑f) y, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul, ← hg₀, e1, e2]

end SchwartzMap

end Flip

section AddChar

namespace AddChar

theorem exists_continuousLinearMap_fourierChar_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by

  obtain ⟨F, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts (⟨χ, hχ⟩ : C(E, Circle)) 0 0
      (by simp)
  have hF : ∀ x, Circle.exp (F x) = χ x := fun x => congrFun hFlift x

  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    let G : C(E, ℝ) := ⟨fun z => F (z + y) - F y, by fun_prop⟩
    have hG : G = F := by
      refine huniq G ⟨by simp [G], ?_⟩
      funext z
      simp only [Function.comp_apply, ContinuousMap.coe_mk, G, Circle.exp_sub, hF,
        AddChar.map_add_eq_mul, mul_div_cancel_right]
    have := congrArg (fun (H : C(E, ℝ)) => H x) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith

  let Fhom : E →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  let l₀ : E →L[ℝ] ℝ := Fhom.toRealLinearMap F.continuous
  refine ⟨(2 * π)⁻¹ • l₀, fun x => ?_⟩
  rw [Real.fourierChar_apply', smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
  exact (hF x).symm

end AddChar

end AddChar
