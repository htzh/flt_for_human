/-
  Poisson summation on a `ℤ`-lattice, in the two forms the cusp-counting argument
  needs: the translated residue sum of a Schwartz function equals the covolume
  inverse times the dual-lattice sum of its Fourier transform, twisted by the
  character `e (B t y)`; and that dual sum is summable.

      `∑' x : L, f (t + x) = covolume L μ⁻¹ * ∑' y : dualSubmodule B.flip L,
         fourierIntegral e μ B f y * e (B t y)`

  The port of the two pin leaves

      `ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral` and
      `ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule`

  (`P2M/Sol/S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral.lean`,
  229 pin lines, and
  `P2M/Sol/S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule.lean`,
  221 pin lines), together with the statements of their `Theorems/` wrappers. The
  pin's `S_` development is `section LatticeTranslate`/`section LatticeSummable` at
  the root namespace; kept here with the wrappers' inline binders and the pin's
  short names. It is a faithful transcription: no statement is weakened, no route
  is generalised, and the pin's proofs are carried verbatim (`spec/check_port.py`
  diffs both public declarations below against the four files named here).

  Both pin files re-declare the `PiPoissonSummation` engine (`intVec`,
  `piFourierIntegral`, `euclideanToPi`, `piFourierIntegral_eq_fourier_euclidean`,
  `coe_basisFun_equivFun_symm`, `finrank_span_basisFun`,
  `summable_norm_intVec_inv_pow`, `summable_norm_schwartz_intVec`,
  `summable_piFourierIntegral_schwartz_intVec`) verbatim, because in the pin the
  first only imports the `Theorems/` wrapper and not the `S_` file. That block is
  written once, in `FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean` (where it
  is stated and checked), and imported here rather than copied (playbook §5); the
  first node's proof is exactly the pin's use of
  `PiPoissonSummation.SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral`.

  The mathematics, in two steps. Choose a `ℤ`-basis `bZ` of `L` and its real
  extension `b`; conjugating by `A = b.equivFun.symm` puts the lattice in the form
  `ℤ^ι`, so the `L`-sum becomes the `ℤ^ι`-sum of `piFourierIntegral`, and Poisson
  summation in `ι` variables (`tsum_add_intVec_eq_tsum_piFourierIntegral`) rewrites
  it as a dual sum. The dual lattice is spanned by `B.flip.dualBasis hB.flip b`
  (`dualSubmodule_span_of_basis`), the pairing identity `hpair` evaluates the
  character, and the change of measure `μ = c • (A_* volume)` identifies the scalar
  `c` with the covolume (`covolume_eq_measure_fundamentalDomain`,
  `fundamentalDomain b` mapping to the unit cube). Summability is Schwartz decay:
  the transformed summand is bounded by `c` times `summable_norm_schwartz_intVec g`,
  the Schwartz function `g` whose Fourier transform is `f`.

  Assumes: `FLTForHuman.Analysis.Fourier.PoissonSummationPi` (the Poisson-summation
  engine and the two headlines it states) and mathlib `v4.34.0`.

  spec-pin: Theorems/Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral.lean
  spec-pin: Theorems/Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule.lean
  spec-pin: P2M/Sol/S_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral.lean
  spec-pin: P2M/Sol/S_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule.lean
-/

import FLTForHuman.Analysis.Fourier.PoissonSummationPi
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp
open scoped FourierTransform InnerProductSpace SchwartzMap

noncomputable section

open P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.PiPoissonSummation LinearMap

/-- Poisson summation on a `ℤ`-lattice: the translated `L`-sum of a Schwartz
function is the covolume inverse times the twisted dual-lattice sum of its Fourier
transform. -/
theorem ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    ∑' x : L, f (t + x) =
      (ZLattice.covolume L μ : ℂ)⁻¹ *
        ∑' y : LinearMap.BilinForm.dualSubmodule B.flip L,
          VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by
  classical

  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let bZ : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let b : Module.Basis ι ℝ V := bZ.ofZLatticeBasis ℝ L
  have hb : ∀ i, b i = (bZ i : V) := fun i => bZ.ofZLatticeBasis_apply ℝ L i

  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]
  have hA_intVec : ∀ n : ι → ℤ, A (intVec n) = ((bZ.equivFun.symm n : L) : V) := fun n => by
    rw [hA, Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, hb]
    exact Int.cast_smul_eq_zsmul ℝ (n i) _

  set s : ι → ℝ := A.symm t with hs
  have ht : t = A s := (A.apply_symm_apply t).symm

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (A v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

  have hLHS : ∑' x : L, f (t + x) = ∑' n : ι → ℤ, h (s + intVec n) := by
    rw [← bZ.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hh, A.map_add, ← ht, hA_intVec]
    rfl

  have hP : ∑' n : ι → ℤ, h (s + intVec n)
      = ∑' m : ι → ℤ, piFourierIntegral h (intVec m) * (𝐞 (∑ i, (m i : ℝ) * s i) : ℂ) :=
    SchwartzMap.tsum_add_intVec_eq_tsum_piFourierIntegral h s

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
  have hμF : μ (ZSpan.fundamentalDomain b) = c := by
    rw [hμν, Measure.smul_apply, hνF, ENNReal.smul_def, smul_eq_mul, mul_one]
  have hcov : ZLattice.covolume L μ = μ.real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain bZ μ)
  have hc : (c : ℝ) = ZLattice.covolume L μ := by
    rw [hcov, Measure.real, hμF, ENNReal.coe_toReal]
  have hc_ne : (c : ℝ) ≠ 0 := by rw [hc]; exact ZLattice.covolume_ne_zero L μ

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  have hbd : ∀ i j, B (b j) (bd i) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB.flip b i j
    simpa only [bd, LinearMap.BilinForm.flip_apply] using this
  have hLd : LinearMap.BilinForm.dualSubmodule B.flip L = span ℤ (Set.range bd) := by
    rw [← bZ.ofZLatticeBasis_span ℝ L]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B.flip hB.flip b
  let ψ : (ι → ℤ) ≃ LinearMap.BilinForm.dualSubmodule B.flip L :=
    ((bd.restrictScalars ℤ).equivFun.symm.toEquiv).trans (LinearEquiv.ofEq _ _ hLd.symm).toEquiv
  have hψ : ∀ k : ι → ℤ, ((ψ k : _) : V) = ∑ i, (k i : ℝ) • bd i := fun k => by
    simp only [ψ, Equiv.trans_apply, LinearEquiv.coe_toEquiv, LinearEquiv.coe_ofEq_apply]
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, Module.Basis.restrictScalars_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (k i) _).symm

  have hpair : ∀ (v : ι → ℝ) (k : ι → ℤ),
      B (A v) (∑ i, (k i : ℝ) • bd i) = ∑ i, v i * (k i : ℝ) := fun v k => by
    rw [hA]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hbd, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  have hterm : ∀ k : ι → ℤ, piFourierIntegral h (intVec k)
      = ((ZLattice.covolume L μ : ℝ) : ℂ)⁻¹ * VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) := by
    intro k
    have h1 : piFourierIntegral h (intVec k)
        = ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v) := by
      unfold piFourierIntegral
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [hh, hψ, hpair, intVec]
    have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v)
        = ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (μ := volume)
      simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
      rw [hν_def, this]
    have h3 : VectorFourier.fourierIntegral 𝐞 μ B f (ψ k)
        = (c : ℝ) • ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      rw [VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [Circle.smul_def, smul_eq_mul, mul_comm]
    rw [h1, h2, h3, ← hc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hc_ne, Complex.ofReal_one, one_mul]

  have hphase : ∀ k : ι → ℤ,
      (𝐞 (∑ i, (k i : ℝ) * s i) : ℂ) = (𝐞 (B t (ψ k)) : ℂ) := fun k => by
    rw [ht, hψ, hpair]
    congr 2
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  rw [hLHS, hP, ← ψ.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [hterm, hphase, mul_assoc]

/-- The twisted dual-lattice sum of the Fourier transform of a Schwartz function is
summable. -/
theorem ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : 𝓢(V, ℂ)) (t : V) :
    Summable fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
      VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ) := by
  classical

  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let bZ : Module.Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let b : Module.Basis ι ℝ V := bZ.ofZLatticeBasis ℝ L

  let A : (ι → ℝ) ≃L[ℝ] V := b.equivFun.symm.toContinuousLinearEquiv
  have hA : ∀ v : ι → ℝ, A v = ∑ i, v i • b i := fun v => by
    simp only [A, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply]

  let h : SchwartzMap (ι → ℝ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A f
  have hh : ∀ v, h v = f (A v) := fun v => by
    simp only [h, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

  set ν : MeasureTheory.Measure V := Measure.map A volume with hν_def
  have : ν.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  set c : NNReal := Measure.addHaarScalarFactor μ ν with hc_def
  have hμν : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν

  let bd : Module.Basis ι ℝ V := B.flip.dualBasis hB.flip b
  have hbd : ∀ i j, B (b j) (bd i) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB.flip b i j
    simpa only [bd, LinearMap.BilinForm.flip_apply] using this
  have hLd : LinearMap.BilinForm.dualSubmodule B.flip L = span ℤ (Set.range bd) := by
    rw [← bZ.ofZLatticeBasis_span ℝ L]
    exact LinearMap.BilinForm.dualSubmodule_span_of_basis B.flip hB.flip b
  let ψ : (ι → ℤ) ≃ LinearMap.BilinForm.dualSubmodule B.flip L :=
    ((bd.restrictScalars ℤ).equivFun.symm.toEquiv).trans (LinearEquiv.ofEq _ _ hLd.symm).toEquiv
  have hψ : ∀ k : ι → ℤ, ((ψ k : _) : V) = ∑ i, (k i : ℝ) • bd i := fun k => by
    simp only [ψ, Equiv.trans_apply, LinearEquiv.coe_toEquiv, LinearEquiv.coe_ofEq_apply]
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, Module.Basis.restrictScalars_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (k i) _).symm

  have hpair : ∀ (v : ι → ℝ) (k : ι → ℤ),
      B (A v) (∑ i, (k i : ℝ) • bd i) = ∑ i, v i * (k i : ℝ) := fun v k => by
    rw [hA]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hbd, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

  have hterm : ∀ k : ι → ℤ,
      VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) = (c : ℝ) • piFourierIntegral h (intVec k) := by
    intro k
    have h1 : piFourierIntegral h (intVec k)
        = ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v) := by
      unfold piFourierIntegral
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [hh, hψ, hpair, intVec]
    have h2 : ∫ v : ι → ℝ, (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (A v)
        = ∫ w, f w * (𝐞 (-(B w (ψ k))) : ℂ) ∂ν := by
      have := MeasurableEmbedding.integral_map A.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun w : V => f w * (𝐞 (-(B w (ψ k))) : ℂ)) (μ := volume)
      simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at this
      rw [hν_def, this]
    rw [VectorFourier.fourierIntegral, hμν, integral_smul_nnreal_measure, NNReal.smul_def, h1, h2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Circle.smul_def, smul_eq_mul, mul_comm]

  let h' : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)) h
  let g' : SchwartzMap (EuclideanSpace ℝ ι) ℂ := 𝓕 h'
  let g : SchwartzMap (ι → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclideanToPi (d := ι)).symm g'
  have hg : ∀ ξ : ι → ℝ, piFourierIntegral (⇑h) ξ = g ξ := fun ξ => by
    rw [piFourierIntegral_eq_fourier_euclidean h ξ]
    simp only [g, g', h', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rfl

  have hsum : Summable fun k : ι → ℤ =>
      ‖VectorFourier.fourierIntegral 𝐞 μ B f (ψ k) * (𝐞 (B t (ψ k)) : ℂ)‖ := by
    have := (summable_norm_schwartz_intVec g).mul_left (c : ℝ)
    refine this.congr fun k => ?_
    rw [norm_mul, Circle.norm_coe, mul_one, hterm, hg, norm_smul, Real.norm_of_nonneg c.coe_nonneg]
  refine Summable.of_norm ?_
  exact (ψ.summable_iff (f := fun y : LinearMap.BilinForm.dualSubmodule B.flip L =>
    ‖VectorFourier.fourierIntegral 𝐞 μ B f y * (𝐞 (B t y) : ℂ)‖)).mp hsum

end
