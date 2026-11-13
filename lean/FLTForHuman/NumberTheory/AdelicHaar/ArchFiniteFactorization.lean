/-
  The archimedean times finite factorization of the adelic integral.

  For a function on `GL2(A)` that splits as an archimedean factor composed with `glArch` and a finite
  factor composed with `glFin`, its integral against the adelic Haar measure is the product of the two
  integrals: the measure is a scalar times the product of the archimedean and finite measures
  (`exists_map_adelicGLHaar_eq_smul_prod`, SET-AF53's row), and the scalar is absorbed by the
  `glArch`/`glFin` components.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral.lean`
  (201 lines, nineteen public rows), with the statement from the wrapper of the same name.  The pin's
  `Ws1` label is a machine token and is rectified to the word namespace `ArchFiniteFactorization`; the
  prelude rows are public in the pin and stay public here.

  Assumes from earlier modules: `NumberTheory/AdelicHaar/ProductMeasure.lean` (the measure split, this
  row's premise), `NumberTheory/AdelicHaar/PlaceMeasure.lean` and `NumberTheory/AdelicLevel/Level.lean`.
  spec-pin: Theorems/Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral.lean
-/
import FLTForHuman.NumberTheory.AdelicHaar.ProductMeasure
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped NNReal ENNReal Pointwise

namespace ArchFiniteFactorization

section SC

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  have : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : Topology.IsEmbedding (fun a : InfiniteAdeleRing K => ((a, 0) : AdeleRing (𝓞 K) K)) :=
    Topology.IsEmbedding.of_comp (continuous_id.prodMk continuous_const) continuous_fst
      Topology.IsEmbedding.id
  exact hf.secondCountableTopology

theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  have : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have hf : Topology.IsEmbedding (fun b : FiniteAdeleRing (𝓞 K) K => ((0, b) : AdeleRing (𝓞 K) K)) :=
    Topology.IsEmbedding.of_comp (continuous_const.prodMk continuous_id) continuous_snd
      Topology.IsEmbedding.id
  exact hf.secondCountableTopology

theorem secondCountableTopology_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] :
    SecondCountableTopology (GL n R) := by
  have : SecondCountableTopology (Matrix n n R) := inferInstanceAs (SecondCountableTopology (n → n → R))
  have : SecondCountableTopology (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_gl (n : Type) [Fintype n] [DecidableEq n]
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] :
    LocallyCompactSpace (GL n R) := by
  have : LocallyCompactSpace (Matrix n n R) := inferInstanceAs (LocallyCompactSpace (n → n → R))
  have : T2Space (Matrix n n R) := inferInstanceAs (T2Space (n → n → R))
  have : LocallyCompactSpace (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end SC

section Split

variable (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]

def fwd : GL n (AdeleRing (𝓞 K) K) →* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  MonoidHom.prod (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K))
    (Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K))

def glue (a : Matrix n n (InfiniteAdeleRing K)) (b : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    Matrix n n (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 K) K)

omit [DecidableEq n] in
theorem glue_mul (a a' : Matrix n n (InfiniteAdeleRing K)) (b b' : Matrix n n (FiniteAdeleRing (𝓞 K) K)) :
    glue n K a b * glue n K a' b' = glue n K (a * a') (b * b') := by
  ext i j
  simp only [glue, Matrix.mul_apply]
  change (_ : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) = _
  refine Prod.ext ?_ ?_
  · show (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    exact map_sum (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ Finset.univ
  · show (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (∑ x, _) = _
    exact map_sum (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) _ Finset.univ

omit [Fintype n] in
theorem glue_one : glue n K (1 : Matrix n n (InfiniteAdeleRing K)) (1 : Matrix n n (FiniteAdeleRing (𝓞 K) K)) = 1 := by
  ext i j
  change ((1 : Matrix n n (InfiniteAdeleRing K)) i j, (1 : Matrix n n (FiniteAdeleRing (𝓞 K) K)) i j) =
    ((1 : Matrix n n (AdeleRing (𝓞 K) K)) i j)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, Matrix.one_apply_ne h]
    rfl

def bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : GL n (AdeleRing (𝓞 K) K) where
  val := glue n K (p.1 : Matrix n n (InfiniteAdeleRing K)) (p.2 : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  inv := glue n K ((p.1⁻¹ : GL n (InfiniteAdeleRing K)) : Matrix n n (InfiniteAdeleRing K))
    ((p.2⁻¹ : GL n (FiniteAdeleRing (𝓞 K) K)) : Matrix n n (FiniteAdeleRing (𝓞 K) K))
  val_inv := by rw [glue_mul, Units.mul_inv, Units.mul_inv, glue_one]
  inv_val := by rw [glue_mul, Units.inv_mul, Units.inv_mul, glue_one]

theorem fwd_bwd (p : GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K)) : fwd n K (bwd n K p) = p :=
  Prod.ext (Units.ext (Matrix.ext fun _ _ => rfl)) (Units.ext (Matrix.ext fun _ _ => rfl))

theorem bwd_fwd (x : GL n (AdeleRing (𝓞 K) K)) : bwd n K (fwd n K x) = x :=
  Units.ext (Matrix.ext fun _ _ => Prod.ext rfl rfl)

def splitMulEquiv : GL n (AdeleRing (𝓞 K) K) ≃* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { toFun := fwd n K
    invFun := bwd n K
    left_inv := bwd_fwd n K
    right_inv := fwd_bwd n K
    map_mul' := map_mul (fwd n K) }

theorem continuous_fwd : Continuous (fwd n K) := by
  refine Continuous.prodMk ?_ ?_
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x)⁻¹ : Matrix n n (InfiniteAdeleRing K))))
          = fun x => (RingHom.mapMatrix (adeleArch (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_fst).comp Units.continuous_coe_inv
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_val
    · have : (fun x : GL n (AdeleRing (𝓞 K) K) =>
          ((↑(Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x)⁻¹ : Matrix n n (FiniteAdeleRing (𝓞 K) K))))
          = fun x => (RingHom.mapMatrix (adeleFin (𝓞 K) K)) ((x⁻¹ : GL n (AdeleRing (𝓞 K) K)) : Matrix _ _ _) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_id.matrix_map continuous_snd).comp Units.continuous_coe_inv

omit [Fintype n] [DecidableEq n] in
theorem continuous_glue : Continuous (fun p : Matrix n n (InfiniteAdeleRing K) × Matrix n n (FiniteAdeleRing (𝓞 K) K) =>
    glue n K p.1 p.2) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_apply_apply i j).comp continuous_fst).prodMk ((continuous_apply_apply i j).comp continuous_snd)

theorem continuous_bwd : Continuous (bwd n K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_glue n K).comp
      ((Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd))
  · exact (continuous_glue n K).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk (Units.continuous_coe_inv.comp continuous_snd))

def splitEquiv : GL n (AdeleRing (𝓞 K) K) ≃ₜ* GL n (InfiniteAdeleRing K) × GL n (FiniteAdeleRing (𝓞 K) K) :=
  { splitMulEquiv n K with
    continuous_toFun := continuous_fwd n K
    continuous_invFun := continuous_bwd n K }

theorem splitEquiv_apply (x : GL n (AdeleRing (𝓞 K) K)) :
    splitEquiv n K x = (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
      Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x) :=
  rfl

end Split

section Main

variable (K : Type) [Field K] [NumberField K]

theorem main
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (Φ : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (Ψ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      (letI := glBorel (Fin 2) (𝓞 K) K
       ∫ x, Φ (glArch (𝓞 K) K x) * Ψ (glFin (𝓞 K) K x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = (c : ℂ) * ((∫ a, Φ a ∂μa) * ∫ b, Ψ b ∂μf) := by
  let : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := glBorel (Fin 2) (𝓞 K) K
  have : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have : SecondCountableTopology (InfiniteAdeleRing K) := secondCountableTopology_infiniteAdeleRing K
  have : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := secondCountableTopology_finiteAdeleRing K
  have : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := secondCountableTopology_gl (Fin 2) _
  have : SecondCountableTopology (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := secondCountableTopology_gl (Fin 2) _
  have : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := locallyCompactSpace_gl (Fin 2) _
  have : LocallyCompactSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := locallyCompactSpace_gl (Fin 2) _
  have : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := Prod.borelSpace
  obtain ⟨c, hc, hmap⟩ := NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod (Fin 2) K μa μf
  refine ⟨c, hc, fun Φ Ψ => ?_⟩
  have key : (∫ p, Φ p.1 * Ψ p.2 ∂(Measure.map (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
      (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x, Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x))
      (adelicGLHaar (Fin 2) (𝓞 K) K)))
      = ∫ x, Φ (glArch (𝓞 K) K x) * Ψ (glFin (𝓞 K) K x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    integral_map_equiv ((splitEquiv (Fin 2) K).toHomeomorph.toMeasurableEquiv) fun p => Φ p.1 * Ψ p.2
  rw [← key, hmap, integral_smul_nnreal_measure, integral_prod_mul]
  rfl

end Main

end ArchFiniteFactorization

theorem NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (Φ : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (Ψ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      (letI := glBorel (Fin 2) (𝓞 K) K
       ∫ x, Φ (glArch (𝓞 K) K x) * Ψ (glFin (𝓞 K) K x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = (c : ℂ) * ((∫ a, Φ a ∂μa) * ∫ b, Ψ b ∂μf) :=
  ArchFiniteFactorization.main K μa μf
