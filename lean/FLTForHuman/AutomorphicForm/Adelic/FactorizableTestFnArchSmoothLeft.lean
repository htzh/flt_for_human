/-
  The **left**-derivative half of the archimedean chart for a factorisable test function.

  `FactorizableTestFnArchSmooth` proves the right half of the pin's one development: for a real
  place `w`, `α` is archimedean-smooth and `archDerivAt hw d α` is again a tensor with the same
  finite factor. This module is the **left** half of the same chart — the pin's `e8l5*` layer and
  `e8leftDeriv` — which that headline never reaches and which the port therefore did not carry:
  the matrix multipliers `liftMulR`/`liftMulL`, the chart maps `liftCD`/`liftLD`/`liftPhi'`, the
  tensor factorisations `lift_factor_lift_mul` / `lift_isFactorizableTestFn_archRealGLAt_mul`, the
  compact support of the chart, and the **left**-acting derivative `leftDerivFactor` along
  `archFlowAt` together with `lift_leftDeriv_tensor` (the left derivative of a tensor is again a
  tensor with the same finite factor).

  It exists as a live module because a consumer needs it: SET-AF6's
  `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` differentiates `rightConv` in
  the **group variable**, which is the left action, and its pin file re-copies this whole layer as
  `l5*`. Until 2026-10-23 the text was the pin's inside `FactorizableTestFnArchSmooth`; it was then
  cut to `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothDead.lean` as dead — the right
  headline does not reach it — and on 2026-11-02 it was promoted back, **public**, at the port's
  content names, with the four declarations that had been lost in an earlier cut restored from the
  pin: `lift_archFlowAt_inv`, `lift_continuous_cD`, `lift_glFin_archFlowAt` and
  `lift_isFactorizableTestFn_leftDeriv`.

  The names are the port's, not the pin's: the rename map is the live module's header
  (`e8l5*` → `lift*`, `e8tc_*` → `chart_*`, `e8r5*` → `flow*`, `e8leftDeriv` → `leftDerivFactor`).
  It follows that this module carries **no `spec-pin:` wire**: the checker matches by last name, so
  a renamed transcription has no pin original to diff against, and the four restored declarations
  would each need a `pin:` marker. The whole surface is therefore **tier 3** — public, built, and
  registered in `spec/UNWIRED-PUBLIC.md` — which is the same economy the live module's own 55
  private declarations represent, made visible instead of hidden.

  Pin source (pinned `aa2d8b3`):
  `P2M/Sol/S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean`
  `:34`–`:557` — the chart core through `e8l5_leftDeriv_tensor`, minus the `e8r5*` right half (which
  is the live module) and minus its `solution` (which is the live headline).
-/

import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.RealVectorSpace

set_option autoImplicit false

namespace AutomorphicForm.IsFactorizableTestFn

open NumberField AutomorphicForm NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion (ringEquivRealOfIsReal isometryEquivRealOfIsReal)
open scoped Topology

noncomputable section

abbrev ArchEntry : Type := Fin 2 → Fin 2 → ℝ

abbrev nonsingEntries : Set ArchEntry := {e : ArchEntry | (Matrix.of e).det ≠ 0}

theorem chart_isOpen_nonsingEntries : IsOpen nonsingEntries := by
  have h : Continuous fun e : ArchEntry => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

section LiftAnalysis

def invEntries (e : ArchEntry) : ArchEntry := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

theorem chart_of_invEntries {e : ArchEntry} : Matrix.of (invEntries e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [invEntries, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem chart_det_invEntries {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (invEntries e)).det ≠ 0 := by
  rw [chart_of_invEntries, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

theorem chart_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i).contDiff

theorem chart_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((chart_contDiff_entry 0 0).mul (chart_contDiff_entry 1 1)).sub ((chart_contDiff_entry 0 1).mul (chart_contDiff_entry 1 0))

theorem chart_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact chart_contDiff_entry _ _ | exact (chart_contDiff_entry _ _).neg

theorem chart_contDiffOn_invEntries : ContDiffOn ℝ (⊤ : ℕ∞) invEntries nonsingEntries :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    (chart_contDiff_adj i j).contDiffOn.div chart_contDiff_det.contDiffOn fun _ he => he

theorem chart_invEntries_mem {e : ArchEntry} (he : e ∈ nonsingEntries) : invEntries e ∈ nonsingEntries := chart_det_invEntries he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

theorem lift_lift_inv (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) :
    (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archRealLiftAt hw (invEntries e) := by
  rw [archRealLiftAt_of_det_ne_zero hw he, archRealLiftAt_of_det_ne_zero hw (chart_det_invEntries he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact chart_of_invEntries.symm

def liftTheta (hw : w.IsReal) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (archMatrixUpdate K w (A.map (ringEquivRealOfIsReal hw).symm) i j,
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j)

theorem lift_coe_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ((archRealGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      liftTheta hw (m : Matrix (Fin 2) (Fin 2) ℝ) :=
  rfl

theorem lift_continuous_Theta (hw : w.IsReal) : Continuous (liftTheta (K := K) hw) := by
  have hentry : ∀ i j : Fin 2, Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j := fun i j =>
    (continuous_apply j).comp (continuous_apply i : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i)
  have hsymm : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  refine continuous_matrix fun i j => Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [archMatrixUpdate_apply_self, Matrix.map_apply]
    exact hsymm.comp (hentry i j)
  · simp only [archMatrixUpdate_apply_of_ne K w _ i j hv]
    exact continuous_const

theorem lift_continuousOn_lift (hw : w.IsReal) :
    ContinuousOn (fun e : ArchEntry => (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)) nonsingEntries := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hdet : ∀ e : nonsingEntries, (Matrix.of (e : ArchEntry)).det ≠ 0 := fun e => e.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ e : nonsingEntries,
        ((archRealLiftAt hw (e : ArchEntry) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
          liftTheta hw (Matrix.of (e : ArchEntry)) := fun e => by
      rw [archRealLiftAt_of_det_ne_zero hw (hdet e), lift_coe_archRealGLAt]
      rfl
    exact ((lift_continuous_Theta hw).comp continuous_subtype_val).congr fun e => (h e).symm
  · have h : ∀ e : nonsingEntries,
        (((archRealLiftAt hw (e : ArchEntry) : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = liftTheta hw (Matrix.of (invEntries (e : ArchEntry))) := fun e => by
      rw [lift_lift_inv hw (hdet e), archRealLiftAt_of_det_ne_zero hw (chart_det_invEntries (hdet e)), lift_coe_archRealGLAt]
      rfl
    exact ((lift_continuous_Theta hw).comp
      (continuousOn_iff_continuous_domRestrict.1 chart_contDiffOn_invEntries.continuousOn)).congr fun e => (h e).symm

end LiftAnalysis

section AffineData

open scoped Classical

section FieldOnly

variable (K : Type) [Field K]

abbrev liftEntry : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

theorem lift_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem lift_continuous_archEntries : Continuous (archEntries K) := by
  have hval : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      (a.val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => (lift_continuous_ringEquiv K).comp ?_
  exact (continuous_apply j).comp
    ((continuous_apply i : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) => m i).comp hval)

theorem lift_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

theorem lift_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  lift_archEntries_eq_mapMatrix K g

theorem lift_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [lift_of_archEntries, Units.val_mul, map_mul]

variable {K}

def liftSingle (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

theorem lift_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) :
    archMatrixUpdate K w m i j = archMatrixUpdate K w 0 i j + liftSingle w (m i j) := by
  funext v
  show archMatrixUpdate K w m i j v =
    archMatrixUpdate K w 0 i j v + Pi.single (M := fun v : InfinitePlace K => v.Completion) w (m i j) v
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self, archMatrixUpdate_apply_self, Pi.single_eq_same, Matrix.zero_apply, zero_add]
  · rw [archMatrixUpdate_apply_of_ne K w m i j hv, archMatrixUpdate_apply_of_ne K w 0 i j hv, Pi.single_eq_of_ne hv,
      add_zero]

def liftConst (w : InfinitePlace K) : liftEntry K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

theorem lift_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      liftConst w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [lift_archMatrixUpdate_entry, map_add]
  rfl

def liftAddHom {w : InfinitePlace K} (hw : w.IsReal) : ℝ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivRealOfIsReal hw).symm.toAddMonoidHom)

theorem liftAddHom_apply {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    liftAddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((ringEquivRealOfIsReal hw).symm r)) :=
  rfl

theorem lift_continuous_addHom {w : InfinitePlace K} (hw : w.IsReal) : Continuous (liftAddHom hw) := by
  have h1 : Continuous fun x : w.Completion => liftSingle w x := continuous_single w
  have h2 : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  have h3 : ⇑(liftAddHom hw) = fun r : ℝ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((ringEquivRealOfIsReal hw).symm r)) :=
    funext fun r => liftAddHom_apply hw r
  rw [h3]
  exact (lift_continuous_ringEquiv K).comp (h1.comp h2)

def liftLin {w : InfinitePlace K} (hw : w.IsReal) : ℝ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (liftAddHom hw).toRealLinearMap (lift_continuous_addHom hw)

def liftLinMat {w : InfinitePlace K} (hw : w.IsReal) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] liftEntry K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (liftLin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

theorem liftLinMat_apply {w : InfinitePlace K} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    liftLinMat hw e i j = liftAddHom hw (e i j) :=
  rfl

end FieldOnly

section NumberFieldPart

variable {K : Type} [Field K] [NumberField K]

theorem lift_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e)) = liftConst w + liftLinMat hw e := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  have h1 : glArch (𝓞 K) K (archRealGLAt hw (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)) :=
    glArch_adelicArchGLIncl K _
  rw [h1]
  funext i j
  rw [lift_archEntries_archGLIncl, glEquivOfRingEquiv_apply_entry, Pi.add_apply, Pi.add_apply, liftLinMat_apply,
    liftAddHom_apply]
  rfl

end NumberFieldPart

end AffineData

section TestData

open MeasureTheory
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

theorem lift_glFin_lift (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archRealLiftAt hw e) = 1 := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

theorem lift_glFin_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 K) K (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl K _

def liftMulRLin (M : liftEntry K) : liftEntry K →ₗ[ℝ] liftEntry K where
  toFun N := Matrix.of.symm (Matrix.of N * Matrix.of M)
  map_add' N₁ N₂ := by
    show Matrix.of.symm ((Matrix.of N₁ + Matrix.of N₂) * Matrix.of M) =
      Matrix.of.symm (Matrix.of N₁ * Matrix.of M) + Matrix.of.symm (Matrix.of N₂ * Matrix.of M)
    rw [Matrix.add_mul]
    rfl
  map_smul' t N := by
    show Matrix.of.symm ((t • Matrix.of N) * Matrix.of M) = t • Matrix.of.symm (Matrix.of N * Matrix.of M)
    rw [Matrix.smul_mul]
    rfl

def liftMulR (M : liftEntry K) : liftEntry K →L[ℝ] liftEntry K := LinearMap.toContinuousLinearMap (liftMulRLin M)

theorem liftMulR_apply (M N : liftEntry K) : liftMulR M N = Matrix.of.symm (Matrix.of N * Matrix.of M) := rfl

def liftMulRL : liftEntry K →ₗ[ℝ] (liftEntry K →L[ℝ] liftEntry K) where
  toFun := liftMulR
  map_add' M₁ M₂ := by
    refine ContinuousLinearMap.ext fun N => ?_
    show Matrix.of.symm (Matrix.of N * (Matrix.of M₁ + Matrix.of M₂)) =
      Matrix.of.symm (Matrix.of N * Matrix.of M₁) + Matrix.of.symm (Matrix.of N * Matrix.of M₂)
    rw [Matrix.mul_add]
    rfl
  map_smul' t M := by
    refine ContinuousLinearMap.ext fun N => ?_
    show Matrix.of.symm (Matrix.of N * (t • Matrix.of M)) = t • Matrix.of.symm (Matrix.of N * Matrix.of M)
    rw [Matrix.mul_smul]
    rfl

theorem lift_continuous_mulR : Continuous (liftMulR : liftEntry K → liftEntry K →L[ℝ] liftEntry K) :=
  (liftMulRL (K := K)).continuous_of_finiteDimensional

def liftMulLLin (A : liftEntry K) : liftEntry K →ₗ[ℝ] liftEntry K where
  toFun N := Matrix.of.symm (Matrix.of A * Matrix.of N)
  map_add' N₁ N₂ := by
    show Matrix.of.symm (Matrix.of A * (Matrix.of N₁ + Matrix.of N₂)) =
      Matrix.of.symm (Matrix.of A * Matrix.of N₁) + Matrix.of.symm (Matrix.of A * Matrix.of N₂)
    rw [Matrix.mul_add]
    rfl
  map_smul' t N := by
    show Matrix.of.symm (Matrix.of A * (t • Matrix.of N)) = t • Matrix.of.symm (Matrix.of A * Matrix.of N)
    rw [Matrix.mul_smul]
    rfl

def liftMulL (A : liftEntry K) : liftEntry K →L[ℝ] liftEntry K := LinearMap.toContinuousLinearMap (liftMulLLin A)

theorem liftMulL_apply (A N : liftEntry K) : liftMulL A N = Matrix.of.symm (Matrix.of A * Matrix.of N) := rfl

theorem lift_archEntries_lift_mul (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y)) =
      liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
        liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw e) := by
  rw [liftMulR_apply, liftMulR_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (archRealLiftAt hw e * y))), map_mul,
    lift_archEntries_mul, lift_archEntries_glArch_lift hw he]
  show Matrix.of.symm ((Matrix.of (liftConst w) + Matrix.of (liftLinMat hw e)) *
    Matrix.of (archEntries K (glArch (𝓞 K) K y))) = _
  rw [Matrix.add_mul]
  rfl

theorem lift_factor_lift_mul (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : liftEntry K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (archRealLiftAt hw e * y) =
      Φ (liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
          liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, lift_archEntries_lift_mul hw he, map_mul, lift_glFin_lift hw he, one_mul]

open scoped Classical in

theorem lift_isFactorizableTestFn_archRealGLAt_mul (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K fun y => α (archRealGLAt hw m * y) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hfa_supp⟩, hff, hαeq⟩ := hα
  refine ⟨fun z => fa (glArch (𝓞 K) K (archRealGLAt hw m) * z), ff,
    ⟨⟨fun N => Φ (liftMulL (archEntries K (glArch (𝓞 K) K (archRealGLAt hw m))) N), ?_, ?_⟩, ?_⟩, hff, ?_⟩
  · exact hΦ.comp (liftMulL (archEntries K (glArch (𝓞 K) K (archRealGLAt hw m)))).contDiff
  · intro z
    beta_reduce
    rw [hfa, liftMulL_apply]
    congr 1
    rw [← lift_archEntries_mul]
    exact (Matrix.of.symm_apply_apply _).symm
  · exact hfa_supp.comp_homeomorph (Homeomorph.mulLeft (glArch (𝓞 K) K (archRealGLAt hw m)))
  · intro y
    beta_reduce
    rw [hαeq, map_mul, map_mul, lift_glFin_archRealGLAt hw m, one_mul]

theorem lift_exists_compact_support (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : HasCompactSupport α)
    {S : Set ArchEntry} (hS : IsCompact S) (hSd : S ⊆ nonsingEntries) :
    ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ e' ∈ S, ∀ y ∉ C, α (archRealLiftAt hw e' * y) = 0 := by
  have hS' : IsCompact (invEntries '' S) := hS.image_of_continuousOn (chart_contDiffOn_invEntries.continuousOn.mono hSd)
  have hS'd : invEntries '' S ⊆ nonsingEntries := by
    rintro _ ⟨e', he', rfl⟩
    exact chart_invEntries_mem (hSd he')
  have hcont : ContinuousOn (fun p : ArchEntry × AdelicGL2 (𝓞 K) K => archRealLiftAt hw p.1 * p.2)
      ((invEntries '' S) ×ˢ tsupport α) :=
    ((lift_continuousOn_lift hw).comp continuousOn_fst fun p hp => hS'd hp.1).mul continuousOn_snd
  refine ⟨(fun p : ArchEntry × AdelicGL2 (𝓞 K) K => archRealLiftAt hw p.1 * p.2) '' ((invEntries '' S) ×ˢ tsupport α),
    (hS'.prod (hα : IsCompact (tsupport α))).image_of_continuousOn hcont, ?_⟩
  · intro e' he' y hy
    by_contra hne
    apply hy
    refine ⟨(invEntries e', archRealLiftAt hw e' * y), ⟨⟨e', he', rfl⟩, subset_tsupport _ hne⟩, ?_⟩
    show archRealLiftAt hw (invEntries e') * (archRealLiftAt hw e' * y) = y
    rw [← lift_lift_inv hw (hSd he'), inv_mul_cancel_left]

end TestData

section Conv

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

def leftDerivFactor (hw : w.IsReal) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0

def liftCurve (d : ArchDir) (t : ℝ) : ArchEntry :=
  Matrix.of.symm
    (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))

theorem lift_curve_mem (d : ArchDir) (t : ℝ) : liftCurve d t ∈ nonsingEntries := by
  show (Matrix.of (liftCurve d t)).det ≠ 0
  rw [liftCurve, Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix d t).isUnit).ne_zero

theorem lift_hasDerivAt_curve (d : ArchDir) :
    HasDerivAt (liftCurve d)
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 :=
  hasDerivAt_of_symm_mul_archFlowMatrix _ d

theorem lift_archFlowAt_eq_lift (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) = archRealLiftAt hw (liftCurve d t) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [liftCurve, ← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]

def liftM (y : AdelicGL2 (𝓞 K) K) : liftEntry K := archEntries K (glArch (𝓞 K) K y)

theorem lift_continuous_M : Continuous (liftM : AdelicGL2 (𝓞 K) K → liftEntry K) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => archEntries K (glArch (𝓞 K) K y)
  exact (lift_continuous_archEntries K).comp (continuous_glArch (𝓞 K) K)

def liftCD (w : InfinitePlace K) (y : AdelicGL2 (𝓞 K) K) : liftEntry K := liftMulR (liftM y) (liftConst w)

def liftLD (hw : w.IsReal) (y : AdelicGL2 (𝓞 K) K) : ArchEntry →L[ℝ] liftEntry K := (liftMulR (liftM y)).comp (liftLinMat hw)

theorem lift_continuous_LD (hw : w.IsReal) : Continuous (liftLD (K := K) hw) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => (liftMulR (liftM y)).comp (liftLinMat hw)
  exact (lift_continuous_mulR.comp lift_continuous_M).clm_comp continuous_const

end Conv

section LeftDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

def liftDir (d : ArchDir) : ArchEntry :=
  (-1 : ℝ) • Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)

theorem lift_hasDerivAt_curve_neg (d : ArchDir) : HasDerivAt (fun t : ℝ => liftCurve d (-t)) (liftDir d) 0 := by
  have h := lift_hasDerivAt_curve d
  rw [← neg_zero] at h
  exact h.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

theorem lift_curve_det (d : ArchDir) (t : ℝ) : (Matrix.of (liftCurve d t)).det ≠ 0 := lift_curve_mem d t

theorem liftMulR_eq_mulL (N X : liftEntry K) : liftMulR N X = liftMulL X N := rfl

def liftPhi' (hw : w.IsReal) (d : ArchDir) (Φ : liftEntry K → ℂ) (N : liftEntry K) : ℂ :=
  fderiv ℝ Φ (liftMulL (liftConst w) N + liftMulL (liftLinMat hw (liftCurve d (-0))) N) (liftMulL (liftLinMat hw (liftDir d)) N)

theorem lift_contDiff_Phi' (hw : w.IsReal) (d : ArchDir) {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (liftPhi' hw d Φ) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2.comp
    ((liftMulL (liftConst w)).contDiff.add (liftMulL (liftLinMat hw (liftCurve d (-0)))).contDiff)).clm_apply
    (liftMulL (liftLinMat hw (liftDir d))).contDiff

theorem lift_hasDerivAt_Phi_curve (hw : w.IsReal) (d : ArchDir) {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (N : liftEntry K) :
    HasDerivAt (fun t : ℝ => Φ (liftMulR N (liftConst w) + liftMulR N (liftLinMat hw (liftCurve d (-t)))))
      (liftPhi' hw d Φ N) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => liftLinMat hw (liftCurve d (-t))) (liftLinMat hw (liftDir d)) 0 :=
    (liftLinMat hw).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (lift_hasDerivAt_curve_neg d)
  have h2 : HasDerivAt (fun t : ℝ => liftMulR N (liftLinMat hw (liftCurve d (-t)))) (liftMulR N (liftLinMat hw (liftDir d))) 0 :=
    (liftMulR N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => liftMulR N (liftConst w) + liftMulR N (liftLinMat hw (liftCurve d (-t))))
      (liftMulR N (liftLinMat hw (liftDir d))) 0 :=
    h2.const_add (liftMulR N (liftConst w))
  have h4 := ((contDiff_infty_iff_fderiv.1 hΦ).1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [liftPhi', ← liftMulR_eq_mulL]
  exact h4

theorem lift_fa_lift_mul (hw : w.IsReal) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {Φ : liftEntry K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    fa (glArch (𝓞 K) K (archRealLiftAt hw e) * z) =
      Φ (liftMulR (archEntries K z) (liftConst w) + liftMulR (archEntries K z) (liftLinMat hw e)) := by
  rw [hfa, ← map_add, liftMulR_apply, ← lift_archEntries_glArch_lift hw he, ← lift_archEntries_mul, Equiv.symm_apply_apply]

theorem lift_leftDeriv_eq (hw : w.IsReal) (d : ArchDir) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (y : AdelicGL2 (𝓞 K) K) :
    leftDerivFactor hw d α y = liftPhi' hw d Φ (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  have hfun : (fun t : ℝ => α (archFlowAt hw d (-t) * y)) = fun t : ℝ =>
      Φ (liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
          liftMulR (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw (liftCurve d (-t)))) *
        ff (glFin (𝓞 K) K y) := by
    funext t
    rw [lift_archFlowAt_eq_lift, lift_factor_lift_mul hw hfa hα (lift_curve_det d (-t)) y]
  show deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact ((lift_hasDerivAt_Phi_curve hw d hΦ _).mul_const _).deriv

theorem lift_hasCompactSupport_Phi' (hw : w.IsReal) (d : ArchDir) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) : HasCompactSupport fun z => liftPhi' hw d Φ (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  simp only [Function.mem_support] at hz
  by_contra hzt
  apply hz

  have hcurve : ContinuousAt (fun t : ℝ => liftCurve d (-t)) 0 := (lift_hasDerivAt_curve_neg d).continuousAt
  have hlift : ContinuousAt (fun t : ℝ => (archRealLiftAt hw (liftCurve d (-t)) : AdelicGL2 (𝓞 K) K)) 0 :=
    ContinuousAt.comp_of_eq
      ((lift_continuousOn_lift hw).continuousAt (chart_isOpen_nonsingEntries.mem_nhds (lift_curve_mem d (-0)))) hcurve rfl
  have horbit : ContinuousAt (fun t : ℝ => glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-t))) * z) 0 :=
    ((continuous_glArch (𝓞 K) K).continuousAt.comp hlift).mul continuousAt_const
  have hz0 : glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-0)) : AdelicGL2 (𝓞 K) K) * z = z := by
    rw [← lift_archFlowAt_eq_lift, neg_zero, archFlowAt_zero, map_one, one_mul]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, fa (glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-t))) * z) = 0 := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-0)) : AdelicGL2 (𝓞 K) K) * z) := by
      rw [hz0]
      exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hzt
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hfun : (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-t))) * z)) = fun t : ℝ =>
      Φ (liftMulR (archEntries K z) (liftConst w) + liftMulR (archEntries K z) (liftLinMat hw (liftCurve d (-t)))) := by
    funext t
    exact lift_fa_lift_mul hw hfa (lift_curve_det d (-t)) z
  have hd : HasDerivAt (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-t))) * z))
      (liftPhi' hw d Φ (archEntries K z)) 0 := by
    rw [hfun]
    exact lift_hasDerivAt_Phi_curve hw d hΦ (archEntries K z)
  have heq : (fun t : ℝ => fa (glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d (-t))) * z)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => (0 : ℂ) :=
    hev.mono fun t ht => ht
  rw [← hd.deriv, heq.deriv_eq, deriv_const]

theorem lift_leftDeriv_tensor (hw : w.IsReal) (d : ArchDir) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
      leftDerivFactor hw d (fun z => fa (glArch (𝓞 K) K z) * ff (glFin (𝓞 K) K z)) =
        fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨fun z => liftPhi' hw d Φ (archEntries K z),
    ⟨⟨liftPhi' hw d Φ, lift_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, lift_hasCompactSupport_Phi' hw d hΦ hfaΦ hsupp⟩, ?_⟩
  funext y
  exact lift_leftDeriv_eq hw d hΦ hfaΦ (fun _ => rfl) y

/-! ### The four declarations restored from the pin (lost in an earlier cut) -/

theorem lift_archFlowAt_inv (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K)⁻¹ = archFlowAt hw d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowAt_add, add_neg_cancel, archFlowAt_zero])

theorem lift_continuous_cD (w : InfinitePlace K) : Continuous (liftCD w) := by
  show Continuous fun y : AdelicGL2 (𝓞 K) K => liftMulR (liftM y) (liftConst w)
  exact (lift_continuous_mulR.comp lift_continuous_M).clm_apply continuous_const

theorem lift_glFin_archFlowAt (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    glFin (𝓞 K) K (archFlowAt hw d t) = 1 := by
  rw [lift_archFlowAt_eq_lift]
  exact lift_glFin_lift hw (lift_curve_det d t)

theorem lift_isFactorizableTestFn_leftDeriv (hw : w.IsReal) (d : ArchDir)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (leftDerivFactor hw d α) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩ := hα
  exact ⟨fun z => liftPhi' hw d Φ (archEntries K z), ff,
    ⟨⟨liftPhi' hw d Φ, lift_contDiff_Phi' hw d hΦ, fun _ => rfl⟩,
      lift_hasCompactSupport_Phi' hw d hΦ hfa hsupp⟩, hff,
    lift_leftDeriv_eq hw d hΦ hfa hαeq⟩

end LeftDerivFactor

end

end AutomorphicForm.IsFactorizableTestFn
