/-
  A factorizable test function is archimedean-smooth at a real place, and its archimedean
  derivative is again a tensor with the same finite factor.

  For `α = fa ⊗ ff` with `fa` an archimedean test factor and `ff` a finite one
  (`IsFactorizableTestFn K α`), and a **real** place `w` of the number field `K`, the pair this
  module is one half of says: `α` is `C^∞` in the archimedean chart at `w` (`IsArchSmoothAt hw α`),
  and for every archimedean direction `d : ArchDir` the right-invariant derivative
  `archDerivAt hw d α` is *again* a tensor — the same finite factor `ff`, a new archimedean test
  factor `fa'`. The headline
  `AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor` is stated
  verbatim from its `Theorems/` wrapper. Everything else is `private`, as in the pin, at subject
  names: the pin's compressed tokens are `E8Ent` → `ArchEntry`, `e8DetSet` → `nonsingEntries`,
  `e8Inv` → `invEntries`, `e8tc_*` → `chart_*`, `e8l5*` → `lift*`, `e8r5*` → `flow*` (its
  `e8l5Phi'` → `liftPhi'`, its `e8r5_main` → `flow_main`), and its `solution` is inlined into the
  headline's proof.

  **The pin's left half is not here.** The pin wrote the development twice — a left derivative
  (`e8l5*`, `e8leftDeriv`) and a right one (`e8r5*`) — and only the right is on the critical path:
  the headline, and the pin's own `solution`, never reach a left-derivative declaration. That half
  was dead in the pin as well; on 2026-10-23 it was cut from this module and is kept, with the
  private premises it needs, on the shelf
  `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothDead.lean`, which imports this
  port's public API only and which nothing here imports.

  The engine is the chart of the test factor at `w`, phase by phase (the pin's six sections are
  kept):

  * `LiftAnalysis` — `ArchEntry = Fin 2 → Fin 2 → ℝ`, the determinant-open set
    `nonsingEntries = {e | (Matrix.of e).det ≠ 0}`, the inverse chart `invEntries` with
    `chart_of_invEntries : Matrix.of (invEntries e) = (Matrix.of e)⁻¹` and its smoothness on `nonsingEntries`, and
    the continuity of the lift `archRealLiftAt hw` on `nonsingEntries` (`lift_continuousOn_lift`), which
    goes through `Units.continuous_iff` and the two entries of the inverse;
  * `AffineData` — `archEntries` as a ring homomorphism of matrices
    (`lift_archEntries_eq_mapMatrix`), and the affine chart that splits
    `archEntries (archRealLiftAt hw e)` into `liftConst w + liftLinMat hw e`
    (`lift_archEntries_glArch_lift`), with the additive/linear pieces `liftSingle`, `liftConst`,
    `liftAddHom`, `liftLin`, `liftLinMat`;
  * `TestData` — the matrix multipliers `liftMulR`/`liftMulL` (`liftMulL_apply`), which are what
    the right half's tensor factorization multiplies by; the two-sided factorization
    (`lift_factor_lift_mul`, `lift_isFactorizableTestFn_archRealGLAt_mul`) and compact support of
    the chart (`lift_exists_compact_support`) are on the shelf;
  * `Conv` — the curve `liftCurve d t` of the flow `archFlowAt`, with `lift_curve_mem`,
    `lift_hasDerivAt_curve` and `lift_archFlowAt_eq_lift`; the left-acting derivative
    `leftDerivFactor` along it is on the shelf;
  * `LeftDerivFactor` — the two chart lemmas the right half reuses, `lift_curve_det` and
    `liftMulR_eq_mulL`; `liftDir`, `liftPhi'` and `lift_leftDeriv_tensor` (the left derivative of a
    tensor is a tensor with the same `ff`) are on the shelf;
  * `RightDerivFactor` — the right-hand twin `flowPhi'`, `flow_isArchSmoothAt`,
    `flow_archDerivAt_eq`, and `flow_main`, the whole statement.

  Transcribed from the two pin copies (pinned `aa2d8b3`):

  * `Theorems/Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean`
    (24 lines) — the statement, verbatim;
  * `P2M/Sol/S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean`
    (721 lines, 85 declarations) — the proof. Its helpers are `private` both there and here (they
    were briefly public in the first landing; see the work order's §9), renamed to their subject
    as above; the 25 of them that are the unreachable left half live on the shelf instead. The
    `P2MW.S_<stem>` wrapper namespace and the `p2m_open`/`p2m_export`/`p2m_reactivate` staging are
    dropped, and the pin's `p2m_exact_reverting` glue does not exist here, so the headline's proof
    is the `flow_main` body.

  No statement deviates from the pin. The complex mirror of this module is
  `FactorizableTestFnArchSmoothComplex.lean`: the two `S_` files are one development written
  twice, and its helpers live under `AutomorphicForm.IsFactorizableTestFn.Complex` because most
  of the last names are shared.

  **Wiring.** This module carries its own wire. The headline is its only public declaration, so
  the checker diffs exactly that one against the two pin copies above; the helpers are `private`
  and not diffed, and the left half is not in this module at all:

  spec-pin: Theorems/Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean   -- comparable copy
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

private abbrev ArchEntry : Type := Fin 2 → Fin 2 → ℝ

private abbrev nonsingEntries : Set ArchEntry := {e : ArchEntry | (Matrix.of e).det ≠ 0}

private theorem chart_isOpen_nonsingEntries : IsOpen nonsingEntries := by
  have h : Continuous fun e : ArchEntry => (Matrix.of e).det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

section LiftAnalysis

private def invEntries (e : ArchEntry) : ArchEntry := fun i j => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j / (Matrix.of e).det

private theorem chart_of_invEntries {e : ArchEntry} : Matrix.of (invEntries e) = (Matrix.of e)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  ext i j
  simp only [invEntries, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

private theorem chart_det_invEntries {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) : (Matrix.of (invEntries e)).det ≠ 0 := by
  rw [chart_of_invEntries, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem chart_contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => e i j :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i).contDiff

private theorem chart_contDiff_det : ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => (Matrix.of e).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((chart_contDiff_entry 0 0).mul (chart_contDiff_entry 1 1)).sub ((chart_contDiff_entry 0 1).mul (chart_contDiff_entry 1 0))

private theorem chart_contDiff_adj (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : ArchEntry => !![e 1 1, -e 0 1; -e 1 0, e 0 0] i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact chart_contDiff_entry _ _ | exact (chart_contDiff_entry _ _).neg

private theorem chart_contDiffOn_invEntries : ContDiffOn ℝ (⊤ : ℕ∞) invEntries nonsingEntries :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
    (chart_contDiff_adj i j).contDiffOn.div chart_contDiff_det.contDiffOn fun _ he => he

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem lift_lift_inv (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) :
    (archRealLiftAt hw e : AdelicGL2 (𝓞 K) K)⁻¹ = archRealLiftAt hw (invEntries e) := by
  rw [archRealLiftAt_of_det_ne_zero hw he, archRealLiftAt_of_det_ne_zero hw (chart_det_invEntries he), ← map_inv]
  congr 1
  apply Units.ext
  rw [Matrix.coe_units_inv]
  exact chart_of_invEntries.symm

private def liftTheta (hw : w.IsReal) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (archMatrixUpdate K w (A.map (ringEquivRealOfIsReal hw).symm) i j,
    (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j)

private theorem lift_coe_archRealGLAt (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ((archRealGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      liftTheta hw (m : Matrix (Fin 2) (Fin 2) ℝ) :=
  rfl

private theorem lift_continuous_Theta (hw : w.IsReal) : Continuous (liftTheta (K := K) hw) := by
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

private theorem lift_continuousOn_lift (hw : w.IsReal) :
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

private abbrev liftEntry : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private theorem lift_continuous_ringEquiv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem lift_archEntries_eq_mapMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (archEntries K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
  funext i j
  rfl

private theorem lift_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) = (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  lift_archEntries_eq_mapMatrix K g

private theorem lift_archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K (a * z)) = Matrix.of (archEntries K a) * Matrix.of (archEntries K z) := by
  simp only [lift_of_archEntries, Units.val_mul, map_mul]

variable {K}

private def liftSingle (w : InfinitePlace K) (x : w.Completion) : InfiniteAdeleRing K :=
  Pi.single (M := fun v : InfinitePlace K => v.Completion) w x

private theorem lift_archMatrixUpdate_entry (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
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

private def liftConst (w : InfinitePlace K) : liftEntry K :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K (archMatrixUpdate K w 0 i j)

private theorem lift_archEntries_archGLIncl (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    archEntries K (archGLIncl K w k) i j =
      liftConst w i j +
        InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((k : Matrix (Fin 2) (Fin 2) w.Completion) i j)) := by
  rw [archEntries_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace K
    (archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j) = _
  rw [lift_archMatrixUpdate_entry, map_add]
  rfl

private def liftAddHom {w : InfinitePlace K} (hw : w.IsReal) : ℝ →+ mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddMonoidHom.comp
    ((AddMonoidHom.single (f := fun v : InfinitePlace K => v.Completion) w).comp
      (ringEquivRealOfIsReal hw).symm.toAddMonoidHom)

private theorem liftAddHom_apply {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    liftAddHom hw r = InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((ringEquivRealOfIsReal hw).symm r)) :=
  rfl

private theorem lift_continuous_addHom {w : InfinitePlace K} (hw : w.IsReal) : Continuous (liftAddHom hw) := by
  have h1 : Continuous fun x : w.Completion => liftSingle w x := continuous_single w
  have h2 : Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r :=
    (isometryEquivRealOfIsReal hw).symm.continuous
  have h3 : ⇑(liftAddHom hw) = fun r : ℝ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K (liftSingle w ((ringEquivRealOfIsReal hw).symm r)) :=
    funext fun r => liftAddHom_apply hw r
  rw [h3]
  exact (lift_continuous_ringEquiv K).comp (h1.comp h2)

private def liftLin {w : InfinitePlace K} (hw : w.IsReal) : ℝ →L[ℝ] mixedEmbedding.mixedSpace K :=
  (liftAddHom hw).toRealLinearMap (lift_continuous_addHom hw)

private def liftLinMat {w : InfinitePlace K} (hw : w.IsReal) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] liftEntry K :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (liftLin hw).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

private theorem liftLinMat_apply {w : InfinitePlace K} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    liftLinMat hw e i j = liftAddHom hw (e i j) :=
  rfl

end FieldOnly

section NumberFieldPart

variable {K : Type} [Field K] [NumberField K]

private theorem lift_archEntries_glArch_lift {w : InfinitePlace K} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
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

private theorem lift_glFin_lift (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0) :
    glFin (𝓞 K) K (archRealLiftAt hw e) = 1 := by
  rw [archRealLiftAt_of_det_ne_zero hw he]
  exact glFin_adelicArchGLIncl K _

private def liftMulRLin (M : liftEntry K) : liftEntry K →ₗ[ℝ] liftEntry K where
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

private def liftMulR (M : liftEntry K) : liftEntry K →L[ℝ] liftEntry K := LinearMap.toContinuousLinearMap (liftMulRLin M)

private def liftMulLLin (A : liftEntry K) : liftEntry K →ₗ[ℝ] liftEntry K where
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

private def liftMulL (A : liftEntry K) : liftEntry K →L[ℝ] liftEntry K := LinearMap.toContinuousLinearMap (liftMulLLin A)

private theorem liftMulL_apply (A N : liftEntry K) : liftMulL A N = Matrix.of.symm (Matrix.of A * Matrix.of N) := rfl

end TestData

section Conv

open MeasureTheory Metric Set
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def liftCurve (d : ArchDir) (t : ℝ) : ArchEntry :=
  Matrix.of.symm
    (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))

private theorem lift_curve_mem (d : ArchDir) (t : ℝ) : liftCurve d t ∈ nonsingEntries := by
  show (Matrix.of (liftCurve d t)).det ≠ 0
  rw [liftCurve, Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix d t).isUnit).ne_zero

private theorem lift_hasDerivAt_curve (d : ArchDir) :
    HasDerivAt (liftCurve d)
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)) 0 :=
  hasDerivAt_of_symm_mul_archFlowMatrix _ d

private theorem lift_archFlowAt_eq_lift (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    (archFlowAt hw d t : AdelicGL2 (𝓞 K) K) = archRealLiftAt hw (liftCurve d t) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [liftCurve, ← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]

end Conv

section LeftDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private theorem lift_curve_det (d : ArchDir) (t : ℝ) : (Matrix.of (liftCurve d t)).det ≠ 0 := lift_curve_mem d t

private theorem liftMulR_eq_mulL (N X : liftEntry K) : liftMulR N X = liftMulL X N := rfl

end LeftDerivFactor

section RightDerivFactor

open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

private def flowDir (d : ArchDir) : ArchEntry :=
  Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * archDirMatrix d)

private theorem flow_hasDerivAt_curve (d : ArchDir) : HasDerivAt (liftCurve d) (flowDir d) 0 :=
  lift_hasDerivAt_curve d

private theorem flow_archEntries_mul_lift (hw : w.IsReal) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    archEntries K (glArch (𝓞 K) K (y * archRealLiftAt hw e)) =
      liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
        liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw e) := by
  rw [liftMulL_apply, liftMulL_apply,
    ← Matrix.of.symm_apply_apply (archEntries K (glArch (𝓞 K) K (y * archRealLiftAt hw e))), map_mul,
    lift_archEntries_mul, lift_archEntries_glArch_lift hw he]
  show Matrix.of.symm (Matrix.of (archEntries K (glArch (𝓞 K) K y)) *
    (Matrix.of (liftConst w) + Matrix.of (liftLinMat hw e))) = _
  rw [Matrix.mul_add]
  rfl

private theorem flow_factor_mul_lift (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : liftEntry K → ℂ} (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (y : AdelicGL2 (𝓞 K) K) :
    α (y * archRealLiftAt hw e) =
      Φ (liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
          liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw e)) *
        ff (glFin (𝓞 K) K y) := by
  rw [hα, hfa, flow_archEntries_mul_lift hw he, map_mul, lift_glFin_lift hw he, mul_one]

private theorem flow_fa_mul_lift (hw : w.IsReal) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {Φ : liftEntry K → ℂ}
    (hfa : ∀ z, fa z = Φ (archEntries K z)) {e : ArchEntry} (he : (Matrix.of e).det ≠ 0)
    (z : GL (Fin 2) (InfiniteAdeleRing K)) :
    fa (z * glArch (𝓞 K) K (archRealLiftAt hw e)) =
      Φ (liftMulL (archEntries K z) (liftConst w) + liftMulL (archEntries K z) (liftLinMat hw e)) := by
  rw [hfa, ← map_add, liftMulL_apply, ← lift_archEntries_glArch_lift hw he, ← lift_archEntries_mul, Equiv.symm_apply_apply]

private theorem flow_isArchSmoothAt (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw α := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, -⟩, -, hαeq⟩ := hα
  intro g
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : ArchEntry =>
      Φ (liftMulL (archEntries K (glArch (𝓞 K) K g)) (liftConst w) +
          liftMulL (archEntries K (glArch (𝓞 K) K g)) (liftLinMat hw e)) * ff (glFin (𝓞 K) K g)) nonsingEntries :=
    ((hΦ.comp (contDiff_const.add ((liftMulL (archEntries K (glArch (𝓞 K) K g))).contDiff.comp
      (liftLinMat hw).contDiff))).mul contDiff_const).contDiffOn
  refine hsm.congr fun e he => ?_
  exact flow_factor_mul_lift hw hfa hαeq he g

private def flowPhi' (hw : w.IsReal) (d : ArchDir) (Φ : liftEntry K → ℂ) (N : liftEntry K) : ℂ :=
  fderiv ℝ Φ (liftMulR (liftConst w) N + liftMulR (liftLinMat hw (liftCurve d 0)) N) (liftMulR (liftLinMat hw (flowDir d)) N)

private theorem flow_contDiff_Phi' (hw : w.IsReal) (d : ArchDir) {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (flowPhi' hw d Φ) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2.comp
    ((liftMulR (liftConst w)).contDiff.add (liftMulR (liftLinMat hw (liftCurve d 0))).contDiff)).clm_apply
    (liftMulR (liftLinMat hw (flowDir d))).contDiff

private theorem flow_hasDerivAt_Phi_curve (hw : w.IsReal) (d : ArchDir) {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (N : liftEntry K) :
    HasDerivAt (fun t : ℝ => Φ (liftMulL N (liftConst w) + liftMulL N (liftLinMat hw (liftCurve d t))))
      (flowPhi' hw d Φ N) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => liftLinMat hw (liftCurve d t)) (liftLinMat hw (flowDir d)) 0 :=
    (liftLinMat hw).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (flow_hasDerivAt_curve d)
  have h2 : HasDerivAt (fun t : ℝ => liftMulL N (liftLinMat hw (liftCurve d t))) (liftMulL N (liftLinMat hw (flowDir d))) 0 :=
    (liftMulL N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun t : ℝ => liftMulL N (liftConst w) + liftMulL N (liftLinMat hw (liftCurve d t)))
      (liftMulL N (liftLinMat hw (flowDir d))) 0 :=
    h2.const_add (liftMulL N (liftConst w))
  have h4 := ((contDiff_infty_iff_fderiv.1 hΦ).1 _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
  simp only [flowPhi', liftMulR_eq_mulL]
  exact h4

private theorem flow_archDerivAt_eq (hw : w.IsReal) (d : ArchDir) {α : AdelicGL2 (𝓞 K) K → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) (y : AdelicGL2 (𝓞 K) K) :
    archDerivAt hw d α y = flowPhi' hw d Φ (archEntries K (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y) := by
  have hfun : (fun t : ℝ => α (y * archFlowAt hw d t)) = fun t : ℝ =>
      Φ (liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftConst w) +
          liftMulL (archEntries K (glArch (𝓞 K) K y)) (liftLinMat hw (liftCurve d t))) *
        ff (glFin (𝓞 K) K y) := by
    funext t
    rw [lift_archFlowAt_eq_lift, flow_factor_mul_lift hw hfa hα (lift_curve_det d t) y]
  show deriv (fun t : ℝ => α (y * archFlowAt hw d t)) 0 = _
  rw [hfun]
  exact ((flow_hasDerivAt_Phi_curve hw d hΦ _).mul_const _).deriv

private theorem flow_hasCompactSupport_Phi' (hw : w.IsReal) (d : ArchDir) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {Φ : liftEntry K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hfa : ∀ z, fa z = Φ (archEntries K z))
    (hsupp : HasCompactSupport fa) : HasCompactSupport fun z => flowPhi' hw d Φ (archEntries K z) := by
  refine hsupp.mono' fun z hz => ?_
  simp only [Function.mem_support] at hz
  by_contra hzt
  apply hz
  have hcurve : ContinuousAt (fun t : ℝ => liftCurve d t) 0 := (flow_hasDerivAt_curve d).continuousAt
  have hlift : ContinuousAt (fun t : ℝ => (archRealLiftAt hw (liftCurve d t) : AdelicGL2 (𝓞 K) K)) 0 :=
    ContinuousAt.comp_of_eq
      ((lift_continuousOn_lift hw).continuousAt (chart_isOpen_nonsingEntries.mem_nhds (lift_curve_mem d 0))) hcurve rfl
  have horbit : ContinuousAt (fun t : ℝ => z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d t))) 0 :=
    continuousAt_const.mul ((continuous_glArch (𝓞 K) K).continuousAt.comp hlift)
  have hz0 : z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d 0) : AdelicGL2 (𝓞 K) K) = z := by
    rw [← lift_archFlowAt_eq_lift, archFlowAt_zero, map_one, mul_one]
  have hev : ∀ᶠ t : ℝ in 𝓝 0, fa (z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d t))) = 0 := by
    have hmem : (tsupport fa)ᶜ ∈ 𝓝 (z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d 0) : AdelicGL2 (𝓞 K) K)) := by
      rw [hz0]
      exact (isClosed_tsupport fa).isOpen_compl.mem_nhds hzt
    filter_upwards [horbit.preimage_mem_nhds hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  have hfun : (fun t : ℝ => fa (z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d t)))) = fun t : ℝ =>
      Φ (liftMulL (archEntries K z) (liftConst w) + liftMulL (archEntries K z) (liftLinMat hw (liftCurve d t))) := by
    funext t
    exact flow_fa_mul_lift hw hfa (lift_curve_det d t) z
  have hd : HasDerivAt (fun t : ℝ => fa (z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d t))))
      (flowPhi' hw d Φ (archEntries K z)) 0 := by
    rw [hfun]
    exact flow_hasDerivAt_Phi_curve hw d hΦ (archEntries K z)
  have heq : (fun t : ℝ => fa (z * glArch (𝓞 K) K (archRealLiftAt hw (liftCurve d t)))) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => (0 : ℂ) :=
    hev.mono fun t ht => ht
  rw [← hd.deriv, heq.deriv_eq, deriv_const]

private theorem flow_main (hw : w.IsReal) (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDir, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAt hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
  refine ⟨flow_isArchSmoothAt hw hα, ?_⟩
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq⟩ := hα
  exact ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hαeq, fun d =>
    ⟨fun z => flowPhi' hw d Φ (archEntries K z),
      ⟨⟨flowPhi' hw d Φ, flow_contDiff_Phi' hw d hΦ, fun _ => rfl⟩, flow_hasCompactSupport_Phi' hw d hΦ hfa hsupp⟩,
      fun y => flow_archDerivAt_eq hw d hΦ hfa hαeq y⟩⟩

end RightDerivFactor

end

open NumberField NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain

theorem isArchSmoothAt_and_archDerivAt_eq_tensor
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDir, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAt hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) :=
  flow_main hw α hα
end AutomorphicForm.IsFactorizableTestFn
