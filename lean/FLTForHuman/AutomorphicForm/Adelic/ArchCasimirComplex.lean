/-
  The complex-place Casimir engine and the right-translate headline.

  The complex mirror of the real-place `CasCore17` engine in `ArchCasimir.lean`:
  the chart `e ↦ φ (g * archComplexLiftAt hw e)`, the derivatives `D1`/`D2`, the
  adjoint action `AdM`, the conjugated derivatives `Dconj`/`DelConj`, the brackets
  and relations for `ArchDirComplex`, the two Casimirs `archCasimirAtComplex` /
  `archCasimirBarAtComplex`, and the package lemma. The headline is the complex
  analogue of `archCasimirAt_rightTranslate_archRealGLAt`: right translation by
  `archComplexGLAt hw m` preserves complex archimedean smoothness, the first and
  second derivatives, and both Casimirs.

  Appended below it are the four complex leaves (SET-AF9), each stated at its `Theorems/` wrapper:
  the fifteen commutator identities of the six complex directions
  (`archDerivAtComplex_commutator_of_isArchSmoothAtComplex`, a `3 × 3` bracket table), the
  weight-one character identities `iH = 0`, `F⁻ = E`, `iF⁻ = −iE`, the Casimir's (and the
  conjugate Casimir's) commutation with a right translation by a row isometry at a different
  place, and `GL₂(ℂ)`-invariance for a function killed by all six derivatives. Their helpers are
  the pin's own and `private`.

  Transcribed from the five pin `S_` files of this header's wire (pinned `aa2d8b3`); the engine
  rests on `ArchDerivCasimirComplex.lean` + `ArchDerivCasimirComplexAPI.lean` (an earlier wave).
  The engine is public and `spec/check_port.py` owns all of it (`101 ok / 0 mismatch / 0
  missing`), like `ArchCasimir.lean`: the checker resolves each public statement by name and,
  failing that, by the statement's content hash.
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

theorem archComplexGLAt_eq_archComplexLiftAt (M : GL (Fin 2) ℂ) :
    archComplexGLAt hw M = archComplexLiftAt hw (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem archComplexGLAt_mul_archComplexLiftAt (M : GL (Fin 2) ℂ) {e : Fin 2 → Fin 2 → ℂ} (h : (Matrix.of e).det ≠ 0) :
    archComplexGLAt hw M * archComplexLiftAt hw e =
      archComplexLiftAt hw (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of e)) := by
  have hM : ((M : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of e))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hM h
  rw [archComplexLiftAt_of_det_ne_zero hw h, archComplexLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

def conjArr (M : GL (Fin 2) ℂ) (e : Fin 2 → Fin 2 → ℂ) : Fin 2 → Fin 2 → ℂ :=
  Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of e * (M : Matrix (Fin 2) (Fin 2) ℂ))

theorem det_conjArr (M : GL (Fin 2) ℂ) (e : Fin 2 → Fin 2 → ℂ) :
    (Matrix.of (conjArr M e)).det = (Matrix.of e).det := by
  rw [conjArr, Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul]
  have hMM : ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    rw [← Matrix.det_mul, show ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ) =
      ((M⁻¹ * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) from rfl, inv_mul_cancel, Units.val_one, Matrix.det_one]
  calc ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * (Matrix.of e).det * (M : Matrix (Fin 2) (Fin 2) ℂ).det
      = (((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det * (M : Matrix (Fin 2) (Fin 2) ℂ).det) * (Matrix.of e).det := by
        ring
    _ = (Matrix.of e).det := by rw [hMM, one_mul]

theorem archComplexLiftAt_mul_archComplexGLAt_eq (M : GL (Fin 2) ℂ) (e : Fin 2 → Fin 2 → ℂ) :
    archComplexLiftAt hw e * archComplexGLAt hw M = archComplexGLAt hw M * archComplexLiftAt hw (conjArr M e) := by
  by_cases h : (Matrix.of e).det ≠ 0
  · have h' : (Matrix.of (conjArr M e)).det ≠ 0 := by rwa [det_conjArr]
    rw [archComplexLiftAt_mul_archComplexGLAt hw h, archComplexGLAt_mul_archComplexLiftAt hw M h']
    congr 1
    rw [conjArr, Equiv.apply_symm_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (M : Matrix (Fin 2) (Fin 2) ℂ) * ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((M * M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) from rfl, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · push Not at h
    have h' : ¬ (Matrix.of (conjArr M e)).det ≠ 0 := by rw [det_conjArr]; exact fun hh => hh h
    have h0 : ¬ (Matrix.of e).det ≠ 0 := fun hh => hh h
    rw [archComplexLiftAt, dite_eq_right h0, archComplexLiftAt, dite_eq_right h', one_mul, mul_one]

def chart (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : (Fin 2 → Fin 2 → ℂ) → ℂ :=
  fun e => φ (g * archComplexLiftAt hw e)

theorem chart_rightTranslate (M : GL (Fin 2) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    chart hw (rightTranslate F (archComplexGLAt hw M) φ) g = chart hw φ (g * archComplexGLAt hw M) ∘ conjArr M := by
  funext e
  show φ (g * archComplexLiftAt hw e * archComplexGLAt hw M) = φ (g * archComplexGLAt hw M * archComplexLiftAt hw (conjArr M e))
  rw [mul_assoc, archComplexLiftAt_mul_archComplexGLAt_eq hw M e, ← mul_assoc]

def conjCLM (M : GL (Fin 2) ℂ) : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (Fin 2 → Fin 2 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := conjArr M
      map_add' := fun x y => by
        unfold conjArr
        rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        rfl
      map_smul' := fun c x => by
        unfold conjArr
        rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        rfl }

theorem conjCLM_apply (M : GL (Fin 2) ℂ) (e : Fin 2 → Fin 2 → ℂ) : conjCLM M e = conjArr M e := rfl

theorem coe_conjCLM (M : GL (Fin 2) ℂ) : (conjCLM M : (Fin 2 → Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ)) = conjArr M := rfl

theorem conjArr_one (M : GL (Fin 2) ℂ) : conjArr M (Matrix.of.symm 1) = Matrix.of.symm 1 := by
  unfold conjArr
  rw [Equiv.apply_symm_apply, Matrix.mul_one,
    show ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ) =
      ((M⁻¹ * M : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) from rfl, inv_mul_cancel, Units.val_one]

end ArchCxGL

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

abbrev U : Set (Fin 2 → Fin 2 → ℂ) := {e | (Matrix.of e).det ≠ 0}

theorem one_mem_U : (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∈ U := by
  show (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

def D1 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y)

theorem contDiffAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℂ} (he : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) e :=
  (hφ g).contDiffAt (isOpen_setOf_det_ne_zero_complex.mem_nhds he)

theorem hasFDerivAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℂ} (he : (Matrix.of e).det ≠ 0) :
    HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e) e :=
  ((contDiffAt_chart hw hφ g he).differentiableAt (by simp)).hasFDerivAt

theorem archDerivAtComplexComplex_apply_mul_lift {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℂ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAtComplex hw d φ (g * archComplexLiftAt hw e) =
      fderiv ℝ (chart hw φ g) e (Matrix.of.symm (Matrix.of e * archDirMatrixComplex d)) := by
  have hdiff : HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact hasFDerivAt_chart hw hφ g he
  have hfun : (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) =
      fun t : ℝ => chart hw φ g (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ))) := by
    funext t
    show _ = φ (g * archComplexLiftAt hw _)
    rw [archFlowAtComplex, mul_assoc, archComplexLiftAt_mul_archComplexGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex e d)).deriv

theorem archDerivAtComplex_eq_D1 {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) : archDerivAtComplex hw d φ g = D1 hw φ g (archDirMatrixComplex d) := by
  have h := archDerivAtComplexComplex_apply_mul_lift hw hφ d g (e := Matrix.of.symm 1) one_mem_U
  rw [archComplexLiftAt_of_symm_one, mul_one, Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

theorem isArchSmoothAtComplex_rightTranslate (M : GL (Fin 2) ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (rightTranslate F (archComplexGLAt hw M) φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (chart hw (rightTranslate F (archComplexGLAt hw M) φ) g) U
  rw [chart_rightTranslate, ← coe_conjCLM]
  refine (hφ (g * archComplexGLAt hw M)).comp (conjCLM M).contDiff.contDiffOn fun e he => ?_
  show (Matrix.of (conjArr M e)).det ≠ 0
  rw [det_conjArr]
  exact he

theorem conjCLM_of_symm (M : GL (Fin 2) ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    conjCLM M (Matrix.of.symm Y) =
      Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Y * (M : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [conjCLM_apply, conjArr, Equiv.apply_symm_apply]

theorem archDerivAtComplex_rightTranslate (M : GL (Fin 2) ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d (rightTranslate F (archComplexGLAt hw M) φ) g =
      D1 hw φ (g * archComplexGLAt hw M)
        (((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex d * (M : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [archDerivAtComplex_eq_D1 hw (isArchSmoothAtComplex_rightTranslate hw M hφ), D1, D1, chart_rightTranslate, ← coe_conjCLM,
    ← conjCLM_of_symm]
  have hd : DifferentiableAt ℝ (chart hw φ (g * archComplexGLAt hw M)) (conjCLM M (Matrix.of.symm 1)) := by
    rw [conjCLM_apply, conjArr_one]
    exact (contDiffAt_chart hw hφ _ one_mem_U).differentiableAt (by simp)
  rw [fderiv_comp _ hd (conjCLM M).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    conjCLM_apply M (Matrix.of.symm 1), conjArr_one]

end ArchCxGL

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

def D2 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm Y) (Matrix.of.symm Z)

omit hw in
theorem hasDerivAt_flow_entries (d : ArchDirComplex) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (archDirMatrixComplex d)) 0 := by
  have h := hasDerivAt_of_symm_mul_archFlowMatrixComplex (Matrix.of.symm 1) d
  simp only [Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

omit hw in
theorem hasDerivAt_flow_mul_const (d : ArchDirComplex) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) * X))
      (Matrix.of.symm (archDirMatrixComplex d * X)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrixComplex_apply d i k).mul_const (X k j)

theorem archDerivAtComplex_archDerivAtComplex_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (i j : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw i (archDerivAtComplex hw j φ) g =
      D2 hw φ g (archDirMatrixComplex i) (archDirMatrixComplex j) + D1 hw φ g (archDirMatrixComplex i * archDirMatrixComplex j) := by
  have hfun : (fun t : ℝ => archDerivAtComplex hw j φ (g * archFlowAtComplex hw i t)) =
      fun t => (fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrixComplex i t : Matrix (Fin 2) (Fin 2) ℂ))))
        (Matrix.of.symm ((archFlowMatrixComplex i t : Matrix (Fin 2) (Fin 2) ℂ) * archDirMatrixComplex j)) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrixComplex i t : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrixComplex i t).isUnit).ne_zero
    rw [archFlowAtComplex, archComplexGLAt_eq_archComplexLiftAt, archDerivAtComplexComplex_apply_mul_lift hw hφ j g hdet,
      Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) (Matrix.of.symm 1) := contDiffAt_chart hw hφ g one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw φ g)) (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ0 : Matrix.of.symm ((archFlowMatrixComplex i 0 : Matrix (Fin 2) (Fin 2) ℂ)) = Matrix.of.symm 1 := by
    rw [archFlowMatrixComplex_zero, Units.val_one]
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrixComplex i t : Matrix (Fin 2) (Fin 2) ℂ))))
      (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrixComplex i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_flow_entries i) hγ0.symm
  have h := hA.clm_apply (hasDerivAt_flow_mul_const i (archDirMatrixComplex j))
  show deriv (fun t : ℝ => archDerivAtComplex hw j φ (g * archFlowAtComplex hw i t)) 0 = _
  rw [hfun, h.deriv]
  simp only [archFlowMatrixComplex_zero, Units.val_one, Matrix.one_mul, D2, D1]

theorem D2_symm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : D2 hw φ g Y Z = D2 hw φ g Z Y :=
  ((contDiffAt_chart hw hφ g one_mem_U).isSymmSndFDerivAt (by simp)).eq _ _

theorem D1_sub (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    D1 hw φ g (Y - Z) = D1 hw φ g Y - D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y - Matrix.of.symm Z) = _
  rw [map_sub]
  rfl

theorem D1_add (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    D1 hw φ g (Y + Z) = D1 hw φ g Y + D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y + Matrix.of.symm Z) = _
  rw [map_add]
  rfl

theorem D1_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (c : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    D1 hw φ g (c • Y) = (c : ℂ) * D1 hw φ g Y := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (c • Matrix.of.symm Y) = _
  rw [map_smul, Complex.real_smul]
  rfl

theorem archDerivAtComplex_comm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (i j : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw i (archDerivAtComplex hw j φ) g - archDerivAtComplex hw j (archDerivAtComplex hw i φ) g =
      D1 hw φ g (archDirMatrixComplex i * archDirMatrixComplex j - archDirMatrixComplex j * archDirMatrixComplex i) := by
  rw [archDerivAtComplex_archDerivAtComplex_eq hw hφ, archDerivAtComplex_archDerivAtComplex_eq hw hφ, D2_symm hw hφ g (archDirMatrixComplex j), D1_sub]
  ring

end ArchCxGL

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

theorem archDerivAtComplex_sub' {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ - ψ) = archDerivAtComplex hw d φ - archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, archDerivAtComplex_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAtComplex_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem D1_neg (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    D1 hw φ g (-Y) = -D1 hw φ g Y := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (-Matrix.of.symm Y) = _
  rw [map_neg]
  rfl

theorem archDelAt_apply (d : ArchDir) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g -
      Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDelAt_add' {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDir) :
    archDelAt hw d (φ + ψ) = archDelAt hw d φ + archDelAt hw d ψ := by
  funext g
  rw [Pi.add_apply, archDelAt_apply, archDelAt_apply, archDelAt_apply, archDerivAtComplex_add hφ hψ,
    archDerivAtComplex_add hφ hψ]
  simp only [Pi.add_apply]
  ring

theorem archDelAt_smul' (d : ArchDir) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDelAt hw d (c • φ) = c • archDelAt hw d φ := by
  funext g
  rw [Pi.smul_apply, archDelAt_apply, archDelAt_apply, archDerivAtComplex_smul, archDerivAtComplex_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit hw in
theorem archDirMatrixComplex_toComplexI (d : ArchDir) :
    archDirMatrixComplex d.toComplexI = Complex.I • archDirMatrixComplex d.toComplex := by
  cases d <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [archDirMatrixComplex, ArchDir.toComplex, ArchDir.toComplexI]

def Del1 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 2 : ℂ) * (D1 hw φ g Y - Complex.I * D1 hw φ g (Complex.I • Y))

def Del2 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 4 : ℂ) * (D2 hw φ g Y Z - D2 hw φ g (Complex.I • Y) (Complex.I • Z) -
    Complex.I * D2 hw φ g Y (Complex.I • Z) - Complex.I * D2 hw φ g (Complex.I • Y) Z)

theorem archDelAt_eq_Del1 {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : archDelAt hw d φ g = Del1 hw φ g (archDirMatrixComplex d.toComplex) := by
  rw [archDelAt_apply, archDerivAtComplex_eq_D1 hw hφ, archDerivAtComplex_eq_D1 hw hφ, archDirMatrixComplex_toComplexI]
  rfl

theorem Del1_add (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    Del1 hw φ g (Y + Z) = Del1 hw φ g Y + Del1 hw φ g Z := by
  simp only [Del1, smul_add, D1_add]
  ring

theorem Del1_sub (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    Del1 hw φ g (Y - Z) = Del1 hw φ g Y - Del1 hw φ g Z := by
  simp only [Del1, smul_sub, D1_sub]
  ring

theorem Del1_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (c : ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    Del1 hw φ g (c • Y) = c * Del1 hw φ g Y := by
  have h1 : c • Y = (c.re : ℝ) • Y + (c.im : ℝ) • (Complex.I • Y) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
    linear_combination -(Y i j) * Complex.re_add_im c
  have h2 : Complex.I • (c • Y) = (c.re : ℝ) • (Complex.I • Y) - (c.im : ℝ) • Y := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
    linear_combination (-(Y i j) * Complex.I) * Complex.re_add_im c + (Y i j) * (c.im : ℂ) * Complex.I_sq
  unfold Del1
  rw [h2, h1, D1_add, D1_sub, D1_smul, D1_smul, D1_smul, D1_smul]
  linear_combination ((1 / 2 : ℂ) * D1 hw φ g Y - (1 / 2 : ℂ) * Complex.I * D1 hw φ g (Complex.I • Y)) *
    Complex.re_add_im c + (1 / 2 : ℂ) * (c.im : ℂ) * D1 hw φ g (Complex.I • Y) * Complex.I_sq

theorem Del2_symm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : Del2 hw φ g Y Z = Del2 hw φ g Z Y := by
  unfold Del2
  rw [D2_symm hw hφ g Y Z, D2_symm hw hφ g (Complex.I • Y) (Complex.I • Z), D2_symm hw hφ g Y (Complex.I • Z),
    D2_symm hw hφ g (Complex.I • Y) Z]
  ring

theorem archDerivAtComplex_archDelAt {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (c : ArchDirComplex) (b : ArchDir) :
    archDerivAtComplex hw c (archDelAt hw b φ) =
      (1 / 2 : ℂ) • (archDerivAtComplex hw c (archDerivAtComplex hw b.toComplex φ) -
        Complex.I • archDerivAtComplex hw c (archDerivAtComplex hw b.toComplexI φ)) := by
  show archDerivAtComplex hw c ((1 / 2 : ℂ) • (archDerivAtComplex hw b.toComplex φ -
    Complex.I • archDerivAtComplex hw b.toComplexI φ)) = _
  rw [archDerivAtComplex_smul, archDerivAtComplex_sub' hw (hφ.archDerivAtComplex _) ((hφ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]

theorem archDelAt_archDelAt_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (a b : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw a (archDelAt hw b φ) g =
      Del2 hw φ g (archDirMatrixComplex a.toComplex) (archDirMatrixComplex b.toComplex) +
        Del1 hw φ g (archDirMatrixComplex a.toComplex * archDirMatrixComplex b.toComplex) := by
  rw [archDelAt_apply, archDerivAtComplex_archDelAt hw hφ, archDerivAtComplex_archDelAt hw hφ]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [archDerivAtComplex_archDerivAtComplex_eq hw hφ, archDerivAtComplex_archDerivAtComplex_eq hw hφ,
    archDerivAtComplex_archDerivAtComplex_eq hw hφ, archDerivAtComplex_archDerivAtComplex_eq hw hφ,
    archDirMatrixComplex_toComplexI, archDirMatrixComplex_toComplexI]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul,
    D1_neg]
  unfold Del2 Del1
  linear_combination (1 / 4 : ℂ) * (D2 hw φ g (Complex.I • archDirMatrixComplex a.toComplex)
    (Complex.I • archDirMatrixComplex b.toComplex) - D1 hw φ g (archDirMatrixComplex a.toComplex *
      archDirMatrixComplex b.toComplex)) * Complex.I_sq

theorem archDelAt_comm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (a b : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw a (archDelAt hw b φ) g - archDelAt hw b (archDelAt hw a φ) g =
      Del1 hw φ g (archDirMatrixComplex a.toComplex * archDirMatrixComplex b.toComplex -
        archDirMatrixComplex b.toComplex * archDirMatrixComplex a.toComplex) := by
  rw [archDelAt_archDelAt_eq hw hφ, archDelAt_archDelAt_eq hw hφ,
    Del2_symm hw hφ g (archDirMatrixComplex b.toComplex) (archDirMatrixComplex a.toComplex), Del1_sub]
  ring

omit hw in
theorem bracket_H_E : archDirMatrixComplex .H * archDirMatrixComplex .E - archDirMatrixComplex .E * archDirMatrixComplex .H =
    (2 : ℂ) • archDirMatrixComplex .E := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; norm_num

omit hw in
theorem bracket_H_Fm : archDirMatrixComplex .H * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .H =
    (-2 : ℂ) • archDirMatrixComplex .Fm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; norm_num

omit hw in
theorem bracket_E_Fm : archDirMatrixComplex .E * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .E =
    (1 : ℂ) • archDirMatrixComplex .H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

theorem rel_E_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw .E (archDelAt hw .H φ) g = archDelAt hw .H (archDelAt hw .E φ) g - 2 * archDelAt hw .E φ g := by
  have h := archDelAt_comm hw hφ .H .E g
  rw [archDelAt_eq_Del1 hw hφ .E]
  simp only [ArchDir.toComplex] at h ⊢
  rw [bracket_H_E, Del1_smul] at h
  linear_combination -h

theorem rel_Fm_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw .Fm (archDelAt hw .H φ) g = archDelAt hw .H (archDelAt hw .Fm φ) g + 2 * archDelAt hw .Fm φ g := by
  have h := archDelAt_comm hw hφ .H .Fm g
  rw [archDelAt_eq_Del1 hw hφ .Fm]
  simp only [ArchDir.toComplex] at h ⊢
  rw [bracket_H_Fm, Del1_smul] at h
  linear_combination -h

theorem rel_Fm_E {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw .Fm (archDelAt hw .E φ) g = archDelAt hw .E (archDelAt hw .Fm φ) g - archDelAt hw .H φ g := by
  have h := archDelAt_comm hw hφ .E .Fm g
  rw [archDelAt_eq_Del1 hw hφ .H]
  simp only [ArchDir.toComplex] at h ⊢
  rw [bracket_E_Fm, Del1_smul] at h
  linear_combination -h

end ArchCxGL

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

def AdM (M : GL (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((M⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * X * (M : Matrix (Fin 2) (Fin 2) ℂ)

omit hw in
theorem AdM_smul (M : GL (Fin 2) ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : AdM M (c • X) = c • AdM M X := by
  unfold AdM
  rw [Matrix.mul_smul, Matrix.smul_mul]

omit hw in
theorem trace_archDirMatrixComplex (d : ArchDirComplex) : Matrix.trace (archDirMatrixComplex d) = 0 := by
  cases d <;> simp [archDirMatrixComplex, Matrix.trace_fin_two]

omit hw in
theorem AdM_traceless (M : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    (AdM M (archDirMatrixComplex d)) 1 1 = -(AdM M (archDirMatrixComplex d)) 0 0 := by
  have h : Matrix.trace (AdM M (archDirMatrixComplex d)) = 0 := by
    rw [AdM, Matrix.trace_units_conj', trace_archDirMatrixComplex]
  rw [Matrix.trace_fin_two] at h
  linear_combination h

omit hw in

theorem eq_smul_archDirMatrixComplex (Y : Matrix (Fin 2) (Fin 2) ℂ) (hY : Y 1 1 = -Y 0 0) :
    Y = Y 0 0 • archDirMatrixComplex .H + Y 0 1 • archDirMatrixComplex .E + Y 1 0 • archDirMatrixComplex .Fm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex, hY]

omit hw in

theorem eq_real_smul_archDirMatrixComplex (Y : Matrix (Fin 2) (Fin 2) ℂ) (hY : Y 1 1 = -Y 0 0) :
    Y = (Y 0 0).re • archDirMatrixComplex .H + (Y 0 0).im • archDirMatrixComplex .iH +
      (Y 0 1).re • archDirMatrixComplex .E + (Y 0 1).im • archDirMatrixComplex .iE +
      (Y 1 0).re • archDirMatrixComplex .Fm + (Y 1 0).im • archDirMatrixComplex .iFm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [archDirMatrixComplex, hY, Complex.real_smul]
  first
    | exact (Complex.re_add_im _).symm
    | (rw [← neg_add, Complex.re_add_im])

def cf (M : GL (Fin 2) ℂ) (d e : ArchDir) : ℂ :=
  match e with
  | .H => (AdM M (archDirMatrixComplex d.toComplex)) 0 0
  | .E => (AdM M (archDirMatrixComplex d.toComplex)) 0 1
  | .Fm => (AdM M (archDirMatrixComplex d.toComplex)) 1 0

def cr (M : GL (Fin 2) ℂ) (d : ArchDirComplex) (e : ArchDirComplex) : ℝ :=
  match e with
  | .H => ((AdM M (archDirMatrixComplex d)) 0 0).re
  | .iH => ((AdM M (archDirMatrixComplex d)) 0 0).im
  | .E => ((AdM M (archDirMatrixComplex d)) 0 1).re
  | .iE => ((AdM M (archDirMatrixComplex d)) 0 1).im
  | .Fm => ((AdM M (archDirMatrixComplex d)) 1 0).re
  | .iFm => ((AdM M (archDirMatrixComplex d)) 1 0).im

def Dconj (M : GL (Fin 2) ℂ) (d : ArchDirComplex) (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  (cr M d .H : ℂ) • archDerivAtComplex hw .H θ + (cr M d .iH : ℂ) • archDerivAtComplex hw .iH θ +
    (cr M d .E : ℂ) • archDerivAtComplex hw .E θ + (cr M d .iE : ℂ) • archDerivAtComplex hw .iE θ +
    (cr M d .Fm : ℂ) • archDerivAtComplex hw .Fm θ + (cr M d .iFm : ℂ) • archDerivAtComplex hw .iFm θ

def DelConj (M : GL (Fin 2) ℂ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  cf M d .H • archDelAt hw .H θ + cf M d .E • archDelAt hw .E θ + cf M d .Fm • archDelAt hw .Fm θ

theorem isArchSmoothAtComplex_Dconj (M : GL (Fin 2) ℂ) (d : ArchDirComplex) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) : IsArchSmoothAtComplex hw (Dconj hw M d θ) :=
  ((((((hθ.archDerivAtComplex .H).smul _).add ((hθ.archDerivAtComplex .iH).smul _)).add
    ((hθ.archDerivAtComplex .E).smul _)).add ((hθ.archDerivAtComplex .iE).smul _)).add
    ((hθ.archDerivAtComplex .Fm).smul _)).add ((hθ.archDerivAtComplex .iFm).smul _)

theorem isArchSmoothAtComplex_DelConj (M : GL (Fin 2) ℂ) (d : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) : IsArchSmoothAtComplex hw (DelConj hw M d θ) :=
  (((hθ.archDelAt .H).smul _).add ((hθ.archDelAt .E).smul _)).add ((hθ.archDelAt .Fm).smul _)

theorem Dconj_apply (M : GL (Fin 2) ℂ) (d : ArchDirComplex) (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Dconj hw M d θ g = (cr M d .H : ℂ) * archDerivAtComplex hw .H θ g + (cr M d .iH : ℂ) * archDerivAtComplex hw .iH θ g +
      (cr M d .E : ℂ) * archDerivAtComplex hw .E θ g + (cr M d .iE : ℂ) * archDerivAtComplex hw .iE θ g +
      (cr M d .Fm : ℂ) * archDerivAtComplex hw .Fm θ g + (cr M d .iFm : ℂ) * archDerivAtComplex hw .iFm θ g := by
  simp only [Dconj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem DelConj_apply (M : GL (Fin 2) ℂ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    DelConj hw M d θ g = cf M d .H * archDelAt hw .H θ g + cf M d .E * archDelAt hw .E θ g +
      cf M d .Fm * archDelAt hw .Fm θ g := by
  simp only [DelConj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem D1_AdM {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ) (M : GL (Fin 2) ℂ) (d : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) : D1 hw θ g (AdM M (archDirMatrixComplex d)) = Dconj hw M d θ g := by
  conv_lhs => rw [eq_real_smul_archDirMatrixComplex (AdM M (archDirMatrixComplex d)) (AdM_traceless M d)]
  rw [D1_add, D1_add, D1_add, D1_add, D1_add, D1_smul, D1_smul, D1_smul, D1_smul, D1_smul, D1_smul,
    ← archDerivAtComplex_eq_D1 hw hθ, ← archDerivAtComplex_eq_D1 hw hθ, ← archDerivAtComplex_eq_D1 hw hθ,
    ← archDerivAtComplex_eq_D1 hw hθ, ← archDerivAtComplex_eq_D1 hw hθ, ← archDerivAtComplex_eq_D1 hw hθ, Dconj_apply]
  rfl

theorem Del1_AdM {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ) (M : GL (Fin 2) ℂ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : Del1 hw θ g (AdM M (archDirMatrixComplex d.toComplex)) = DelConj hw M d θ g := by
  conv_lhs => rw [eq_smul_archDirMatrixComplex (AdM M (archDirMatrixComplex d.toComplex)) (AdM_traceless M _)]
  rw [Del1_add, Del1_add, Del1_smul, Del1_smul, Del1_smul]
  rw [show archDirMatrixComplex ArchDirComplex.H = archDirMatrixComplex (ArchDir.H).toComplex from rfl,
    show archDirMatrixComplex ArchDirComplex.E = archDirMatrixComplex (ArchDir.E).toComplex from rfl,
    show archDirMatrixComplex ArchDirComplex.Fm = archDirMatrixComplex (ArchDir.Fm).toComplex from rfl,
    ← archDelAt_eq_Del1 hw hθ, ← archDelAt_eq_Del1 hw hθ, ← archDelAt_eq_Del1 hw hθ, DelConj_apply]
  rfl

theorem archDerivAtComplex_rightTranslate_eq_Dconj (M : GL (Fin 2) ℂ) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (rightTranslate F (archComplexGLAt hw M) θ) =
      rightTranslate F (archComplexGLAt hw M) (Dconj hw M d θ) := by
  funext g
  rw [archDerivAtComplex_rightTranslate hw M hθ, ← AdM, D1_AdM hw hθ]
  rfl

theorem archDelAt_rightTranslate_eq_DelConj (M : GL (Fin 2) ℂ) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) (d : ArchDir) :
    archDelAt hw d (rightTranslate F (archComplexGLAt hw M) θ) =
      rightTranslate F (archComplexGLAt hw M) (DelConj hw M d θ) := by
  funext g
  rw [archDelAt_apply, archDerivAtComplex_rightTranslate hw M hθ, archDerivAtComplex_rightTranslate hw M hθ,
    archDirMatrixComplex_toComplexI, Matrix.mul_smul, Matrix.smul_mul, ← AdM]
  show Del1 hw θ (g * archComplexGLAt hw M) (AdM M (archDirMatrixComplex d.toComplex)) = _
  rw [Del1_AdM hw hθ]
  rfl

theorem archDerivAtComplex_Dconj (M : GL (Fin 2) ℂ) (d i : ArchDirComplex) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw i (Dconj hw M d θ) g =
      (cr M d .H : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .H θ) g +
      (cr M d .iH : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iH θ) g +
      (cr M d .E : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .E θ) g +
      (cr M d .iE : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iE θ) g +
      (cr M d .Fm : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .Fm θ) g +
      (cr M d .iFm : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iFm θ) g := by
  have sH := (hθ.archDerivAtComplex .H).smul (cr M d .H : ℂ)
  have siH := (hθ.archDerivAtComplex .iH).smul (cr M d .iH : ℂ)
  have sE := (hθ.archDerivAtComplex .E).smul (cr M d .E : ℂ)
  have siE := (hθ.archDerivAtComplex .iE).smul (cr M d .iE : ℂ)
  have sFm := (hθ.archDerivAtComplex .Fm).smul (cr M d .Fm : ℂ)
  have siFm := (hθ.archDerivAtComplex .iFm).smul (cr M d .iFm : ℂ)
  unfold Dconj
  rw [archDerivAtComplex_add ((((sH.add siH).add sE).add siE).add sFm) siFm,
    archDerivAtComplex_add (((sH.add siH).add sE).add siE) sFm,
    archDerivAtComplex_add ((sH.add siH).add sE) siE,
    archDerivAtComplex_add (sH.add siH) sE,
    archDerivAtComplex_add sH siH,
    archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul, archDerivAtComplex_smul,
    archDerivAtComplex_smul, archDerivAtComplex_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem archDelAt_DelConj (M : GL (Fin 2) ℂ) (d i : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) (g : AdelicGL2 (𝓞 F) F) :
    archDelAt hw i (DelConj hw M d θ) g = cf M d .H * archDelAt hw i (archDelAt hw .H θ) g +
      cf M d .E * archDelAt hw i (archDelAt hw .E θ) g + cf M d .Fm * archDelAt hw i (archDelAt hw .Fm θ) g := by
  unfold DelConj
  rw [archDelAt_add' hw (((hθ.archDelAt .H).smul _).add ((hθ.archDelAt .E).smul _)) ((hθ.archDelAt .Fm).smul _),
    archDelAt_add' hw ((hθ.archDelAt .H).smul _) ((hθ.archDelAt .E).smul _), archDelAt_smul', archDelAt_smul',
    archDelAt_smul']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit hw in
theorem continuous_rightTranslate {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : Continuous θ) (k : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F k θ) :=
  hθ.comp (continuous_id.mul continuous_const)

theorem continuous_Dconj (M : GL (Fin 2) ℂ) (d : ArchDirComplex) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∀ e : ArchDirComplex, Continuous (archDerivAtComplex hw e θ)) : Continuous (Dconj hw M d θ) := by
  have e : Dconj hw M d θ = fun g =>
      (cr M d .H : ℂ) * archDerivAtComplex hw .H θ g + (cr M d .iH : ℂ) * archDerivAtComplex hw .iH θ g +
      (cr M d .E : ℂ) * archDerivAtComplex hw .E θ g + (cr M d .iE : ℂ) * archDerivAtComplex hw .iE θ g +
      (cr M d .Fm : ℂ) * archDerivAtComplex hw .Fm θ g + (cr M d .iFm : ℂ) * archDerivAtComplex hw .iFm θ g :=
    funext fun g => Dconj_apply hw M d θ g
  rw [e]
  exact (((((continuous_const.mul (h .H)).add (continuous_const.mul (h .iH))).add
    (continuous_const.mul (h .E))).add (continuous_const.mul (h .iE))).add
    (continuous_const.mul (h .Fm))).add (continuous_const.mul (h .iFm))

theorem continuous_archDerivAtComplex_Dconj (M : GL (Fin 2) ℂ) (d i : ArchDirComplex) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ)
    (h2 : ∀ e e' : ArchDirComplex, Continuous (archDerivAtComplex hw e (archDerivAtComplex hw e' θ))) :
    Continuous (archDerivAtComplex hw i (Dconj hw M d θ)) := by
  have : archDerivAtComplex hw i (Dconj hw M d θ) = fun g =>
      (cr M d .H : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .H θ) g +
      (cr M d .iH : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iH θ) g +
      (cr M d .E : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .E θ) g +
      (cr M d .iE : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iE θ) g +
      (cr M d .Fm : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .Fm θ) g +
      (cr M d .iFm : ℂ) * archDerivAtComplex hw i (archDerivAtComplex hw .iFm θ) g :=
    funext fun g => archDerivAtComplex_Dconj hw M d i hθ g
  rw [this]
  exact (((((continuous_const.mul (h2 i .H)).add (continuous_const.mul (h2 i .iH))).add
    (continuous_const.mul (h2 i .E))).add (continuous_const.mul (h2 i .iE))).add
    (continuous_const.mul (h2 i .Fm))).add (continuous_const.mul (h2 i .iFm))

end ArchCxGL

namespace ArchCxGL

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

omit hw in
theorem AdM_eq (M : GL (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    AdM M X = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ • (Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℂ) * X *
      (M : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [AdM, Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_mul]

omit hw in
theorem cf_H_H (M : GL (Fin 2) ℂ) :
    cf M .H .H = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 +
      (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_H_E (M : GL (Fin 2) ℂ) :
    cf M .H .E = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * (2 * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_H_Fm (M : GL (Fin 2) ℂ) :
    cf M .H .Fm = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * (-(2 * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_E_H (M : GL (Fin 2) ℂ) :
    cf M .E .H = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_E_E (M : GL (Fin 2) ℂ) :
    cf M .E .E = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_E_Fm (M : GL (Fin 2) ℂ) :
    cf M .E .Fm = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_Fm_H (M : GL (Fin 2) ℂ) :
    cf M .Fm .H = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_Fm_E (M : GL (Fin 2) ℂ) :
    cf M .Fm .E = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit hw in
theorem cf_Fm_Fm (M : GL (Fin 2) ℂ) :
    cf M .Fm .Fm = ((M : Matrix (Fin 2) (Fin 2) ℂ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  simp only [cf, ArchDir.toComplex, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, archDirMatrixComplex, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem casimir_identity (M : GL (Fin 2) ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * DelConj hw M .H (DelConj hw M .H φ) g - (1 / 2 : ℂ) * DelConj hw M .H φ g +
      DelConj hw M .E (DelConj hw M .Fm φ) g) = archCasimirAtComplex hw φ g := by
  have hdet : ((M : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hdetR : ((M : Matrix (Fin 2) (Fin 2) ℂ)).det = (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := Matrix.det_fin_two _
  show _ = (-((1 / 4 : ℂ) • archDelAt hw .H (archDelAt hw .H φ) - (1 / 2 : ℂ) • archDelAt hw .H φ +
    archDelAt hw .E (archDelAt hw .Fm φ))) g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, DelConj_apply,
    archDelAt_DelConj hw M _ _ hφ, rel_E_H hw hφ, rel_Fm_H hw hφ, rel_Fm_E hw hφ,
    cf_H_H, cf_H_E, cf_H_Fm, cf_E_H, cf_E_E, cf_E_Fm, cf_Fm_H, cf_Fm_E, cf_Fm_Fm]
  rw [hdetR] at hdet ⊢
  field_simp
  ring

theorem archCasimirAtComplex_rightTranslate (M : GL (Fin 2) ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw (rightTranslate F (archComplexGLAt hw M) φ) =
      rightTranslate F (archComplexGLAt hw M) (archCasimirAtComplex hw φ) := by
  have h1 : archDelAt hw .H (rightTranslate F (archComplexGLAt hw M) φ) =
      rightTranslate F (archComplexGLAt hw M) (DelConj hw M .H φ) :=
    archDelAt_rightTranslate_eq_DelConj hw M hφ .H
  have h2 : archDelAt hw .H (archDelAt hw .H (rightTranslate F (archComplexGLAt hw M) φ)) =
      rightTranslate F (archComplexGLAt hw M) (DelConj hw M .H (DelConj hw M .H φ)) := by
    rw [h1]
    exact archDelAt_rightTranslate_eq_DelConj hw M (isArchSmoothAtComplex_DelConj hw M .H hφ) .H
  have h3 : archDelAt hw .Fm (rightTranslate F (archComplexGLAt hw M) φ) =
      rightTranslate F (archComplexGLAt hw M) (DelConj hw M .Fm φ) :=
    archDelAt_rightTranslate_eq_DelConj hw M hφ .Fm
  have h4 : archDelAt hw .E (archDelAt hw .Fm (rightTranslate F (archComplexGLAt hw M) φ)) =
      rightTranslate F (archComplexGLAt hw M) (DelConj hw M .E (DelConj hw M .Fm φ)) := by
    rw [h3]
    exact archDelAt_rightTranslate_eq_DelConj hw M (isArchSmoothAtComplex_DelConj hw M .Fm hφ) .E
  rw [archCasimirAtComplex, h2, h1, h4]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rightTranslate]
  exact casimir_identity hw M hφ (g * archComplexGLAt hw M)

def conjFn (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun g => starRingEnd ℂ (φ g)

omit hw in
theorem conjFn_conjFn (φ : AdelicGL2 (𝓞 F) F → ℂ) : conjFn (conjFn φ) = φ := by
  funext g; exact Complex.conj_conj _

omit hw in
theorem rightTranslate_conjFn (k : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F k (conjFn φ) = conjFn (rightTranslate F k φ) := rfl

theorem isArchSmoothAtComplex_conjFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (conjFn φ) := by
  intro g
  have h := Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)
  simp only [Function.comp_def, Complex.conjCLE_apply] at h
  exact h

theorem archDerivAtComplex_conjFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (conjFn φ) = conjFn (archDerivAtComplex hw d φ) := by
  funext g
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hφ.differentiableAt_flow d g).hasDerivAt
  have h' : HasDerivAt (fun t : ℝ => starRingEnd ℂ (φ (g * archFlowAtComplex hw d t)))
      (starRingEnd ℂ (deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0)) 0 := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using h
  exact h'.deriv

theorem archDelBarAt_eq_conjFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir) :
    archDelBarAt hw d φ = conjFn (archDelAt hw d (conjFn φ)) := by
  funext g
  simp only [archDelBarAt, conjFn, Pi.smul_apply, Pi.add_apply, smul_eq_mul, archDelAt_apply,
    archDerivAtComplex_conjFn hw hφ]
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj, Complex.conj_I]
  ring

theorem archCasimirBarAtComplex_eq_conjFn {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirBarAtComplex hw φ = conjFn (archCasimirAtComplex hw (conjFn φ)) := by
  have hc := isArchSmoothAtComplex_conjFn hw hφ
  have e1 : archDelBarAt hw .H φ = conjFn (archDelAt hw .H (conjFn φ)) := archDelBarAt_eq_conjFn hw hφ .H
  have e2 : archDelBarAt hw .H (archDelBarAt hw .H φ) = conjFn (archDelAt hw .H (archDelAt hw .H (conjFn φ))) := by
    rw [e1, archDelBarAt_eq_conjFn hw (isArchSmoothAtComplex_conjFn hw (hc.archDelAt .H)), conjFn_conjFn]
  have e3 : archDelBarAt hw .E (archDelBarAt hw .Fm φ) = conjFn (archDelAt hw .E (archDelAt hw .Fm (conjFn φ))) := by
    rw [archDelBarAt_eq_conjFn hw hφ .Fm,
      archDelBarAt_eq_conjFn hw (isArchSmoothAtComplex_conjFn hw (hc.archDelAt .Fm)), conjFn_conjFn]
  unfold archCasimirBarAtComplex archCasimirAtComplex
  rw [e2, e1, e3]
  funext g
  simp only [conjFn, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_add, map_sub,
    map_mul, map_div₀, map_one, map_ofNat]

theorem archCasimirBarAtComplex_rightTranslate (M : GL (Fin 2) ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirBarAtComplex hw (rightTranslate F (archComplexGLAt hw M) φ) =
      rightTranslate F (archComplexGLAt hw M) (archCasimirBarAtComplex hw φ) := by
  rw [archCasimirBarAtComplex_eq_conjFn hw (isArchSmoothAtComplex_rightTranslate hw M hφ), ← rightTranslate_conjFn,
    archCasimirAtComplex_rightTranslate hw M (isArchSmoothAtComplex_conjFn hw hφ), ← rightTranslate_conjFn,
    ← archCasimirBarAtComplex_eq_conjFn hw hφ]

theorem package (M : GL (Fin 2) ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    IsArchSmoothAtComplex hw (rightTranslate F (archComplexGLAt hw M) x) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate F (archComplexGLAt hw M) x))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
      (rightTranslate F (archComplexGLAt hw M) x)))) ∧
    archCasimirAtComplex hw (rightTranslate F (archComplexGLAt hw M) x) =
      rightTranslate F (archComplexGLAt hw M) (archCasimirAtComplex hw x) ∧
    archCasimirBarAtComplex hw (rightTranslate F (archComplexGLAt hw M) x) =
      rightTranslate F (archComplexGLAt hw M) (archCasimirBarAtComplex hw x) := by
  refine ⟨isArchSmoothAtComplex_rightTranslate hw M hxs, fun d => ?_, fun d d' => ?_,
    archCasimirAtComplex_rightTranslate hw M hxs, archCasimirBarAtComplex_rightTranslate hw M hxs⟩
  · rw [archDerivAtComplex_rightTranslate_eq_Dconj hw M hxs]
    exact continuous_rightTranslate (continuous_Dconj hw M d hD1) _
  · rw [archDerivAtComplex_rightTranslate_eq_Dconj hw M hxs,
      archDerivAtComplex_rightTranslate_eq_Dconj hw M (isArchSmoothAtComplex_Dconj hw M d' hxs)]
    refine continuous_rightTranslate (continuous_Dconj hw M d fun e => ?_) _
    exact continuous_archDerivAtComplex_Dconj hw M d' e hxs hD2

end ArchCxGL
set_option linter.unusedVariables false in
/-- Right translation by a complex archimedean element preserves complex
archimedean smoothness, the first and second flow derivatives, and both Casimirs. -/
theorem archCasimirAtComplex_rightTranslate_archComplexGLAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ m : GL (Fin 2) ℂ,
        IsArchSmoothAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (archComplexGLAt hw m) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (archComplexGLAt hw m) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (archComplexGLAt hw m) x) =
          rightTranslate K (archComplexGLAt hw m) (archCasimirBarAtComplex hw x) := by
  intro m
  exact ArchCxGL.package hw m x hxs hD1 hD2


/-! ### The four complex leaves

The complex twin of the four real leaves: the fifteen commutator identities of the six complex
directions (a `3 × 3` bracket table on `archDirMatrixComplex`), the weight-one character identities
`iH = 0`, `F⁻ = E`, `iF⁻ = −iE`, the Casimir's commutation with a right translation by a row
isometry at a different place (both Casimirs), and `GL₂(ℂ)`-invariance for a function killed by all
six derivatives. Each headline is stated at its `Theorems/` wrapper; the helpers are the pin's own,
`private` as the pin has them (its local `dirM` is the port's `archDirMatrixComplex`).

The port's `ArchCxGL` already holds the six-direction chart engine this leaf continues
(`archDerivAtComplex_eq_D1`, `archDerivAtComplex_archDerivAtComplex_eq`, `D2_symm`, `D1_sub`,
`D1_smul`, `archDerivAtComplex_comm`), stated with `archDirMatrixComplex` where the pin writes its
local `dirM`; those are imported, not re-stated. -/

/-! #### The bracket table -/

namespace Ws26

namespace CommC

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix
open ArchCxGL

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

private theorem D1_zero (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    D1 hw φ g 0 = 0 := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm 0) = 0
  have : (Matrix.of.symm (0 : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Fin 2 → ℂ) = 0 := rfl
  rw [this, map_zero]

private theorem comm_of_bracket {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    {i j k : ArchDirComplex} {c : ℝ} {c' : ℂ} (hc : (c : ℂ) = c')
    (hb : archDirMatrixComplex i * archDirMatrixComplex j - archDirMatrixComplex j * archDirMatrixComplex i
      = c • archDirMatrixComplex k) :
    archDerivAtComplex hw i (archDerivAtComplex hw j φ) -
      archDerivAtComplex hw j (archDerivAtComplex hw i φ) = c' • archDerivAtComplex hw k φ := by
  funext g
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, archDerivAtComplex_comm hw hφ, hb, D1_smul,
    ← archDerivAtComplex_eq_D1 hw hφ, hc]

private theorem comm_of_bracket_zero {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    {i j : ArchDirComplex}
    (hb : archDirMatrixComplex i * archDirMatrixComplex j - archDirMatrixComplex j * archDirMatrixComplex i = 0) :
    archDerivAtComplex hw i (archDerivAtComplex hw j φ) - archDerivAtComplex hw j (archDerivAtComplex hw i φ) = 0 := by
  funext g
  rw [Pi.sub_apply, Pi.zero_apply, archDerivAtComplex_comm hw hφ, hb, D1_zero]

section brackets

omit hw

private theorem br_H_E :
    archDirMatrixComplex .H * archDirMatrixComplex .E - archDirMatrixComplex .E * archDirMatrixComplex .H =
      (2 : ℝ) • archDirMatrixComplex .E := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; norm_num

private theorem br_H_Fm :
    archDirMatrixComplex .H * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .H =
      (-2 : ℝ) • archDirMatrixComplex .Fm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; norm_num

private theorem br_E_Fm :
    archDirMatrixComplex .E * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .E =
      (1 : ℝ) • archDirMatrixComplex .H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_H_iE :
    archDirMatrixComplex .H * archDirMatrixComplex .iE - archDirMatrixComplex .iE * archDirMatrixComplex .H =
      (2 : ℝ) • archDirMatrixComplex .iE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_H_iFm :
    archDirMatrixComplex .H * archDirMatrixComplex .iFm - archDirMatrixComplex .iFm * archDirMatrixComplex .H =
      (-2 : ℝ) • archDirMatrixComplex .iFm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_E_iFm :
    archDirMatrixComplex .E * archDirMatrixComplex .iFm - archDirMatrixComplex .iFm * archDirMatrixComplex .E =
      (1 : ℝ) • archDirMatrixComplex .iH := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_iE_Fm :
    archDirMatrixComplex .iE * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .iE =
      (1 : ℝ) • archDirMatrixComplex .iH := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_iH_E :
    archDirMatrixComplex .iH * archDirMatrixComplex .E - archDirMatrixComplex .E * archDirMatrixComplex .iH =
      (2 : ℝ) • archDirMatrixComplex .iE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_iH_Fm :
    archDirMatrixComplex .iH * archDirMatrixComplex .Fm - archDirMatrixComplex .Fm * archDirMatrixComplex .iH =
      (-2 : ℝ) • archDirMatrixComplex .iFm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_iH_iE :
    archDirMatrixComplex .iH * archDirMatrixComplex .iE - archDirMatrixComplex .iE * archDirMatrixComplex .iH =
      (-2 : ℝ) • archDirMatrixComplex .E := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_iH_iFm :
    archDirMatrixComplex .iH * archDirMatrixComplex .iFm - archDirMatrixComplex .iFm * archDirMatrixComplex .iH =
      (2 : ℝ) • archDirMatrixComplex .Fm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]; ring

private theorem br_iE_iFm :
    archDirMatrixComplex .iE * archDirMatrixComplex .iFm - archDirMatrixComplex .iFm * archDirMatrixComplex .iE =
      (-1 : ℝ) • archDirMatrixComplex .H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_H_iH :
    archDirMatrixComplex .H * archDirMatrixComplex .iH - archDirMatrixComplex .iH * archDirMatrixComplex .H = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_E_iE :
    archDirMatrixComplex .E * archDirMatrixComplex .iE - archDirMatrixComplex .iE * archDirMatrixComplex .E = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

private theorem br_Fm_iFm :
    archDirMatrixComplex .Fm * archDirMatrixComplex .iFm - archDirMatrixComplex .iFm * archDirMatrixComplex .Fm = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrixComplex]

end brackets

private theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comm_of_bracket hw hφ (by norm_num) br_H_E
  · exact comm_of_bracket hw hφ (by norm_num) br_H_Fm
  · exact comm_of_bracket hw hφ (by norm_num) br_E_Fm
  · exact comm_of_bracket hw hφ (by norm_num) br_H_iE
  · exact comm_of_bracket hw hφ (by norm_num) br_H_iFm
  · exact comm_of_bracket hw hφ (by norm_num) br_E_iFm
  · exact comm_of_bracket hw hφ (by norm_num) br_iE_Fm
  · exact comm_of_bracket hw hφ (by norm_num) br_iH_E
  · exact comm_of_bracket hw hφ (by norm_num) br_iH_Fm
  · exact comm_of_bracket hw hφ (by norm_num) br_iH_iE
  · exact comm_of_bracket hw hφ (by norm_num) br_iH_iFm
  · exact comm_of_bracket hw hφ (by norm_num) br_iE_iFm
  · exact comm_of_bracket_zero hw hφ br_H_iH
  · exact comm_of_bracket_zero hw hφ br_E_iE
  · exact comm_of_bracket_zero hw hφ br_Fm_iFm

end CommC

end Ws26

/-- **Headline.** The fifteen `𝔰𝔩₂(ℂ)` commutator identities of the six archimedean directions on a
complex-smooth `φ`: the `H`/`E`/`F⁻` triple as at a real place, the `iH`/`iE`/`iF⁻` triple, and the
mixed brackets. -/
theorem archDerivAtComplex_commutator_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 :=
  Ws26.CommC.main hw φ hφ

/-! #### The weight-one character identities -/

namespace Ws50KDER0

open Matrix Complex AutomorphicForm.WindowedSiegel NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
private theorem norm_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  have h : ∀ x : w.Completion, ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := fun x =>
    (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  conv_rhs => rw [← (ringEquivComplexOfIsComplex hw).apply_symm_apply z]
  rw [h]

private theorem apply_mul_archComplexGLAt_of_mem {w : InfinitePlace F} (hw : w.IsComplex)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hχ : HasArchCharacterAt₀ F w 1 φ)
    (m : GL (Fin 2) ℂ) (hm : m ∈ rowIsometrySubgroup₀ ℂ) (g : AdelicGL2 (𝓞 F) F) :
    φ (g * archComplexGLAt hw m) = φ g := by
  have hk := map_mem_rowIsometrySubgroup₀_of_normPreserving (ringEquivComplexOfIsComplex hw).symm
    (norm_ringEquivComplexOfIsComplex_symm hw) m hm
  have h := hχ ⟨_, hk⟩ g
  rw [MonoidHom.one_apply, Units.val_one, one_mul] at h
  exact h

private theorem mem_rowIsometrySubgroup₀_complex (m : GL (Fin 2) ℂ)
    (hdet : (m : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (hiso : ∀ x y : ℂ,
      ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
        + ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    m ∈ rowIsometrySubgroup₀ ℂ :=
  (mem_rowIsometrySubgroup₀_iff ℂ).mpr ⟨hdet, by rw [hdet]; exact norm_one, hiso⟩

private noncomputable def rotGL (t : ℝ) : GL (Fin 2) ℂ where
  val := !![(Real.cos t : ℂ), -(Real.sin t : ℂ); (Real.sin t : ℂ), (Real.cos t : ℂ)]
  inv := !![(Real.cos t : ℂ), (Real.sin t : ℂ); -(Real.sin t : ℂ), (Real.cos t : ℂ)]
  val_inv := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;>
      linear_combination h
  inv_val := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;>
      linear_combination h

private noncomputable def swayGL (t : ℝ) : GL (Fin 2) ℂ where
  val := !![(Real.cos t : ℂ), (Real.sin t : ℂ) * I; (Real.sin t : ℂ) * I, (Real.cos t : ℂ)]
  inv := !![(Real.cos t : ℂ), -((Real.sin t : ℂ) * I); -((Real.sin t : ℂ) * I), (Real.cos t : ℂ)]
  val_inv := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;>
      simp only [Complex.I_sq] <;> linear_combination h
  inv_val := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;>
      simp only [Complex.I_sq] <;> linear_combination h

private theorem rotGL_mem (t : ℝ) : rotGL t ∈ rowIsometrySubgroup₀ ℂ := by
  have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · simp [rotGL, Matrix.det_fin_two, -Complex.ofReal_cos, -Complex.ofReal_sin]; linear_combination h
  · intro x y
    simp only [rotGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr := Real.cos_sq_add_sin_sq t
    ring_nf
    nlinarith [hr, sq_nonneg x.re, sq_nonneg x.im, sq_nonneg y.re, sq_nonneg y.im]

private theorem swayGL_mem (t : ℝ) : swayGL t ∈ rowIsometrySubgroup₀ ℂ := by
  have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · simp [swayGL, Matrix.det_fin_two, -Complex.ofReal_cos, -Complex.ofReal_sin]; ring_nf; simp only [Complex.I_sq]; linear_combination h
  · intro x y
    simp only [swayGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr := Real.cos_sq_add_sin_sq t
    ring_nf
    nlinarith [hr, sq_nonneg x.re, sq_nonneg x.im, sq_nonneg y.re, sq_nonneg y.im]

private theorem flow_iH_mem (t : ℝ) : archFlowMatrixComplex .iH t ∈ rowIsometrySubgroup₀ ℂ := by
  have hcoe : ((archFlowMatrixComplex .iH t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp ((t : ℂ) * I), 0; 0, Complex.exp (-((t : ℂ) * I))] := by
    show ((splitTorusGL2Complex ((t : ℂ) * I) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [splitTorusGL2Complex_coe]
  have hn1 : ‖Complex.exp ((t : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hn2 : ‖Complex.exp (-((t : ℂ) * I))‖ = 1 := by
    rw [show -((t : ℂ) * I) = ((-t : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-t)
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · rw [hcoe, Matrix.det_fin_two_of, ← Complex.exp_add]; simp
  · intro x y
    rw [hcoe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add, norm_mul, hn1, hn2, mul_one]

private theorem archComplexGLAt_eq_lift {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m = archComplexLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero
  have h := archComplexLiftAt_mul_archComplexGLAt hw hdet m
  rw [archComplexLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

private theorem hasDerivAt_chart {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ) (hM0 : M 0 = 1)
    (hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm (M t) : Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm M') 0) :
    HasDerivAt (fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm (M t))))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm M')) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (M 0)) := by
    rw [hM0]
    exact (((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  exact hdiff.comp_hasDerivAt (0 : ℝ) hM

private theorem archDerivAtComplex_eq {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d φ g =
      fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm (archDirMatrixComplex d)) := by
  have hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex d)) 0 := by
    have h := hasDerivAt_of_symm_mul_archFlowMatrixComplex (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) d
    simp only [Equiv.apply_symm_apply, one_mul] at h
    exact h
  have h := hasDerivAt_chart hφ g (fun t => ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))
    (archDirMatrixComplex d)
    (by show ((archFlowMatrixComplex d 0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1; rw [archFlowMatrixComplex_zero, Units.val_one])
    hM
  have hfun : (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm
        ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) := by
    funext t; rw [archFlowAtComplex, archComplexGLAt_eq_lift]
  unfold archDerivAtComplex
  rw [hfun]
  exact h.deriv

private theorem fderiv_apply_eq_zero_of_mem {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hχ : HasArchCharacterAt₀ F w 1 φ) (g : AdelicGL2 (𝓞 F) F)
    (M : ℝ → GL (Fin 2) ℂ) (hmem : ∀ t, M t ∈ rowIsometrySubgroup₀ ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ)
    (hM0 : M 0 = 1)
    (hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm M') 0) :
    fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm M') = 0 := by
  have h := hasDerivAt_chart hφ g (fun t => ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) M'
    (by show ((M 0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1; rw [hM0, Units.val_one]) hM
  have hconst : (fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm
      ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))) = fun _ => φ g := by
    funext t
    rw [← archComplexGLAt_eq_lift, apply_mul_archComplexGLAt_of_mem hw hχ (M t) (hmem t) g]
  rw [hconst] at h
  exact (h.unique (hasDerivAt_const (0 : ℝ) (φ g))).symm ▸ rfl

private theorem hasDerivAt_rotGL :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((rotGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex .Fm - archDirMatrixComplex .E)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).ofReal_comp
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j
  · simpa [rotGL, archDirMatrixComplex] using hc
  · have h__af := hs.neg
    simp [rotGL, archDirMatrixComplex] at h__af ⊢
    exact h__af
  · simpa [rotGL, archDirMatrixComplex] using hs
  · simpa [rotGL, archDirMatrixComplex] using hc

private theorem hasDerivAt_swayGL :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((swayGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex .iE + archDirMatrixComplex .iFm)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ) * I) I 0 := by
    simpa using ((Real.hasDerivAt_sin 0).ofReal_comp).mul_const I
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j
  · simpa [swayGL, archDirMatrixComplex] using hc
  · simpa [swayGL, archDirMatrixComplex] using hs
  · simpa [swayGL, archDirMatrixComplex] using hs
  · simpa [swayGL, archDirMatrixComplex] using hc

private theorem rotGL_zero : rotGL 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotGL]

private theorem swayGL_zero : swayGL 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swayGL]

end Ws50KDER0

open Ws50KDER0 in
/-- **Headline.** At weight `1` the complex character kills the `iH`-derivative and forces the two
pairs `F⁻ = E`, `iF⁻ = −iE`: the sway and rotation row-isometry arguments of the pin. -/
theorem archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hχ : HasArchCharacterAt₀ F w 1 φ) :
    archDerivAtComplex hw .iH φ = 0 ∧
    archDerivAtComplex hw .Fm φ = archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iFm φ = -archDerivAtComplex hw .iE φ := by
  set L := fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (1 * archComplexLiftAt hw e))
    (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) with hL
  refine ⟨?_, ?_, ?_⟩
  ·
    funext g
    have hconst : (fun t : ℝ => φ (g * archFlowAtComplex hw .iH t)) = fun _ => φ g := by
      funext t
      exact apply_mul_archComplexGLAt_of_mem hw hχ _ (flow_iH_mem t) g
    show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw .iH t)) 0 = 0
    rw [hconst, deriv_const]
  · funext g
    have h0 := fderiv_apply_eq_zero_of_mem hφ hχ g rotGL rotGL_mem _ rotGL_zero hasDerivAt_rotGL
    rw [archDerivAtComplex_eq hφ, archDerivAtComplex_eq hφ]
    have hsub : (Matrix.of.symm (archDirMatrixComplex .Fm - archDirMatrixComplex .E) : Fin 2 → Fin 2 → ℂ) =
        Matrix.of.symm (archDirMatrixComplex .Fm) - Matrix.of.symm (archDirMatrixComplex .E) := rfl
    rw [hsub, map_sub, sub_eq_zero] at h0
    exact h0
  · funext g
    have h0 := fderiv_apply_eq_zero_of_mem hφ hχ g swayGL swayGL_mem _ swayGL_zero hasDerivAt_swayGL
    rw [Pi.neg_apply, archDerivAtComplex_eq hφ, archDerivAtComplex_eq hφ]
    have hadd : (Matrix.of.symm (archDirMatrixComplex .iE + archDirMatrixComplex .iFm) : Fin 2 → Fin 2 → ℂ) =
        Matrix.of.symm (archDirMatrixComplex .iE) + Matrix.of.symm (archDirMatrixComplex .iFm) := rfl
    rw [hadd, map_add, add_eq_zero_iff_neg_eq] at h0
    exact h0.symm

/-! #### The row isometry at a different place -/

namespace CommAway40

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

section Commuting

variable {w : InfinitePlace F} (hw : w.IsComplex) {k : AdelicGL2 (𝓞 F) F}
  (hk : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * k = k * archComplexGLAt hw m)

include hk

private theorem archComplexLiftAt_mul_comm (e : Fin 2 → Fin 2 → ℂ) :
    archComplexLiftAt hw e * k = k * archComplexLiftAt hw e := by
  unfold archComplexLiftAt
  split_ifs
  · exact hk _
  · rw [one_mul, mul_one]

private theorem archFlowAtComplex_mul_comm (d : ArchDirComplex) (t : ℝ) :
    archFlowAtComplex hw d t * k = k * archFlowAtComplex hw d t :=
  hk _

private theorem isArchSmoothAtComplex_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (rightTranslate F k φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e * k)) =
      fun e => φ (g * k * archComplexLiftAt hw e) := by
    funext e
    rw [mul_assoc, archComplexLiftAt_mul_comm hw hk e, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

private theorem archDerivAtComplex_rightTranslate (d : ArchDirComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAtComplex hw d (rightTranslate F k φ) = rightTranslate F k (archDerivAtComplex hw d φ) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t * k)) 0 =
    deriv (fun t : ℝ => φ (g * k * archFlowAtComplex hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAtComplex_mul_comm hw hk d t, ← mul_assoc]

private theorem archDelAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDelAt hw d (rightTranslate F k φ) = rightTranslate F k (archDelAt hw d φ) := by
  unfold archDelAt
  rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
  rfl

private theorem archDelBarAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDelBarAt hw d (rightTranslate F k φ) = rightTranslate F k (archDelBarAt hw d φ) := by
  unfold archDelBarAt
  rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
  rfl

private theorem archCasimirAtComplex_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAtComplex hw (rightTranslate F k φ) =
      rightTranslate F k (archCasimirAtComplex hw φ) := by
  unfold archCasimirAtComplex
  simp only [archDelAt_rightTranslate hw hk]
  rfl

private theorem archCasimirBarAtComplex_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirBarAtComplex hw (rightTranslate F k φ) =
      rightTranslate F k (archCasimirBarAtComplex hw φ) := by
  unfold archCasimirBarAtComplex
  simp only [archDelBarAt_rightTranslate hw hk]
  rfl

private theorem package (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    IsArchSmoothAtComplex hw (rightTranslate F k x) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate F k x))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightTranslate F k x)))) ∧
    archCasimirAtComplex hw (rightTranslate F k x) = rightTranslate F k (archCasimirAtComplex hw x) ∧
    archCasimirBarAtComplex hw (rightTranslate F k x) = rightTranslate F k (archCasimirBarAtComplex hw x) := by
  refine ⟨isArchSmoothAtComplex_rightTranslate hw hk hxs, fun d => ?_, fun d d' => ?_,
    archCasimirAtComplex_rightTranslate hw hk x, archCasimirBarAtComplex_rightTranslate hw hk x⟩
  · rw [archDerivAtComplex_rightTranslate hw hk]
    exact CuspidalConstituent.continuous_rightTranslate F (hD1 d) k
  · rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
    exact CuspidalConstituent.continuous_rightTranslate F (hD2 d d') k

end Commuting

private theorem archComplexGLAt_mul_rowIsometryInclAt₀_comm {w w' : InfinitePlace F} (hw : w.IsComplex)
    (hne : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * rowIsometryInclAt₀ F w' k = rowIsometryInclAt₀ F w' k * archComplexGLAt hw m := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt F w _ * adelicArchGLInclAt F w' _ = adelicArchGLInclAt F w' _ * adelicArchGLInclAt F w _
  exact (commute_adelicArchGLInclAt_of_ne F (Ne.symm hne) _ _).eq

end CommAway40

-- The pin's `hw' : w' ≠ w` is a hypothesis the statement carries and no proof step needs; it stays
-- spelled `hw'` because the checker compares binder spelling.
set_option linter.unusedVariables false in
/-- **Headline.** Both Casimirs commute with right translation by a row isometry at a *different*
place, and complex smoothness with the first/second derivative continuities is preserved. -/
theorem archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x) := by
  have _ := hxc
  intro w' hw' k
  exact CommAway40.package hw (CommAway40.archComplexGLAt_mul_rowIsometryInclAt₀_comm hw hw' k) x hxs hD1 hD2

/-! #### Killing all six derivatives gives `GL₂(ℂ)`-invariance -/

namespace InvZeroC

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

private theorem apply_mul_archFlowAtComplex_eq (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex)
    (hd : archDerivAtComplex hw d φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archFlowAtComplex hw d t) = φ g := by
  set f : ℝ → ℂ := fun t => φ (g * archFlowAtComplex hw d t) with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 0 := by
      have hda := (hφ.differentiableAt_flow d (g * archFlowAtComplex hw d t)).hasDerivAt
      have hz : deriv (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) 0 = 0 :=
        congrFun hd (g * archFlowAtComplex hw d t)
      rwa [hz] at hda
    have h1 : (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s)) =
        fun s => f (t + s) := by
      funext s
      simp only [hf, archFlowAtComplex_add, mul_assoc]
    rw [h1, show (0 : ℝ) = t - t by simp] at h0
    have h2 := h0.comp_sub_const t t
    have h3 : (fun x : ℝ => f (t + (x - t))) = f := by
      funext x; congr 1; ring
    rw [h3] at h2
    exact h2
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hderiv t).deriv) t 0
  have h0 : f 0 = φ g := by simp only [hf, archFlowAtComplex_zero, mul_one]
  rw [← h0, ← hconst]

private theorem apply_mul_upper (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hE : archDerivAtComplex hw .E φ = 0) (hiE : archDerivAtComplex hw .iE φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (z : ℂ) :
    φ (g * archComplexGLAt hw (unipotentGL2 z)) = φ g := by
  have hz : unipotentGL2 z = unipotentGL2 ((z.re : ℝ) : ℂ) * unipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I) := by
    rw [← unipotentGL2_add]; congr 1; exact (Complex.re_add_im z).symm
  rw [hz, map_mul, ← mul_assoc]
  have h1 : archComplexGLAt hw (unipotentGL2 ((z.re : ℝ) : ℂ)) = archFlowAtComplex hw .E z.re := rfl
  have h2 : archComplexGLAt hw (unipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I)) = archFlowAtComplex hw .iE z.im := rfl
  rw [h1, h2, apply_mul_archFlowAtComplex_eq hw φ hφ .iE hiE, apply_mul_archFlowAtComplex_eq hw φ hφ .E hE]

private theorem apply_mul_lower (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hFm : archDerivAtComplex hw .Fm φ = 0) (hiFm : archDerivAtComplex hw .iFm φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (z : ℂ) :
    φ (g * archComplexGLAt hw (lowerUnipotentGL2 z)) = φ g := by
  have hz : lowerUnipotentGL2 z =
      lowerUnipotentGL2 ((z.re : ℝ) : ℂ) * lowerUnipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I) := by
    rw [← lowerUnipotentGL2_add]; congr 1; exact (Complex.re_add_im z).symm
  rw [hz, map_mul, ← mul_assoc]
  have h1 : archComplexGLAt hw (lowerUnipotentGL2 ((z.re : ℝ) : ℂ)) = archFlowAtComplex hw .Fm z.re := rfl
  have h2 : archComplexGLAt hw (lowerUnipotentGL2 (((z.im : ℝ) : ℂ) * Complex.I)) =
    archFlowAtComplex hw .iFm z.im := rfl
  rw [h1, h2, apply_mul_archFlowAtComplex_eq hw φ hφ .iFm hiFm, apply_mul_archFlowAtComplex_eq hw φ hφ .Fm hFm]

omit hw in
private theorem exists_eq_lower_upper_lower_upper (h : GL (Fin 2) ℂ)
    (hh : Matrix.GeneralLinearGroup.det h = 1) :
    ∃ s x c y : ℂ, h = lowerUnipotentGL2 s * unipotentGL2 x * lowerUnipotentGL2 c * unipotentGL2 y := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hh
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two] at this
    exact this
  set a := (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 with ha
  set b := (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 with hb
  set c := (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 with hc
  set d := (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 with hd
  have heta : (h : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _
  by_cases hc0 : c = 0
  · have ha0 : a ≠ 0 := by
      intro h0; rw [h0, hc0] at hdet; simp at hdet
    refine ⟨-1, (a - 1) / a, a, (b + d - 1) / a, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, heta, lowerUnipotentGL2_coe, lowerUnipotentGL2_coe,
      unipotentGL2_coe, unipotentGL2_coe]
    rw [hc0] at hdet ⊢
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | linear_combination hdet | linear_combination -hdet | linear_combination a * hdet |
        linear_combination (-a) * hdet | linear_combination c * hdet | linear_combination (-c) * hdet | ring1
  · refine ⟨0, (a - 1) / c, c, (d - 1) / c, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, heta, lowerUnipotentGL2_coe, lowerUnipotentGL2_coe,
      unipotentGL2_coe, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
      first | linear_combination hdet | linear_combination -hdet | linear_combination a * hdet |
        linear_combination (-a) * hdet | linear_combination c * hdet | linear_combination (-c) * hdet | ring1

private theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by
  obtain ⟨s, x, c, y, rfl⟩ := exists_eq_lower_upper_lower_upper h hh
  rw [map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    apply_mul_upper hw φ hφ (hD .E) (hD .iE), apply_mul_lower hw φ hφ (hD .Fm) (hD .iFm),
    apply_mul_upper hw φ hφ (hD .E) (hD .iE), apply_mul_lower hw φ hφ (hD .Fm) (hD .iFm)]

end InvZeroC

/-- **Headline.** A complex-smooth function killed by all six complex archimedean derivatives is
right-invariant under `GL₂(ℂ)` at the place, for determinant-one elements. -/
theorem apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g :=
  InvZeroC.main hw φ hφ hD g h hh

/-! #### SET-AF10 — the left complex Casimir acts by `archCasimirAtComplex`

The pin's `ElemC`/`CasLRC` prelude: the decomposition `y = m · y'` with the archimedean
component of `y'` at `w` trivial, the left-acting derivatives `Ld` along the negative flow,
`leftCas_one` at the identity, and transport to an arbitrary `y`. Helpers are the pin's own
and `private`; the headline is the `Theorems/` wrapper's statement. -/

namespace ElemC

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

-- The port's copy of `glArch_ext` lives in `ArchCasimir.lean` — in the *transcription* namespace
-- `Elem17LR`, not at `AutomorphicForm.*` — so importing that whole engine to reach it buys less than
-- these five lines: re-stated here, `private`, from the pin's own statement (pin `:930`).
omit [NumberField F] in
private theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

private theorem glArch_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    glArch (𝓞 F) F (archComplexGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) :=
  glArch_adelicArchGLIncl F _

private theorem archComponent_glArch_archComplexGLAt_of_ne {w w' : InfinitePlace F} (hw : w.IsComplex)
    (hw' : w' ≠ w) (m : GL (Fin 2) ℂ) :
    archComponent F w' (glArch (𝓞 F) F (archComplexGLAt hw m)) = 1 := by
  rw [glArch_archComplexGLAt, archComponent_archGLIncl_of_ne F hw']

private theorem glFin_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    glFin (𝓞 F) F (archComplexGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

private theorem archComplexGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace F} (hw : w.IsComplex)
    (m : GL (Fin 2) ℂ) {g : AdelicGL2 (𝓞 F) F}
    (hg : archComponent F w (glArch (𝓞 F) F g) = 1) :
    archComplexGLAt hw m * g = g * archComplexGLAt hw m := by
  apply eq_of_glArch_eq_of_glFin_eq
  · rw [map_mul, map_mul]
    apply glArch_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw' : w' = w
    · subst hw'; rw [hg, mul_one, one_mul]
    · rw [archComponent_glArch_archComplexGLAt_of_ne hw hw', one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_archComplexGLAt, one_mul, mul_one]

end ElemC

namespace CasLRC

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix ArchCxGL

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

private def Ld (d : ArchDirComplex) (θ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) : ℂ :=
  deriv (fun t : ℝ => θ (archFlowAtComplex hw d (-t) * y)) 0

omit hw in
private theorem hasDerivAt_negflow_mul_const (d : ArchDirComplex) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrixComplex d (-t) : Matrix (Fin 2) (Fin 2) ℂ) * X))
      (Matrix.of.symm (-(archDirMatrixComplex d * X))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h0 : HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i k)
      (archDirMatrixComplex d i k) (-0) := by
    rw [neg_zero]; exact hasDerivAt_archFlowMatrixComplex_apply d i k
  have h := (h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).mul_const (X k j)
  simpa using h

omit hw in
private theorem hasDerivAt_const_mul_negflow (d : ArchDirComplex) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm (X * (archFlowMatrixComplex d (-t) : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (-(X * archDirMatrixComplex d))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h0 : HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) k j)
      (archDirMatrixComplex d k j) (-0) := by
    rw [neg_zero]; exact hasDerivAt_archFlowMatrixComplex_apply d k j
  have h := (h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).const_mul (X i k)
  simpa using h

private theorem negflow_mul_lift (d : ArchDirComplex) (t : ℝ) {e : Fin 2 → Fin 2 → ℂ}
    (he : (Matrix.of e).det ≠ 0) :
    archFlowAtComplex hw d (-t) * archComplexLiftAt hw e =
      1 * archComplexLiftAt hw (Matrix.of.symm ((archFlowMatrixComplex d (-t) : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.of e)) := by
  rw [one_mul, archFlowAtComplex, archComplexGLAt_mul_archComplexLiftAt hw _ he]

private theorem Ld_apply_lift {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (d : ArchDirComplex) {e : Fin 2 → Fin 2 → ℂ} (he : (Matrix.of e).det ≠ 0) :
    Ld hw d θ (archComplexLiftAt hw e) =
      fderiv ℝ (chart hw θ 1) e (Matrix.of.symm (-(archDirMatrixComplex d * Matrix.of e))) := by
  have hfun : (fun t : ℝ => θ (archFlowAtComplex hw d (-t) * archComplexLiftAt hw e)) =
      fun t => chart hw θ 1 (Matrix.of.symm ((archFlowMatrixComplex d (-t) : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.of e)) := by
    funext t
    rw [negflow_mul_lift hw d t he]
    rfl
  have h0 : Matrix.of.symm ((archFlowMatrixComplex d (-0) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of e) = e := by
    rw [neg_zero, archFlowMatrixComplex_zero, Units.val_one, Matrix.one_mul, Equiv.symm_apply_apply]
  have hdiff : HasFDerivAt (chart hw θ 1) (fderiv ℝ (chart hw θ 1) e)
      (Matrix.of.symm ((archFlowMatrixComplex d (-0) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of e)) := by
    rw [h0]; exact hasFDerivAt_chart hw hθ 1 he
  show deriv (fun t : ℝ => θ (archFlowAtComplex hw d (-t) * archComplexLiftAt hw e)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_negflow_mul_const d (Matrix.of e))).deriv

private theorem Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (d : ArchDirComplex) : Ld hw d θ 1 = -archDerivAtComplex hw d θ 1 := by
  have h := Ld_apply_lift hw hθ d (e := Matrix.of.symm 1) one_mem_U
  rw [archComplexLiftAt_of_symm_one, Equiv.apply_symm_apply, Matrix.mul_one] at h
  rw [h, archDerivAtComplex_eq_D1 hw hθ, D1]
  show fderiv ℝ (chart hw θ 1) (Matrix.of.symm 1) (-Matrix.of.symm (archDirMatrixComplex d)) = _
  rw [map_neg]

private theorem Ld_Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (i j : ArchDirComplex) :
    Ld hw i (Ld hw j θ) 1 =
      D2 hw θ 1 (archDirMatrixComplex i) (archDirMatrixComplex j) +
        D1 hw θ 1 (archDirMatrixComplex j * archDirMatrixComplex i) := by
  have hfun : (fun t : ℝ => Ld hw j θ (archFlowAtComplex hw i (-t) * 1)) =
      fun t => (fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ))))
        (Matrix.of.symm (-(archDirMatrixComplex j * (archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrixComplex i (-t)).isUnit).ne_zero
    rw [mul_one, archFlowAtComplex, archComplexGLAt_eq_archComplexLiftAt, Ld_apply_lift hw hθ j hdet,
      Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw θ 1) (Matrix.of.symm 1) := contDiffAt_chart hw hθ 1 one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw θ 1)) (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (-archDirMatrixComplex i)) 0 := by
    have h := hasDerivAt_negflow_mul_const i (1 : Matrix (Fin 2) (Fin 2) ℂ)
    simp only [Matrix.mul_one] at h
    exact h
  have hγ0 : Matrix.of.symm ((archFlowMatrixComplex i (-0) : Matrix (Fin 2) (Fin 2) ℂ)) = Matrix.of.symm 1 := by
    rw [neg_zero, archFlowMatrixComplex_zero, Units.val_one]
  have hA : HasDerivAt
      (fun t : ℝ => fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ))))
      (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1) (Matrix.of.symm (-archDirMatrixComplex i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hv : HasDerivAt
      (fun t : ℝ => Matrix.of.symm (-(archDirMatrixComplex j * (archFlowMatrixComplex i (-t) : Matrix (Fin 2) (Fin 2) ℂ))))
      (Matrix.of.symm (archDirMatrixComplex j * archDirMatrixComplex i)) 0 := by
    have h := (hasDerivAt_const_mul_negflow i (archDirMatrixComplex j)).neg
    convert h using 1
    · funext t i j
      simp only [Matrix.of_symm_apply, Pi.neg_apply, Matrix.neg_apply]
    · funext i j
      simp only [Matrix.of_symm_apply, Pi.neg_apply, Matrix.neg_apply, neg_neg]
  have h := hA.clm_apply hv
  show deriv (fun t : ℝ => Ld hw j θ (archFlowAtComplex hw i (-t) * 1)) 0 = _
  rw [hfun, h.deriv]
  simp only [neg_zero, archFlowMatrixComplex_zero, Units.val_one, Matrix.mul_one, D2, D1]
  have e1 : (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (-archDirMatrixComplex i)) =
      -((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrixComplex i))) := map_neg _ _
  have e2 : ((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrixComplex i)))
      (Matrix.of.symm (-archDirMatrixComplex j)) =
      -(((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrixComplex i)))
        (Matrix.of.symm (archDirMatrixComplex j))) :=
    map_neg _ _
  rw [e1, _root_.neg_apply, e2, neg_neg]

private theorem Ld_Ld_one_eq {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (i j : ArchDirComplex) :
    Ld hw i (Ld hw j θ) 1 = archDerivAtComplex hw j (archDerivAtComplex hw i θ) 1 := by
  rw [Ld_Ld_one hw hθ, archDerivAtComplex_archDerivAtComplex_eq hw hθ, D2_symm hw hθ]

private theorem archDelBarAt_apply' (d : ArchDir) (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archDelBarAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g +
      Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelBarAt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

private theorem casimirs_apply {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (g : AdelicGL2 (𝓞 F) F) :
    archCasimirAtComplex hw θ g =
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .H (archDerivAtComplex hw .H θ) g -
          Complex.I * archDerivAtComplex hw .H (archDerivAtComplex hw .iH θ) g) -
          Complex.I * ((1 / 2 : ℂ) * (archDerivAtComplex hw .iH (archDerivAtComplex hw .H θ) g -
          Complex.I * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH θ) g)))) -
        (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .H θ g - Complex.I * archDerivAtComplex hw .iH θ g)) +
        (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm θ) g -
          Complex.I * archDerivAtComplex hw .E (archDerivAtComplex hw .iFm θ) g) -
          Complex.I * ((1 / 2 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm θ) g -
          Complex.I * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm θ) g)))) ∧
    archCasimirBarAtComplex hw θ g =
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .H (archDerivAtComplex hw .H θ) g +
          Complex.I * archDerivAtComplex hw .H (archDerivAtComplex hw .iH θ) g) +
          Complex.I * ((1 / 2 : ℂ) * (archDerivAtComplex hw .iH (archDerivAtComplex hw .H θ) g +
          Complex.I * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH θ) g)))) -
        (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .H θ g + Complex.I * archDerivAtComplex hw .iH θ g)) +
        (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm θ) g +
          Complex.I * archDerivAtComplex hw .E (archDerivAtComplex hw .iFm θ) g) +
          Complex.I * ((1 / 2 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm θ) g +
          Complex.I * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm θ) g)))) := by
  have hb : ∀ (c : ArchDirComplex) (b : ArchDir), archDerivAtComplex hw c (archDelBarAt hw b θ) =
      (1 / 2 : ℂ) • (archDerivAtComplex hw c (archDerivAtComplex hw b.toComplex θ) +
        Complex.I • archDerivAtComplex hw c (archDerivAtComplex hw b.toComplexI θ)) := by
    intro c b
    show archDerivAtComplex hw c ((1 / 2 : ℂ) • (archDerivAtComplex hw b.toComplex θ +
      Complex.I • archDerivAtComplex hw b.toComplexI θ)) = _
    rw [archDerivAtComplex_smul, archDerivAtComplex_add (hθ.archDerivAtComplex _) ((hθ.archDerivAtComplex _).smul _),
      archDerivAtComplex_smul]
  constructor
  · unfold archCasimirAtComplex
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, archDelAt_apply,
      archDerivAtComplex_archDelAt hw hθ, ArchDir.toComplex, ArchDir.toComplexI]
  · unfold archCasimirBarAtComplex
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, archDelBarAt_apply', hb,
      ArchDir.toComplex, ArchDir.toComplexI]

private theorem leftCas_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ) :
    -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H θ) 1 + ((-Complex.I) : ℂ) * Ld hw .H (Ld hw .iH θ) 1 + ((-Complex.I) : ℂ) * Ld hw .iH (Ld hw .H θ) 1 + (-1 : ℂ) * Ld hw .iH (Ld hw .iH θ) 1)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H θ 1 + ((-Complex.I) : ℂ) * Ld hw .iH θ 1)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm θ) 1 + ((-Complex.I) : ℂ) * Ld hw .E (Ld hw .iFm θ) 1 + ((-Complex.I) : ℂ) * Ld hw .iE (Ld hw .Fm θ) 1 + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm θ) 1)) = archCasimirAtComplex hw θ 1 ∧
    -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H θ) 1 + (Complex.I : ℂ) * Ld hw .H (Ld hw .iH θ) 1 + (Complex.I : ℂ) * Ld hw .iH (Ld hw .H θ) 1 + (-1 : ℂ) * Ld hw .iH (Ld hw .iH θ) 1)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H θ 1 + (Complex.I : ℂ) * Ld hw .iH θ 1)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm θ) 1 + (Complex.I : ℂ) * Ld hw .E (Ld hw .iFm θ) 1 + (Complex.I : ℂ) * Ld hw .iE (Ld hw .Fm θ) 1 + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm θ) 1)) = archCasimirBarAtComplex hw θ 1 := by
  have hc := AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw θ hθ
  have r1 : archDerivAtComplex hw .Fm (archDerivAtComplex hw .E θ) 1 =
      archDerivAtComplex hw .E (archDerivAtComplex hw .Fm θ) 1 - archDerivAtComplex hw .H θ 1 := by
    have h := congrFun hc.2.2.1 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul] at h
    linear_combination -h
  have r2 : archDerivAtComplex hw .iFm (archDerivAtComplex hw .E θ) 1 =
      archDerivAtComplex hw .E (archDerivAtComplex hw .iFm θ) 1 - archDerivAtComplex hw .iH θ 1 := by
    have h := congrFun hc.2.2.2.2.2.1 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul] at h
    linear_combination -h
  have r3 : archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE θ) 1 =
      archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm θ) 1 - archDerivAtComplex hw .iH θ 1 := by
    have h := congrFun hc.2.2.2.2.2.2.1 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul] at h
    linear_combination -h
  have r4 : archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE θ) 1 =
      archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm θ) 1 + archDerivAtComplex hw .H θ 1 := by
    have h := congrFun hc.2.2.2.2.2.2.2.2.2.2.2.1 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linear_combination -h
  obtain ⟨k1, k2⟩ := casimirs_apply hw hθ 1
  simp only [Ld_Ld_one_eq hw hθ, Ld_one hw hθ]
  rw [k1, k2, r1, r2, r3, r4]
  constructor
  · linear_combination ((1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH θ) 1 +
        (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm θ) 1) * Complex.I_sq
  · linear_combination ((1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH θ) 1 +
        (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm θ) 1) * Complex.I_sq

-- The port's copy of `rightTranslate_mul` lives in `ArchCasimir.lean` (`OsAlg17`), outside this
-- module's import closure; the same reasoning as `glArch_ext` above — re-stated `private` from the
-- pin's own statement (pin `:1162`).
omit hw in
private theorem rightTranslate_mul (a b : AdelicGL2 (𝓞 F) F) (θ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (a * b) θ = rightTranslate F a (rightTranslate F b θ) := by
  funext z
  simp only [rightTranslate, mul_assoc]

private theorem Ld_rightTranslate (d : ArchDirComplex) (θ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) :
    Ld hw d (rightTranslate F y θ) = rightTranslate F y (Ld hw d θ) := by
  funext z
  simp only [Ld, rightTranslate, mul_assoc]

private theorem exists_decomp (y : AdelicGL2 (𝓞 F) F) :
    ∃ (m : GL (Fin 2) ℂ) (y' : AdelicGL2 (𝓞 F) F), archComponent F w (glArch (𝓞 F) F y') = 1 ∧
      y = archComplexGLAt hw m * y' := by
  set c := archComponent F w (glArch (𝓞 F) F y) with hc
  set m : GL (Fin 2) ℂ := glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) c with hm
  have hm' : archComplexGLAt hw m = adelicArchGLInclAt F w c := archComplexGLAt_glEquivOfRingEquiv hw c
  have hmc : archComponent F w (glArch (𝓞 F) F (archComplexGLAt hw m)) = c := by
    rw [hm']
    show archComponent F w (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w c))) = c
    rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  refine ⟨m, (archComplexGLAt hw m)⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
  rw [map_mul, map_mul, map_inv, map_inv, hmc, ← hc, inv_mul_cancel]

private theorem casimirs_rightTranslate_any (y : AdelicGL2 (𝓞 F) F) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAtComplex hw θ) :
    archCasimirAtComplex hw (rightTranslate F y θ) = rightTranslate F y (archCasimirAtComplex hw θ) ∧
    archCasimirBarAtComplex hw (rightTranslate F y θ) = rightTranslate F y (archCasimirBarAtComplex hw θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℂ, archComplexGLAt hw M * y' = y' * archComplexGLAt hw M :=
    fun M => ElemC.archComplexGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  constructor
  · rw [rightTranslate_mul, rightTranslate_mul,
      ArchCxGL.archCasimirAtComplex_rightTranslate hw m
        (CommAway40.isArchSmoothAtComplex_rightTranslate hw hk hθ),
      CommAway40.archCasimirAtComplex_rightTranslate hw hk]
  · rw [rightTranslate_mul, rightTranslate_mul,
      ArchCxGL.archCasimirBarAtComplex_rightTranslate hw m
        (CommAway40.isArchSmoothAtComplex_rightTranslate hw hk hθ),
      CommAway40.archCasimirBarAtComplex_rightTranslate hw hk]

private theorem isArchSmoothAtComplex_rightTranslate_any (y : AdelicGL2 (𝓞 F) F)
    {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ) :
    IsArchSmoothAtComplex hw (rightTranslate F y θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℂ, archComplexGLAt hw M * y' = y' * archComplexGLAt hw M :=
    fun M => ElemC.archComplexGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  rw [rightTranslate_mul]
  exact ArchCxGL.isArchSmoothAtComplex_rightTranslate hw m
    (CommAway40.isArchSmoothAtComplex_rightTranslate hw hk hθ)

private theorem leftCas_eq {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAtComplex hw θ)
    (y : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H θ) y + ((-Complex.I) : ℂ) * Ld hw .H (Ld hw .iH θ) y + ((-Complex.I) : ℂ) * Ld hw .iH (Ld hw .H θ) y + (-1 : ℂ) * Ld hw .iH (Ld hw .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H θ y + ((-Complex.I) : ℂ) * Ld hw .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm θ) y + ((-Complex.I) : ℂ) * Ld hw .E (Ld hw .iFm θ) y + ((-Complex.I) : ℂ) * Ld hw .iE (Ld hw .Fm θ) y + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm θ) y)) = archCasimirAtComplex hw θ y ∧
    -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H θ) y + (Complex.I : ℂ) * Ld hw .H (Ld hw .iH θ) y + (Complex.I : ℂ) * Ld hw .iH (Ld hw .H θ) y + (-1 : ℂ) * Ld hw .iH (Ld hw .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H θ y + (Complex.I : ℂ) * Ld hw .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm θ) y + (Complex.I : ℂ) * Ld hw .E (Ld hw .iFm θ) y + (Complex.I : ℂ) * Ld hw .iE (Ld hw .Fm θ) y + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm θ) y)) = archCasimirBarAtComplex hw θ y := by
  have h := leftCas_one hw (isArchSmoothAtComplex_rightTranslate_any hw y hθ)
  obtain ⟨c1, c2⟩ := casimirs_rightTranslate_any hw y hθ
  simp only [Ld_rightTranslate, c1, c2] at h
  simpa only [rightTranslate, one_mul] using h

end CasLRC

/-- **Headline.** The left-acting complex Casimir element agrees with `archCasimirAtComplex` at every
point, and likewise the bar-Casimir with `archCasimirBarAtComplex`; the complex analogue of
`leftCasimir_eq_archCasimirAt_of_isArchSmoothAt`. -/
theorem leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAtComplex hw θ) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + ((-Complex.I) : ℂ) * L .H (L .iH θ) y + ((-Complex.I) : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + ((-Complex.I) : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + ((-Complex.I) : ℂ) * L .E (L .iFm θ) y + ((-Complex.I) : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirAtComplex hw θ y ∧
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H θ) y + (Complex.I : ℂ) * L .H (L .iH θ) y + (Complex.I : ℂ) * L .iH (L .H θ) y + (-1 : ℂ) * L .iH (L .iH θ) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H θ y + (Complex.I : ℂ) * L .iH θ y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm θ) y + (Complex.I : ℂ) * L .E (L .iFm θ) y + (Complex.I : ℂ) * L .iE (L .Fm θ) y + (-1 : ℂ) * L .iE (L .iFm θ) y)) = archCasimirBarAtComplex hw θ y := by
  intro L y
  exact CasLRC.leftCas_eq hw hθ y

/-! #### SET-AF10 — the four complex Casimir leaves

The compact Casimir at `iH`-weight `n` with the raising operator vanishing acts by `−(n²+2)`;
the two `∂̄∂`/`∂∂̄` identities at `iH`-weight `m`; and the Casimir decomposition
`archCasimirAtComplex + archCasimirBarAtComplex` in terms of the compact Casimir and the
`iH`/`E+F⁻`/`iF⁻−iE` derivatives. Each is its `Theorems/` wrapper's statement, proved by the
pin's `solution` from the fifteen-fold commutator conjunction. -/

/-- **Headline.** At `iH`-weight `n` with the compact raising operator vanishing, the compact Casimir
acts by `−((n)² + 2)`. -/
theorem archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (n : ℕ)
    (hwt : archDerivAtComplex hw .iH φ = (Complex.I * (n : ℂ)) • φ)
    (hJ : archDerivAtComplex hw .Fm φ - archDerivAtComplex hw .E φ
      + Complex.I • (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) = 0) :
    archKCasimirAtComplex hw φ = (-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • φ := by
  obtain ⟨-, -, h3, -, -, h6, h7, -, -, -, -, -, -, h14, h15⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d
  have hsc : ∀ (c : ℂ) (d : ArchDirComplex), IsArchSmoothAtComplex hw (c • archDerivAtComplex hw d φ) :=
    fun c d => (hs d).smul c
  have Dsub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      archDerivAtComplex hw X (u - v) = archDerivAtComplex hw X u - archDerivAtComplex hw X v := by
    intro X u v hu hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul,
      neg_one_smul, ← sub_eq_add_neg]

  have hJX : ∀ X : ArchDirComplex,
      archDerivAtComplex hw X (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw X (archDerivAtComplex hw .E φ)
        + Complex.I • (archDerivAtComplex hw X (archDerivAtComplex hw .iE φ)
          + archDerivAtComplex hw X (archDerivAtComplex hw .iFm φ)) = 0 := by
    intro X
    have h := congrArg (archDerivAtComplex hw X) hJ
    have h0 : archDerivAtComplex hw X (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
      funext g; exact congrFun (archDerivAtComplex_const hw X 0) g
    have hsm2 : IsArchSmoothAtComplex hw
        (Complex.I • (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ)) := ((hs _).add (hs _)).smul _
    rw [h0, archDerivAtComplex_add ((hs _).sub (hs _)) hsm2, Dsub _ _ _ (hs _) (hs _), archDerivAtComplex_smul,
      archDerivAtComplex_add (hs _) (hs _)] at h
    exact h
  have hEJ := hJX .E
  have hFJ := hJX .Fm
  have hiEJ := hJX .iE
  have hiFJ := hJX .iFm

  simp only [archKCasimirAtComplex, archDerivAtComplex_add (hs _) (hs _), Dsub _ _ _ (hs _) (hs _)]
  have hHH : archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) = (Complex.I * (n : ℂ)) • ((Complex.I * (n : ℂ)) • φ) := by
    rw [hwt, archDerivAtComplex_smul, hwt]
  rw [hHH]
  rw [hwt] at h6 h7
  funext g
  replace h6 := congrFun h6 g
  replace h7 := congrFun h7 g
  replace h14 := congrFun h14 g
  replace h15 := congrFun h15 g
  replace hEJ := congrFun hEJ g
  replace hFJ := congrFun hFJ g
  replace hiEJ := congrFun hiEJ g
  replace hiFJ := congrFun hiFJ g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h6 h7 h14 h15 hEJ hFJ hiEJ hiFJ ⊢
  linear_combination -(hEJ - hFJ + Complex.I * hiEJ + Complex.I * hiFJ) + Complex.I * h14 + Complex.I * h6
    + Complex.I * h7 - Complex.I * h15
    + (2 * (n : ℂ) * φ g + (n : ℂ) ^ 2 * φ g
        + archDerivAtComplex hw .iE (archDerivAtComplex hw .iE φ) g
        + archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g
        + archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) g
        + archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

/-- **Headline.** The `E`/`F⁻`-mixed `∂̄∂` identity at `iH`-weight `m`. -/
theorem archDelAt_Fm_archDelAt_E_add_archDelBarAt_E_archDelBarAt_Fm_eq_of_archDerivAtComplex_iH_eq_smul
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .Fm (archDelAt hw .E φ) + archDelBarAt hw .E (archDelBarAt hw .Fm φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 + Complex.I * m / 2) • φ := by

  obtain ⟨-, -, hEF, -, -, hEiF, hiEF, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ

  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d

  have linSub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u - c • v)) = a • (archDerivAtComplex hw X u - c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, sub_eq_add_neg, ← neg_smul, archDerivAtComplex_add hu (hv.smul _),
      archDerivAtComplex_smul, neg_smul, ← sub_eq_add_neg]
  have linAdd : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u + c • v)) = a • (archDerivAtComplex hw X u + c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul]

  simp only [archDelAt, archDelBarAt, archCasimirAtComplex, archCasimirBarAtComplex, ArchDir.toComplex,
    ArchDir.toComplexI, linSub _ _ _ (hs _) (hs _), linAdd _ _ _ (hs _) (hs _)]

  have hHH : archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) = m • (m • φ) := by
    rw [hm, archDerivAtComplex_smul, hm]
  rw [hHH]
  rw [hm] at hEiF hiEF

  funext g
  have h3 := congrFun hEF g
  have h6 := congrFun hEiF g
  have h7 := congrFun hiEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h6 h7 h12 ⊢
  linear_combination (1 / 4 : ℂ) * h3 - (1 / 4 : ℂ) * h12 - (Complex.I / 4) * h6 - (Complex.I / 4) * h7
    + ((1 / 4 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g
        - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) g) + m ^ 2 * φ g / 8) * Complex.I_sq

/-- **Headline.** The twin `∂∂̄` identity at `iH`-weight `m`, in the other order. -/
theorem archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .E (archDelAt hw .Fm φ) + archDelBarAt hw .Fm (archDelBarAt hw .E φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 - Complex.I * m / 2) • φ := by
  obtain ⟨-, -, hEF, -, -, hEiF, hiEF, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d
  have linSub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u - c • v)) = a • (archDerivAtComplex hw X u - c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, sub_eq_add_neg, ← neg_smul, archDerivAtComplex_add hu (hv.smul _),
      archDerivAtComplex_smul, neg_smul, ← sub_eq_add_neg]
  have linAdd : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u + c • v)) = a • (archDerivAtComplex hw X u + c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul]
  simp only [archDelAt, archDelBarAt, archCasimirAtComplex, archCasimirBarAtComplex, ArchDir.toComplex,
    ArchDir.toComplexI, linSub _ _ _ (hs _) (hs _), linAdd _ _ _ (hs _) (hs _)]
  have hHH : archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) = m • (m • φ) := by
    rw [hm, archDerivAtComplex_smul, hm]
  rw [hHH]
  rw [hm] at hEiF hiEF
  rw [hm]
  funext g
  have h3 := congrFun hEF g
  have h6 := congrFun hEiF g
  have h7 := congrFun hiEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h6 h7 h12 ⊢
  linear_combination (1 / 4 : ℂ) * h3 + (Complex.I / 4) * h6 + (Complex.I / 4) * h7 - (1 / 4 : ℂ) * h12
    + ((1 / 4 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g
        - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) g) + m ^ 2 * φ g / 8) * Complex.I_sq

/-- **Headline.** The Casimir decomposition: `archCasimirAtComplex + archCasimirBarAtComplex` in terms
of the compact Casimir and the `iH`/`E+F⁻`/`iF⁻−iE` derivatives. -/
theorem archCasimirAtComplex_add_archCasimirBarAtComplex_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
      = (1 / 8 : ℂ) • archKCasimirAtComplex hw φ
        - (1 / 8 : ℂ) • (archDerivAtComplex hw .H (archDerivAtComplex hw .H φ) +
            (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ) +
              archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ + archDerivAtComplex hw .Fm φ)) +
            (archDerivAtComplex hw .iFm (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ) -
              archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ - archDerivAtComplex hw .iE φ))) := by
  obtain ⟨-, -, hEF, -, -, -, -, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d
  have hsc : ∀ (c : ℂ) (d : ArchDirComplex), IsArchSmoothAtComplex hw (c • archDerivAtComplex hw d φ) :=
    fun c d => (hs d).smul c
  have Dsub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v →
      archDerivAtComplex hw X (u - v) = archDerivAtComplex hw X u - archDerivAtComplex hw X v := by
    intro X u v hu hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul,
      neg_one_smul, ← sub_eq_add_neg]
  simp only [archCasimirAtComplex, archCasimirBarAtComplex, archKCasimirAtComplex, archDelAt, archDelBarAt,
    ArchDir.toComplex, ArchDir.toComplexI, archDerivAtComplex_smul,
    archDerivAtComplex_add (hs _) (hs _), archDerivAtComplex_add (hs _) (hsc _ _),
    Dsub _ _ _ (hs _) (hs _), Dsub _ _ _ (hs _) (hsc _ _)]
  funext g
  have h3 := congrFun hEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h12 ⊢
  linear_combination (-(1 / 4) : ℂ) * h3 + (1 / 4 : ℂ) * h12
    + (-(1 / 8 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g
        - (1 / 2 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

end AutomorphicForm
