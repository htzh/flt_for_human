/-
  The `𝔰𝔩₂` (Casimir) calculus at a real place, and its three headlines.

  For a real place `w` of a number field `F` the three directions `H`, `E`, `F⁻` are realised as
  one-parameter subgroups of `GL₂(𝔸_F)` (`archFlowAt`), and `archDerivAt hw d φ g =
  deriv (fun t => φ (g * archFlowAt hw d t)) 0` is the right-invariant derivative. The module
  carries the calculus those derivatives obey:

  * the *chart* `e ↦ φ (g · archRealLiftAt hw e)` on `det e ≠ 0`, its first and second
    derivatives `D1`/`D2`, the mixed-partial identity `archDerivAt_archDerivAt_eq` through the
    chart, and `archDerivAt_comm` (the commutator of two derivatives is `D1` of the commutator);
  * the adjoint action `AdM M X = M⁻¹ · X · M` with its nine structure coefficients `cf_*`, the
    three brackets `[H,E] = 2E`, `[H,F⁻] = -2F⁻`, `[E,F⁻] = H` (`bracket_*`) and their `rel_*`
    forms, and `Dconj`, the same operator written as a combination of `H`, `E`, `F⁻`;
  * `casimir_identity`: the Casimir `Ω` of a right translate is the composition of the translated
    Casimir with the adjoint operator — hence `Ω` commutes with the flows;
  * `leftCasimir_eq`: the enveloping-algebra element acting on the *left*,
    `L d γ y = deriv (fun t => γ (archFlowAt hw d (-t) * y)) 0`, agrees with `archCasimirAt`, via
    the decomposition `y = archRealGLAt hw m * y'` of an adelic point into its archimedean
    component at `w` and a part of archimedean component `1`;
  * the Maass raising/lowering calculus `E^± = D_H ± i (D_E + D_F⁻)`, `lower`/`raise`: from a
    weight `m` and a Casimir eigenvalue `lam`, `(E^-)^j θ` and `(E^+)^j θ` stay smooth of weight
    `m ∓ 2ij` and eigenvalue `lam`, and the two iterated products factorise into
    `∏ j ∈ range M, (-4λ + (m ∓ 2ij)² ∓ 2i(m ∓ 2ij))`.

  and closes with the three headlines, whose statements are copied verbatim from the three
  `Theorems/Thm_AutomorphicForm_*.lean` wrappers, binder for binder (the pin's
  `p2m_exact_reverting` glue does not exist here, so each headline's proof is the pin's `solution`
  body inlined):

  * `archCasimirAt_rightTranslate_archRealGLAt` — the Casimir of a right translate by an
    archimedean point is the translate of the Casimir, with smoothness and the first/second
    derivative continuities preserved;
  * `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` — the left-acting Casimir element agrees with
    `archCasimirAt`;
  * `iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul` — the Maass raising/lowering
    calculus and its two iterated factorisations.

  **The four real leaves (SET-AF9).** Appended below the three headlines, each stated at its
  `Theorems/` wrapper, they are the continuation of the same calculus: the three `𝔰𝔩₂` commutators
  on a smooth `φ` (`archDerivAt_commutator_of_isArchSmoothAt`), the weight identity
  `D_E − D_{F⁻} = I·n` on a function with an archimedean character
  (`archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt`), the Casimir's commutation with
  a right translation by a row isometry at a *different* place, and `GL₂(ℝ)`-invariance for a
  function killed by `E` and `F⁻`. Their helpers are the pin's own and `private`.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the seven `spec-pin:` lines
  of this header name the seven pin `S_` files the module transcribes, and the checker resolves
  each public statement against them by name and, failing that, by the statement's content hash.
  So a later proof can import
  `AutomorphicForm.CasCore.*`, `…CommAway.*`, `…ElemLR.*`, `…CasLR.*`, `…OsAlg.*`, `…OsInf.*`,
  `…InvZero.*` directly, all under their subject names: the pin's pipeline stage ids (`…17`, `…22`,
  `…40` — the pin's own README calls such labels pipeline artefacts, not mathematics) are stripped
  from the namespaces, as are its file wrappers.

  Transcribed from the three pin `S_` files (pinned `aa2d8b3`), which are one development written
  three times: `S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean` (569 lines),
  `S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean` (856) and
  `S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean` (917).
  Byte-normalised the shared prefix is 552 lines, 56 names / 538 declaration lines: the
  `CasCore` engine, written **once** here (the pin wrote it three times, `private` only in the
  third copy). The 64-declaration engine is 63 here: the pin's local `continuous_rightTranslate` —
  duplicated inside the pin itself, in `CasCore` at `S_…iterate_raise….lean:482` and again in
  `CommAway` at `S_…leftCasimir….lean:607` — is the port's
  `AutomorphicForm.CuspidalConstituent.continuous_rightTranslate`, so both copies are dropped
  rather than re-proved.

  The pin's `private theorem _root_.CasCore.…` / `_root_.CommAway.…` root-namespace shadows
  (its `p2m_export` workaround for the triplication) are resolved per lemma: the two `CasCore`
  ones (`isArchSmoothAt_rightTranslate`, `archCasimirAt_rightTranslate`) restate engine lemmas with
  identical statements, so sourcing the engine from the copy without shadows drops them; the two
  `CommAway` ones are *not* restatements — their hypothesis is a `k` commuting with
  `archRealGLAt hw '' GL₂(ℝ)` (`hk`) rather than a specific `archRealGLAt hw M` — so they are kept
  and renamed `isArchSmoothAt_rightTranslate_of_glArch_eq_one` /
  `archCasimirAt_rightTranslate_of_glArch_eq_one`, which is exactly what distinguishes them from
  the `CasCore` namesakes.
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
-- `D2_symm` (mixed partials commute through the chart) is `ContDiffAt.isSymmSndFDerivAt`,
-- which the pin reached through its whole-library import; it is not in the closure of the two
-- port modules above, and it is load-bearing for `archDerivAt_comm`, hence for all three
-- headlines, so the one mathlib module that proves it is imported here explicitly.
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain AdelicLevel
open AutomorphicForm.CuspidalConstituent

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archRealGLAt_eq_archRealLiftAt (M : GL (Fin 2) ℝ) :
    archRealGLAt hw M = archRealLiftAt hw (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (M : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem archRealGLAt_mul_archRealLiftAt (M : GL (Fin 2) ℝ) {e : Fin 2 → Fin 2 → ℝ} (h : (Matrix.of e).det ≠ 0) :
    archRealGLAt hw M * archRealLiftAt hw e =
      archRealLiftAt hw (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  have hM : ((M : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hM h
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

def conjArr (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e * (M : Matrix (Fin 2) (Fin 2) ℝ))

theorem det_conjArr (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of (conjArr M e)).det = (Matrix.of e).det := by
  rw [conjArr, Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_mul]
  have hMM : ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.det_mul, show ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (M : Matrix (Fin 2) (Fin 2) ℝ) =
      ((M⁻¹ * M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, inv_mul_cancel, Units.val_one, Matrix.det_one]
  calc ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (Matrix.of e).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det
      = (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det * (M : Matrix (Fin 2) (Fin 2) ℝ).det) * (Matrix.of e).det := by
        ring
    _ = (Matrix.of e).det := by rw [hMM, one_mul]

theorem archRealLiftAt_mul_archRealGLAt_eq (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    archRealLiftAt hw e * archRealGLAt hw M = archRealGLAt hw M * archRealLiftAt hw (conjArr M e) := by
  by_cases h : (Matrix.of e).det ≠ 0
  · have h' : (Matrix.of (conjArr M e)).det ≠ 0 := by rwa [det_conjArr]
    rw [archRealLiftAt_mul_archRealGLAt hw h, archRealGLAt_mul_archRealLiftAt hw M h']
    congr 1
    rw [conjArr, Equiv.apply_symm_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (M : Matrix (Fin 2) (Fin 2) ℝ) * ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((M * M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · push Not at h
    have h' : ¬ (Matrix.of (conjArr M e)).det ≠ 0 := by rw [det_conjArr]; exact fun hh => hh h
    have h0 : ¬ (Matrix.of e).det ≠ 0 := fun hh => hh h
    rw [archRealLiftAt, dite_eq_right h0, archRealLiftAt, dite_eq_right h', one_mul, mul_one]

def chart (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : (Fin 2 → Fin 2 → ℝ) → ℂ :=
  fun e => φ (g * archRealLiftAt hw e)

theorem chart_rightTranslate (M : GL (Fin 2) ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    chart hw (rightTranslate F (archRealGLAt hw M) φ) g = chart hw φ (g * archRealGLAt hw M) ∘ conjArr M := by
  funext e
  show φ (g * archRealLiftAt hw e * archRealGLAt hw M) = φ (g * archRealGLAt hw M * archRealLiftAt hw (conjArr M e))
  rw [mul_assoc, archRealLiftAt_mul_archRealGLAt_eq hw M e, ← mul_assoc]

def conjCLM (M : GL (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
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

theorem conjCLM_apply (M : GL (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) : conjCLM M e = conjArr M e := rfl

theorem coe_conjCLM (M : GL (Fin 2) ℝ) : (conjCLM M : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ)) = conjArr M := rfl

theorem conjArr_one (M : GL (Fin 2) ℝ) : conjArr M (Matrix.of.symm 1) = Matrix.of.symm 1 := by
  unfold conjArr
  rw [Equiv.apply_symm_apply, Matrix.mul_one,
    show ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (M : Matrix (Fin 2) (Fin 2) ℝ) =
      ((M⁻¹ * M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from rfl, inv_mul_cancel, Units.val_one]

end CasCore

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

abbrev U : Set (Fin 2 → Fin 2 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem one_mem_U : (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ U := by
  show (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

def D1 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y)

theorem contDiffAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) e :=
  (hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds he)

theorem hasFDerivAt_chart {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e) e :=
  ((contDiffAt_chart hw hφ g he).differentiableAt (by simp)).hasFDerivAt

theorem archDerivAt_apply_mul_archRealLiftAt {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (chart hw φ g) e (Matrix.of.symm (Matrix.of e * archDirMatrix d)) := by
  have hdiff : HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact hasFDerivAt_chart hw hφ g he
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => chart hw φ g (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show _ = φ (g * archRealLiftAt hw _)
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

theorem archDerivAt_eq_D1 {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : archDerivAt hw d φ g = D1 hw φ g (archDirMatrix d) := by
  have h := archDerivAt_apply_mul_archRealLiftAt hw hφ d g (e := Matrix.of.symm 1) one_mem_U
  rw [archRealLiftAt_of_symm_one, mul_one, Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

theorem isArchSmoothAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F (archRealGLAt hw M) φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (chart hw (rightTranslate F (archRealGLAt hw M) φ) g) U
  rw [chart_rightTranslate, ← coe_conjCLM]
  refine (hφ (g * archRealGLAt hw M)).comp (conjCLM M).contDiff.contDiffOn fun e he => ?_
  show (Matrix.of (conjArr M e)).det ≠ 0
  rw [det_conjArr]
  exact he

theorem conjCLM_of_symm (M : GL (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    conjCLM M (Matrix.of.symm Y) =
      Matrix.of.symm (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Y * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [conjCLM_apply, conjArr, Equiv.apply_symm_apply]

theorem archDerivAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ)
    (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (rightTranslate F (archRealGLAt hw M) φ) g =
      D1 hw φ (g * archRealGLAt hw M)
        (((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [archDerivAt_eq_D1 hw (isArchSmoothAt_rightTranslate hw M hφ), D1, D1, chart_rightTranslate, ← coe_conjCLM,
    ← conjCLM_of_symm]
  have hd : DifferentiableAt ℝ (chart hw φ (g * archRealGLAt hw M)) (conjCLM M (Matrix.of.symm 1)) := by
    rw [conjCLM_apply, conjArr_one]
    exact (contDiffAt_chart hw hφ _ one_mem_U).differentiableAt (by simp)
  rw [fderiv_comp _ hd (conjCLM M).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    conjCLM_apply M (Matrix.of.symm 1), conjArr_one]

end CasCore

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def D2 (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm Y) (Matrix.of.symm Z)

omit hw in
theorem hasDerivAt_flow_entries (d : ArchDir) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (archDirMatrix d)) 0 := by
  have h := hasDerivAt_of_symm_mul_archFlowMatrix (Matrix.of.symm 1) d
  simp only [Equiv.apply_symm_apply, Matrix.one_mul] at h
  exact h

omit hw in
theorem hasDerivAt_flow_mul_const (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) * X))
      (Matrix.of.symm (archDirMatrix d * X)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrix_apply d i k).mul_const (X k j)

theorem archDerivAt_archDerivAt_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (i j : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (archDerivAt hw j φ) g =
      D2 hw φ g (archDirMatrix i) (archDirMatrix j) + D1 hw φ g (archDirMatrix i * archDirMatrix j) := by
  have hfun : (fun t : ℝ => archDerivAt hw j φ (g * archFlowAt hw i t)) =
      fun t => (fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ))))
        (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix j)) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix i t).isUnit).ne_zero
    rw [archFlowAt, archRealGLAt_eq_archRealLiftAt, archDerivAt_apply_mul_archRealLiftAt hw hφ j g hdet,
      Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw φ g) (Matrix.of.symm 1) := contDiffAt_chart hw hφ g one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw φ g)) (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ0 : Matrix.of.symm ((archFlowMatrix i 0 : Matrix (Fin 2) (Fin 2) ℝ)) = Matrix.of.symm 1 := by
    rw [archFlowMatrix_zero, Units.val_one]
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (chart hw φ g) (Matrix.of.symm ((archFlowMatrix i t : Matrix (Fin 2) (Fin 2) ℝ))))
      (fderiv ℝ (fderiv ℝ (chart hw φ g)) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_flow_entries i) hγ0.symm
  have h := hA.clm_apply (hasDerivAt_flow_mul_const i (archDirMatrix j))
  show deriv (fun t : ℝ => archDerivAt hw j φ (g * archFlowAt hw i t)) 0 = _
  rw [hfun, h.deriv]
  simp only [archFlowMatrix_zero, Units.val_one, Matrix.one_mul, D2, D1]

theorem D2_symm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℝ) : D2 hw φ g Y Z = D2 hw φ g Z Y :=
  ((contDiffAt_chart hw hφ g one_mem_U).isSymmSndFDerivAt (by simp)).eq _ _

theorem D1_sub (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (Y - Z) = D1 hw φ g Y - D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y - Matrix.of.symm Z) = _
  rw [map_sub]
  rfl

theorem D1_add (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (Y Z : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (Y + Z) = D1 hw φ g Y + D1 hw φ g Z := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm Y + Matrix.of.symm Z) = _
  rw [map_add]
  rfl

theorem D1_smul (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (c : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    D1 hw φ g (c • Y) = (c : ℂ) * D1 hw φ g Y := by
  show fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (c • Matrix.of.symm Y) = _
  rw [map_smul, Complex.real_smul]
  rfl

theorem archDerivAt_comm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (i j : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (archDerivAt hw j φ) g - archDerivAt hw j (archDerivAt hw i φ) g =
      D1 hw φ g (archDirMatrix i * archDirMatrix j - archDirMatrix j * archDirMatrix i) := by
  rw [archDerivAt_archDerivAt_eq hw hφ, archDerivAt_archDerivAt_eq hw hφ, D2_symm hw hφ g (archDirMatrix j), D1_sub]
  ring

end CasCore

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def AdM (M : GL (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((M⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * X * (M : Matrix (Fin 2) (Fin 2) ℝ)

omit hw in
theorem trace_archDirMatrix (d : ArchDir) : Matrix.trace (archDirMatrix d) = 0 := by
  cases d <;> simp [archDirMatrix, Matrix.trace_fin_two]

omit hw in
theorem AdM_traceless (M : GL (Fin 2) ℝ) (d : ArchDir) : (AdM M (archDirMatrix d)) 1 1 = -(AdM M (archDirMatrix d)) 0 0 := by
  have h : Matrix.trace (AdM M (archDirMatrix d)) = 0 := by
    rw [AdM, Matrix.trace_units_conj', trace_archDirMatrix]
  rw [Matrix.trace_fin_two] at h
  linarith

omit hw in

theorem eq_smul_archDirMatrix (Y : Matrix (Fin 2) (Fin 2) ℝ) (hY : Y 1 1 = -Y 0 0) :
    Y = Y 0 0 • archDirMatrix .H + Y 0 1 • archDirMatrix .E + Y 1 0 • archDirMatrix .Fm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archDirMatrix, hY]

def cf (M : GL (Fin 2) ℝ) (d e : ArchDir) : ℂ :=
  match e with
  | .H => ((AdM M (archDirMatrix d)) 0 0 : ℝ)
  | .E => ((AdM M (archDirMatrix d)) 0 1 : ℝ)
  | .Fm => ((AdM M (archDirMatrix d)) 1 0 : ℝ)

def Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  cf M d .H • archDerivAt hw .H θ + cf M d .E • archDerivAt hw .E θ + cf M d .Fm • archDerivAt hw .Fm θ

theorem isArchSmoothAt_Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    IsArchSmoothAt hw (Dconj hw M d θ) :=
  (((hθ.archDerivAt .H).smul _).add ((hθ.archDerivAt .E).smul _)).add ((hθ.archDerivAt .Fm).smul _)

theorem Dconj_apply (M : GL (Fin 2) ℝ) (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Dconj hw M d θ g = cf M d .H * archDerivAt hw .H θ g + cf M d .E * archDerivAt hw .E θ g +
      cf M d .Fm * archDerivAt hw .Fm θ g := by
  simp only [Dconj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem D1_AdM {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (M : GL (Fin 2) ℝ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) : D1 hw θ g (AdM M (archDirMatrix d)) = Dconj hw M d θ g := by
  conv_lhs => rw [eq_smul_archDirMatrix (AdM M (archDirMatrix d)) (AdM_traceless M d)]
  rw [D1_add, D1_add, D1_smul, D1_smul, D1_smul, ← archDerivAt_eq_D1 hw hθ, ← archDerivAt_eq_D1 hw hθ,
    ← archDerivAt_eq_D1 hw hθ, Dconj_apply]
  rfl

theorem archDerivAt_rightTranslate_eq_Dconj (M : GL (Fin 2) ℝ) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ)
    (d : ArchDir) : archDerivAt hw d (rightTranslate F (archRealGLAt hw M) θ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M d θ) := by
  funext g
  rw [archDerivAt_rightTranslate hw M hθ, ← AdM, D1_AdM hw hθ]
  rfl

theorem archDerivAt_Dconj (M : GL (Fin 2) ℝ) (d i : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw i (Dconj hw M d θ) g = cf M d .H * archDerivAt hw i (archDerivAt hw .H θ) g +
      cf M d .E * archDerivAt hw i (archDerivAt hw .E θ) g + cf M d .Fm * archDerivAt hw i (archDerivAt hw .Fm θ) g := by
  unfold Dconj
  rw [archDerivAt_add (((hθ.archDerivAt .H).smul _).add ((hθ.archDerivAt .E).smul _)) ((hθ.archDerivAt .Fm).smul _),
    archDerivAt_add ((hθ.archDerivAt .H).smul _) ((hθ.archDerivAt .E).smul _), archDerivAt_smul, archDerivAt_smul,
    archDerivAt_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit hw in
theorem rightTranslate_combo (k : AdelicGL2 (𝓞 F) F) (a b : ℂ) (θ₁ θ₂ θ₃ : AdelicGL2 (𝓞 F) F → ℂ) :
    -(a • rightTranslate F k θ₁ - b • rightTranslate F k θ₂ + rightTranslate F k θ₃) =
      rightTranslate F k (-(a • θ₁ - b • θ₂ + θ₃)) := by
  funext g
  simp only [rightTranslate, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

end CasCore

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit hw in
theorem AdM_eq (M : GL (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    AdM M X = ((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ • (Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℝ) * X * (M : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [AdM, Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_mul]

omit hw in
theorem cf_H_H (M : GL (Fin 2) ℝ) :
    cf M .H .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 + (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_H_E (M : GL (Fin 2) ℝ) :
    cf M .H .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_H_Fm (M : GL (Fin 2) ℝ) :
    cf M .H .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-(2 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_H (M : GL (Fin 2) ℝ) :
    cf M .E .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_E (M : GL (Fin 2) ℝ) :
    cf M .E .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_E_Fm (M : GL (Fin 2) ℝ) :
    cf M .E .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_H (M : GL (Fin 2) ℝ) :
    cf M .Fm .H = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_E (M : GL (Fin 2) ℝ) :
    cf M .Fm .E = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * (-((M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1)) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem cf_Fm_Fm (M : GL (Fin 2) ℝ) :
    cf M .Fm .Fm = ((((M : Matrix (Fin 2) (Fin 2) ℝ)).det⁻¹ * ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℝ) : ℂ) := by
  simp only [cf, AdM_eq, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    archDirMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  ring

omit hw in
theorem bracket_H_E : archDirMatrix .H * archDirMatrix .E - archDirMatrix .E * archDirMatrix .H = (2 : ℝ) • archDirMatrix .E := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix]; norm_num

omit hw in
theorem bracket_H_Fm : archDirMatrix .H * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .H = (-2 : ℝ) • archDirMatrix .Fm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix]; norm_num

omit hw in
theorem bracket_E_Fm : archDirMatrix .E * archDirMatrix .Fm - archDirMatrix .Fm * archDirMatrix .E = (1 : ℝ) • archDirMatrix .H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [archDirMatrix]

theorem rel_E_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .E (archDerivAt hw .H φ) g = archDerivAt hw .H (archDerivAt hw .E φ) g - 2 * archDerivAt hw .E φ g := by
  have h := archDerivAt_comm hw hφ .H .E g
  rw [bracket_H_E, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

theorem rel_Fm_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .Fm (archDerivAt hw .H φ) g = archDerivAt hw .H (archDerivAt hw .Fm φ) g + 2 * archDerivAt hw .Fm φ g := by
  have h := archDerivAt_comm hw hφ .H .Fm g
  rw [bracket_H_Fm, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

theorem rel_Fm_E {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .Fm (archDerivAt hw .E φ) g = archDerivAt hw .E (archDerivAt hw .Fm φ) g - archDerivAt hw .H φ g := by
  have h := archDerivAt_comm hw hφ .E .Fm g
  rw [bracket_E_Fm, D1_smul, ← archDerivAt_eq_D1 hw hφ] at h
  push_cast at h
  linear_combination -h

end CasCore

namespace CasCore

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem continuous_Dconj (M : GL (Fin 2) ℝ) (d : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∀ e : ArchDir, Continuous (archDerivAt hw e θ)) : Continuous (Dconj hw M d θ) := by
  unfold Dconj
  exact (((h .H).const_smul (cf M d .H)).add ((h .E).const_smul (cf M d .E))).add ((h .Fm).const_smul (cf M d .Fm))

theorem continuous_archDerivAt_Dconj (M : GL (Fin 2) ℝ) (d i : ArchDir) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : IsArchSmoothAt hw θ) (h2 : ∀ e e' : ArchDir, Continuous (archDerivAt hw e (archDerivAt hw e' θ))) :
    Continuous (archDerivAt hw i (Dconj hw M d θ)) := by
  have : archDerivAt hw i (Dconj hw M d θ) = fun g => cf M d .H * archDerivAt hw i (archDerivAt hw .H θ) g +
      cf M d .E * archDerivAt hw i (archDerivAt hw .E θ) g + cf M d .Fm * archDerivAt hw i (archDerivAt hw .Fm θ) g :=
    funext fun g => archDerivAt_Dconj hw M d i hθ g
  rw [this]
  exact ((continuous_const.mul (h2 i .H)).add (continuous_const.mul (h2 i .E))).add (continuous_const.mul (h2 i .Fm))

theorem casimir_identity (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (g : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * Dconj hw M .H (Dconj hw M .H φ) g - (1 / 2 : ℂ) * Dconj hw M .H φ g + Dconj hw M .E (Dconj hw M .Fm φ) g) =
      archCasimirAt hw φ g := by
  have hdet : (((M : Matrix (Fin 2) (Fin 2) ℝ)).det : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hdetR : ((M : Matrix (Fin 2) (Fin 2) ℝ)).det = (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := Matrix.det_fin_two _
  show _ = (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H φ) - (1 / 2 : ℂ) • archDerivAt hw .H φ +
    archDerivAt hw .E (archDerivAt hw .Fm φ))) g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Dconj_apply,
    archDerivAt_Dconj hw M _ _ hφ, rel_E_H hw hφ, rel_Fm_H hw hφ, rel_Fm_E hw hφ,
    cf_H_H, cf_H_E, cf_H_Fm, cf_E_H, cf_E_E, cf_E_Fm, cf_Fm_H, cf_Fm_E, cf_Fm_Fm]
  push_cast
  rw [hdetR] at hdet ⊢
  push_cast at hdet ⊢
  field_simp
  ring

theorem archCasimirAt_rightTranslate (M : GL (Fin 2) ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (archCasimirAt hw φ) := by
  have h1 : archDerivAt hw .H (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M .H φ) :=
    archDerivAt_rightTranslate_eq_Dconj hw M hφ .H
  have h2 : archDerivAt hw .H (archDerivAt hw .H (rightTranslate F (archRealGLAt hw M) φ)) =
      rightTranslate F (archRealGLAt hw M) (Dconj hw M .H (Dconj hw M .H φ)) := by
    rw [h1]
    exact archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M .H hφ) .H
  have h3 : archDerivAt hw .Fm (rightTranslate F (archRealGLAt hw M) φ) = rightTranslate F (archRealGLAt hw M) (Dconj hw M .Fm φ) :=
    archDerivAt_rightTranslate_eq_Dconj hw M hφ .Fm
  have h4 : archDerivAt hw .E (archDerivAt hw .Fm (rightTranslate F (archRealGLAt hw M) φ)) =
      rightTranslate F (archRealGLAt hw M) (Dconj hw M .E (Dconj hw M .Fm φ)) := by
    rw [h3]
    exact archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M .Fm hφ) .E
  rw [archCasimirAt, h2, h1, h4]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rightTranslate]
  exact casimir_identity hw M hφ (g * archRealGLAt hw M)

theorem package (M : GL (Fin 2) ℝ) (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    IsArchSmoothAt hw (rightTranslate F (archRealGLAt hw M) x) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate F (archRealGLAt hw M) x))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightTranslate F (archRealGLAt hw M) x)))) ∧
    archCasimirAt hw (rightTranslate F (archRealGLAt hw M) x) = rightTranslate F (archRealGLAt hw M) (archCasimirAt hw x) := by
  refine ⟨isArchSmoothAt_rightTranslate hw M hxs, fun d => ?_, fun d d' => ?_, archCasimirAt_rightTranslate hw M hxs⟩
  · rw [archDerivAt_rightTranslate_eq_Dconj hw M hxs]
    exact CuspidalConstituent.continuous_rightTranslate F (continuous_Dconj hw M d hD1) _
  · rw [archDerivAt_rightTranslate_eq_Dconj hw M hxs, archDerivAt_rightTranslate_eq_Dconj hw M (isArchSmoothAt_Dconj hw M d' hxs)]
    refine CuspidalConstituent.continuous_rightTranslate F (continuous_Dconj hw M d fun e => ?_) _
    exact continuous_archDerivAt_Dconj hw M d' e hxs hD2

end CasCore

namespace CommAway

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

section Commuting

variable {w : InfinitePlace F} (hw : w.IsReal) {k : AdelicGL2 (𝓞 F) F}
  (hk : ∀ m : GL (Fin 2) ℝ, archRealGLAt hw m * k = k * archRealGLAt hw m)

include hk

theorem archRealLiftAt_mul_comm (e : Fin 2 → Fin 2 → ℝ) : archRealLiftAt hw e * k = k * archRealLiftAt hw e := by
  unfold archRealLiftAt
  split_ifs
  · exact hk _
  · rw [one_mul, mul_one]

theorem archFlowAt_mul_comm (d : ArchDir) (t : ℝ) : archFlowAt hw d t * k = k * archFlowAt hw d t :=
  hk _

theorem isArchSmoothAt_rightTranslate_of_glArch_eq_one {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    IsArchSmoothAt hw (rightTranslate F k φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * k)) =
      fun e => φ (g * k * archRealLiftAt hw e) := by
    funext e
    rw [mul_assoc, archRealLiftAt_mul_comm hw hk e, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

theorem archDerivAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (rightTranslate F k φ) = rightTranslate F k (archDerivAt hw d φ) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t * k)) 0 = deriv (fun t : ℝ => φ (g * k * archFlowAt hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_mul_comm hw hk d t, ← mul_assoc]

theorem archCasimirAt_rightTranslate_of_glArch_eq_one (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (rightTranslate F k φ) = rightTranslate F k (archCasimirAt hw φ) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_rightTranslate hw hk .H φ,
    archDerivAt_rightTranslate hw hk .H (archDerivAt hw .H φ), archDerivAt_rightTranslate hw hk .Fm φ,
    archDerivAt_rightTranslate hw hk .E (archDerivAt hw .Fm φ)]
  rfl

theorem package (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    IsArchSmoothAt hw (rightTranslate F k x) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate F k x))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightTranslate F k x)))) ∧
    archCasimirAt hw (rightTranslate F k x) = rightTranslate F k (archCasimirAt hw x) := by
  refine ⟨isArchSmoothAt_rightTranslate_of_glArch_eq_one hw hk hxs, fun d => ?_, fun d d' => ?_, archCasimirAt_rightTranslate_of_glArch_eq_one hw hk x⟩
  · rw [archDerivAt_rightTranslate hw hk]
    exact CuspidalConstituent.continuous_rightTranslate F (hD1 d) k
  · rw [archDerivAt_rightTranslate hw hk, archDerivAt_rightTranslate hw hk]
    exact CuspidalConstituent.continuous_rightTranslate F (hD2 d d') k

end Commuting

theorem archRealGLAt_mul_rowIsometryInclAt₀_comm {w w' : InfinitePlace F} (hw : w.IsReal) (hne : w' ≠ w)
    (k : rowIsometrySubgroup₀ w'.Completion) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m * rowIsometryInclAt₀ F w' k = rowIsometryInclAt₀ F w' k * archRealGLAt hw m := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt F w _ * adelicArchGLInclAt F w' _ = adelicArchGLInclAt F w' _ * adelicArchGLInclAt F w _
  exact (commute_adelicArchGLInclAt_of_ne F (Ne.symm hne) _ _).eq

end CommAway

namespace ElemLR

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
/-- Wire restatement of `AutomorphicForm.ext_archComponent`
(`AutomorphicForm/Adelic/ArchComponentDictionary.lean`, the one home of the fact): this module's
`spec-pin:` file names it here, so the name stays; the proof is one application. -/
theorem glArch_ext {x y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w x = archComponent F w y) : x = y :=
  ext_archComponent h

theorem glArch_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {w w' : InfinitePlace F} (hw : w.IsReal) (hw' : w' ≠ w)
    (m : GL (Fin 2) ℝ) : archComponent F w' (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hw']

theorem glFin_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

theorem archRealGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {g : AdelicGL2 (𝓞 F) F} (hg : archComponent F w (glArch (𝓞 F) F g) = 1) :
    archRealGLAt hw m * g = g * archRealGLAt hw m := by
  apply eq_of_glArch_eq_of_glFin_eq F
  · rw [map_mul, map_mul]
    apply glArch_ext
    intro w'
    rw [map_mul, map_mul]
    by_cases hw' : w' = w
    · subst hw'; rw [hg, mul_one, one_mul]
    · rw [archComponent_glArch_archRealGLAt_of_ne hw hw', one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_archRealGLAt, one_mul, mul_one]

end ElemLR

namespace CasLR

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def Ld (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) : ℂ :=
  deriv (fun t : ℝ => θ (archFlowAt hw d (-t) * y)) 0

omit hw in
theorem hasDerivAt_negflow_mul_const (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * X))
      (Matrix.of.symm (-(archDirMatrix d * X))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((hasDerivAt_archFlowMatrix_apply d i k).comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) neg_zero.symm).mul_const (X k j)
  simpa using h

omit hw in
theorem hasDerivAt_const_mul_negflow (d : ArchDir) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.of.symm (X * (archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (-(X * archDirMatrix d))) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((hasDerivAt_archFlowMatrix_apply d k j).comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) neg_zero.symm).const_mul (X i k)
  simpa using h

theorem negflow_mul_lift (d : ArchDir) (t : ℝ) {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archFlowAt hw d (-t) * archRealLiftAt hw e =
      1 * archRealLiftAt hw (Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
  rw [one_mul, archFlowAt, archRealGLAt_mul_archRealLiftAt hw _ he]

theorem Ld_apply_lift {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    Ld hw d θ (archRealLiftAt hw e) = fderiv ℝ (chart hw θ 1) e (Matrix.of.symm (-(archDirMatrix d * Matrix.of e))) := by
  have hfun : (fun t : ℝ => θ (archFlowAt hw d (-t) * archRealLiftAt hw e)) =
      fun t => chart hw θ 1 (Matrix.of.symm ((archFlowMatrix d (-t) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
    funext t
    rw [negflow_mul_lift hw d t he]
    rfl
  have h0 : Matrix.of.symm ((archFlowMatrix d (-0) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e) = e := by
    rw [neg_zero, archFlowMatrix_zero, Units.val_one, Matrix.one_mul, Equiv.symm_apply_apply]
  have hdiff : HasFDerivAt (chart hw θ 1) (fderiv ℝ (chart hw θ 1) e)
      (Matrix.of.symm ((archFlowMatrix d (-0) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of e)) := by
    rw [h0]; exact hasFDerivAt_chart hw hθ 1 he
  show deriv (fun t : ℝ => θ (archFlowAt hw d (-t) * archRealLiftAt hw e)) 0 = _
  rw [hfun]
  exact (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_negflow_mul_const d (Matrix.of e))).deriv

theorem Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir) :
    Ld hw d θ 1 = -archDerivAt hw d θ 1 := by
  have h := Ld_apply_lift hw hθ d (e := Matrix.of.symm 1) one_mem_U
  rw [archRealLiftAt_of_symm_one, Equiv.apply_symm_apply, Matrix.mul_one] at h
  rw [h, archDerivAt_eq_D1 hw hθ, D1]
  show fderiv ℝ (chart hw θ 1) (Matrix.of.symm 1) (-Matrix.of.symm (archDirMatrix d)) = _
  rw [map_neg]

theorem Ld_Ld_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (i j : ArchDir) :
    Ld hw i (Ld hw j θ) 1 = D2 hw θ 1 (archDirMatrix i) (archDirMatrix j) + D1 hw θ 1 (archDirMatrix j * archDirMatrix i) := by
  have hfun : (fun t : ℝ => Ld hw j θ (archFlowAt hw i (-t) * 1)) =
      fun t => (fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
        (Matrix.of.symm (-(archDirMatrix j * (archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    have hdet : (Matrix.of (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
      rw [Equiv.apply_symm_apply]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrix i (-t)).isUnit).ne_zero
    rw [mul_one, archFlowAt, archRealGLAt_eq_archRealLiftAt, Ld_apply_lift hw hθ j hdet, Equiv.apply_symm_apply]
  have hchart : ContDiffAt ℝ (⊤ : ℕ∞) (chart hw θ 1) (Matrix.of.symm 1) := contDiffAt_chart hw hθ 1 one_mem_U
  have hA0 : HasFDerivAt (fderiv ℝ (chart hw θ 1)) (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1))
      (Matrix.of.symm 1) :=
    ((hchart.fderiv_right (m := 2) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.of.symm (-archDirMatrix i)) 0 := by
    have h := hasDerivAt_negflow_mul_const i (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp only [Matrix.mul_one] at h
    exact h
  have hγ0 : Matrix.of.symm ((archFlowMatrix i (-0) : Matrix (Fin 2) (Fin 2) ℝ)) = Matrix.of.symm 1 := by
    rw [neg_zero, archFlowMatrix_zero, Units.val_one]
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (chart hw θ 1) (Matrix.of.symm ((archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
      (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1) (Matrix.of.symm (-archDirMatrix i))) 0 :=
    hA0.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hv : HasDerivAt (fun t : ℝ => Matrix.of.symm (-(archDirMatrix j * (archFlowMatrix i (-t) : Matrix (Fin 2) (Fin 2) ℝ))))
      (Matrix.of.symm (archDirMatrix j * archDirMatrix i)) 0 := by
    have h := (hasDerivAt_const_mul_negflow i (archDirMatrix j)).neg
    convert h using 1
    all_goals first | rfl | exact (neg_neg _).symm
  have h := hA.clm_apply hv
  show deriv (fun t : ℝ => Ld hw j θ (archFlowAt hw i (-t) * 1)) 0 = _
  rw [hfun, h.deriv]
  simp only [neg_zero, archFlowMatrix_zero, Units.val_one, Matrix.mul_one, D2, D1]
  have e1 : (fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (-archDirMatrix i)) =
      -((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) := map_neg _ _
  have e2 : ((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) (Matrix.of.symm (-archDirMatrix j)) =
      -(((fderiv ℝ (fderiv ℝ (chart hw θ 1)) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix i))) (Matrix.of.symm (archDirMatrix j))) :=
    map_neg _ _
  rw [e1, _root_.neg_apply, e2, neg_neg]

theorem leftCasimir_one {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H θ) 1 - (1 / 2 : ℂ) * Ld hw .H θ 1 + Ld hw .E (Ld hw .Fm θ) 1) = archCasimirAt hw θ 1 := by
  rw [Ld_Ld_one hw hθ, Ld_Ld_one hw hθ, Ld_one hw hθ]
  have h1 := archDerivAt_archDerivAt_eq hw hθ .H .H 1
  have h2 := archDerivAt_archDerivAt_eq hw hθ .E .Fm 1
  have h3 : D1 hw θ 1 (archDirMatrix .Fm * archDirMatrix .E) = D1 hw θ 1 (archDirMatrix .E * archDirMatrix .Fm) - archDerivAt hw .H θ 1 := by
    have hb : archDirMatrix .Fm * archDirMatrix .E = archDirMatrix .E * archDirMatrix .Fm - (1 : ℝ) • archDirMatrix .H := by
      rw [← bracket_E_Fm]; abel
    rw [hb, D1_sub, D1_smul, ← archDerivAt_eq_D1 hw hθ]
    push_cast
    ring
  show _ = (-((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H θ) - (1 / 2 : ℂ) • archDerivAt hw .H θ +
    archDerivAt hw .E (archDerivAt hw .Fm θ))) 1
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2, h3]
  ring

omit hw in
theorem rightTranslate_mul (a b : AdelicGL2 (𝓞 F) F) (θ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (a * b) θ = rightTranslate F a (rightTranslate F b θ) := by
  funext z
  simp only [rightTranslate, mul_assoc]

theorem Ld_rightTranslate (d : ArchDir) (θ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    Ld hw d (rightTranslate F y θ) = rightTranslate F y (Ld hw d θ) := by
  funext z
  simp only [Ld, rightTranslate, mul_assoc]

theorem exists_decomp (y : AdelicGL2 (𝓞 F) F) :
    ∃ (m : GL (Fin 2) ℝ) (y' : AdelicGL2 (𝓞 F) F), archComponent F w (glArch (𝓞 F) F y') = 1 ∧ y = archRealGLAt hw m * y' := by
  set m : GL (Fin 2) ℝ := (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (archComponent F w (glArch (𝓞 F) F y)) with hm
  refine ⟨m, (archRealGLAt hw m)⁻¹ * y, ?_, by rw [mul_inv_cancel_left]⟩
  rw [map_mul, map_mul, map_inv, map_inv, ElemLR.archComponent_glArch_archRealGLAt_self, hm, MulEquiv.apply_symm_apply,
    inv_mul_cancel]

theorem archCasimirAt_rightTranslate_any (y : AdelicGL2 (𝓞 F) F) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    archCasimirAt hw (rightTranslate F y θ) = rightTranslate F y (archCasimirAt hw θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℝ, archRealGLAt hw M * y' = y' * archRealGLAt hw M :=
    fun M => ElemLR.archRealGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  rw [rightTranslate_mul, rightTranslate_mul, CasCore.archCasimirAt_rightTranslate hw m (CommAway.isArchSmoothAt_rightTranslate_of_glArch_eq_one hw hk hθ),
    CommAway.archCasimirAt_rightTranslate_of_glArch_eq_one hw hk]

theorem isArchSmoothAt_rightTranslate_any (y : AdelicGL2 (𝓞 F) F) {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) :
    IsArchSmoothAt hw (rightTranslate F y θ) := by
  obtain ⟨m, y', hy', rfl⟩ := exists_decomp hw y
  have hk : ∀ M : GL (Fin 2) ℝ, archRealGLAt hw M * y' = y' * archRealGLAt hw M :=
    fun M => ElemLR.archRealGLAt_mul_comm_of_archComponent_eq_one hw M hy'
  rw [rightTranslate_mul]
  exact CasCore.isArchSmoothAt_rightTranslate hw m (CommAway.isArchSmoothAt_rightTranslate_of_glArch_eq_one hw hk hθ)

theorem leftCasimir_eq {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (y : AdelicGL2 (𝓞 F) F) :
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H θ) y - (1 / 2 : ℂ) * Ld hw .H θ y + Ld hw .E (Ld hw .Fm θ) y) = archCasimirAt hw θ y := by
  have h := leftCasimir_one hw (isArchSmoothAt_rightTranslate_any hw y hθ)
  rw [Ld_rightTranslate, Ld_rightTranslate, Ld_rightTranslate, Ld_rightTranslate, archCasimirAt_rightTranslate_any hw y hθ] at h
  simpa only [rightTranslate, one_mul] using h

end CasLR

namespace OsAlg

open CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

def Dk (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := archDerivAt hw .E θ - archDerivAt hw .Fm θ

def lower (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H θ - Complex.I • (archDerivAt hw .E θ + archDerivAt hw .Fm θ)

def raise (θ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H θ + Complex.I • (archDerivAt hw .E θ + archDerivAt hw .Fm θ)

section Smooth

variable {θ : AdelicGL2 (𝓞 F) F → ℂ}

-- The `hθ` hypothesis is the pin's (its section variable `θ`), and it is unused in both proofs;
-- it is kept because the statement is the pin's, hence the one local linter exemption in the file.
set_option linter.unusedVariables false in
theorem smooth_sub (hθ : IsArchSmoothAt hw θ) {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    IsArchSmoothAt hw (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

theorem archDerivAt_sub' {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  rw [sub_eq_add_neg, archDerivAt_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAt_smul, neg_one_smul, ← sub_eq_add_neg]

theorem smooth_Dk (hθ : IsArchSmoothAt hw θ) : IsArchSmoothAt hw (Dk hw θ) := smooth_sub hw hθ (hθ.archDerivAt .E) (hθ.archDerivAt .Fm)

theorem smooth_lower (hθ : IsArchSmoothAt hw θ) : IsArchSmoothAt hw (lower hw θ) :=
  smooth_sub hw hθ (hθ.archDerivAt .H) (((hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)).smul _)

theorem smooth_raise (hθ : IsArchSmoothAt hw θ) : IsArchSmoothAt hw (raise hw θ) :=
  (hθ.archDerivAt .H).add (((hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)).smul _)

theorem archDerivAt_lower (hθ : IsArchSmoothAt hw θ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (lower hw θ) g = archDerivAt hw d (archDerivAt hw .H θ) g -
      Complex.I * (archDerivAt hw d (archDerivAt hw .E θ) g + archDerivAt hw d (archDerivAt hw .Fm θ) g) := by
  unfold lower
  rw [archDerivAt_sub' hw (hθ.archDerivAt .H) (((hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)).smul _), archDerivAt_smul,
    archDerivAt_add (hθ.archDerivAt .E) (hθ.archDerivAt .Fm)]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem archDerivAt_raise (hθ : IsArchSmoothAt hw θ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (raise hw θ) g = archDerivAt hw d (archDerivAt hw .H θ) g +
      Complex.I * (archDerivAt hw d (archDerivAt hw .E θ) g + archDerivAt hw d (archDerivAt hw .Fm θ) g) := by
  unfold raise
  rw [archDerivAt_add (hθ.archDerivAt .H) (((hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)).smul _), archDerivAt_smul,
    archDerivAt_add (hθ.archDerivAt .E) (hθ.archDerivAt .Fm)]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem lower_apply (g : AdelicGL2 (𝓞 F) F) :
    lower hw θ g = archDerivAt hw .H θ g - Complex.I * (archDerivAt hw .E θ g + archDerivAt hw .Fm θ g) := by
  simp only [lower, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem raise_apply (g : AdelicGL2 (𝓞 F) F) :
    raise hw θ g = archDerivAt hw .H θ g + Complex.I * (archDerivAt hw .E θ g + archDerivAt hw .Fm θ g) := by
  simp only [raise, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem Dk_apply (g : AdelicGL2 (𝓞 F) F) : Dk hw θ g = archDerivAt hw .E θ g - archDerivAt hw .Fm θ g := by
  simp only [Dk, Pi.sub_apply]

theorem weight_deriv (hθ : IsArchSmoothAt hw θ) {m : ℂ} (hm : Dk hw θ = m • θ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (archDerivAt hw .E θ) g - archDerivAt hw d (archDerivAt hw .Fm θ) g = m * archDerivAt hw d θ g := by
  have h := congrArg (archDerivAt hw d) hm
  rw [Dk, archDerivAt_sub' hw (hθ.archDerivAt .E) (hθ.archDerivAt .Fm), archDerivAt_smul] at h
  have := congrFun h g
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this

theorem weight_apply {m : ℂ} (hm : Dk hw θ = m • θ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .E θ g - archDerivAt hw .Fm θ g = m * θ g := by
  have := congrFun hm g
  simpa only [Dk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this

theorem Dk_lower (hθ : IsArchSmoothAt hw θ) {m : ℂ} (hm : Dk hw θ = m • θ) : Dk hw (lower hw θ) = (m - 2 * Complex.I) • lower hw θ := by
  funext g
  rw [Dk_apply, Pi.smul_apply, smul_eq_mul, archDerivAt_lower hw hθ, archDerivAt_lower hw hθ, lower_apply hw,
    rel_E_H hw hθ, rel_Fm_H hw hθ, rel_Fm_E hw hθ]
  have w1 := weight_deriv hw hθ hm .H g
  have w2 := weight_deriv hw hθ hm .E g
  have w3 := weight_deriv hw hθ hm .Fm g
  rw [rel_Fm_E hw hθ] at w3
  linear_combination w1 - Complex.I * w2 - Complex.I * w3 +
    (-2 * archDerivAt hw .E θ g - 2 * archDerivAt hw .Fm θ g) * Complex.I_sq

theorem Dk_raise (hθ : IsArchSmoothAt hw θ) {m : ℂ} (hm : Dk hw θ = m • θ) : Dk hw (raise hw θ) = (m + 2 * Complex.I) • raise hw θ := by
  funext g
  rw [Dk_apply, Pi.smul_apply, smul_eq_mul, archDerivAt_raise hw hθ, archDerivAt_raise hw hθ, raise_apply hw,
    rel_E_H hw hθ, rel_Fm_H hw hθ, rel_Fm_E hw hθ]
  have w1 := weight_deriv hw hθ hm .H g
  have w2 := weight_deriv hw hθ hm .E g
  have w3 := weight_deriv hw hθ hm .Fm g
  rw [rel_Fm_E hw hθ] at w3
  linear_combination w1 + Complex.I * w2 + Complex.I * w3 +
    (-2 * archDerivAt hw .E θ g - 2 * archDerivAt hw .Fm θ g) * Complex.I_sq

end Smooth

end OsAlg

namespace OsAlg

open CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem relF_E_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .H φ) = archDerivAt hw .H (archDerivAt hw .E φ) - (2 : ℂ) • archDerivAt hw .E φ := by
  funext g; rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rel_E_H hw hφ]

theorem relF_Fm_H {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .Fm (archDerivAt hw .H φ) = archDerivAt hw .H (archDerivAt hw .Fm φ) + (2 : ℂ) • archDerivAt hw .Fm φ := by
  funext g; rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rel_Fm_H hw hφ]

theorem relF_E_Fm {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .E (archDerivAt hw .Fm φ) = archDerivAt hw .Fm (archDerivAt hw .E φ) + archDerivAt hw .H φ := by
  funext g; rw [Pi.add_apply, rel_Fm_E hw hφ]; ring

theorem casimir_apply (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archCasimirAt hw φ g = -((1 / 4 : ℂ) * archDerivAt hw .H (archDerivAt hw .H φ) g - (1 / 2 : ℂ) * archDerivAt hw .H φ g +
      archDerivAt hw .E (archDerivAt hw .Fm φ) g) := by
  simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem archDerivAt_casimir {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (archCasimirAt hw θ) g = -((1 / 4 : ℂ) * archDerivAt hw d (archDerivAt hw .H (archDerivAt hw .H θ)) g -
      (1 / 2 : ℂ) * archDerivAt hw d (archDerivAt hw .H θ) g + archDerivAt hw d (archDerivAt hw .E (archDerivAt hw .Fm θ)) g) := by
  have h1 : IsArchSmoothAt hw ((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H θ)) := ((hθ.archDerivAt .H).archDerivAt .H).smul _
  have h2 : IsArchSmoothAt hw ((1 / 2 : ℂ) • archDerivAt hw .H θ) := (hθ.archDerivAt .H).smul _
  have h3 : IsArchSmoothAt hw (archDerivAt hw .E (archDerivAt hw .Fm θ)) := (hθ.archDerivAt .Fm).archDerivAt .E
  rw [archCasimirAt, ← neg_one_smul ℂ (_ - _ + _), archDerivAt_smul, archDerivAt_add (smooth_sub hw hθ h1 h2) h3,
    archDerivAt_sub' hw h1 h2, archDerivAt_smul, archDerivAt_smul]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem casimir_comm_H {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (g : AdelicGL2 (𝓞 F) F) :
    archCasimirAt hw (archDerivAt hw .H θ) g = archDerivAt hw .H (archCasimirAt hw θ) g := by
  rw [casimir_apply, archDerivAt_casimir hw hθ]

  have h : archDerivAt hw .E (archDerivAt hw .Fm (archDerivAt hw .H θ)) g =
      archDerivAt hw .H (archDerivAt hw .E (archDerivAt hw .Fm θ)) g := by
    rw [relF_Fm_H hw hθ, archDerivAt_add ((hθ.archDerivAt .Fm).archDerivAt .H) ((hθ.archDerivAt .Fm).smul _), archDerivAt_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, rel_E_H hw (hθ.archDerivAt .Fm)]
    ring
  rw [h]

theorem casimir_comm_E {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (g : AdelicGL2 (𝓞 F) F) :
    archCasimirAt hw (archDerivAt hw .E θ) g = archDerivAt hw .E (archCasimirAt hw θ) g := by
  rw [casimir_apply, archDerivAt_casimir hw hθ]
  have hH := hθ.archDerivAt .H
  have e1 : archDerivAt hw .E (archDerivAt hw .H (archDerivAt hw .H θ)) g =
      archDerivAt hw .H (archDerivAt hw .H (archDerivAt hw .E θ)) g - 4 * archDerivAt hw .H (archDerivAt hw .E θ) g +
        4 * archDerivAt hw .E θ g := by
    rw [rel_E_H hw hH, relF_E_H hw hθ, archDerivAt_sub' hw ((hθ.archDerivAt .E).archDerivAt .H) ((hθ.archDerivAt .E).smul _),
      archDerivAt_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : archDerivAt hw .E (archDerivAt hw .H θ) g = archDerivAt hw .H (archDerivAt hw .E θ) g - 2 * archDerivAt hw .E θ g :=
    rel_E_H hw hθ g
  have e3 : archDerivAt hw .E (archDerivAt hw .E (archDerivAt hw .Fm θ)) g =
      archDerivAt hw .E (archDerivAt hw .Fm (archDerivAt hw .E θ)) g + archDerivAt hw .H (archDerivAt hw .E θ) g -
        2 * archDerivAt hw .E θ g := by
    rw [relF_E_Fm hw hθ, archDerivAt_add ((hθ.archDerivAt .E).archDerivAt .Fm) hH, Pi.add_apply, rel_E_H hw hθ]
    ring
  rw [e1, e2, e3]
  ring

theorem casimir_comm_Fm {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (g : AdelicGL2 (𝓞 F) F) :
    archCasimirAt hw (archDerivAt hw .Fm θ) g = archDerivAt hw .Fm (archCasimirAt hw θ) g := by
  rw [casimir_apply, archDerivAt_casimir hw hθ]
  have hH := hθ.archDerivAt .H
  have hFm := hθ.archDerivAt .Fm
  have e1 : archDerivAt hw .Fm (archDerivAt hw .H (archDerivAt hw .H θ)) g =
      archDerivAt hw .H (archDerivAt hw .H (archDerivAt hw .Fm θ)) g + 4 * archDerivAt hw .H (archDerivAt hw .Fm θ) g +
        4 * archDerivAt hw .Fm θ g := by
    rw [rel_Fm_H hw hH, relF_Fm_H hw hθ, archDerivAt_add (hFm.archDerivAt .H) (hFm.smul _), archDerivAt_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : archDerivAt hw .Fm (archDerivAt hw .H θ) g = archDerivAt hw .H (archDerivAt hw .Fm θ) g + 2 * archDerivAt hw .Fm θ g :=
    rel_Fm_H hw hθ g
  have e3 : archDerivAt hw .Fm (archDerivAt hw .E (archDerivAt hw .Fm θ)) g =
      archDerivAt hw .E (archDerivAt hw .Fm (archDerivAt hw .Fm θ)) g - archDerivAt hw .H (archDerivAt hw .Fm θ) g :=
    rel_Fm_E hw hFm g
  rw [e1, e2, e3]
  ring

theorem casimir_comm {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) (d : ArchDir) :
    archCasimirAt hw (archDerivAt hw d θ) = archDerivAt hw d (archCasimirAt hw θ) := by
  funext g
  cases d
  · exact casimir_comm_H hw hθ g
  · exact casimir_comm_E hw hθ g
  · exact casimir_comm_Fm hw hθ g

theorem casimir_lower {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {lam : ℂ}
    (hΩ : archCasimirAt hw θ = lam • θ) : archCasimirAt hw (lower hw θ) = lam • lower hw θ := by
  have hsum : IsArchSmoothAt hw (archDerivAt hw .E θ + archDerivAt hw .Fm θ) := (hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)
  unfold lower
  rw [sub_eq_add_neg, ← neg_smul, archCasimirAt_add (hθ.archDerivAt .H) (hsum.smul _), archCasimirAt_smul,
    archCasimirAt_add (hθ.archDerivAt .E) (hθ.archDerivAt .Fm), casimir_comm hw hθ, casimir_comm hw hθ, casimir_comm hw hθ, hΩ,
    archDerivAt_smul, archDerivAt_smul, archDerivAt_smul]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem casimir_raise {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {lam : ℂ}
    (hΩ : archCasimirAt hw θ = lam • θ) : archCasimirAt hw (raise hw θ) = lam • raise hw θ := by
  have hsum : IsArchSmoothAt hw (archDerivAt hw .E θ + archDerivAt hw .Fm θ) := (hθ.archDerivAt .E).add (hθ.archDerivAt .Fm)
  unfold raise
  rw [archCasimirAt_add (hθ.archDerivAt .H) (hsum.smul _), archCasimirAt_smul,
    archCasimirAt_add (hθ.archDerivAt .E) (hθ.archDerivAt .Fm), casimir_comm hw hθ, casimir_comm hw hθ, casimir_comm hw hθ, hΩ,
    archDerivAt_smul, archDerivAt_smul, archDerivAt_smul]
  funext g
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem raise_lower {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) :
    raise hw (lower hw θ) = (-4 * lam + m ^ 2 - 2 * Complex.I * m) • θ := by
  funext g
  rw [raise_apply, archDerivAt_lower hw hθ, archDerivAt_lower hw hθ, archDerivAt_lower hw hθ, Pi.smul_apply, smul_eq_mul,
    rel_E_H hw hθ, rel_Fm_H hw hθ, rel_Fm_E hw hθ]
  have wE := weight_deriv hw hθ hm .E g
  have wF := weight_deriv hw hθ hm .Fm g
  rw [rel_Fm_E hw hθ] at wF
  have w0 := weight_apply hw hm g
  have hc := congrFun hΩ g
  rw [casimir_apply, Pi.smul_apply, smul_eq_mul] at hc
  linear_combination wE - wF + (m - 2 * Complex.I) * w0 - 4 * hc +
    (-(archDerivAt hw .E (archDerivAt hw .E θ) g) - archDerivAt hw .E (archDerivAt hw .Fm θ) g -
      (archDerivAt hw .E (archDerivAt hw .Fm θ) g - archDerivAt hw .H θ g) - archDerivAt hw .Fm (archDerivAt hw .Fm θ) g) * Complex.I_sq

theorem lower_raise {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) :
    lower hw (raise hw θ) = (-4 * lam + m ^ 2 + 2 * Complex.I * m) • θ := by
  funext g
  rw [lower_apply, archDerivAt_raise hw hθ, archDerivAt_raise hw hθ, archDerivAt_raise hw hθ, Pi.smul_apply, smul_eq_mul,
    rel_E_H hw hθ, rel_Fm_H hw hθ, rel_Fm_E hw hθ]
  have wE := weight_deriv hw hθ hm .E g
  have wF := weight_deriv hw hθ hm .Fm g
  rw [rel_Fm_E hw hθ] at wF
  have w0 := weight_apply hw hm g
  have hc := congrFun hΩ g
  rw [casimir_apply, Pi.smul_apply, smul_eq_mul] at hc
  linear_combination wE - wF + (m + 2 * Complex.I) * w0 - 4 * hc -
    ((archDerivAt hw .E (archDerivAt hw .E θ) g) + archDerivAt hw .E (archDerivAt hw .Fm θ) g +
      (archDerivAt hw .E (archDerivAt hw .Fm θ) g - archDerivAt hw .H θ g) + archDerivAt hw .Fm (archDerivAt hw .Fm θ) g) * Complex.I_sq

end OsAlg

namespace OsAlg

open CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem lower_smul (c : ℂ) (θ : AdelicGL2 (𝓞 F) F → ℂ) : lower hw (c • θ) = c • lower hw θ := by
  unfold lower
  rw [archDerivAt_smul, archDerivAt_smul, archDerivAt_smul]
  funext g
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem raise_smul (c : ℂ) (θ : AdelicGL2 (𝓞 F) F → ℂ) : raise hw (c • θ) = c • raise hw θ := by
  unfold raise
  rw [archDerivAt_smul, archDerivAt_smul, archDerivAt_smul]
  funext g
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem raise_iter_smul (M : ℕ) (c : ℂ) (θ : AdelicGL2 (𝓞 F) F → ℂ) :
    (raise hw)^[M] (c • θ) = c • (raise hw)^[M] θ := by
  induction M generalizing θ with
  | zero => rfl
  | succ M ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, raise_smul, ih]

theorem lower_iter_smul (M : ℕ) (c : ℂ) (θ : AdelicGL2 (𝓞 F) F → ℂ) :
    (lower hw)^[M] (c • θ) = c • (lower hw)^[M] θ := by
  induction M generalizing θ with
  | zero => rfl
  | succ M ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, lower_smul, ih]

theorem lower_iter_props {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) (j : ℕ) :
    IsArchSmoothAt hw ((lower hw)^[j] θ) ∧ Dk hw ((lower hw)^[j] θ) = (m - 2 * Complex.I * j) • (lower hw)^[j] θ ∧
      archCasimirAt hw ((lower hw)^[j] θ) = lam • (lower hw)^[j] θ := by
  induction j with
  | zero =>
    refine ⟨hθ, ?_, hΩ⟩
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, sub_zero]
    exact hm
  | succ j ih =>
    obtain ⟨hs, hk, hc⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨smooth_lower hw hs, ?_, casimir_lower hw hs hc⟩
    rw [Dk_lower hw hs hk]
    congr 1
    push_cast
    ring

theorem raise_iter_props {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) (j : ℕ) :
    IsArchSmoothAt hw ((raise hw)^[j] θ) ∧ Dk hw ((raise hw)^[j] θ) = (m + 2 * Complex.I * j) • (raise hw)^[j] θ ∧
      archCasimirAt hw ((raise hw)^[j] θ) = lam • (raise hw)^[j] θ := by
  induction j with
  | zero =>
    refine ⟨hθ, ?_, hΩ⟩
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero]
    exact hm
  | succ j ih =>
    obtain ⟨hs, hk, hc⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨smooth_raise hw hs, ?_, casimir_raise hw hs hc⟩
    rw [Dk_raise hw hs hk]
    congr 1
    push_cast
    ring

theorem raise_iter_lower_iter {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) (M : ℕ) :
    (raise hw)^[M] ((lower hw)^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m - 2 * Complex.I * j) ^ 2 - 2 * Complex.I * (m - 2 * Complex.I * j))) • θ := by
  induction M with
  | zero => simp
  | succ M ih =>
    obtain ⟨hs, hk, hc⟩ := lower_iter_props hw hθ hm hΩ M
    rw [Function.iterate_succ_apply' (lower hw), Function.iterate_succ_apply (raise hw), raise_lower hw hs hk hc,
      raise_iter_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]

theorem lower_iter_raise_iter {θ : AdelicGL2 (𝓞 F) F → ℂ} (hθ : IsArchSmoothAt hw θ) {m lam : ℂ}
    (hm : Dk hw θ = m • θ) (hΩ : archCasimirAt hw θ = lam • θ) (M : ℕ) :
    (lower hw)^[M] ((raise hw)^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m + 2 * Complex.I * j) ^ 2 + 2 * Complex.I * (m + 2 * Complex.I * j))) • θ := by
  induction M with
  | zero => simp
  | succ M ih =>
    obtain ⟨hs, hk, hc⟩ := raise_iter_props hw hθ hm hΩ M
    rw [Function.iterate_succ_apply' (raise hw), Function.iterate_succ_apply (lower hw), lower_raise hw hs hk hc,
      lower_iter_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]

end OsAlg


/-! ### The three headlines -/

/-- **Headline 1.** The Casimir of a right translate by an archimedean point: it is the
translate of the Casimir, and smoothness together with the first and second derivative
continuities is preserved. -/
theorem archCasimirAt_rightTranslate_archRealGLAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ m : GL (Fin 2) ℝ,
        IsArchSmoothAt hw (rightTranslate K (archRealGLAt hw m) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (archRealGLAt hw m) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (archRealGLAt hw m) x)))) ∧
        archCasimirAt hw (rightTranslate K (archRealGLAt hw m) x) =
          rightTranslate K (archRealGLAt hw m) (archCasimirAt hw x) := by
  have _ := hxc
  intro m
  exact CasCore.package hw m x hxs hD1 hD2

/-- **Headline 2.** The pin's `leftCasimir` — the enveloping-algebra element acting by left
translation, `L d γ y = deriv (fun t => γ (archFlowAt hw d (-t) * y)) 0` — agrees with
`archCasimirAt` on a smooth `θ`. -/
theorem leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * L .H (L .H θ) y - (1 / 2 : ℂ) * L .H θ y + L .E (L .Fm θ) y) = archCasimirAt hw θ y := by
  intro L y
  exact CasLR.leftCasimir_eq hw hθ y

/-- **Headline 3.** The Maass raising/lowering calculus: from weight `m` and Casimir eigenvalue
`lam`, the iterates of `lower`/`raise` stay smooth with the shifted weights, and the two
iterated products factorise. -/
theorem iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) (m lam : ℂ)
    (hm : archDerivAt hw .E θ - archDerivAt hw .Fm θ = m • θ)
    (hΩ : archCasimirAt hw θ = lam • θ) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, IsArchSmoothAt hw (lower^[j] θ) ∧
      archDerivAt hw .E (lower^[j] θ) - archDerivAt hw .Fm (lower^[j] θ) = (m - 2 * Complex.I * j) • lower^[j] θ ∧
      archCasimirAt hw (lower^[j] θ) = lam • lower^[j] θ) ∧
    (∀ j : ℕ, IsArchSmoothAt hw (raise^[j] θ) ∧
      archDerivAt hw .E (raise^[j] θ) - archDerivAt hw .Fm (raise^[j] θ) = (m + 2 * Complex.I * j) • raise^[j] θ ∧
      archCasimirAt hw (raise^[j] θ) = lam • raise^[j] θ) ∧
    (∀ M : ℕ, raise^[M] (lower^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m - 2 * Complex.I * j) ^ 2 - 2 * Complex.I * (m - 2 * Complex.I * j))) • θ) ∧
    (∀ M : ℕ, lower^[M] (raise^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m + 2 * Complex.I * j) ^ 2 + 2 * Complex.I * (m + 2 * Complex.I * j))) • θ) := by
  intro lower raise
  exact ⟨fun j => OsAlg.lower_iter_props hw hθ hm hΩ j, fun j => OsAlg.raise_iter_props hw hθ hm hΩ j,
    fun M => OsAlg.raise_iter_lower_iter hw hθ hm hΩ M, fun M => OsAlg.lower_iter_raise_iter hw hθ hm hΩ M⟩


/-! ### The four real leaves

The continuation of the calculus above: the three `𝔰𝔩₂` commutators on a smooth `φ`, the character
identity `D_E − D_{F⁻} = 2·(weight)`, the Casimir's commutation with a right translation by a row
isometry at a *different* place, and the invariance of a function killed by `E` and `F⁻` under
`GL₂(ℝ)` at the place. Each headline is stated at its `Theorems/` wrapper; the helpers are the pin's
own, `private` exactly as the pin has them. -/

/-! #### The three commutators -/



open CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private theorem main
        (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) = (2 : ℂ) • archDerivAt hw .E φ ∧
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) = (-2 : ℂ) • archDerivAt hw .Fm φ ∧
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ := by
  refine ⟨?_, ?_, ?_⟩
  · funext g
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rel_E_H hw hφ g]; ring
  · funext g
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rel_Fm_H hw hφ g]; ring
  · funext g
    rw [Pi.sub_apply, rel_Fm_E hw hφ g]; ring



/-- **Headline.** The three `𝔰𝔩₂` commutator identities of the archimedean flows on a smooth `φ`:
`[H,E] = 2E`, `[H,F⁻] = -2F⁻`, `[E,F⁻] = H`. -/
theorem archDerivAt_commutator_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) = (2 : ℂ) • archDerivAt hw .E φ ∧
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) = (-2 : ℂ) • archDerivAt hw .Fm φ ∧
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ :=
  main hw φ hφ

/-! #### The character identity -/

namespace OsInf

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix
open CasCore

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private def rotMat (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos t, Real.sin t; -Real.sin t, Real.cos t]

omit hw in
private theorem det_rotMat (t : ℝ) : (rotMat t).det = 1 := by
  rw [rotMat, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq t]

private def rotGL (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat t) (by rw [det_rotMat]; exact one_ne_zero)

omit hw in
private theorem rotGL_coe (t : ℝ) : ((rotGL t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat t := rfl

omit hw in
private theorem rotGL_mem (t : ℝ) : rotGL t ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat t, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    simp only [rotGL_coe, rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq t

private def rotSO (t : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL t, rotGL_mem t⟩

omit hw in
private theorem archWeightOneℝ_rotSO (t : ℝ) :
    ((archWeightOneℝ (rotSO t) : ℂˣ) : ℂ) = Complex.exp (t * Complex.I) := by
  rw [Complex.exp_mul_I]
  show (⟨Real.cos t, Real.sin t⟩ : ℂ) = _
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]

omit [NumberField F] hw in
private theorem norm_symm (hw : w.IsReal) (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

private def rotAt (t : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm hw) (rotSO t)

private theorem adelicArchGLInclAt_rotAt (t : ℝ) :
    adelicArchGLInclAt F w ((rotAt hw t : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) =
      archRealGLAt hw (rotGL t) := rfl

omit [NumberField F] in
private theorem archWeightCharAt_rotAt (n : ℤ) (t : ℝ) :
    ((archWeightCharAt hw n (rotAt hw t) : ℂˣ) : ℂ) = Complex.exp (Complex.I * n * t) := by
  have hmap : rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) (rotAt hw t) = rotSO t := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat t i j)) = rotMat t i j
    exact RingEquiv.apply_symm_apply _ _
  simp only [archWeightCharAt, archWeightOneAt, MonoidHom.comp_apply, hmap, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val,
    archWeightOneℝ_rotSO, ← Complex.exp_int_mul]
  congr 1
  ring

omit hw in
private theorem hasDerivAt_rotMat_entries :
    HasDerivAt (fun t : ℝ => Matrix.of.symm (rotMat t)) (Matrix.of.symm (archDirMatrix .E - archDirMatrix .Fm)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_symm_apply, rotMat, archDirMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      sub_zero, zero_sub]
  · simpa using Real.hasDerivAt_cos 0
  · simpa using Real.hasDerivAt_sin 0
  · have h__af := (Real.hasDerivAt_sin 0).neg
    simp at h__af
    exact h__af
  · simpa using Real.hasDerivAt_cos 0

omit hw in
private theorem rotMat_zero : rotMat 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]

private theorem one_mem_U' : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero

private theorem archDerivAt_eq_fderiv {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ g = fderiv ℝ (chart hw φ g) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix d)) := by
  have hdiff : HasFDerivAt (chart hw φ g) (fderiv ℝ (chart hw φ g) (Matrix.of.symm 1))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact (((hφ g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds one_mem_U')).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw d t)) =
      fun t : ℝ => chart hw φ g (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) := by
    funext t
    show _ = φ (g * archRealLiftAt hw _)
    rw [← archRealLiftAt_mul_archRealGLAt hw one_mem_U', archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 = _
  rw [hfun]
  have h := (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix _ d)).deriv
  simp only [Function.comp_def, Equiv.apply_symm_apply, Matrix.one_mul] at h ⊢
  exact h

private theorem main (n : ℤ) (y : AdelicGL2 (𝓞 F) F → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ F w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y := by
  funext g
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, archDerivAt_eq_fderiv hw hys, archDerivAt_eq_fderiv hw hys]
  have hpath : ∀ t : ℝ, y (g * archRealGLAt hw (rotGL t)) = Complex.exp (Complex.I * n * t) * y g := by
    intro t
    rw [← adelicArchGLInclAt_rotAt hw, hyn (rotAt hw t) g, archWeightCharAt_rotAt]
  have hfun : (chart hw y g) ∘ (fun t : ℝ => Matrix.of.symm (rotMat t)) =
      fun t : ℝ => Complex.exp (Complex.I * n * t) * y g := by
    funext t
    show chart hw y g (Matrix.of.symm (rotMat t)) = _
    rw [← hpath t, archRealGLAt_eq_archRealLiftAt]
    rfl
  have hdiff : HasFDerivAt (chart hw y g) (fderiv ℝ (chart hw y g) (Matrix.of.symm 1)) (Matrix.of.symm (rotMat 0)) := by
    rw [rotMat_zero]
    exact (((hys g).contDiffAt (isOpen_setOf_det_ne_zero.mem_nhds (one_mem_U'))).differentiableAt (by simp)).hasFDerivAt
  have hL : HasDerivAt ((chart hw y g) ∘ (fun t : ℝ => Matrix.of.symm (rotMat t)))
      (fderiv ℝ (chart hw y g) (Matrix.of.symm 1) (Matrix.of.symm (archDirMatrix .E - archDirMatrix .Fm))) 0 :=
    hdiff.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotMat_entries
  have hR : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * n * t) * y g) (Complex.I * n * y g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * n * (t : ℂ)) (Complex.I * n) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (Complex.I * n)
    have h2 := (h1.cexp).mul_const (y g)
    simpa using h2
  rw [hfun] at hL
  have heq := hL.unique hR
  rw [← heq]
  show _ = (fderiv ℝ (chart hw y g) (Matrix.of.symm 1)) (Matrix.of.symm (archDirMatrix .E) - Matrix.of.symm (archDirMatrix .Fm))
  rw [map_sub]

end OsInf

/-- **Headline.** On a function with archimedean character `archWeightCharAt hw n`, the difference of
the `E` and `F⁻` derivatives is multiplication by `I·n`: the Casimir acts by the character. -/
theorem archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y :=
  OsInf.main hw n y hys hyn

/-! #### The row isometry at a different place -/

-- The pin's `hw' : w' ≠ w` is a hypothesis the statement carries and no proof step needs; it stays
-- spelled `hw'` because the checker compares binder spelling.
set_option linter.unusedVariables false in
/-- **Headline.** The Casimir commutes with right translation by a row isometry at a *different*
place, and smoothness with the first/second derivative continuities is preserved. -/
theorem archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x) := by
  have _ := hxc
  intro w' hw' k
  exact CommAway.package hw (CommAway.archRealGLAt_mul_rowIsometryInclAt₀_comm hw hw' k) x hxs hD1 hD2

/-! #### Killing `E` and `F⁻` gives `GL₂(ℝ)`-invariance -/

namespace InvZero

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private theorem apply_mul_archFlowAt_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (hd : archDerivAt hw d φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archFlowAt hw d t) = φ g := by
  set f : ℝ → ℂ := fun t => φ (g * archFlowAt hw d t) with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s)) 0 0 := by
      have hda := (hφ.differentiableAt_flow d (g * archFlowAt hw d t)).hasDerivAt
      have hz : deriv (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s)) 0 = 0 := by
        have := congrFun hd (g * archFlowAt hw d t)
        exact this
      rwa [hz] at hda
    have h1 : (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s)) = fun s => f (t + s) := by
      funext s
      simp only [hf, archFlowAt_add, mul_assoc]
    rw [h1, show (0 : ℝ) = t - t by simp] at h0
    have h2 := h0.comp_sub_const t t
    have h3 : (fun x : ℝ => f (t + (x - t))) = f := by
      funext x; congr 1; ring
    rw [h3] at h2
    exact h2
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hderiv t).deriv) t 0
  have h0 : f 0 = φ g := by simp only [hf, archFlowAt_zero, mul_one]
  rw [← h0, ← hconst]

private theorem apply_mul_upper (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (hE : archDerivAt hw .E φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archRealGLAt hw (unipotentGL2 t)) = φ g :=
  apply_mul_archFlowAt_eq hw φ hφ .E hE g t

private theorem apply_mul_lower (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (hF : archDerivAt hw .Fm φ = 0) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    φ (g * archRealGLAt hw (lowerUnipotentGL2 t)) = φ g :=
  apply_mul_archFlowAt_eq hw φ hφ .Fm hF g t

private theorem exists_eq_lower_upper_lower_upper (h : GL (Fin 2) ℝ)
    (hh : Matrix.GeneralLinearGroup.det h = 1) :
    ∃ s x c y : ℝ, h = lowerUnipotentGL2 s * unipotentGL2 x * lowerUnipotentGL2 c * unipotentGL2 y := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      - (h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
    have := congrArg (fun u : ℝˣ => (u : ℝ)) hh
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two] at this
    exact this
  set a := (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := (h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set c := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hc
  set d := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hd
  have heta : (h : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] := by
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
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith [hdet]
  · refine ⟨0, (a - 1) / c, c, (d - 1) / c, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, heta, lowerUnipotentGL2_coe, lowerUnipotentGL2_coe,
      unipotentGL2_coe, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith [hdet]

private theorem main (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (hE : archDerivAt hw .E φ = 0) (hF : archDerivAt hw .Fm φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archRealGLAt hw h) = φ g := by
  obtain ⟨s, x, c, y, rfl⟩ := exists_eq_lower_upper_lower_upper h hh
  rw [map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    apply_mul_upper hw φ hφ hE, apply_mul_lower hw φ hφ hF, apply_mul_upper hw φ hφ hE, apply_mul_lower hw φ hφ hF]

end InvZero

/-- **Headline.** A smooth function whose `E` and `F⁻` derivatives both vanish is right-invariant
under `GL₂(ℝ)` at the place, for determinant-one elements. -/
theorem apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (hE : archDerivAt hw .E φ = 0) (hF : archDerivAt hw .Fm φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archRealGLAt hw h) = φ g :=
  InvZero.main hw φ hφ hE hF g h hh

