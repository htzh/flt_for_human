/-
  The complex-place Iwasawa engine -- core (tier 3, unlisted).

  At an archimedean place the Iwasawa decomposition writes a translate of an
  invertible `2x2` complex matrix as a triangular (Borel) factor times a compact
  (unitary) factor; the pin proves it by hand and then estimates the compact
  factor's smoothness. This module is the shared spine of that development,
  written once. The pinned repository carries it in full inside each of six
  self-contained `S_` files under `P2M/Sol/` (6,540 raw lines for the nine
  complex nodes, 3,368 net new after dedup); here the three big files' common
  blocks are transcribed once:

  * `CplxIwasawa` -- the compact factor `kC`, the Borel factor `borelC`, their
    GL2 lifts and the control lemmas;
  * `CplxSmooth` -- the quadratic form `uQuad`, the coercive form `lamQuad`, the
    floor `floorK` and the iterated-derivative bounds on `radC` and `kC`;
  * `KCUnif` -- the explicit decay constants and their uniform-in-`g` forms;
  * `RhoTwoAux` -- the decomposition pair's private helpers;
  * `Engine` -- the four layer-0 kernels.

  The pin's proof-local copies of `botP`/`botQ`/`radC`/`kC` are byte-identical
  to `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean` and are dropped
  in its favour (playbook section 2.4); the pin's `B2bCL2` prelude is dropped in
  favour of the `CplxIwasawa` copy it duplicates. Every transcribed declaration
  carries a `-- pin:` provenance comment. The pin's own `M4aP3B.FourierDecay`
  block is homed at `FLTForHuman/MeasureTheory/FourierDecay.lean` and imported.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Basic
import FLTForHuman.MeasureTheory.FourierDecay

set_option autoImplicit false
-- The pin is written for Lean v4.33.1; in v4.34.0 `simp` already carries several
-- of the arguments the pin lists explicitly.  Keeping the pin's proof text
-- verbatim (playbook section 4) leaves those arguments redundant, so the linter
-- that would flag them is off for this file.
set_option linter.unusedSimpArgs false

noncomputable section

open ComplexConjugate
open scoped ContDiff

namespace AutomorphicForm.ComplexIwasawa


namespace CplxIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

-- pin: weylUnipC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:21)
def weylUnipC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] * !![1, z; 0, 1] * g


-- pin: botNormSqC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:27)
def botNormSqC : ℝ := Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

-- pin: centerC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:29)
def centerC : ℂ := -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) / (botNormSqC g : ℂ)



-- pin: borelC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:37)
def borelC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-g.det / (radC g z : ℂ),
     (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
     0, (radC g z : ℂ)]

variable {g}

-- pin: radC_sq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:44)
theorem radC_sq (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

-- pin: weylUnipC_eq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:48)
theorem weylUnipC_eq (z : ℂ) :
    weylUnipC g z = !![g 1 0, g 1 1; g 0 0 + z * g 1 0, g 0 1 + z * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylUnipC, Matrix.mul_apply, Fin.sum_univ_two]

-- pin: botNormSqC_pos (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:53)
theorem botNormSqC_pos (hg : g.det ≠ 0) : 0 < botNormSqC g := by
  rw [botNormSqC]
  rcases (add_nonneg (Complex.normSq_nonneg (g 1 0)) (Complex.normSq_nonneg (g 1 1))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hc : Complex.normSq (g 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    have hd : Complex.normSq (g 1 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, Complex.normSq_eq_zero.1 hc, Complex.normSq_eq_zero.1 hd,
      mul_zero, mul_zero, sub_zero]

-- pin: radC_sq_eq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:67)
theorem radC_sq_eq (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = botNormSqC g * Complex.normSq (z - centerC g)
      + Complex.normSq g.det / botNormSqC g := by
  have hA : botNormSqC g ≠ 0 := (botNormSqC_pos hg).ne'
  have hAc : (botNormSqC g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  have hz : z - centerC g = ((botNormSqC g : ℂ) * z + ((starRingEnd ℂ) (g 1 0) * g 0 0
      + (starRingEnd ℂ) (g 1 1) * g 0 1)) / (botNormSqC g : ℂ) := by
    rw [centerC]
    field_simp
    try ring
  rw [radC_sq, hz, Complex.normSq_div, Complex.normSq_ofReal, Matrix.det_fin_two]
  field_simp
  simp only [botP, botQ, botNormSqC, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

-- pin: radC_pos (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:84)
theorem radC_pos (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

-- pin: norm_det_div_sqrt_le_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:106)
theorem norm_det_div_sqrt_le_radC (hg : g.det ≠ 0) (z : ℂ) :
    ‖g.det‖ / Real.sqrt (botNormSqC g) ≤ radC g z := by
  have hA := botNormSqC_pos hg
  have hd : 0 ≤ ‖g.det‖ / Real.sqrt (botNormSqC g) := by positivity
  have hsq : (‖g.det‖ / Real.sqrt (botNormSqC g)) ^ 2 ≤ radC g z ^ 2 := by
    rw [div_pow, Real.sq_sqrt hA.le, Complex.sq_norm, radC_sq_eq hg z]
    have h2 : 0 ≤ botNormSqC g * Complex.normSq (z - centerC g) :=
      mul_nonneg (botNormSqC_pos hg).le (Complex.normSq_nonneg _)
    linarith
  calc ‖g.det‖ / Real.sqrt (botNormSqC g)
      = Real.sqrt ((‖g.det‖ / Real.sqrt (botNormSqC g)) ^ 2) := (Real.sqrt_sq hd).symm
    _ ≤ Real.sqrt (radC g z ^ 2) := Real.sqrt_le_sqrt hsq
    _ = radC g z := Real.sqrt_sq (radC_pos hg z).le

-- pin: kC_mul_conjTranspose (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:120)
theorem kC_mul_conjTranspose (hg : g.det ≠ 0) (z : ℂ) :
    kC g z * (kC g z).conjTranspose = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

-- pin: conjTranspose_mul_kC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:139)
theorem conjTranspose_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

-- pin: det_kC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:158)
theorem det_kC (hg : g.det ≠ 0) (z : ℂ) : (kC g z).det = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have e : (kC g z).det = (botQ g z * (starRingEnd ℂ) (botQ g z)
      + botP g z * (starRingEnd ℂ) (botP g z)) / ((radC g z : ℂ) * (radC g z : ℂ)) := by
    rw [kC, Matrix.det_fin_two_of]
    ring
  have num : ((Complex.normSq (botQ g z) + Complex.normSq (botP g z) : ℝ) : ℂ)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [e, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, num,
    div_self (mul_ne_zero hr hr)]

-- pin: det_borelC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:173)
theorem det_borelC (hg : g.det ≠ 0) (z : ℂ) : (borelC g z).det = -g.det := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  rw [borelC, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ hr]

-- pin: weylUnipC_eq_borelC_mul_kC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:177)
theorem weylUnipC_eq_borelC_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    weylUnipC g z = borelC g z * kC g z := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  simp only [botP, botQ, map_add, map_mul] at key
  rw [weylUnipC_eq, borelC, kC, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, botP, botQ, map_add, map_mul] <;>
    (try field_simp) <;>
    (rw [pow_two ((radC g z : ℂ)), ← key]
     ring)

-- pin: norm_row_sq_kC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:197)
theorem norm_row_sq_kC (hg : g.det ≠ 0) (z : ℂ) (x y : ℂ) :
    ‖x * kC g z 0 0 + y * kC g z 1 0‖ ^ 2 + ‖x * kC g z 0 1 + y * kC g z 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hrr : radC g z * radC g z = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
    rw [← pow_two]
    exact radC_sq g z
  have e1 : x * kC g z 0 0 + y * kC g z 1 0
      = (x * (starRingEnd ℂ) (botQ g z) + y * botP g z) / (radC g z : ℂ) := by
    simp [kC]
    try ring
  have e2 : x * kC g z 0 1 + y * kC g z 1 1
      = (-(x * (starRingEnd ℂ) (botP g z)) + y * botQ g z) / (radC g z : ℂ) := by
    simp [kC]
    try ring
  rw [e1, e2]
  simp only [Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal]
  rw [← add_div, hrr]
  have hpos : 0 < Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
    rw [← radC_sq g z]
    exact pow_pos (radC_pos hg z) 2
  rw [div_eq_iff hpos.ne']
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

-- pin: contDiff_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:222)
theorem contDiff_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := by
  have hnormSq : ContDiff ℝ ∞ Complex.normSq := by
    have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
      funext w
      exact Complex.normSq_apply w
    rw [h]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hinner : ContDiff ℝ ∞ (fun z => Complex.normSq (botP g z) + Complex.normSq (botQ g z)) :=
    (hnormSq.comp hP).add (hnormSq.comp hQ)
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : Complex.normSq (botP g z) + Complex.normSq (botQ g z) ≠ 0 := by
    rw [← radC_sq g z]
    exact (pow_pos (radC_pos hg z) 2).ne'
  have h := (Real.contDiffAt_sqrt hpos).comp z hinner.contDiffAt
  simp [radC, Function.comp_def] at h
  exact h

-- pin: contDiff_kC_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:247)
theorem contDiff_kC_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun z => kC g z i j) := by
  have hradInv : ContDiff ℝ ∞ (fun z => (radC g z)⁻¹) :=
    (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'
  have hradInvC : ContDiff ℝ ∞ (fun z => (((radC g z)⁻¹ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hradInv
  have hconj : ContDiff ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) := Complex.conjCLE.contDiff
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hPc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botP g z)) := hconj.comp hP
  have hQc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botQ g z)) := hconj.comp hQ
  have hdiv : ∀ (w : ℂ) (r : ℝ), w / (r : ℂ) = w * ((r⁻¹ : ℝ) : ℂ) := by
    intro w r
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  fin_cases i <;> fin_cases j <;>
    simp only [kC, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    simp only [hdiv, neg_div]
  · exact hQc.mul hradInvC
  · first
    | exact (hPc.mul hradInvC).neg
    | exact hPc.neg.mul hradInvC
  · exact hP.mul hradInvC
  · exact hQ.mul hradInvC

-- pin: contDiff_borelC_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:276)
theorem contDiff_borelC_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun z => borelC g z i j) := by
  have hradC : ContDiff ℝ ∞ (fun z => ((radC g z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_radC hg)
  have hradInv : ContDiff ℝ ∞ (fun z => (radC g z)⁻¹) :=
    (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'
  have hradInvC : ContDiff ℝ ∞ (fun z => (((radC g z)⁻¹ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hradInv
  have hconj : ContDiff ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) := Complex.conjCLE.contDiff
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hPc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botP g z)) := hconj.comp hP
  have hQc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botQ g z)) := hconj.comp hQ
  have hdiv : ∀ (w : ℂ) (r : ℝ), w / (r : ℂ) = w * ((r⁻¹ : ℝ) : ℂ) := by
    intro w r
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  fin_cases i <;> fin_cases j <;>
    simp only [borelC, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    simp only [hdiv, neg_div]
  · first
    | exact (contDiff_const.mul hradInvC).neg
    | exact contDiff_const.mul hradInvC
  · exact ((contDiff_const.mul hPc).add (contDiff_const.mul hQc)).mul hradInvC
  · exact contDiff_const
  · exact hradC

-- pin: kCGL (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:307)
def kCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨kC g z, (kC g z).conjTranspose, kC_mul_conjTranspose hg z, conjTranspose_mul_kC hg z⟩

-- pin: coe_kCGL (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:310)
@[scoped simp] theorem coe_kCGL (hg : g.det ≠ 0) (z : ℂ) :
    ((kCGL hg z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kC g z := rfl

-- pin: borelCGL (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:313)
def borelCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borelC g z)
    (by rw [det_borelC hg z]; exact neg_ne_zero.2 hg)

-- pin: coe_borelCGL (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:317)
@[scoped simp] theorem coe_borelCGL (hg : g.det ≠ 0) (z : ℂ) :
    ((borelCGL hg z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = borelC g z := rfl

-- pin: weylC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:320)
def weylC : GL (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

-- pin: unipC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:325)
def unipC (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨!![1, z; 0, 1], !![1, -z; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

-- pin: weylC_mul_unipC_mul_eq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:330)
theorem weylC_mul_unipC_mul_eq (g : GL (Fin 2) ℂ) (z : ℂ) :
    weylC * unipC z * g
      = borelCGL (g := (g : Matrix (Fin 2) (Fin 2) ℂ))
          (Matrix.GeneralLinearGroup.det_ne_zero g) z
        * kCGL (Matrix.GeneralLinearGroup.det_ne_zero g) z := by
  apply Units.ext
  simp only [Units.val_mul, coe_borelCGL, coe_kCGL]
  exact weylUnipC_eq_borelC_mul_kC (Matrix.GeneralLinearGroup.det_ne_zero g) z

-- pin: ctrl_weylUnipC_w (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:339)
theorem ctrl_weylUnipC_w : weylUnipC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [weylUnipC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: ctrl_radC_w (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:344)
theorem ctrl_radC_w : radC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

-- pin: ctrl_kC_w (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:349)
theorem ctrl_kC_w : kC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [kC, Matrix.one_fin_two, ctrl_radC_w, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

-- pin: ctrl_borelC_w (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:354)
theorem ctrl_borelC_w : borelC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [borelC, Matrix.one_fin_two, ctrl_radC_w, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of]

-- pin: ctrl_radC_c1 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:359)
theorem ctrl_radC_c1 : radC !![Complex.I, 0; 0, 1] 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

-- pin: ctrl_decomp_c1 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:364)
theorem ctrl_decomp_c1 :
    weylUnipC !![Complex.I, 0; 0, 1] 0
      = borelC !![Complex.I, 0; 0, 1] 0 * kC !![Complex.I, 0; 0, 1] 0 := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c1, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of]

-- pin: ctrl_radC_c2 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:372)
theorem ctrl_radC_c2 : radC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) = 3 := by
  rw [radC, show (3 : ℝ) = Real.sqrt 9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

-- pin: ctrl_decomp_c2 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:378)
theorem ctrl_decomp_c2 :
    weylUnipC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)
      = borelC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) * kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c2, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of, Complex.ext_iff] <;>
    norm_num

-- pin: ctrl_radC_c3 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:387)
theorem ctrl_radC_c3 : radC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) = 3 := by
  rw [radC, show (3 : ℝ) = Real.sqrt 9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

-- pin: ctrl_decomp_c3 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:393)
theorem ctrl_decomp_c3 :
    weylUnipC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I)
      = borelC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) * kC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c3, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of, Complex.ext_iff] <;>
    norm_num

-- pin: ctrl_kC_unitary_c2 (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:402)
theorem ctrl_kC_unitary_c2 :
    kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)
      * (kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)).conjTranspose = 1 := by
  rw [kC, ctrl_radC_c2, botP, botQ, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat,
      Complex.ext_iff] <;>
    norm_num

end CplxIwasawa

namespace CplxSmooth

open scoped ContDiff Nat

open CplxIwasawa

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: ctrl_radC_one_zero (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:430)
theorem ctrl_radC_one_zero : radC (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply, Matrix.one_apply]

-- pin: ctrl_kC_one_zero (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:435)
theorem ctrl_kC_one_zero :
    kC (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = !![0, -1; 1, 0] := by
  rw [kC, ctrl_radC_one_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [botP, botQ, Matrix.one_apply]

-- pin: ctrl_fderiv_botQ_one (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:442)
theorem ctrl_fderiv_botQ_one (z : ℂ) :
    fderiv ℝ (botQ (1 : Matrix (Fin 2) (Fin 2) ℂ)) z = ContinuousLinearMap.id ℝ ℂ := by
  have h : botQ (1 : Matrix (Fin 2) (Fin 2) ℂ) = id := by
    funext w
    simp [botQ, Matrix.one_apply]
  rw [h, fderiv_id]

-- pin: iteratedDerivWithin_rpow_const (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:449)
theorem iteratedDerivWithin_rpow_const {c : ℝ} (hc : 0 < c) (r : ℝ) (k : ℕ) :
    Set.EqOn (iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c))
      (fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k)) (Set.Ioi c) := by
  induction k with
  | zero =>
    intro v hv
    simp [iteratedDerivWithin_zero]
  | succ k ih =>
    intro v hv
    have hvpos : 0 < v := hc.trans hv
    have hopen : IsOpen (Set.Ioi c) := isOpen_Ioi
    rw [iteratedDerivWithin_succ, derivWithin_of_isOpen hopen hv]
    have hev : iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c)
        =ᶠ[nhds v] fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun v : ℝ => v ^ (r - k))
        ((r - k) * v ^ (r - k - 1)) v :=
      Real.hasDerivAt_rpow_const (Or.inl hvpos.ne')
    rw [deriv_const_mul _ hd.differentiableAt, hd.deriv]
    rw [Finset.prod_range_succ]
    push_cast
    ring_nf

-- pin: norm_iteratedDerivWithin_rpow_neg_half_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:474)
theorem norm_iteratedDerivWithin_rpow_neg_half_le {c : ℝ} (hc : 0 < c) (k : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) (Set.Ioi c) v‖
      ≤ k ! * c ^ (-(1 : ℝ) / 2 - k) := by
  have hvpos : (0 : ℝ) < v := hc.trans hv
  rw [iteratedDerivWithin_rpow_const hc (-(1 : ℝ) / 2) k hv]
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| ≤ (k ! : ℝ) := by
    rw [Finset.abs_prod]
    have hfac : (k ! : ℝ) = ∏ i ∈ Finset.range k, ((i : ℝ) + 1) := by
      induction k with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => ?_)
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hneg : (-(1 : ℝ) / 2 - i) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have h2 : |v ^ (-(1 : ℝ) / 2 - (k : ℝ))| ≤ c ^ (-(1 : ℝ) / 2 - k) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hvpos.le _)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
      (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hvpos) hv.le
  calc |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| * |v ^ (-(1 : ℝ) / 2 - (k : ℝ))|
      ≤ (k ! : ℝ) * c ^ (-(1 : ℝ) / 2 - k) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

-- pin: uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:502)
def uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ → ℝ := fun w =>
  botNormSqC g * Complex.normSq (w - centerC g) + Complex.normSq g.det / botNormSqC g

-- pin: uQuad_eq_radC_sq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:505)
theorem uQuad_eq_radC_sq (hg : g.det ≠ 0) (w : ℂ) : uQuad g w = radC g w ^ 2 :=
  (radC_sq_eq hg w).symm

-- pin: uQuad_ge (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:508)
theorem uQuad_ge (hg : g.det ≠ 0) (w : ℂ) :
    Complex.normSq g.det / botNormSqC g ≤ uQuad g w := by
  have h : 0 ≤ botNormSqC g * Complex.normSq (w - centerC g) :=
    mul_nonneg (botNormSqC_pos hg).le (Complex.normSq_nonneg _)
  unfold uQuad
  linarith

-- pin: uQuad_eq_coords (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:515)
theorem uQuad_eq_coords (w : ℂ) :
    uQuad g w = botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
      + Complex.normSq g.det / botNormSqC g := by
  unfold uQuad
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

-- pin: hasFDerivAt_uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:522)
theorem hasFDerivAt_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) :
    HasFDerivAt (uQuad g)
      ((2 * botNormSqC g * (w - centerC g).re) • Complex.reCLM
        + (2 * botNormSqC g * (w - centerC g).im) • Complex.imCLM) w := by
  have hre : HasFDerivAt (fun v : ℂ => (v.re - (centerC g).re) ^ 2)
      ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.re - (centerC g).re)
        (Complex.reCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.reCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have him : HasFDerivAt (fun v : ℂ => (v.im - (centerC g).im) ^ 2)
      ((2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.im - (centerC g).im)
        (Complex.imCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.imCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have hsum := ((hre.add him).const_mul (botNormSqC g)).add_const
    (Complex.normSq g.det / botNormSqC g)
  have huq : HasFDerivAt (uQuad g)
      (botNormSqC g • ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ))) w := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards with v
    rw [uQuad_eq_coords]
    simp only [Pi.add_apply]
  convert huq using 1
  ext v
  simp [smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

-- pin: lamQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:553)
def lamQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight ((2 * botNormSqC g) • (Complex.reCLM : ℂ →L[ℝ] ℝ))
    + Complex.imCLM.smulRight ((2 * botNormSqC g) • (Complex.imCLM : ℂ →L[ℝ] ℝ))

-- pin: lamQuad_apply_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:557)
@[scoped simp] theorem lamQuad_apply_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (v w : ℂ) :
    lamQuad g v w = 2 * botNormSqC g * v.re * w.re + 2 * botNormSqC g * v.im * w.im := by
  simp [lamQuad, ContinuousLinearMap.smulRight_apply]
  ring

-- pin: norm_lamQuad_apply_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:562)
theorem norm_lamQuad_apply_le (g : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) :
    ‖lamQuad g v‖ ≤ 4 * botNormSqC g * ‖v‖ := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hA) (norm_nonneg v)) fun w => ?_
  rw [lamQuad_apply_apply, Real.norm_eq_abs]
  have hre : |v.re * w.re| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm v) (Complex.abs_re_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have him : |v.im * w.im| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_im_le_norm v) (Complex.abs_im_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left hre'.2 hA, mul_le_mul_of_nonneg_left hre'.1 hA,
      mul_le_mul_of_nonneg_left him'.2 hA, mul_le_mul_of_nonneg_left him'.1 hA]

-- pin: norm_lamQuad_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:584)
theorem norm_lamQuad_le (g : Matrix (Fin 2) (Fin 2) ℂ) : ‖lamQuad g‖ ≤ 4 * botNormSqC g := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hA)
    fun v => norm_lamQuad_apply_le g v

-- pin: fderiv_uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:591)
theorem fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    fderiv ℝ (uQuad g) z = lamQuad g (z - centerC g) := by
  rw [(hasFDerivAt_uQuad g z).fderiv]
  ext w
  simp [smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

-- pin: hasFDerivAt_fderiv_uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:599)
theorem hasFDerivAt_fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    HasFDerivAt (fderiv ℝ (uQuad g)) (lamQuad g) z := by
  have heq : fderiv ℝ (uQuad g) = fun w => lamQuad g (w - centerC g) :=
    funext (fderiv_uQuad g)
  rw [heq]
  have hcomp := (lamQuad g).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (centerC g))
  exact hcomp

-- pin: norm_iteratedFDeriv_uQuad_one (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:607)
theorem norm_iteratedFDeriv_uQuad_one (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * ‖z - centerC g‖ := by
  have h1 : ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  rw [h1, norm_iteratedFDeriv_zero, fderiv_uQuad]
  exact norm_lamQuad_apply_le g _

-- pin: norm_iteratedFDeriv_uQuad_two (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:615)
theorem norm_iteratedFDeriv_uQuad_two (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 (uQuad g) z‖ ≤ 4 * botNormSqC g := by
  have h2 : ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 1)).symm
  have h1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  have hfd : fderiv ℝ (fderiv ℝ (uQuad g)) z = lamQuad g :=
    (hasFDerivAt_fderiv_uQuad g z).fderiv
  rw [h2, h1, norm_iteratedFDeriv_zero, hfd]
  exact norm_lamQuad_le g

-- pin: norm_iteratedFDeriv_uQuad_ge_three (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:628)
theorem norm_iteratedFDeriv_uQuad_ge_three (g : Matrix (Fin 2) (Fin 2) ℂ) {i : ℕ}
    (hi : 3 ≤ i) (z : ℂ) : ‖iteratedFDeriv ℝ i (uQuad g) z‖ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have hfd2 : fderiv ℝ (fderiv ℝ (uQuad g)) = fun _ => lamQuad g :=
    funext fun w => (hasFDerivAt_fderiv_uQuad g w).fderiv
  have h3 : ‖iteratedFDeriv ℝ (k + 3) (uQuad g) z‖
      = ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 2)).symm
  have h4 : ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
  rw [h3, h4, hfd2, iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
  simp

-- pin: contDiff_uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:642)
theorem contDiff_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (uQuad g) := by
  have h : uQuad g = fun w =>
      botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
        + Complex.normSq g.det / botNormSqC g :=
    funext fun w => uQuad_eq_coords w
  rw [h]
  exact (contDiff_const.mul (((Complex.reCLM.contDiff.sub contDiff_const).pow 2).add
    ((Complex.imCLM.contDiff.sub contDiff_const).pow 2))).add contDiff_const

-- pin: contDiff_inv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:651)
theorem contDiff_inv_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ fun w => (radC g w)⁻¹ :=
  (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'

-- pin: rpow_neg_half_eq_inv_sqrt (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:654)
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1:ℝ)/2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]
  norm_num

-- pin: uQuad_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:659)
theorem uQuad_le (hg : g.det ≠ 0) (w : ℂ) :
    uQuad g w ≤ (botNormSqC g + Complex.normSq g.det / botNormSqC g)
      * (1 + ‖w - centerC g‖) ^ 2 := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) ≤ Complex.normSq g.det / botNormSqC g :=
    div_nonneg (Complex.normSq_nonneg _) hA.le
  have hd : (0:ℝ) ≤ ‖w - centerC g‖ := norm_nonneg _
  have h1 : Complex.normSq (w - centerC g) = ‖w - centerC g‖ ^ 2 := by
    rw [Complex.sq_norm]
  unfold uQuad
  rw [h1]
  nlinarith [sq_nonneg (‖w - centerC g‖)]

-- pin: norm_iteratedFDeriv_uQuad_one_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:672)
theorem norm_iteratedFDeriv_uQuad_one_le (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * (1 + ‖z - centerC g‖) := by
  refine (norm_iteratedFDeriv_uQuad_one g z).trans ?_
  have hA : (0:ℝ) ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - centerC g)]) (by linarith)

-- pin: floorK (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:680)
def floorK (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) / 18

-- pin: floorK_pos (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:683)
theorem floorK_pos (hg : g.det ≠ 0) : 0 < floorK g := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  exact div_pos (lt_min hA hM) (by norm_num)

-- pin: floorK_mul_lt_uQuad (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:689)
theorem floorK_mul_lt_uQuad (hg : g.det ≠ 0) (z : ℂ) {v : ℂ} (hv : v ∈ Metric.ball z 1) :
    floorK g * (1 + ‖z - centerC g‖) ^ 2 < uQuad g v := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hmin : (0:ℝ) < min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) := lt_min hA hM
  have hminA : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) ≤ botNormSqC g :=
    min_le_left _ _
  have hminM : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g)
      ≤ Complex.normSq g.det / botNormSqC g := min_le_right _ _
  have hvz : ‖v - z‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.1 hv
  have hnv : Complex.normSq (v - centerC g) = ‖v - centerC g‖ ^ 2 := by
    rw [Complex.sq_norm]
  have huv : uQuad g v
      = botNormSqC g * ‖v - centerC g‖ ^ 2 + Complex.normSq g.det / botNormSqC g := by
    unfold uQuad
    rw [hnv]
  have hd0 : (0:ℝ) ≤ ‖z - centerC g‖ := norm_nonneg _
  have hvc0 : (0:ℝ) ≤ ‖v - centerC g‖ := norm_nonneg _
  unfold floorK
  rcases le_total (‖z - centerC g‖) 2 with hcase | hcase
  · have h1 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1
      (le_of_lt (div_pos hmin (by norm_num : (0:ℝ) < 18)))
    have h4 : (0:ℝ) ≤ botNormSqC g * ‖v - centerC g‖ ^ 2 :=
      mul_nonneg hA.le (sq_nonneg _)
    rw [huv]
    linarith
  · have hvc : ‖z - centerC g‖ - 1 < ‖v - centerC g‖ := by
      have htri : ‖z - centerC g‖ ≤ ‖z - v‖ + ‖v - centerC g‖ := by
        calc ‖z - centerC g‖ = ‖z - v + (v - centerC g)‖ := by
              rw [show z - v + (v - centerC g) = z - centerC g from by ring]
          _ ≤ ‖z - v‖ + ‖v - centerC g‖ := norm_add_le _ _
      have hzv : ‖z - v‖ < 1 := by rwa [norm_sub_rev]
      linarith
    have hd1 : (0:ℝ) ≤ ‖z - centerC g‖ - 1 := by linarith
    have h1 : 1 + ‖z - centerC g‖ ≤ 3 * (‖z - centerC g‖ - 1) := by linarith
    have h2 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 * (‖z - centerC g‖ - 1) ^ 2 := by nlinarith
    have h4 : (‖z - centerC g‖ - 1) ^ 2 < ‖v - centerC g‖ ^ 2 := by nlinarith
    have h5 := mul_lt_mul_of_pos_left h4 hA
    rw [huv]
    nlinarith [sq_nonneg (‖z - centerC g‖ - 1), hmin.le, hM.le]

-- pin: exists_decay_bound_iteratedFDeriv_inv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:734)
theorem exists_decay_bound_iteratedFDeriv_inv_radC (hg : g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖
        ≤ C / (1 + ‖z - centerC g‖) ^ (n + 1) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hK : (0:ℝ) < floorK g := floorK_pos hg
  have hM0 : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hupos : ∀ w : ℂ, (0:ℝ) < uQuad g w := fun w => lt_of_lt_of_le hM0 (uQuad_ge hg w)
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc2 : (0:ℝ) < 4 * botNormSqC g / floorK g + 1 := by
    have h0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
    linarith
  have hsK : (0:ℝ) < (Real.sqrt (floorK g))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hK)
  refine ⟨(n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹,
    mul_pos (mul_pos (mul_pos hfac hfac) (pow_pos hc2 n)) hsK, fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hcz : (0:ℝ) < floorK g * (1 + ‖z - centerC g‖) ^ 2 := mul_pos hK (pow_pos hW0 2)
  have hball : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
  have hmaps : Set.MapsTo (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
      (Metric.ball z 1) (Set.Ioi (1:ℝ)) := fun v hv =>
    Set.mem_Ioi.2 ((one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hv))
  have hrw : (fun w => (radC g w)⁻¹)
      = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
          • ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
             fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) w := by
    funext w
    have hu := hupos w
    have h1 : radC g w = Real.sqrt (uQuad g w) := by
      rw [uQuad_eq_radC_sq hg w, Real.sqrt_sq (radC_pos hg w).le]
    have hL : (Real.sqrt (uQuad g w))⁻¹ = uQuad g w ^ (-(1:ℝ)/2) :=
      (rpow_neg_half_eq_inv_sqrt hu.le).symm
    have hne : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2) ≠ 0 :=
      (Real.rpow_pos_of_pos hcz _).ne'
    have hR : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * (uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) ^ (-(1:ℝ)/2)
        = uQuad g w ^ (-(1:ℝ)/2) := by
      rw [show uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)
          = uQuad g w * (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ from div_eq_mul_inv _ _,
        Real.mul_rpow hu.le (inv_nonneg.2 hcz.le), Real.inv_rpow hcz.le,
        mul_comm (uQuad g w ^ (-(1:ℝ)/2)), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h1, hL, smul_eq_mul, Function.comp_apply, hR]
  rw [hrw]
  have hũ : ContDiff ℝ ∞ fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (contDiff_uQuad g).div_const _
  have hũz : (1:ℝ) < uQuad g z / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hball)
  have hcomp_cd : ContDiffAt ℝ ∞ ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
      fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z :=
    (Real.contDiffAt_rpow_const_of_ne (by linarith : uQuad g z
      / (floorK g * (1 + ‖z - centerC g‖) ^ 2) ≠ 0)).comp z hũ.contDiffAt
  rw [iteratedFDeriv_const_smul_apply' (hcomp_cd.of_le (mod_cast le_top))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hcz _)]
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ))
        ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖ ≤ (n ! : ℝ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    calc ‖iteratedDerivWithin i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi 1)
          ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖
        ≤ i ! * (1:ℝ) ^ (-(1 : ℝ) / 2 - i) :=
          norm_iteratedDerivWithin_rpow_neg_half_le one_pos i (hmaps hball)
      _ = (i ! : ℝ) := by rw [Real.one_rpow, mul_one]
      _ ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i
          (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
        ≤ ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen i Metric.isOpen_ball hball]
    have hsm : (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
        = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ • uQuad g w := by
      funext w
      rw [smul_eq_mul, div_eq_inv_mul]
    rw [hsm, iteratedFDeriv_const_smul_apply'
      ((contDiff_uQuad g).contDiffAt.of_le (mod_cast le_top))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcz)]
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hb := norm_iteratedFDeriv_uQuad_one_le g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
            * (4 * botNormSqC g * (1 + ‖z - centerC g‖))
            = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := by
          field_simp
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
              * (4 * botNormSqC g * (1 + ‖z - centerC g‖)) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) * (1 + ‖z - centerC g‖)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hW0.le)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 1 := by
              rw [pow_one, ← div_eq_mul_inv]
      · have hb := norm_iteratedFDeriv_uQuad_two g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g)
            = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := by
          field_simp
        have hX0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
        have hX1 : 4 * botNormSqC g / floorK g ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 := by
          nlinarith
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 :=
              mul_le_mul_of_nonneg_right hX1 (sq_nonneg _)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 2 := by
              rw [div_pow, inv_pow, ← div_eq_mul_inv]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, mul_zero]
      exact pow_nonneg (div_nonneg hc2.le hW0.le) i
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hgOn hũ.contDiffOn
    (mod_cast le_top) isOpen_Ioi.uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn
    hmaps hball hC hD
  rw [← iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hball]
  have hczhalf : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
      = (Real.sqrt (floorK g))⁻¹ * (1 + ‖z - centerC g‖)⁻¹ := by
    have h1 : floorK g * (1 + ‖z - centerC g‖) ^ 2
        = (Real.sqrt (floorK g) * (1 + ‖z - centerC g‖)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
    have hb0 : (0:ℝ) ≤ Real.sqrt (floorK g) * (1 + ‖z - centerC g‖) :=
      mul_nonneg (Real.sqrt_nonneg _) hW0.le
    rw [h1, rpow_neg_half_eq_inv_sqrt (sq_nonneg _), Real.sqrt_sq hb0, mul_inv]
  calc (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ‖iteratedFDerivWithin ℝ n ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
            fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
      ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ((n ! : ℝ) * n !
          * ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hcz _).le
    _ = (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹
        / (1 + ‖z - centerC g‖) ^ (n + 1) := by
        rw [hczhalf, div_pow, pow_succ]
        have hsne : Real.sqrt (floorK g) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
        field_simp

-- pin: exists_decay_bound_iteratedFDeriv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:873)
theorem exists_decay_bound_iteratedFDeriv_radC (hg : g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (radC g) z‖
        ≤ C * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
  obtain ⟨C0, hC0, hB0⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  obtain ⟨C1, hC1, hB1⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 1)
  obtain ⟨C2, hC2, hB2⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 2)
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) ≤ Complex.normSq g.det / botNormSqC g :=
    div_nonneg (Complex.normSq_nonneg _) hA.le
  have h1p : (0:ℝ) < (botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0 :=
    mul_pos (by linarith) hC0
  have h2p : (0:ℝ) < 4 * botNormSqC g * C1 := mul_pos (by linarith) hC1
  have h3p : (0:ℝ) < 4 * botNormSqC g * C2 := mul_pos (by linarith) hC2
  refine ⟨2 ^ n * ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
      + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2),
    mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) n) (by linarith), fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hrw : radC g = fun w => uQuad g w * (radC g w)⁻¹ := by
    funext w
    rw [uQuad_eq_radC_sq hg w, pow_two, mul_assoc, mul_inv_cancel₀ (radC_pos hg w).ne',
      mul_one]
  rw [hrw]
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (contDiff_uQuad g) (contDiff_inv_radC hg) z
    (mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (uQuad g) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w => (radC g w)⁻¹) z‖
        ≤ (n.choose i : ℝ) * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
            + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
            * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hu0 : ‖iteratedFDeriv ℝ 0 (uQuad g) z‖
            ≤ (botNormSqC g + Complex.normSq g.det / botNormSqC g)
              * (1 + ‖z - centerC g‖) ^ 2 := by
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
            abs_of_pos (lt_of_lt_of_le (div_pos (Complex.normSq_pos.2 hg) hA)
              (uQuad_ge hg z))]
          exact uQuad_le hg z
        calc ‖iteratedFDeriv ℝ 0 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 0) (fun w => (radC g w)⁻¹) z‖
            ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g)
                * (1 + ‖z - centerC g‖) ^ 2) * (C0 / (1 + ‖z - centerC g‖) ^ (n + 1)) := by
              rw [Nat.sub_zero]
              exact mul_le_mul hu0 (hB0 z) (norm_nonneg _)
                (mul_nonneg (by linarith) (sq_nonneg _))
          _ = (botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_two, pow_succ]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h2p, h3p]
      · have hu1 := norm_iteratedFDeriv_uQuad_one_le g z
        have hn1 : 1 ≤ n := hin
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        calc ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
            ≤ (4 * botNormSqC g * (1 + ‖z - centerC g‖))
                * (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) :=
              mul_le_mul hu1 (hB1 z) (norm_nonneg _)
                (mul_nonneg (by linarith) hW0.le)
          _ = 4 * botNormSqC g * C1
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [hsub]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h1p, h3p]
      · have hu2 := norm_iteratedFDeriv_uQuad_two g z
        have hn2 : 2 ≤ n := hin
        have hsub : n - 2 + 1 = n - 1 := by omega
        have hsub2 : n - 1 + 1 = n := by omega
        calc ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 2) (fun w => (radC g w)⁻¹) z‖
            ≤ (4 * botNormSqC g) * (C2 / (1 + ‖z - centerC g‖) ^ (n - 2 + 1)) :=
              mul_le_mul hu2 (hB2 z) (norm_nonneg _) (by linarith)
          _ = 4 * botNormSqC g * C2
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [hsub, show (1 + ‖z - centerC g‖) ^ n
                  = (1 + ‖z - centerC g‖) ^ (n - 1) * (1 + ‖z - centerC g‖) from by
                rw [← pow_succ, hsub2]]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h1p, h2p]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, zero_mul]
      positivity
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (uQuad g) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w => (radC g w)⁻¹) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
            + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
            * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) :=
        Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
          + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
          * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ = 2 ^ n * ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
          + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
          * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
        ring

-- pin: conjCLM (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:992)
def conjCLM : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

-- pin: conjCLM_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:994)
@[scoped simp] theorem conjCLM_apply (w : ℂ) : conjCLM w = (starRingEnd ℂ) w := rfl

-- pin: exists_bound_iteratedFDeriv_inv_radC_smul_affine (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:996)
theorem exists_bound_iteratedFDeriv_inv_radC_smul_affine (hg : g.det ≠ 0)
    (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹ • (c₀ + L w)) z‖ ≤ C := by
  obtain ⟨C0, hC0, hB0⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  obtain ⟨C1, hC1, hB1⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 1)
  have hcq0 : (0:ℝ) ≤ ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ := by positivity
  have hLC1 : (0:ℝ) ≤ ‖L‖ * C1 := mul_nonneg (norm_nonneg _) hC1.le
  have hcqC0 : (0:ℝ) ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 := mul_nonneg hcq0 hC0.le
  have h2n : (0:ℝ) < 2 ^ n := pow_pos (by norm_num) n
  refine ⟨2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1,
    by nlinarith, fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hq : ContDiff ℝ ∞ fun w : ℂ => c₀ + L w := contDiff_const.add L.contDiff
  refine (norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (contDiff_inv_radC hg) hq z
    (mod_cast le_top)).trans ?_
  have hq0 : ‖c₀ + L z‖ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖) := by
    have h1 : ‖c₀ + L z‖ ≤ ‖c₀‖ + ‖L‖ * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact L.le_opNorm z
    have h2 : ‖z‖ ≤ ‖z - centerC g‖ + ‖centerC g‖ := by
      calc ‖z‖ = ‖z - centerC g + centerC g‖ := by
            rw [show z - centerC g + centerC g = z from by ring]
        _ ≤ ‖z - centerC g‖ + ‖centerC g‖ := norm_add_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg L)
    nlinarith [mul_nonneg (norm_nonneg c₀) (norm_nonneg (z - centerC g)),
      mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (centerC g)))
        (norm_nonneg (z - centerC g)),
      mul_nonneg (norm_nonneg L) (norm_nonneg (z - centerC g))]
  have hfd : (fderiv ℝ fun w : ℂ => c₀ + L w) = fun _ => L :=
    funext fun w => ((L.hasFDerivAt (x := w)).const_add c₀).fderiv
  have hq1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖ ≤ ‖L‖ := by
    have h1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ 0 (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := 0)).symm
    rw [h1, norm_iteratedFDeriv_zero, hfd]
  have hq2 : ∀ k : ℕ, ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖ = 0 := by
    intro k
    have h1 : ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
    rw [h1, hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
        ≤ (n.choose i : ℝ) * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge (n - i) 2 with h2 | h2
    · have hcase : n - i = 0 ∨ n - i = 1 := by omega
      rcases hcase with h0 | h1
      · have hieq : i = n := by omega
        rw [hieq, Nat.sub_self, norm_iteratedFDeriv_zero]
        calc ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ * ‖c₀ + L z‖
            ≤ (C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
              * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖)) :=
              mul_le_mul (hB0 z) hq0 (norm_nonneg _)
                (div_nonneg hC0.le (pow_nonneg hW0.le _))
          _ = (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_succ]
              field_simp
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 :=
              div_le_self hcqC0 (one_le_pow₀ hW1)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by linarith
      · have hieq : i = n - 1 := by omega
        have hn1 : 1 ≤ n := by omega
        rw [hieq, show n - (n - 1) = 1 from by omega]
        calc ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
              * ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
            ≤ (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) * ‖L‖ :=
              mul_le_mul (hB1 z) hq1 (norm_nonneg _)
                (div_nonneg hC1.le (pow_nonneg hW0.le _))
          _ ≤ C1 * ‖L‖ :=
              mul_le_mul_of_nonneg_right
                (div_le_self hC1.le (one_le_pow₀ hW1)) (norm_nonneg _)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by
              nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 2 := ⟨n - i - 2, by omega⟩
      rw [hk, hq2 k, mul_zero]
      nlinarith
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by linarith

-- pin: norm_iteratedDerivWithin_rpow_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1093)
theorem norm_iteratedDerivWithin_rpow_le {c : ℝ} (hc : 0 < c) (r : ℝ) (k : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun y : ℝ => y ^ r) (Set.Ioi c) v‖
      ≤ (∏ j ∈ Finset.range k, (|r| + j)) * v ^ (r - k) := by
  have hvpos : (0:ℝ) < v := hc.trans hv
  rw [iteratedDerivWithin_rpow_const hc r k hv, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hvpos.le _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hvpos.le _)
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => ?_)
  rw [sub_eq_add_neg]
  calc |r + -(j:ℝ)| = ‖r + -(j:ℝ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖r‖ + ‖-(j:ℝ)‖ := norm_add_le _ _
    _ = |r| + (j:ℝ) := by rw [Real.norm_eq_abs, norm_neg, Real.norm_eq_abs, Nat.abs_cast]

-- pin: exists_bound_iteratedFDeriv_rpow_neg_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1108)
theorem exists_bound_iteratedFDeriv_rpow_neg_radC (hg : g.det ≠ 0) (κ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => radC g w ^ (-κ)) z‖ ≤ C * radC g z ^ (-κ) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hm : (0:ℝ) < ‖g.det‖ / Real.sqrt (botNormSqC g) :=
    div_pos (norm_pos_iff.2 hg) (Real.sqrt_pos.2 hA)
  have htow : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ (k + 1) (radC g) z‖ ≤ C := by
    intro k
    obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_radC hg (k + 1)
    refine ⟨C, hC, fun z => (hB z).trans ?_⟩
    have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
    have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
    have h1 : (1:ℝ) ≤ (1 + ‖z - centerC g‖) ^ k := one_le_pow₀ hW1
    rw [pow_succ, div_le_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hW0.le)
    nlinarith [h2]
  choose CR hCR using htow
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hP : (0:ℝ) < (|(-κ)| + n + 1) ^ n := pow_pos (by positivity) n
  have hMx : (0:ℝ) < max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hDsum : (0:ℝ) ≤ ∑ k ∈ Finset.range n, CR k :=
    Finset.sum_nonneg fun k _ => (hCR k).1.le
  have hD1 : (1:ℝ) ≤ 1 + ∑ k ∈ Finset.range n, CR k := by linarith
  refine ⟨(n ! : ℝ) * (((|(-κ)| + n + 1) ^ n)
      * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n)
      * (1 + ∑ k ∈ Finset.range n, CR k) ^ n,
    mul_pos (mul_pos hfac (mul_pos hP (pow_pos hMx n))) (pow_pos (by linarith) n),
    fun z => ?_⟩
  have hrad := radC_pos hg z
  have hradm := norm_det_div_sqrt_le_radC hg z
  have hm2 : ‖g.det‖ / Real.sqrt (botNormSqC g) / 2 < radC g z := by nlinarith
  have hrange : Set.range (radC g)
      ⊆ Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) := by
    rintro y ⟨w, rfl⟩
    have h1 := norm_det_div_sqrt_le_radC hg w
    have h2 := radC_pos hg w
    exact Set.mem_Ioi.2 (by nlinarith)
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-κ))
      (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans (by linarith) (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-κ))
          (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) (radC g z)‖
        ≤ ((|(-κ)| + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n * radC g z ^ (-κ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    refine (norm_iteratedDerivWithin_rpow_le (by linarith) (-κ) i
      (Set.mem_Ioi.2 hm2)).trans ?_
    have hsplit : radC g z ^ (-κ - (i:ℝ)) = radC g z ^ (-κ) * (radC g z ^ ((i:ℝ)))⁻¹ := by
      rw [show -κ - (i:ℝ) = -κ + -(i:ℝ) from by ring, Real.rpow_add hrad,
        Real.rpow_neg hrad.le ((i:ℝ))]
    have hpowinv : (radC g z ^ ((i:ℝ)))⁻¹
        ≤ (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n := by
      rw [Real.rpow_natCast]
      have hmh : (0:ℝ) < (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i :=
        pow_pos (by linarith) i
      have h1 : (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i ≤ radC g z ^ i :=
        pow_le_pow_left₀ (by linarith) (by linarith) i
      have h2 := one_div_le_one_div_of_le hmh h1
      rw [one_div, one_div] at h2
      refine h2.trans ?_
      rw [← inv_pow, inv_div]
      have hb1 : (1:ℝ) ≤ max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) := le_max_left _ _
      have h3 : (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) ^ i
          ≤ (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ i :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) i
      exact h3.trans (pow_le_pow_right₀ hb1 hi)
    have hprod : (∏ j ∈ Finset.range i, (|(-κ)| + j))
        ≤ (|(-κ)| + n + 1) ^ n := by
      have hstep1 : (∏ j ∈ Finset.range i, (|(-κ)| + j))
          ≤ ∏ _j ∈ Finset.range i, (|(-κ)| + (n:ℝ) + 1) := by
        refine Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j hj => ?_)
        have hjn : (j:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hj) hi)
        linarith
      refine hstep1.trans ?_
      rw [Finset.prod_const, Finset.card_range]
      have hb1 : (1:ℝ) ≤ |(-κ)| + (n:ℝ) + 1 := by
        have h1 := abs_nonneg (-κ)
        have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      exact pow_le_pow_right₀ hb1 hi
    rw [hsplit]
    have hr0 : (0:ℝ) ≤ radC g z ^ (-κ) := Real.rpow_nonneg hrad.le _
    have hi0 : (0:ℝ) ≤ (radC g z ^ ((i:ℝ)))⁻¹ :=
      inv_nonneg.2 (Real.rpow_nonneg hrad.le _)
    calc (∏ j ∈ Finset.range i, (|(-κ)| + j)) * (radC g z ^ (-κ) * (radC g z ^ ((i:ℝ)))⁻¹)
        ≤ ((|(-κ)| + n + 1) ^ n)
          * (radC g z ^ (-κ)
            * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n) :=
          mul_le_mul hprod (mul_le_mul_of_nonneg_left hpowinv hr0)
            (mul_nonneg hr0 hi0) hP.le
      _ = ((|(-κ)| + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n * radC g z ^ (-κ) := by
          ring
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (radC g) z‖ ≤ (1 + ∑ k ∈ Finset.range n, CR k) ^ i := by
    intro i hi1 hin
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < n := by omega
    have h1 : CR k ≤ 1 + ∑ j ∈ Finset.range n, CR j := by
      have hle := Finset.single_le_sum (f := CR) (fun j _ => (hCR j).1.le)
        (Finset.mem_range.2 hk)
      linarith
    refine ((hCR k).2 z).trans (h1.trans ?_)
    exact le_self_pow₀ hD1 (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) hrange isOpen_Ioi.uniqueDiffOn hgOn
    (contDiff_radC hg) (mod_cast le_top) z hC hD
  have hfun : (fun w => radC g w ^ (-κ)) = (fun y : ℝ => y ^ (-κ)) ∘ radC g := rfl
  rw [hfun]
  refine hcomp.trans (le_of_eq ?_)
  ring

-- pin: exists_bound_iteratedFDeriv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1225)
theorem exists_bound_iteratedFDeriv_radC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (radC g) z‖ ≤ C := by
  intro n hn
  obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_radC hg n
  refine ⟨C, hC, fun z => (hB z).trans ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have h1 : 1 + ‖z - centerC g‖ ≤ (1 + ‖z - centerC g‖) ^ n := le_self_pow₀ hW1 (by omega)
  rw [div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h1 hC.le

-- pin: exists_bound_iteratedFDeriv_inv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1236)
theorem exists_bound_iteratedFDeriv_inv_radC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C := by
  intro n
  obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  refine ⟨C, hC, fun z => (hB z).trans ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  exact div_le_self hC.le (one_le_pow₀ hW1)

-- pin: exists_bound_iteratedFDeriv_kC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1245)
theorem exists_bound_iteratedFDeriv_kC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by
  intro n
  obtain ⟨C00, h00, hb00⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    ((starRingEnd ℂ) (g 0 1)) ((starRingEnd ℂ) (g 1 1) • conjCLM) n
  obtain ⟨C01, h01, hb01⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (-(starRingEnd ℂ) (g 0 0)) ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) n
  obtain ⟨C10, h10, hb10⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (g 0 0) (g 1 0 • ContinuousLinearMap.id ℝ ℂ) n
  obtain ⟨C11, h11, hb11⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (g 0 1) (g 1 1 • ContinuousLinearMap.id ℝ ℂ) n
  refine ⟨C00 + C01 + C10 + C11, by linarith, ?_⟩
  intro i j z
  fin_cases i <;> fin_cases j
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 0) z‖ ≤ _
    have heq : (fun w => kC g w 0 0)
        = fun w => (radC g w)⁻¹ • ((starRingEnd ℂ) (g 0 1) + ((starRingEnd ℂ) (g 1 1) • conjCLM) w) := by
      funext w
      show (starRingEnd ℂ) (botQ g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb00 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 1) z‖ ≤ _
    have heq : (fun w => kC g w 0 1)
        = fun w => (radC g w)⁻¹ • (-(starRingEnd ℂ) (g 0 0) + ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) w) := by
      funext w
      show -(starRingEnd ℂ) (botP g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb01 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 0) z‖ ≤ _
    have heq : (fun w => kC g w 1 0)
        = fun w => (radC g w)⁻¹ • (g 0 0 + (g 1 0 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botP g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb10 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 1) z‖ ≤ _
    have heq : (fun w => kC g w 1 1)
        = fun w => (radC g w)⁻¹ • (g 0 1 + (g 1 1 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botQ g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb11 z).trans (by linarith)

-- pin: exists_bound_iteratedFDeriv_borelC (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1301)
theorem exists_bound_iteratedFDeriv_borelC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => borelC g w i j) z‖ ≤ C := by
  intro n hn
  obtain ⟨Ca, hCa, hba⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg (-g.det) 0 n
  obtain ⟨Cb, hCb, hbb⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (g 1 0 * (starRingEnd ℂ) (g 0 0) + g 1 1 * (starRingEnd ℂ) (g 0 1))
    ((g 1 0 * (starRingEnd ℂ) (g 1 0) + g 1 1 * (starRingEnd ℂ) (g 1 1)) • conjCLM) n
  obtain ⟨Cr, hCr, hbr⟩ := exists_bound_iteratedFDeriv_radC hg n hn
  refine ⟨Ca + Cb + Cr, by linarith, ?_⟩
  intro i j z
  fin_cases i <;> fin_cases j
  · show ‖iteratedFDeriv ℝ n (fun w => borelC g w 0 0) z‖ ≤ _
    have heq : (fun w => borelC g w 0 0)
        = fun w => (radC g w)⁻¹ • (-g.det + (0 : ℂ →L[ℝ] ℂ) w) := by
      funext w
      show -g.det / ((radC g w : ℝ) : ℂ) = _
      simp only [zero_apply, add_zero, Complex.real_smul,
        Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hba z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => borelC g w 0 1) z‖ ≤ _
    have heq : (fun w => borelC g w 0 1)
        = fun w => (radC g w)⁻¹
            • ((g 1 0 * (starRingEnd ℂ) (g 0 0) + g 1 1 * (starRingEnd ℂ) (g 0 1))
              + ((g 1 0 * (starRingEnd ℂ) (g 1 0) + g 1 1 * (starRingEnd ℂ) (g 1 1))
                • conjCLM) w) := by
      funext w
      show (g 1 0 * (starRingEnd ℂ) (botP g w) + g 1 1 * (starRingEnd ℂ) (botQ g w))
          / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, botQ, map_add, map_mul, smul_apply,
        conjCLM_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hbb z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => borelC g w 1 0) z‖ ≤ _
    have heq : (fun w => borelC g w 1 0) = fun _ : ℂ => (0 : ℂ) := rfl
    rw [heq, iteratedFDeriv_const_of_ne (show n ≠ 0 by omega)]
    simp only [Pi.zero_apply, norm_zero]
    linarith
  · show ‖iteratedFDeriv ℝ n (fun w => borelC g w 1 1) z‖ ≤ _
    have heq : (fun w => borelC g w 1 1) = Complex.ofRealLI ∘ radC g := rfl
    rw [heq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (contDiff_radC hg).contDiffAt (mod_cast le_top)]
    exact (hbr z).trans (by linarith)

-- pin: exists_norm_borelC_le (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1348)
theorem exists_norm_borelC_le (hg : g.det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ), ‖borelC g z i j‖ ≤ C * (1 + ‖z‖) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) ≤ Complex.normSq g.det / botNormSqC g :=
    div_nonneg (Complex.normSq_nonneg _) hA.le
  have hsA : (0:ℝ) < Real.sqrt (botNormSqC g) := Real.sqrt_pos.2 hA
  have hp1 : (0:ℝ) ≤ ‖g 1 0‖ + ‖g 1 1‖ := by positivity
  have hz00 : (0:ℝ) ≤ 1 + ‖centerC g‖ := by linarith [norm_nonneg (centerC g)]
  have hp2 : (0:ℝ) ≤ Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
      * (1 + ‖centerC g‖) := mul_nonneg (Real.sqrt_nonneg _) hz00
  refine ⟨Real.sqrt (botNormSqC g) + (‖g 1 0‖ + ‖g 1 1‖)
      + Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g) * (1 + ‖centerC g‖),
    by linarith, ?_⟩
  intro i j z
  have hrad := radC_pos hg z
  have hradm := norm_det_div_sqrt_le_radC hg z
  have hz1 : (1:ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hPle : ‖botP g z‖ ≤ radC g z := by
    have h1 : Complex.normSq (botP g z) ≤ radC g z ^ 2 := by
      rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
      linarith [Complex.normSq_nonneg (botQ g z)]
    have h2 : ‖botP g z‖ ^ 2 ≤ radC g z ^ 2 := by
      rw [Complex.sq_norm]
      exact h1
    nlinarith [norm_nonneg (botP g z), hrad.le]
  have hQle : ‖botQ g z‖ ≤ radC g z := by
    have h1 : Complex.normSq (botQ g z) ≤ radC g z ^ 2 := by
      rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
      linarith [Complex.normSq_nonneg (botP g z)]
    have h2 : ‖botQ g z‖ ^ 2 ≤ radC g z ^ 2 := by
      rw [Complex.sq_norm]
      exact h1
    nlinarith [norm_nonneg (botQ g z), hrad.le]
  fin_cases i <;> fin_cases j
  · show ‖borelC g z 0 0‖ ≤ _
    have h1 : ‖borelC g z 0 0‖ = ‖g.det‖ / radC g z := by
      show ‖-g.det / ((radC g z : ℝ) : ℂ)‖ = _
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrad]
    have h2 : ‖g.det‖ / radC g z ≤ Real.sqrt (botNormSqC g) := by
      rw [div_le_iff₀ hrad]
      have h3 := mul_le_mul_of_nonneg_left hradm hsA.le
      have h4 : Real.sqrt (botNormSqC g) * (‖g.det‖ / Real.sqrt (botNormSqC g)) = ‖g.det‖ := by
        field_simp
      rw [h4] at h3
      linarith
    rw [h1]
    calc ‖g.det‖ / radC g z ≤ Real.sqrt (botNormSqC g) := h2
      _ = Real.sqrt (botNormSqC g) * 1 := (mul_one _).symm
      _ ≤ (Real.sqrt (botNormSqC g) + (‖g 1 0‖ + ‖g 1 1‖)
            + Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
              * (1 + ‖centerC g‖)) * (1 + ‖z‖) :=
          mul_le_mul (by linarith) hz1 one_pos.le (by linarith)
  · show ‖borelC g z 0 1‖ ≤ _
    have hnum : ‖g 1 0 * (starRingEnd ℂ) (botP g z) + g 1 1 * (starRingEnd ℂ) (botQ g z)‖
        ≤ (‖g 1 0‖ + ‖g 1 1‖) * radC g z := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
      nlinarith [mul_le_mul_of_nonneg_left hPle (norm_nonneg (g 1 0)),
        mul_le_mul_of_nonneg_left hQle (norm_nonneg (g 1 1))]
    have h1 : ‖borelC g z 0 1‖ ≤ ‖g 1 0‖ + ‖g 1 1‖ := by
      have hx : ‖borelC g z 0 1‖
          = ‖g 1 0 * (starRingEnd ℂ) (botP g z) + g 1 1 * (starRingEnd ℂ) (botQ g z)‖
            / radC g z := by
        show ‖(g 1 0 * (starRingEnd ℂ) (botP g z) + g 1 1 * (starRingEnd ℂ) (botQ g z))
            / ((radC g z : ℝ) : ℂ)‖ = _
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrad]
      rw [hx, div_le_iff₀ hrad]
      exact hnum
    calc ‖borelC g z 0 1‖ ≤ ‖g 1 0‖ + ‖g 1 1‖ := h1
      _ = (‖g 1 0‖ + ‖g 1 1‖) * 1 := (mul_one _).symm
      _ ≤ (Real.sqrt (botNormSqC g) + (‖g 1 0‖ + ‖g 1 1‖)
            + Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
              * (1 + ‖centerC g‖)) * (1 + ‖z‖) :=
          mul_le_mul (by linarith) hz1 one_pos.le (by linarith)
  · show ‖borelC g z 1 0‖ ≤ _
    have h1 : ‖borelC g z 1 0‖ = 0 := by
      show ‖(0 : ℂ)‖ = _
      rw [norm_zero]
    rw [h1]
    exact mul_nonneg (by linarith) (by linarith)
  · show ‖borelC g z 1 1‖ ≤ _
    have h1 : ‖borelC g z 1 1‖ = radC g z := by
      show ‖((radC g z : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrad]
    have h3 : radC g z = Real.sqrt (uQuad g z) := by
      rw [uQuad_eq_radC_sq hg z, Real.sqrt_sq hrad.le]
    have h2 : radC g z ≤ Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
        * (1 + ‖z - centerC g‖) := by
      rw [h3]
      refine (Real.sqrt_le_sqrt (uQuad_le hg z)).trans (le_of_eq ?_)
      rw [show (botNormSqC g + Complex.normSq g.det / botNormSqC g)
            * (1 + ‖z - centerC g‖) ^ 2
          = (Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
            * (1 + ‖z - centerC g‖)) ^ 2 from by
        rw [mul_pow, Real.sq_sqrt (by linarith)]]
      rw [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _)
        (by linarith [norm_nonneg (z - centerC g)]))]
    have h6 : 1 + ‖z - centerC g‖ ≤ (1 + ‖centerC g‖) * (1 + ‖z‖) := by
      have h7 : ‖z - centerC g‖ ≤ ‖z‖ + ‖centerC g‖ := norm_sub_le _ _
      nlinarith [norm_nonneg z, norm_nonneg (centerC g),
        mul_nonneg (norm_nonneg (centerC g)) (norm_nonneg z)]
    rw [h1]
    calc radC g z
        ≤ Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
          * (1 + ‖z - centerC g‖) := h2
      _ ≤ Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
          * ((1 + ‖centerC g‖) * (1 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg _)
      _ = Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
          * (1 + ‖centerC g‖) * (1 + ‖z‖) := by ring
      _ ≤ (Real.sqrt (botNormSqC g) + (‖g 1 0‖ + ‖g 1 1‖)
            + Real.sqrt (botNormSqC g + Complex.normSq g.det / botNormSqC g)
              * (1 + ‖centerC g‖)) * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)

-- pin: exists_bound_iteratedFDeriv_mul (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1463)
theorem exists_bound_iteratedFDeriv_mul {f h : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hbf : ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ), ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (hbh : ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ), ‖iteratedFDeriv ℝ n h z‖ ≤ C) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => f w * h w) z‖ ≤ C := by
  intro n
  choose Cf hCf using hbf
  choose Ch hCh using hbh
  have hpos : (0:ℝ) < ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Ch (n - i) := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    have h1 : (0:ℝ) < (n.choose i : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    exact mul_pos (mul_pos h1 (hCf i).1) (hCh (n - i)).1
  refine ⟨_, hpos, fun z => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf hh z (mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (n - i) h z‖
      ≤ (n.choose i : ℝ) * Cf i * ‖iteratedFDeriv ℝ (n - i) h z‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((hCf i).2 z) (Nat.cast_nonneg _)) (norm_nonneg _)
    _ ≤ (n.choose i : ℝ) * Cf i * Ch (n - i) :=
        mul_le_mul_of_nonneg_left ((hCh (n - i)).2 z)
          (mul_nonneg (Nat.cast_nonneg _) (hCf i).1.le)

-- pin: exists_bound_iteratedFDeriv_add (S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean:1488)
theorem exists_bound_iteratedFDeriv_add {f h : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hbf : ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ), ‖iteratedFDeriv ℝ n f z‖ ≤ C)
    (hbh : ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ), ‖iteratedFDeriv ℝ n h z‖ ≤ C) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => f w + h w) z‖ ≤ C := by
  intro n
  obtain ⟨Cf, hCf, hbf'⟩ := hbf n
  obtain ⟨Ch, hCh, hbh'⟩ := hbh n
  refine ⟨Cf + Ch, by linarith, fun z => ?_⟩
  have heq : (fun w => f w + h w) = f + h := rfl
  rw [heq, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (mod_cast le_top))
    (hh.contDiffAt.of_le (mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hbf' z) (hbh' z))

end CplxSmooth

namespace KCUnif

open CplxIwasawa CplxSmooth
open scoped ContDiff Nat ComplexConjugate

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: decay_explicit (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1317)
theorem decay_explicit (hg : g.det ≠ 0) (n : ℕ) (z : ℂ) :
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖
        ≤ ((n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹) / (1 + ‖z - centerC g‖) ^ (n + 1) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hK : (0:ℝ) < floorK g := floorK_pos hg
  have hM0 : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hupos : ∀ w : ℂ, (0:ℝ) < uQuad g w := fun w => lt_of_lt_of_le hM0 (uQuad_ge hg w)
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc2 : (0:ℝ) < 4 * botNormSqC g / floorK g + 1 := by
    have h0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
    linarith
  have hsK : (0:ℝ) < (Real.sqrt (floorK g))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hK)
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hcz : (0:ℝ) < floorK g * (1 + ‖z - centerC g‖) ^ 2 := mul_pos hK (pow_pos hW0 2)
  have hball : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
  have hmaps : Set.MapsTo (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
      (Metric.ball z 1) (Set.Ioi (1:ℝ)) := fun v hv =>
    Set.mem_Ioi.2 ((one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hv))
  have hrw : (fun w => (radC g w)⁻¹)
      = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
          • ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
             fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) w := by
    funext w
    have hu := hupos w
    have h1 : radC g w = Real.sqrt (uQuad g w) := by
      rw [uQuad_eq_radC_sq hg w, Real.sqrt_sq (radC_pos hg w).le]
    have hL : (Real.sqrt (uQuad g w))⁻¹ = uQuad g w ^ (-(1:ℝ)/2) :=
      (rpow_neg_half_eq_inv_sqrt hu.le).symm
    have hne : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2) ≠ 0 :=
      (Real.rpow_pos_of_pos hcz _).ne'
    have hR : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * (uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) ^ (-(1:ℝ)/2)
        = uQuad g w ^ (-(1:ℝ)/2) := by
      rw [show uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)
          = uQuad g w * (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ from div_eq_mul_inv _ _,
        Real.mul_rpow hu.le (inv_nonneg.2 hcz.le), Real.inv_rpow hcz.le,
        mul_comm (uQuad g w ^ (-(1:ℝ)/2)), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h1, hL, smul_eq_mul, Function.comp_apply, hR]
  rw [hrw]
  have hũ : ContDiff ℝ ∞ fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (contDiff_uQuad g).div_const _
  have hũz : (1:ℝ) < uQuad g z / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hball)
  have hcomp_cd : ContDiffAt ℝ ∞ ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
      fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z :=
    (Real.contDiffAt_rpow_const_of_ne (by linarith : uQuad g z
      / (floorK g * (1 + ‖z - centerC g‖) ^ 2) ≠ 0)).comp z hũ.contDiffAt
  rw [iteratedFDeriv_const_smul_apply' (hcomp_cd.of_le (mod_cast le_top))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hcz _)]
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ))
        ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖ ≤ (n ! : ℝ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    calc ‖iteratedDerivWithin i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi 1)
          ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖
        ≤ i ! * (1:ℝ) ^ (-(1 : ℝ) / 2 - i) :=
          norm_iteratedDerivWithin_rpow_neg_half_le one_pos i (hmaps hball)
      _ = (i ! : ℝ) := by rw [Real.one_rpow, mul_one]
      _ ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i
          (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
        ≤ ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen i Metric.isOpen_ball hball]
    have hsm : (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
        = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ • uQuad g w := by
      funext w
      rw [smul_eq_mul, div_eq_inv_mul]
    rw [hsm, iteratedFDeriv_const_smul_apply'
      ((contDiff_uQuad g).contDiffAt.of_le (mod_cast le_top))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcz)]
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hb := norm_iteratedFDeriv_uQuad_one_le g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
            * (4 * botNormSqC g * (1 + ‖z - centerC g‖))
            = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := by
          field_simp
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
              * (4 * botNormSqC g * (1 + ‖z - centerC g‖)) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) * (1 + ‖z - centerC g‖)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hW0.le)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 1 := by
              rw [pow_one, ← div_eq_mul_inv]
      · have hb := norm_iteratedFDeriv_uQuad_two g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g)
            = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := by
          field_simp
        have hX0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
        have hX1 : 4 * botNormSqC g / floorK g ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 := by
          nlinarith
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 :=
              mul_le_mul_of_nonneg_right hX1 (sq_nonneg _)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 2 := by
              rw [div_pow, inv_pow, ← div_eq_mul_inv]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, mul_zero]
      exact pow_nonneg (div_nonneg hc2.le hW0.le) i
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hgOn hũ.contDiffOn
    (mod_cast le_top) isOpen_Ioi.uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn
    hmaps hball hC hD
  rw [← iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hball]
  have hczhalf : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
      = (Real.sqrt (floorK g))⁻¹ * (1 + ‖z - centerC g‖)⁻¹ := by
    have h1 : floorK g * (1 + ‖z - centerC g‖) ^ 2
        = (Real.sqrt (floorK g) * (1 + ‖z - centerC g‖)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
    have hb0 : (0:ℝ) ≤ Real.sqrt (floorK g) * (1 + ‖z - centerC g‖) :=
      mul_nonneg (Real.sqrt_nonneg _) hW0.le
    rw [h1, rpow_neg_half_eq_inv_sqrt (sq_nonneg _), Real.sqrt_sq hb0, mul_inv]
  calc (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ‖iteratedFDerivWithin ℝ n ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
            fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
      ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ((n ! : ℝ) * n !
          * ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hcz _).le
    _ = (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹
        / (1 + ‖z - centerC g‖) ^ (n + 1) := by
        rw [hczhalf, div_pow, pow_succ]
        have hsne : Real.sqrt (floorK g) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
        field_simp

-- pin: affine_of_bounds (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1453)
theorem affine_of_bounds (hg : g.det ≠ 0)
    (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ) (n : ℕ) {C0 C1 : ℝ} (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hB0 : ∀ z : ℂ, ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
    (hB1 : ∀ z : ℂ, ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖ ≤ C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1))
    (z : ℂ) :
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹ • (c₀ + L w)) z‖ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by
  have hcq0 : (0:ℝ) ≤ ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ := by positivity
  have hLC1 : (0:ℝ) ≤ ‖L‖ * C1 := mul_nonneg (norm_nonneg _) hC1.le
  have hcqC0 : (0:ℝ) ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 := mul_nonneg hcq0 hC0.le
  have h2n : (0:ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hq : ContDiff ℝ ∞ fun w : ℂ => c₀ + L w := contDiff_const.add L.contDiff
  refine (norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (contDiff_inv_radC hg) hq z
    (mod_cast le_top)).trans ?_
  have hq0 : ‖c₀ + L z‖ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖) := by
    have h1 : ‖c₀ + L z‖ ≤ ‖c₀‖ + ‖L‖ * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact L.le_opNorm z
    have h2 : ‖z‖ ≤ ‖z - centerC g‖ + ‖centerC g‖ := by
      calc ‖z‖ = ‖z - centerC g + centerC g‖ := by
            rw [show z - centerC g + centerC g = z from by ring]
        _ ≤ ‖z - centerC g‖ + ‖centerC g‖ := norm_add_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg L)
    nlinarith [mul_nonneg (norm_nonneg c₀) (norm_nonneg (z - centerC g)),
      mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (centerC g)))
        (norm_nonneg (z - centerC g)),
      mul_nonneg (norm_nonneg L) (norm_nonneg (z - centerC g))]
  have hfd : (fderiv ℝ fun w : ℂ => c₀ + L w) = fun _ => L :=
    funext fun w => ((L.hasFDerivAt (x := w)).const_add c₀).fderiv
  have hq1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖ ≤ ‖L‖ := by
    have h1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ 0 (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := 0)).symm
    rw [h1, norm_iteratedFDeriv_zero, hfd]
  have hq2 : ∀ k : ℕ, ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖ = 0 := by
    intro k
    have h1 : ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
    rw [h1, hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
        ≤ (n.choose i : ℝ) * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge (n - i) 2 with h2 | h2
    · have hcase : n - i = 0 ∨ n - i = 1 := by omega
      rcases hcase with h0 | h1
      · have hieq : i = n := by omega
        rw [hieq, Nat.sub_self, norm_iteratedFDeriv_zero]
        calc ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ * ‖c₀ + L z‖
            ≤ (C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
              * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖)) :=
              mul_le_mul (hB0 z) hq0 (norm_nonneg _)
                (div_nonneg hC0.le (pow_nonneg hW0.le _))
          _ = (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_succ]
              field_simp
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 :=
              div_le_self hcqC0 (one_le_pow₀ hW1)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by linarith
      · have hieq : i = n - 1 := by omega
        have hn1 : 1 ≤ n := by omega
        rw [hieq, show n - (n - 1) = 1 from by omega]
        calc ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
              * ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
            ≤ (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) * ‖L‖ :=
              mul_le_mul (hB1 z) hq1 (norm_nonneg _)
                (div_nonneg hC1.le (pow_nonneg hW0.le _))
          _ ≤ C1 * ‖L‖ :=
              mul_le_mul_of_nonneg_right
                (div_le_self hC1.le (one_le_pow₀ hW1)) (norm_nonneg _)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by
              nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 2 := ⟨n - i - 2, by omega⟩
      rw [hk, hq2 k, mul_zero]
      nlinarith
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by linarith

end KCUnif

namespace KCUnif

open CplxIwasawa CplxSmooth
open scoped ContDiff Nat ComplexConjugate

-- pin: continuous_botNormSqC (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1561)
theorem continuous_botNormSqC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => botNormSqC g := by
  unfold botNormSqC
  exact (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 0)).add
    (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 1))

-- pin: continuous_detC (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1566)
theorem continuous_detC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det := by
  have : (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) = fun g => g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
    funext fun g => Matrix.det_fin_two g
  rw [this]; fun_prop

-- pin: continuous_centerC_num (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1571)
theorem continuous_centerC_num : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) := by
  fun_prop

-- pin: Kdec (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1574)
def Kdec (g : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) : ℝ :=
  (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹

-- pin: KdecU (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1577)
def KdecU (A₁ f₀ : ℝ) (n : ℕ) : ℝ := (n ! : ℝ) * n ! * (4 * A₁ / f₀ + 1) ^ n * (Real.sqrt f₀)⁻¹

-- pin: KdecU_pos (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1579)
theorem KdecU_pos {A₁ f₀ : ℝ} (hA : 0 ≤ A₁) (hf : 0 < f₀) (n : ℕ) : 0 < KdecU A₁ f₀ n := by
  unfold KdecU
  have h1 : (0 : ℝ) < n ! := by positivity
  have h2 : 0 < 4 * A₁ / f₀ + 1 := by positivity
  exact mul_pos (mul_pos (mul_pos h1 h1) (pow_pos h2 n)) (inv_pos.2 (Real.sqrt_pos.2 hf))

-- pin: Kdec_le_KdecU (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1585)
theorem Kdec_le_KdecU {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {A₁ f₀ : ℝ} (hf : 0 < f₀)
    (hA : botNormSqC g ≤ A₁) (hfl : f₀ ≤ floorK g) (n : ℕ) : Kdec g n ≤ KdecU A₁ f₀ n := by
  unfold Kdec KdecU
  have hA0 : 0 < botNormSqC g := botNormSqC_pos hg
  have hK : 0 < floorK g := floorK_pos hg
  have h1 : 4 * botNormSqC g / floorK g + 1 ≤ 4 * A₁ / f₀ + 1 := by
    have : botNormSqC g / floorK g ≤ A₁ / f₀ := div_le_div₀ (hA0.le.trans hA) hA hf hfl
    have e1 : 4 * botNormSqC g / floorK g = 4 * (botNormSqC g / floorK g) := by ring
    have e2 : 4 * A₁ / f₀ = 4 * (A₁ / f₀) := by ring
    linarith
  have h2 : (Real.sqrt (floorK g))⁻¹ ≤ (Real.sqrt f₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hf) (Real.sqrt_le_sqrt hfl)
  have h0 : (0 : ℝ) ≤ n ! * n ! := by positivity
  have h3 : (0 : ℝ) ≤ 4 * A₁ / f₀ + 1 := by
    have : 0 ≤ A₁ := hA0.le.trans hA
    positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 n) h0) h2
    (inv_nonneg.2 (Real.sqrt_nonneg _)) (mul_nonneg h0 (pow_nonneg h3 n))

-- pin: exists_uniform_constants (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1604)
theorem exists_uniform_constants (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) :
    ∃ A₁ f₀ Zc E : ℝ, 0 ≤ A₁ ∧ 0 < f₀ ∧ 0 ≤ Zc ∧ 0 ≤ E ∧ ∀ g ∈ 𝒢,
      botNormSqC g ≤ A₁ ∧ f₀ ≤ floorK g ∧ ‖centerC g‖ ≤ Zc ∧ ∀ i j : Fin 2, ‖g i j‖ ≤ E := by
  obtain ⟨A₁, hA₁⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSqC g) continuous_botNormSqC.continuousOn
  obtain ⟨cA, hcA⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (botNormSqC g)⁻¹)
    ((continuous_botNormSqC.continuousOn).inv₀ fun g hg => (botNormSqC_pos (hdet g hg)).ne')
  obtain ⟨cD, hcD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => ‖g.det‖⁻¹)
    (continuous_detC.continuousOn.norm.inv₀ fun g hg => (norm_pos_iff.2 (hdet g hg)).ne')
  obtain ⟨Zc, hZc⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => centerC g)
    (continuous_centerC_num.continuousOn.div (Complex.continuous_ofReal.comp continuous_botNormSqC).continuousOn
      fun g hg => Complex.ofReal_ne_zero.2 (botNormSqC_pos (hdet g hg)).ne')
  have hE : ∀ i j : Fin 2, ∃ Eij : ℝ, ∀ g ∈ 𝒢, ‖g i j‖ ≤ Eij := fun i j =>
    h𝒢.exists_bound_of_continuousOn (f := fun g => g i j) (continuous_id.matrix_elem i j).continuousOn
  choose Ef hEf using hE
  set A := max 1 A₁ with hAdef
  set a := max 1 cA with hadef
  set d := max 1 cD with hddef
  set E := max 0 (max (max (Ef 0 0) (Ef 0 1)) (max (Ef 1 0) (Ef 1 1))) with hEdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have ha1 : 1 ≤ a := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_left _ _
  refine ⟨A, min a⁻¹ ((d ^ 2)⁻¹ * A⁻¹) / 18, max 0 Zc, E, by positivity, by positivity, le_max_left _ _, le_max_left _ _,
    fun g hg => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := hA₁ g hg
    rw [Real.norm_of_nonneg (botNormSqC_pos (hdet g hg)).le] at this
    exact this.trans (le_max_right _ _)
  · have hApos := botNormSqC_pos (hdet g hg)
    have hdet0 : 0 < ‖g.det‖ := norm_pos_iff.2 (hdet g hg)
    have h1 : (botNormSqC g)⁻¹ ≤ a := by
      have := hcA g hg; rw [norm_inv, Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)
    have h2 : ‖g.det‖⁻¹ ≤ d := by
      have := hcD g hg; rw [norm_inv, norm_norm] at this
      exact this.trans (le_max_right _ _)
    have hAup : botNormSqC g ≤ A := by
      have := hA₁ g hg; rw [Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)

    have hb1 : a⁻¹ ≤ botNormSqC g := by
      rw [inv_le_comm₀ (by positivity) hApos]; exact h1
    have hb2 : (d ^ 2)⁻¹ * A⁻¹ ≤ Complex.normSq g.det / botNormSqC g := by
      rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
      refine mul_le_mul ?_ ((inv_le_inv₀ (by positivity) hApos).mpr hAup) (by positivity) (sq_nonneg _)
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hdet0).mpr h2) 2
    unfold floorK
    exact div_le_div_of_nonneg_right (le_min ((min_le_left _ _).trans hb1) ((min_le_right _ _).trans hb2)) (by norm_num)
  · exact (hZc g hg).trans (le_max_right _ _)
  · intro i j
    refine (hEf i j g hg).trans ?_
    fin_cases i <;> fin_cases j <;> simp [hEdef]

-- pin: main (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1656)
theorem main (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by
  obtain ⟨A₁, f₀, Zc, E, hA₁, hf₀, hZc, hE, hG⟩ := exists_uniform_constants 𝒢 h𝒢 hdet
  set C0 := KdecU A₁ f₀ n with hC0def
  set C1 := KdecU A₁ f₀ (n - 1) with hC1def
  have hC0 : 0 < C0 := KdecU_pos hA₁ hf₀ n
  have hC1 : 0 < C1 := KdecU_pos hA₁ hf₀ (n - 1)
  set U : ℝ := 2 ^ n * ((E + E * Zc + E) * C0 + E * C1) + 1 with hU
  refine ⟨U, by positivity, fun g hg i j z => ?_⟩
  obtain ⟨hA, hfl, hZ, hEg⟩ := hG g hg
  have hgd := hdet g hg

  have hW : ∀ z : ℂ, 0 < 1 + ‖z - centerC g‖ := fun z => by positivity
  have hB0 : ∀ z : ℂ, ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C0 / (1 + ‖z - centerC g‖) ^ (n + 1) := fun z =>
    (decay_explicit hgd n z).trans (div_le_div_of_nonneg_right (Kdec_le_KdecU hgd hf₀ hA hfl n) (by positivity))
  have hB1 : ∀ z : ℂ, ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖ ≤ C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1) :=
    fun z => (decay_explicit hgd (n - 1) z).trans
      (div_le_div_of_nonneg_right (Kdec_le_KdecU hgd hf₀ hA hfl (n - 1)) (by positivity))

  have hunif : ∀ (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ), ‖c₀‖ ≤ E → ‖L‖ ≤ E →
      2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 ≤ U := by
    intro c₀ L hc hL
    have h1 : ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ ≤ E + E * Zc + E := by
      have := mul_le_mul hL hZ (norm_nonneg _) hE
      linarith
    have h2 : (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 ≤ (E + E * Zc + E) * C0 + E * C1 :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hC0.le) (mul_le_mul_of_nonneg_right hL hC1.le)
    have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
    simp only [hU]; linarith
  have hconj : ∀ x : ℂ, ‖(starRingEnd ℂ) x‖ = ‖x‖ := fun x => Complex.norm_conj x
  have hconjCLM : ‖(conjCLM : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [conjCLM_apply, one_mul]; exact (hconj w).le
  have hidCLM : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hLconj : ∀ x : ℂ, ‖x • (conjCLM : ℂ →L[ℝ] ℂ)‖ ≤ ‖x‖ := fun x =>
    (norm_smul_le x (conjCLM : ℂ →L[ℝ] ℂ)).trans (by nlinarith [norm_nonneg x, norm_nonneg (conjCLM : ℂ →L[ℝ] ℂ)])
  have hLid : ∀ x : ℂ, ‖x • ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖x‖ := fun x =>
    (norm_smul_le x (ContinuousLinearMap.id ℝ ℂ)).trans
      (by nlinarith [norm_nonneg x, norm_nonneg (ContinuousLinearMap.id ℝ ℂ)])
  fin_cases i <;> fin_cases j
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 0) z‖ ≤ _
    have heq : (fun w => kC g w 0 0)
        = fun w => (radC g w)⁻¹ • ((starRingEnd ℂ) (g 0 1) + ((starRingEnd ℂ) (g 1 1) • conjCLM) w) := by
      funext w
      show (starRingEnd ℂ) (botQ g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ ?_ ?_)
    · rw [hconj]; exact hEg 0 1
    · exact (hLconj _).trans (by rw [hconj]; exact hEg 1 1)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 1) z‖ ≤ _
    have heq : (fun w => kC g w 0 1)
        = fun w => (radC g w)⁻¹ • (-(starRingEnd ℂ) (g 0 0) + ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) w) := by
      funext w
      show -(starRingEnd ℂ) (botP g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ ?_ ?_)
    · rw [norm_neg, hconj]; exact hEg 0 0
    · exact (hLconj _).trans (by rw [norm_neg, hconj]; exact hEg 1 0)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 0) z‖ ≤ _
    have heq : (fun w => kC g w 1 0)
        = fun w => (radC g w)⁻¹ • (g 0 0 + (g 1 0 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botP g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ (hEg 0 0) ((hLid _).trans (hEg 1 0)))
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 1) z‖ ≤ _
    have heq : (fun w => kC g w 1 1)
        = fun w => (radC g w)⁻¹ • (g 0 1 + (g 1 1 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botQ g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ (hEg 0 1) ((hLid _).trans (hEg 1 1)))

end KCUnif

namespace RhoTwoAux

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: radC_sq_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:19)
private theorem radC_sq_aux (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

-- pin: radC_pos_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:23)
private theorem radC_pos_aux (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

-- pin: key_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:45)
private theorem key_aux (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  norm_cast
  rw [← pow_two]
  linarith [radC_sq_aux g z]

-- pin: weylUnip_eq_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:53)
private theorem weylUnip_eq_aux (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![g 1 0, g 1 1; g 0 0 + z * g 1 0, g 0 1 + z * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

-- pin: conjTranspose_mul_kC_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:59)
private theorem conjTranspose_mul_kC_aux (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos_aux hg z).ne'
  have key := key_aux g z
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

-- pin: det_kC_aux (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:73)
private theorem det_kC_aux (hg : g.det ≠ 0) (z : ℂ) : (kC g z).det = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos_aux hg z).ne'
  have e : (kC g z).det = (botQ g z * (starRingEnd ℂ) (botQ g z)
      + botP g z * (starRingEnd ℂ) (botP g z)) / ((radC g z : ℂ) * (radC g z : ℂ)) := by
    rw [kC, Matrix.det_fin_two_of]
    ring
  have num : ((Complex.normSq (botQ g z) + Complex.normSq (botP g z) : ℝ) : ℂ)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq_aux g z]
  rw [e, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, num,
    div_self (mul_ne_zero hr hr)]

end RhoTwoAux

namespace Engine

-- pin: contDiff_and_exists_bound_iteratedFDeriv_kC_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean:1313)
theorem contDiff_and_exists_bound_iteratedFDeriv_kC_apply
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => kC g w i j)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
        ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  ⟨fun i j => CplxIwasawa.contDiff_kC_apply hg i j,
    CplxSmooth.exists_bound_iteratedFDeriv_kC hg⟩

-- pin: exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact (S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean:1750)
theorem exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  KCUnif.main 𝒢 h𝒢 hdet n

open RhoTwoAux in
-- pin: kC_mem_specialUnitaryGroup (S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean:93)
theorem kC_mem_specialUnitaryGroup
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  exact ⟨by rw [Matrix.star_eq_conjTranspose]; exact conjTranspose_mul_kC_aux hg z, det_kC_aux hg z⟩

open RhoTwoAux in
-- pin: weyl_mul_unipotent_mul_eq_borel_mul_kC (S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean:93)
theorem weyl_mul_unipotent_mul_eq_borel_mul_kC
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![-g.det / (radC g z : ℂ),
            (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
           0, (radC g z : ℂ)] * kC g z := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos_aux hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := key_aux g z
  simp only [botP, botQ, map_add, map_mul] at key
  rw [weylUnip_eq_aux, kC, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, botP, botQ, map_add, map_mul] <;>
    (try field_simp) <;>
    (rw [pow_two ((radC g z : ℂ)), ← key]
     ring)

end Engine


end AutomorphicForm.ComplexIwasawa

end
