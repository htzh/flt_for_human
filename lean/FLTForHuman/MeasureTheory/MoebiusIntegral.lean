/-
  The Möbius change of variables, at the real and at the complex place.

  For `a b c d` with `a * d - b * c ≠ 0`, the fractional linear transformation
  `u ↦ (b + u * d) / (a + u * c)` is a measure-preserving reparametrisation of `ℝ`
  (resp. `ℂ`) once the Jacobian factor is put in:

  * `integral_abs_det_div_sq_mul_comp_moebius_real` —
    `∫ x, (|a * d - b * c| / (a + x * c) ^ 2) * G ((b + x * d) / (a + x * c)) = ∫ u, G u`;
  * `integral_normSq_det_div_mul_comp_moebius_complex` — the same identity at the complex
    place, where the Jacobian of `u ↦ (b + u * d) / (a + u * c)` as an `ℝ`-linear map is
    multiplication by `(a * d - b * c) / (a + z * c) ^ 2` with determinant
    `‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4`.

  The engine is the area formula in one dimension (`integral_image_eq_integral_abs_deriv_smul`)
  and in finite dimension (`integral_image_eq_integral_abs_det_fderiv_smul`), applied on the
  set where the denominator does not vanish; that set is conull because a nonconstant affine
  function `z ↦ p + z * q` vanishes on a null set.

  Transcribed from the D–S shelf's `MeasureTheory` leaves (pinned `aa2d8b34`), rows 8 and 9 of
  the order, from
  `S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.lean` and
  `S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.lean`. Generic measure
  theory on `ℝ` and `ℂ`, so its home is `MeasureTheory/` (playbook §3.1); the pin's
  generation namespaces are dropped and the statements stay the pin's.

  spec-pin: P2M/Sol/S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.lean
  spec-pin: P2M/Sol/S_MeasureTheory_integral_normSq_det_div_mul_comp_moebius_complex.lean
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace MeasureTheory

namespace MoebiusComplex

/-- A nonconstant affine map `z ↦ p + z * q` on `ℂ` vanishes on a null set. -/
theorem volume_affine_zero (p q : ℂ) (h : p ≠ 0 ∨ q ≠ 0) : volume {z : ℂ | p + z * q = 0} = 0 := by
  rcases eq_or_ne q 0 with hq | hq
  · have hp : p ≠ 0 := h.resolve_right (not_not.mpr hq)
    exact measure_mono_null (fun z hz => (hp (by simpa [hq] using hz)).elim) measure_empty
  · refine measure_mono_null (fun z hz => ?_) (measure_singleton (-p / q))
    simp only [Set.mem_ofPred_eq] at hz
    rw [Set.mem_singleton_iff, eq_div_iff hq]
    linear_combination hz

/-- Multiplication by `l` on `ℂ`, seen as an `ℝ`-linear endomorphism. -/
def D (l : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.toSpanSingleton ℂ l).restrictScalars ℝ

theorem det_D (l : ℂ) : (D l).det = ‖l‖ ^ 2 := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

/-- The Möbius change of variables at the complex place; the row below is its `_hdet` form. -/
theorem main (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by
  set s : Set ℂ := {z | a + z * c ≠ 0} with hs_def
  set t : Set ℂ := {u | d - u * c ≠ 0} with ht_def
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hdet; rw [h.1, h.2]; ring
  have hdc : d ≠ 0 ∨ -c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not, neg_eq_zero] at h
    apply hdet; rw [h.1, h.2]; ring
  have hs : MeasurableSet s := (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (fun y : ℂ => (b + y * d) / (a + y * c))
      (D ((a * d - b * c) / (a + z * c) ^ 2)) s z := by
    intro z hz
    have h1 : HasDerivAt (fun y : ℂ => b + y * d) d z := by
      simpa using ((hasDerivAt_id z).mul_const d).const_add b
    have h2 : HasDerivAt (fun y : ℂ => a + y * c) c z := by
      simpa using ((hasDerivAt_id z).mul_const c).const_add a
    have h3 := h1.div h2 hz
    have h4 : HasDerivAt (fun y : ℂ => (b + y * d) / (a + y * c)) ((a * d - b * c) / (a + z * c) ^ 2) z := by
      refine h3.congr_deriv ?_
      congr 1; ring
    have h5 := h4.hasFDerivAt.restrictScalars ℝ
    exact h5.hasFDerivWithinAt
  have hinj : Set.InjOn (fun y : ℂ => (b + y * d) / (a + y * c)) s := by
    intro x hx y hy hxy
    dsimp only at hxy
    rw [div_eq_div_iff hx hy] at hxy
    have h0 : (x - y) * (a * d - b * c) = 0 := by linear_combination hxy
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hdet
  have himage : (fun y : ℂ => (b + y * d) / (a + y * c)) '' s = t := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change d - (b + x * d) / (a + x * c) * c ≠ 0
      have hx' : a + x * c ≠ 0 := hx
      rw [show d - (b + x * d) / (a + x * c) * c = (a * d - b * c) / (a + x * c) by field_simp; ring]
      exact div_ne_zero hdet hx'
    · intro hu
      change d - u * c ≠ 0 at hu
      have hden : a + (u * a - b) / (d - u * c) * c ≠ 0 := by
        rw [show a + (u * a - b) / (d - u * c) * c = (a * d - b * c) / (d - u * c) by field_simp; ring]
        exact div_ne_zero hdet hu
      refine ⟨(u * a - b) / (d - u * c), hden, ?_⟩
      change (b + (u * a - b) / (d - u * c) * d) / (a + (u * a - b) / (d - u * c) * c) = u
      rw [div_eq_iff hden]
      field_simp
      ring
  have key := integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv hinj G
  rw [himage] at key
  have hs_ae : s =ᵐ[volume] Set.univ := by
    rw [ae_eq_univ, hs_def, show {z : ℂ | a + z * c ≠ 0}ᶜ = {z | a + z * c = 0} by ext; simp]
    exact volume_affine_zero a c hac
  have ht_ae : t =ᵐ[volume] Set.univ := by
    rw [ae_eq_univ, ht_def, show {u : ℂ | d - u * c ≠ 0}ᶜ = {u | d + u * (-c) = 0} by
      ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
      constructor <;> intro h <;> linear_combination h]
    exact volume_affine_zero d (-c) hdc
  rw [setIntegral_congr_set ht_ae, setIntegral_congr_set hs_ae, Measure.restrict_univ] at key
  rw [key]
  congr 1
  funext z
  rw [Complex.real_smul, det_D, abs_of_nonneg (sq_nonneg _), norm_div, norm_pow, div_pow, ← pow_mul]

end MoebiusComplex

theorem integral_normSq_det_div_mul_comp_moebius_complex
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ z : ℂ, ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ) * G ((b + z * d) / (a + z * c))
      = ∫ u : ℂ, G u := by
  exact MoebiusComplex.main a b c d _hdet G

namespace MoebiusReal

/-- A nonconstant affine map `x ↦ p + x * q` on `ℝ` vanishes on a null set. -/
theorem volume_affine_zero (p q : ℝ) (h : p ≠ 0 ∨ q ≠ 0) : volume {x : ℝ | p + x * q = 0} = 0 := by
  rcases eq_or_ne q 0 with hq | hq
  · have hp : p ≠ 0 := h.resolve_right (not_not.mpr hq)
    exact measure_mono_null (fun x hx => (hp (by simpa [hq] using hx)).elim) measure_empty
  · refine measure_mono_null (fun x hx => ?_) (measure_singleton (-p / q))
    simp only [Set.mem_ofPred_eq] at hx
    rw [Set.mem_singleton_iff, eq_div_iff hq]
    linarith

/-- The Möbius change of variables at the real place; the row below is its `_hdet` form. -/
theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by
  set s : Set ℝ := {x | a + x * c ≠ 0} with hs_def
  set t : Set ℝ := {u | d - u * c ≠ 0} with ht_def
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hdet; rw [h.1, h.2]; ring
  have hdc : d ≠ 0 ∨ -c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not, neg_eq_zero] at h
    apply hdet; rw [h.1, h.2]; ring
  have hs : MeasurableSet s := (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
  have hderiv : ∀ x ∈ s, HasDerivWithinAt (fun y : ℝ => (b + y * d) / (a + y * c))
      ((a * d - b * c) / (a + x * c) ^ 2) s x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b + y * d) d x := by
      simpa using ((hasDerivAt_id x).mul_const d).const_add b
    have h2 : HasDerivAt (fun y : ℝ => a + y * c) c x := by
      simpa using ((hasDerivAt_id x).mul_const c).const_add a
    have h3 := h1.div h2 hx
    refine (h3.congr_deriv ?_).hasDerivWithinAt
    congr 1; ring
  have hinj : Set.InjOn (fun y : ℝ => (b + y * d) / (a + y * c)) s := by
    intro x hx y hy hxy
    dsimp only at hxy
    rw [div_eq_div_iff hx hy] at hxy
    have h0 : (x - y) * (a * d - b * c) = 0 := by linear_combination hxy
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h hdet
  have himage : (fun y : ℝ => (b + y * d) / (a + y * c)) '' s = t := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      change d - (b + x * d) / (a + x * c) * c ≠ 0
      have hx' : a + x * c ≠ 0 := hx
      rw [show d - (b + x * d) / (a + x * c) * c = (a * d - b * c) / (a + x * c) by field_simp; ring]
      exact div_ne_zero hdet hx'
    · intro hu
      change d - u * c ≠ 0 at hu
      have hden : a + (u * a - b) / (d - u * c) * c ≠ 0 := by
        rw [show a + (u * a - b) / (d - u * c) * c = (a * d - b * c) / (d - u * c) by field_simp; ring]
        exact div_ne_zero hdet hu
      refine ⟨(u * a - b) / (d - u * c), hden, ?_⟩
      change (b + (u * a - b) / (d - u * c) * d) / (a + (u * a - b) / (d - u * c) * c) = u
      rw [div_eq_iff hden]
      field_simp
      ring
  have key := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj G
  rw [himage] at key
  have hs_ae : s =ᵐ[volume] Set.univ := by
    rw [ae_eq_univ, hs_def, show {x : ℝ | a + x * c ≠ 0}ᶜ = {x | a + x * c = 0} by ext; simp]
    exact volume_affine_zero a c hac
  have ht_ae : t =ᵐ[volume] Set.univ := by
    rw [ae_eq_univ, ht_def, show {u : ℝ | d - u * c ≠ 0}ᶜ = {u | d + u * (-c) = 0} by
      ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]; constructor <;> intro h <;> linarith]
    exact volume_affine_zero d (-c) hdc
  rw [setIntegral_congr_set ht_ae, setIntegral_congr_set hs_ae, Measure.restrict_univ] at key
  rw [key]
  congr 1
  funext x
  rw [Complex.real_smul, abs_div, abs_of_nonneg (sq_nonneg (a + x * c))]

end MoebiusReal

theorem integral_abs_det_div_sq_mul_comp_moebius_real
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
    ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
      = ∫ u : ℝ, G u := by
  exact MoebiusReal.main a b c d _hdet G

end MeasureTheory
