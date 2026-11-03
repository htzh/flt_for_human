/-
  The archimedean Whittaker profile and the equation the Casimir forces on it.

  At a real place, an adelic function that is an eigenfunction of the Casimir with eigenvalue `lam`,
  transforms by the unipotent character `x ↦ exp (2 π i ε x)` and has weight `n` under the maximal
  compact has a profile `f (y) = F (diag (√y, 1/√y))` which is twice differentiable on `y > 0` and
  satisfies the classical Whittaker equation

    `y² f'' + (1/4 − ν² + 2 π ε n y − 4 π² y²) f = 0`   with  `ν² = 1/4 − lam`,

  the second-order equation whose solutions are the archimedean Whittaker functions. At a complex
  place the same three conditions become a *pair* of Casimir equations, one for each of
  `archCasimirAtComplex` and `archCasimirBarAtComplex`, and a weight-`k` vector-valued profile
  `f p y = F p (diag (√y, 1/√y))`, `p : Fin (n+1)`, satisfies two coupled second-order equations: the
  first raises the `k`-type index `p → p+1`, the second lowers it `p → p−1`. The two are the
  holomorphic and the antiholomorphic half of the complex Casimir, and the coupling is the band of
  the weight-`(n+1)` representation of the maximal compact.

  This is the *local* object behind the global adelic `whittakerCoefficient`: the coefficient's local
  component at the place satisfies this equation, which is what the later bound on the coefficient at
  a `diagOne` point consumes.

  Transcribed from `P2M/Sol/S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean`
  (347 lines, 13 public declarations; the pin's `IwasawaAux` block, its `kIw` chart) and
  `P2M/Sol/S_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean`
  (695 lines, 57 public declarations; the pin's `IwasawaC41` block, its `psiK`/`zeta`/`rotR`/`rotS`
  chart), pinned `aa2d8b3`. The two `Theorems/` wrappers carry the headlines' statements; the pin's
  pipeline labels (`IwasawaC41`, the `p2m_*` scaffolding) are dropped from the namespaces. It rests on
  the archimedean Casimir calculus of `ArchDerivCasimir.lean` and `ArchDerivCasimirComplexAPI.lean`
  (the flows, the dictionary `ArchDir → archDirMatrix`, the smoothness and derivative API), and on the
  mathlib special-function modules the pin's `S_` files name.

  **Wiring.** `spec/check_port.py` owns this module: the two `Theorems/` wrappers and the two `S_`
  files are the wire, and the pin's two files are a flat public surface (70 public declarations, no
  `private` prelude), so the engine below is public at the pin's names rather than private.
  spec-pin: Theorems/Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean
  spec-pin: Theorems/Thm_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix Complex
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

namespace AutomorphicForm

/-! ## The real place: the Iwasawa chart of the profile -/

namespace IwasawaChart

theorem splitTorusGL2_mul (s t : ℝ) : splitTorusGL2 s * splitTorusGL2 t = splitTorusGL2 (s + t) := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]; ring_nf

theorem splitTorusGL2_mul_unipotentGL2 (s t : ℝ) :
    splitTorusGL2 s * unipotentGL2 t = unipotentGL2 (Real.exp (2 * s) * t) * splitTorusGL2 s := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add, Real.exp_neg]
  field_simp

theorem inv_sqrt_mul_inv_sqrt (t : ℝ) : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ = (1 + t ^ 2)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity)]

def kIw (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹]
    (by
      rw [Matrix.det_fin_two_of]
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have h2 : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
      have : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ - -t * (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹)
          = (1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
      rw [this, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne']
      exact one_ne_zero)

theorem kIw_coe (t : ℝ) : (kIw t : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹; t * (Real.sqrt (1 + t ^ 2))⁻¹, (Real.sqrt (1 + t ^ 2))⁻¹] := rfl

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
theorem sq_sqrt_one_add_sq (t : ℝ) : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)

theorem det_kIw (t : ℝ) : ((kIw t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [kIw_coe, Matrix.det_fin_two_of]
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have : (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹ - -t * (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹)
      = (1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
  rw [this, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne']

theorem kIw_mem (t : ℝ) : kIw t ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_kIw t, ?_, ?_⟩
  · rw [det_kIw, norm_one]
  · intro x y
    rw [kIw_coe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have key : (x * (Real.sqrt (1 + t ^ 2))⁻¹ + y * (t * (Real.sqrt (1 + t ^ 2))⁻¹)) ^ 2 +
        (x * (-t * (Real.sqrt (1 + t ^ 2))⁻¹) + y * (Real.sqrt (1 + t ^ 2))⁻¹) ^ 2 =
        (x ^ 2 + y ^ 2) * ((1 + t ^ 2) * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹)) := by ring
    rw [key, inv_sqrt_mul_inv_sqrt, mul_inv_cancel₀ hpos.ne', mul_one]

theorem archWeightCharℝ_kIw (n : ℤ) (t : ℝ) :
    ((archWeightCharℝ n ⟨kIw t, kIw_mem t⟩ : ℂˣ) : ℂ) =
      ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n := by
  show (((zpowGroupHom n).comp archWeightOneℝ ⟨kIw t, kIw_mem t⟩ : ℂˣ) : ℂ) = _
  simp only [MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  congr 1

theorem lowerUnipotentGL2_iwasawa (t : ℝ) :
    lowerUnipotentGL2 t = unipotentGL2 (t / (1 + t ^ 2)) * splitTorusGL2 (-(Real.log (1 + t ^ 2)) / 2) * kIw t := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hsq := sq_sqrt_one_add_sq t
  have hs := sqrt_one_add_sq_pos t
  have hexp : Real.exp (-(Real.log (1 + t ^ 2)) / 2) = (Real.sqrt (1 + t ^ 2))⁻¹ := by
    rw [show -(Real.log (1 + t ^ 2)) / 2 = -(Real.log (1 + t ^ 2) / 2) by ring, Real.exp_neg,
      show Real.log (1 + t ^ 2) / 2 = Real.log (Real.sqrt (1 + t ^ 2)) by
        rw [Real.log_sqrt hpos.le], Real.exp_log hs]
  have hexp' : Real.exp (-(-(Real.log (1 + t ^ 2)) / 2)) = Real.sqrt (1 + t ^ 2) := by
    rw [show -(-(Real.log (1 + t ^ 2)) / 2) = Real.log (Real.sqrt (1 + t ^ 2)) by
      rw [Real.log_sqrt hpos.le]; ring, Real.exp_log hs]
  have hii := inv_sqrt_mul_inv_sqrt t
  have hsi : Real.sqrt (1 + t ^ 2) * (Real.sqrt (1 + t ^ 2))⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  ext i j
  simp only [Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe, splitTorusGL2_coe, kIw_coe, hexp, hexp']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ·
    rw [hii]; field_simp
  ·
    have : (Real.sqrt (1 + t ^ 2))⁻¹ * (t * (Real.sqrt (1 + t ^ 2))⁻¹) = t * ((Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (1 + t ^ 2))⁻¹) := by ring
    rw [this, hii]; field_simp; ring
  ·
    field_simp
  ·
    field_simp

end IwasawaChart

open IwasawaChart

/-! ## The real place: the Whittaker equation -/

theorem gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
    (F : GL (Fin 2) ℝ → ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (lam ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (DF : ArchDir → GL (Fin 2) ℝ → ℂ) (DHH DEF : GL (Fin 2) ℝ → ℂ)
    (hD : ∀ (d : ArchDir) (h : GL (Fin 2) ℝ), HasDerivAt (fun t : ℝ => F (h * archFlowMatrix d t)) (DF d h) 0)
    (hDHH : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .H (h * archFlowMatrix .H t)) (DHH h) 0)
    (hDEF : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .Fm (h * archFlowMatrix .E t)) (DEF h) 0)
    (hΩ : ∀ h : GL (Fin 2) ℝ, -((1 / 4 : ℂ) * DHH h - (1 / 2 : ℂ) * DF .H h + DEF h) = lam * F h)
    (hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      F (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * F h)
    (hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      F (h * k) = ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) * F h) :
    let f : ℝ → ℂ := fun y => F (splitTorusGL2 (Real.log y / 2))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by
  intro f

  have hflowH : ∀ t : ℝ, archFlowMatrix .H t = splitTorusGL2 t := fun _ => rfl
  have hflowE : ∀ t : ℝ, archFlowMatrix .E t = unipotentGL2 t := fun _ => rfl
  have hflowF : ∀ t : ℝ, archFlowMatrix .Fm t = lowerUnipotentGL2 t := fun _ => rfl
  let a : ℝ → GL (Fin 2) ℝ := fun y => splitTorusGL2 (Real.log y / 2)
  have hf_def : ∀ y, f y = F (a y) := fun _ => rfl

  have haH : ∀ (y s : ℝ), 0 < y → 0 < s → a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2) = a s := by
    intro y s hy hs
    rw [hflowH]; show splitTorusGL2 _ * splitTorusGL2 _ = splitTorusGL2 _
    rw [splitTorusGL2_mul]; congr 1; ring
  have hinner : ∀ y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => Real.log s / 2 - Real.log y / 2) (1 / (2 * y)) y := by
    intro y hy
    have h := ((Real.hasDerivAt_log hy.ne').div_const 2).sub_const (Real.log y / 2)
    convert h using 1
    all_goals first | rfl | field_simp

  let fD : ℝ → ℂ := fun y => (1 / (2 * y) : ℝ) • DF .H (a y)
  have hf1 : ∀ y : ℝ, 0 < y → HasDerivAt f (fD y) y := by
    intro y hy
    have hG : HasDerivAt (fun t : ℝ => F (a y * archFlowMatrix .H t)) (DF .H (a y))
        (Real.log y / 2 - Real.log y / 2) := by rw [sub_self]; exact hD .H (a y)
    have hcomp := hG.scomp y (hinner y hy)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    show f s = F (a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2))
    rw [haH y s hy hs]
  have hderiv_f : ∀ y : ℝ, 0 < y → deriv f y = fD y := fun y hy => (hf1 y hy).deriv

  have hG1 : ∀ y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => DF .H (a s)) ((1 / (2 * y) : ℝ) • DHH (a y)) y := by
    intro y hy
    have hG : HasDerivAt (fun t : ℝ => DF .H (a y * archFlowMatrix .H t)) (DHH (a y))
        (Real.log y / 2 - Real.log y / 2) := by rw [sub_self]; exact hDHH (a y)
    have hcomp := hG.scomp y (hinner y hy)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    show DF .H (a s) = DF .H (a y * archFlowMatrix .H (Real.log s / 2 - Real.log y / 2))
    rw [haH y s hy hs]

  let fDD : ℝ → ℂ := fun y => (1 / (2 * y) : ℝ) • ((1 / (2 * y) : ℝ) • DHH (a y)) + (-(1 / (2 * y ^ 2)) : ℝ) • DF .H (a y)
  have hf2 : ∀ y : ℝ, 0 < y → HasDerivAt fD (fDD y) y := by
    intro y hy
    have h1 : HasDerivAt (fun s : ℝ => (1 / (2 * s) : ℝ)) (-(1 / (2 * y ^ 2))) y := by
      have := ((hasDerivAt_id y).const_mul 2).inv (by positivity)
      convert this using 1
      · funext s; simp [one_div]
      · simp only [id]
        field_simp
    have := h1.smul (hG1 y hy)
    convert this using 1
  have hderiv_fD : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (fDD y) y := by
    intro y hy
    refine (hf2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_f s hs
  refine ⟨fun y hy => (hf1 y hy).differentiableAt.differentiableWithinAt,
    fun y hy => (hderiv_fD y hy).differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy
  rw [(hderiv_fD y hy).deriv]

  have hNF : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      DF .Fm (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * DF .Fm h := by
    intro x h
    have h1 := hD .Fm (unipotentGL2 x * h)
    have h2 : HasDerivAt (fun t : ℝ => F (unipotentGL2 x * h * archFlowMatrix .Fm t))
        (Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * DF .Fm h) 0 := by
      have := (hD .Fm h).const_mul (Complex.exp (2 * Real.pi * Complex.I * (ε * x)))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show F (unipotentGL2 x * h * archFlowMatrix .Fm t) = _
      rw [mul_assoc, hN]
    exact h1.unique h2

  have hay_n : ∀ t : ℝ, a y * unipotentGL2 t = unipotentGL2 (y * t) * a y := by
    intro t
    show splitTorusGL2 _ * unipotentGL2 t = unipotentGL2 (y * t) * splitTorusGL2 _
    rw [splitTorusGL2_mul_unipotentGL2]
    have : Real.exp (2 * (Real.log y / 2)) * t = y * t := by
      rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]
    rw [this]
  have hDEF_val : DEF (a y) = (2 * Real.pi * Complex.I * (ε * y)) * DF .Fm (a y) := by
    have h1 := hDEF (a y)
    have h2 : HasDerivAt (fun t : ℝ => DF .Fm (a y * archFlowMatrix .E t))
        ((2 * Real.pi * Complex.I * (ε * y)) * DF .Fm (a y)) 0 := by
      have hfun : (fun t : ℝ => DF .Fm (a y * archFlowMatrix .E t)) =
          fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * t))) * DF .Fm (a y) := by
        funext t; rw [hflowE, hay_n, hNF]; push_cast; ring_nf
      rw [hfun]
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * t))))
          (Complex.exp (2 * Real.pi * Complex.I * (ε * (y * 0))) * (2 * Real.pi * Complex.I * (ε * y))) 0 := by
        have hlin : HasDerivAt (fun t : ℝ => (2 * Real.pi * Complex.I * (ε * (y * t)) : ℂ))
          (2 * Real.pi * Complex.I * (ε * y)) 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * Real.pi * Complex.I * (ε * y))
          convert this using 1
          · funext t; simp only [id]; ring
          · simp
        exact hlin.cexp
      have := hexp.mul_const (DF .Fm (a y))
      convert this using 1
      simp
    exact h1.unique h2

  have hDF_val : DF .Fm (a y) = (2 * Real.pi * Complex.I * (ε * y) - Complex.I * n) * f y := by
    have h1 := hD .Fm (a y)

    have hfun : (fun t : ℝ => F (a y * archFlowMatrix .Fm t)) = fun t : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))) *
          (((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n *
            f (y / (1 + t ^ 2))) := by
      funext t
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have htor : a y * splitTorusGL2 (-(Real.log (1 + t ^ 2)) / 2) = a (y / (1 + t ^ 2)) := by
        show splitTorusGL2 _ * splitTorusGL2 _ = splitTorusGL2 _
        rw [splitTorusGL2_mul]; congr 1
        rw [Real.log_div hy.ne' hpos.ne']; ring
      rw [hflowF, lowerUnipotentGL2_iwasawa, ← mul_assoc, ← mul_assoc, hay_n, mul_assoc (unipotentGL2 _),
        mul_assoc (unipotentGL2 _), hN, hK (kIw t) (kIw_mem t), archWeightCharℝ_kIw, htor, hf_def]
      push_cast; ring_nf

    have hx : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) 1 0 := by
      have hnum := hasDerivAt_id (0 : ℝ)
      have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
        simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
      have := hnum.div hden (by norm_num)
      convert this using 1
      all_goals first | rfl | simp
    have hE1 : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))))
        (2 * Real.pi * Complex.I * (ε * y)) 0 := by
      have hlin : HasDerivAt (fun t : ℝ => (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2)))) : ℂ))
          (2 * Real.pi * Complex.I * (ε * y)) 0 := by
        have := (hx.ofReal_comp).const_mul (2 * Real.pi * Complex.I * (ε * y))
        convert this using 1
        · funext t; push_cast; ring
        · simp
      have := hlin.cexp
      convert this using 1
      simp
    have hbase : HasDerivAt (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)))
        (-Complex.I) 0 := by

      have hc : HasDerivAt (fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹) 0 0 := by
        have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
          simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
        have hs := hden.sqrt (by norm_num)
        have hi := hs.inv (by norm_num)
        convert hi using 1
        all_goals first | rfl | simp
      have hc' : HasDerivAt (fun t : ℝ => ((Real.sqrt (1 + t ^ 2))⁻¹ : ℂ)) 0 0 := by
        simpa using hc.ofReal_comp
      have hl : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) * Complex.I)) (-Complex.I) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).const_sub 1
        convert this using 1
        all_goals first | rfl | simp
      have hprod := hc'.mul hl
      have hfeq : (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ))) =
          fun t : ℝ => ((Real.sqrt (1 + t ^ 2))⁻¹ : ℂ) * (1 - (t : ℂ) * Complex.I) := by
        funext t
        apply Complex.ext <;> simp; ring
      rw [hfeq]
      convert hprod using 1
      simp
    have hpow : HasDerivAt (fun t : ℝ => ((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n)
        (-(Complex.I * n)) 0 := by
      have h0 : ((⟨(Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹, -(0 : ℝ) * (Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹⟩ : ℂ)) = 1 := by
        apply Complex.ext <;> simp
      have hz := (hasDerivAt_zpow n (1 : ℂ) (Or.inl one_ne_zero))
      rw [← h0] at hz
      have := hz.comp (0 : ℝ) hbase
      convert this using 1
      all_goals first | rfl | skip
      rw [h0]; simp; ring
    have hfin : HasDerivAt (fun t : ℝ => f (y / (1 + t ^ 2))) 0 0 := by
      have hin : HasDerivAt (fun t : ℝ => y / (1 + t ^ 2)) 0 0 := by
        have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
          simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
        have := (hasDerivAt_const (0 : ℝ) y).div hden (by norm_num)
        convert this using 1
        all_goals first | rfl | simp
      have hfy : HasDerivAt f (fD y) (y / (1 + (0 : ℝ) ^ 2)) := by simpa using hf1 y hy
      have := hfy.scomp (0 : ℝ) hin
      simpa [Function.comp_def] using this
    have h2c : HasDerivAt (fun t : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (ε * (y * (t / (1 + t ^ 2))))) *
          (((⟨(Real.sqrt (1 + t ^ 2))⁻¹, -t * (Real.sqrt (1 + t ^ 2))⁻¹⟩ : ℂ)) ^ n *
            f (y / (1 + t ^ 2))))
        ((2 * Real.pi * Complex.I * (ε * y)) * f y + (-(Complex.I * n)) * f y) 0 := by
      have h0 : ((⟨(Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹, -(0 : ℝ) * (Real.sqrt (1 + (0 : ℝ) ^ 2))⁻¹⟩ : ℂ)) = 1 := by
        apply Complex.ext <;> simp
      convert hE1.mul (hpow.mul hfin) using 1
      have h1c : ((⟨1, 0⟩ : ℂ)) = 1 := rfl
      simp [h1c]
      try ring
    rw [← hfun] at h2c
    have h3 := h1.unique h2c
    rw [h3]
    ring

  have hΩy := hΩ (a y)
  have hε2 : (ε : ℂ) ^ 2 = 1 := by
    rcases hε with h | h <;> simp [h]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hlam : lam = 1 / 4 - ν ^ 2 := by rw [hν]; ring
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'

  rw [hDEF_val, hDF_val, hf_def] at hΩy
  have hy2 : (y : ℂ) ^ 2 * fDD y = -(1 / 2 : ℂ) * DF .H (a y) + (1 / 4 : ℂ) * DHH (a y) := by
    simp only [fDD, Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [hy2, hf_def]
  push_cast
  linear_combination (-1 : ℂ) * hΩy
    + ((-4 * (Real.pi : ℂ) ^ 2 * (ε : ℂ) ^ 2 * (y : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * (ε : ℂ) * (y : ℂ) * (n : ℂ)) * F (a y)) * hI2
    + (4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2 * F (a y)) * hε2 - (F (a y)) * hν

/-! ## The complex place: the vector-valued Iwasawa chart -/

namespace IwasawaChartComplex

open Complex Matrix

theorem splitTorusGL2Complex_coe' (z : ℂ) :
    ((splitTorusGL2Complex z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![exp z, 0; 0, exp (-z)] := rfl

theorem splitTorus_mul_unipotent (z x : ℂ) :
    splitTorusGL2Complex z * unipotentGL2 x = unipotentGL2 (exp (2 * z) * x) * splitTorusGL2Complex z := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2Complex_coe', unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show (2 : ℂ) * z = z + z by ring, Complex.exp_add, Complex.exp_neg]
  field_simp

theorem splitTorus_mul_splitTorus (z z' : ℂ) :
    splitTorusGL2Complex z * splitTorusGL2Complex z' = splitTorusGL2Complex (z + z') :=
  (splitTorusGL2Complex_add z z').symm

def rotR (s : ℝ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![((Real.cos s : ℝ) : ℂ), -((Real.sin s : ℝ) : ℂ); ((Real.sin s : ℝ) : ℂ), ((Real.cos s : ℝ) : ℂ)]
    (by
      rw [Matrix.det_fin_two_of]
      have h : ((Real.cos s : ℝ) : ℂ) * ((Real.cos s : ℝ) : ℂ) - -((Real.sin s : ℝ) : ℂ) * ((Real.sin s : ℝ) : ℂ) = 1 := by
        have := Real.cos_sq_add_sin_sq s
        calc _ = (((Real.cos s ^ 2 + Real.sin s ^ 2 : ℝ)) : ℂ) := by push_cast; ring
          _ = 1 := by rw [this]; simp
      rw [h]; exact one_ne_zero)

def rotS (s : ℝ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((Real.cos s : ℝ) : ℂ), I * ((Real.sin s : ℝ) : ℂ); I * ((Real.sin s : ℝ) : ℂ), ((Real.cos s : ℝ) : ℂ)]
    (by
      rw [Matrix.det_fin_two_of]
      have h : ((Real.cos s : ℝ) : ℂ) * ((Real.cos s : ℝ) : ℂ) - I * ((Real.sin s : ℝ) : ℂ) * (I * ((Real.sin s : ℝ) : ℂ)) = 1 := by
        have := Real.cos_sq_add_sin_sq s
        calc _ = (((Real.cos s ^ 2 : ℝ)) : ℂ) - I * I * (((Real.sin s ^ 2 : ℝ)) : ℂ) := by push_cast; ring
          _ = (((Real.cos s ^ 2 + Real.sin s ^ 2 : ℝ)) : ℂ) := by rw [Complex.I_mul_I]; push_cast; ring
          _ = 1 := by rw [this]; simp
      rw [h]; exact one_ne_zero)

theorem rotR_coe (s : ℝ) : ((rotR s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] := by
  simp [rotR, Matrix.GeneralLinearGroup.mkOfDetNeZero, Complex.ofReal_cos, Complex.ofReal_sin]

theorem rotS_coe (s : ℝ) : ((rotS s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.cos s, I * Complex.sin s; I * Complex.sin s, Complex.cos s] := by
  simp [rotS, Matrix.GeneralLinearGroup.mkOfDetNeZero, Complex.ofReal_cos, Complex.ofReal_sin]

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)

theorem cexp_neg_log_half (t : ℝ) : exp (((-(Real.log (1 + t ^ 2)) / 2 : ℝ) : ℂ)) = (((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  rw [← Complex.ofReal_exp]
  congr 1
  rw [show -(Real.log (1 + t ^ 2)) / 2 = -(Real.log (Real.sqrt (1 + t ^ 2))) by rw [Real.log_sqrt hpos.le]; ring,
    Real.exp_neg, Real.exp_log (sqrt_one_add_sq_pos t)]

theorem cexp_neg_neg_log_half (t : ℝ) : exp (-(((-(Real.log (1 + t ^ 2)) / 2 : ℝ) : ℂ))) = ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 1
  rw [show -(-(Real.log (1 + t ^ 2)) / 2) = Real.log (Real.sqrt (1 + t ^ 2)) by rw [Real.log_sqrt hpos.le]; ring,
    Real.exp_log (sqrt_one_add_sq_pos t)]

theorem cos_arctan' (t : ℝ) : Complex.cos (Real.arctan t) = (((Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_cos, Real.cos_arctan, one_div]

theorem sin_arctan' (t : ℝ) : Complex.sin (Real.arctan t) = ((t * (Real.sqrt (1 + t ^ 2))⁻¹ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_sin, Real.sin_arctan, div_eq_mul_inv]

theorem lowerUnipotent_real_iwasawa (t : ℝ) :
    lowerUnipotentGL2 ((t : ℝ) : ℂ) =
      unipotentGL2 (((t / (1 + t ^ 2) : ℝ)) : ℂ) * splitTorusGL2Complex ((-(Real.log (1 + t ^ 2)) / 2 : ℝ) : ℂ) *
        rotR (Real.arctan t) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  set s : ℝ := Real.sqrt (1 + t ^ 2) with hsdef
  have hs : 0 < s := sqrt_one_add_sq_pos t
  have hs2 : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hs2C : (s : ℂ) ^ 2 = 1 + (t : ℂ) ^ 2 := by exact_mod_cast hs2
  have h1t : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by rw [← hs2C]; exact pow_ne_zero 2 hsC
  have hx : (((t / (1 + t ^ 2) : ℝ)) : ℂ) = (t : ℂ) / (s : ℂ) ^ 2 := by rw [hs2C]; push_cast; ring
  ext i j
  simp only [Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe, splitTorusGL2Complex_coe', rotR_coe,
    cexp_neg_log_half, cexp_neg_neg_log_half, cos_arctan', sin_arctan', ← hsdef, hx]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  all_goals (first | ring1 | linear_combination hs2C)

theorem lowerUnipotent_imag_iwasawa (t : ℝ) :
    lowerUnipotentGL2 (((t : ℝ) : ℂ) * I) =
      unipotentGL2 (-(I * (((t / (1 + t ^ 2) : ℝ)) : ℂ))) * splitTorusGL2Complex ((-(Real.log (1 + t ^ 2)) / 2 : ℝ) : ℂ) *
        rotS (Real.arctan t) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  set s : ℝ := Real.sqrt (1 + t ^ 2) with hsdef
  have hs : 0 < s := sqrt_one_add_sq_pos t
  have hs2 : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hs2C : (s : ℂ) ^ 2 = 1 + (t : ℂ) ^ 2 := by exact_mod_cast hs2
  have h1t : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by rw [← hs2C]; exact pow_ne_zero 2 hsC
  have hx : (((t / (1 + t ^ 2) : ℝ)) : ℂ) = (t : ℂ) / (s : ℂ) ^ 2 := by rw [hs2C]; push_cast; ring
  have hI : I * I = -1 := Complex.I_mul_I
  ext i j
  simp only [Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe, splitTorusGL2Complex_coe', rotS_coe,
    cexp_neg_log_half, cexp_neg_neg_log_half, cos_arctan', sin_arctan', ← hsdef, hx]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  all_goals (first | ring1 | linear_combination hs2C + ((t:ℂ)^2) * hI)

section Generic

def aT (y : ℝ) : GL (Fin 2) ℂ := splitTorusGL2Complex (((Real.log y / 2 : ℝ)) : ℂ)

theorem flowH (t : ℝ) : archFlowMatrixComplex .H t = splitTorusGL2Complex (t : ℂ) := rfl
theorem flowiH (t : ℝ) : archFlowMatrixComplex .iH t = splitTorusGL2Complex ((t : ℂ) * I) := rfl
theorem flowE (t : ℝ) : archFlowMatrixComplex .E t = unipotentGL2 (t : ℂ) := rfl
theorem flowiE (t : ℝ) : archFlowMatrixComplex .iE t = unipotentGL2 ((t : ℂ) * I) := rfl
theorem flowFm (t : ℝ) : archFlowMatrixComplex .Fm t = lowerUnipotentGL2 (t : ℂ) := rfl
theorem flowiFm (t : ℝ) : archFlowMatrixComplex .iFm t = lowerUnipotentGL2 ((t : ℂ) * I) := rfl

theorem aT_mul_flowH (y s : ℝ) (hy : 0 < y) (hs : 0 < s) :
    aT y * archFlowMatrixComplex .H (Real.log s / 2 - Real.log y / 2) = aT s := by
  have _ : 0 < y := hy
  have _ : 0 < s := hs
  rw [flowH, aT, aT, splitTorus_mul_splitTorus]; congr 1; push_cast; ring

theorem hasDerivAt_log_half (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ => Real.log s / 2 - Real.log y / 2) (1 / (2 * y)) y := by
  have h := ((Real.hasDerivAt_log hy.ne').div_const 2).sub_const (Real.log y / 2)
  convert h using 1
  all_goals first | rfl | field_simp

theorem hasDerivAt_torus (G DG : GL (Fin 2) ℂ → ℂ)
    (hG : ∀ h, HasDerivAt (fun t : ℝ => G (h * archFlowMatrixComplex .H t)) (DG h) 0) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ => G (aT s)) ((1 / (2 * y) : ℝ) • DG (aT y)) y := by
  have h0 : HasDerivAt (fun t : ℝ => G (aT y * archFlowMatrixComplex .H t)) (DG (aT y))
      (Real.log y / 2 - Real.log y / 2) := by rw [sub_self]; exact hG (aT y)
  have hcomp := h0.scomp y (hasDerivAt_log_half y hy)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hy] with s hs
  show G (aT s) = G (aT y * archFlowMatrixComplex .H (Real.log s / 2 - Real.log y / 2))
  rw [aT_mul_flowH y s hy hs]

def psiK (κ x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (κ * x).re : ℝ) : ℂ))

theorem covariant_deriv (κ : ℂ) (G DG : GL (Fin 2) ℂ → ℂ) (d : ArchDirComplex)
    (hG : ∀ h, HasDerivAt (fun t : ℝ => G (h * archFlowMatrixComplex d t)) (DG h) 0)
    (hN : ∀ (x : ℂ) (h : GL (Fin 2) ℂ), G (unipotentGL2 x * h) = psiK κ x * G h) :
    ∀ (x : ℂ) (h : GL (Fin 2) ℂ), DG (unipotentGL2 x * h) = psiK κ x * DG h := by
  intro x h
  have h1 := hG (unipotentGL2 x * h)
  have h2 : HasDerivAt (fun t : ℝ => G (unipotentGL2 x * h * archFlowMatrixComplex d t)) (psiK κ x * DG h) 0 := by
    have := (hG h).const_mul (psiK κ x)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show G (unipotentGL2 x * h * archFlowMatrixComplex d t) = _
    rw [mul_assoc, hN]
  exact h1.unique h2

theorem aT_mul_unipotent (y : ℝ) (hy : 0 < y) (x : ℂ) : aT y * unipotentGL2 x = unipotentGL2 ((y : ℂ) * x) * aT y := by
  rw [aT, splitTorus_mul_unipotent]
  congr 2
  rw [show (2 : ℂ) * (((Real.log y / 2 : ℝ)) : ℂ) = ((Real.log y : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    Real.exp_log hy]

theorem hasDerivAt_psiK_real (κ : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (t : ℂ))) (2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ)) 0 := by
  unfold psiK
  have hre : ∀ t : ℝ, (κ * ((y : ℂ) * (t : ℂ))).re = κ.re * (y * t) := by
    intro t; simp [Complex.mul_re]
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((2 * (κ * ((y : ℂ) * (t : ℂ))).re : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ))
    convert h using 1
    · funext t; rw [hre]; simp only [id]; push_cast; ring
    · simp
  have := hlin.cexp
  convert this using 1
  simp

theorem hasDerivAt_psiK_imag (κ : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * ((t : ℂ) * I))) (2 * Real.pi * Complex.I * ((-(2 * y * κ.im) : ℝ) : ℂ)) 0 := by
  unfold psiK
  have hre : ∀ t : ℝ, (κ * ((y : ℂ) * ((t : ℂ) * I))).re = -(κ.im * (y * t)) := by
    intro t; simp [Complex.mul_re, Complex.mul_im]
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((2 * (κ * ((y : ℂ) * ((t : ℂ) * I))).re : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * ((-(2 * y * κ.im) : ℝ) : ℂ)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * Real.pi * Complex.I * ((-(2 * y * κ.im) : ℝ) : ℂ))
    convert h using 1
    · funext t; rw [hre]; simp only [id]; push_cast; ring
    · simp
  have := hlin.cexp
  convert this using 1
  simp

theorem derivE_torus (κ : ℂ) (G : GL (Fin 2) ℂ → ℂ) (V : ℂ) (y : ℝ) (hy : 0 < y)
    (hN : ∀ (x : ℂ) (h : GL (Fin 2) ℂ), G (unipotentGL2 x * h) = psiK κ x * G h)
    (hV : HasDerivAt (fun t : ℝ => G (aT y * archFlowMatrixComplex .E t)) V 0) :
    V = 2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ) * G (aT y) := by
  have hfun : (fun t : ℝ => G (aT y * archFlowMatrixComplex .E t)) = fun t : ℝ => psiK κ ((y : ℂ) * (t : ℂ)) * G (aT y) := by
    funext t; rw [flowE, aT_mul_unipotent y hy, hN]
  rw [hfun] at hV
  have h2 := (hasDerivAt_psiK_real κ y).mul_const (G (aT y))
  exact hV.unique h2

theorem deriviE_torus (κ : ℂ) (G : GL (Fin 2) ℂ → ℂ) (V : ℂ) (y : ℝ) (hy : 0 < y)
    (hN : ∀ (x : ℂ) (h : GL (Fin 2) ℂ), G (unipotentGL2 x * h) = psiK κ x * G h)
    (hV : HasDerivAt (fun t : ℝ => G (aT y * archFlowMatrixComplex .iE t)) V 0) :
    V = 2 * Real.pi * Complex.I * ((-(2 * y * κ.im) : ℝ) : ℂ) * G (aT y) := by
  have hfun : (fun t : ℝ => G (aT y * archFlowMatrixComplex .iE t)) = fun t : ℝ => psiK κ ((y : ℂ) * ((t : ℂ) * I)) * G (aT y) := by
    funext t; rw [flowiE, aT_mul_unipotent y hy, hN]
  rw [hfun] at hV
  have h2 := (hasDerivAt_psiK_imag κ y).mul_const (G (aT y))
  exact hV.unique h2

def zeta (t : ℝ) : ℂˣ := Units.mk0 (Complex.exp ((t : ℂ) * I)) (Complex.exp_ne_zero _)

theorem zeta_coe (t : ℝ) : ((zeta t : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * I) := rfl
theorem zeta_inv_coe (t : ℝ) : (((zeta t)⁻¹ : ℂˣ) : ℂ) = Complex.exp (-((t : ℂ) * I)) := by
  rw [Units.val_inv_eq_inv_val, zeta_coe, Complex.exp_neg]
theorem norm_zeta (t : ℝ) : ‖((zeta t : ℂˣ) : ℂ)‖ = 1 := by rw [zeta_coe, Complex.norm_exp_ofReal_mul_I]

theorem flowiH_eq_circle (t : ℝ) : archFlowMatrixComplex .iH t = circleGL2 (zeta t) := by
  rw [flowiH]
  ext i j
  simp only [splitTorusGL2Complex_coe', show ((circleGL2 (zeta t) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![((zeta t : ℂˣ) : ℂ), 0; 0, (((zeta t)⁻¹ : ℂˣ) : ℂ)] from rfl, zeta_coe, zeta_inv_coe]

theorem hasDerivAt_zeta_zpow (q : ℤ) :
    HasDerivAt (fun t : ℝ => (((zeta t : ℂˣ) : ℂ)) ^ q) (Complex.I * q) 0 := by
  have hfun : (fun t : ℝ => (((zeta t : ℂˣ) : ℂ)) ^ q) = fun t : ℝ => Complex.exp ((t : ℂ) * (Complex.I * q)) := by
    funext t; rw [zeta_coe, ← Complex.exp_int_mul]; congr 1; ring
  rw [hfun]
  have h := (Complex.hasDerivAt_exp ((0 : ℝ) * (Complex.I * q))).comp (0 : ℝ)
    ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (Complex.I * q))
  simp at h
  exact h

theorem deriviH_of_weight (G : GL (Fin 2) ℂ → ℂ) (q : ℤ) (h : GL (Fin 2) ℂ) (V : ℂ)
    (hM : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ, G (h * circleGL2 ζ) = (ζ : ℂ) ^ q * G h)
    (hV : HasDerivAt (fun t : ℝ => G (h * archFlowMatrixComplex .iH t)) V 0) :
    V = Complex.I * q * G h := by
  have hfun : (fun t : ℝ => G (h * archFlowMatrixComplex .iH t)) = fun t : ℝ => (((zeta t : ℂˣ) : ℂ)) ^ q * G h := by
    funext t; rw [flowiH_eq_circle, hM _ (norm_zeta t)]
  rw [hfun] at hV
  exact hV.unique ((hasDerivAt_zeta_zpow q).mul_const (G h))

theorem circle_mul_splitTorus (ζ : ℂˣ) (z : ℂ) : circleGL2 ζ * splitTorusGL2Complex z = splitTorusGL2Complex z * circleGL2 ζ := by
  ext i j
  simp only [Units.val_mul, splitTorusGL2Complex_coe', show ((circleGL2 ζ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)] from rfl]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem weight_derivH (G DG : GL (Fin 2) ℂ → ℂ) (q : ℤ)
    (hG : ∀ h, HasDerivAt (fun t : ℝ => G (h * archFlowMatrixComplex .H t)) (DG h) 0)
    (hM : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ, G (h * circleGL2 ζ) = (ζ : ℂ) ^ q * G h) :
    ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ, DG (h * circleGL2 ζ) = (ζ : ℂ) ^ q * DG h := by
  intro ζ hζ h
  have h1 := hG (h * circleGL2 ζ)
  have h2 : HasDerivAt (fun t : ℝ => G (h * circleGL2 ζ * archFlowMatrixComplex .H t)) ((ζ : ℂ) ^ q * DG h) 0 := by
    have := (hG h).const_mul ((ζ : ℂ) ^ q)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show G (h * circleGL2 ζ * archFlowMatrixComplex .H t) = _
    rw [mul_assoc, flowH, circle_mul_splitTorus, ← mul_assoc, ← flowH, hM ζ hζ]
  exact h1.unique h2

theorem weight_deriviH (G DG : GL (Fin 2) ℂ → ℂ) (q : ℤ)
    (hG : ∀ h, HasDerivAt (fun t : ℝ => G (h * archFlowMatrixComplex .iH t)) (DG h) 0)
    (hM : ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ, G (h * circleGL2 ζ) = (ζ : ℂ) ^ q * G h) :
    ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ, DG (h * circleGL2 ζ) = (ζ : ℂ) ^ q * DG h := by
  intro ζ hζ h
  have h1 := hG (h * circleGL2 ζ)
  have h2 : HasDerivAt (fun t : ℝ => G (h * circleGL2 ζ * archFlowMatrixComplex .iH t)) ((ζ : ℂ) ^ q * DG h) 0 := by
    have := (hG h).const_mul ((ζ : ℂ) ^ q)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show G (h * circleGL2 ζ * archFlowMatrixComplex .iH t) = _
    rw [mul_assoc, flowiH, circle_mul_splitTorus, ← mul_assoc, ← flowiH, hM ζ hζ]
  exact h1.unique h2

end Generic

section Iwasawa

theorem aT_mul_aIw (y : ℝ) (hy : 0 < y) (t : ℝ) :
    aT y * splitTorusGL2Complex ((-(Real.log (1 + t ^ 2)) / 2 : ℝ) : ℂ) = aT (y / (1 + t ^ 2)) := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  rw [aT, aT, splitTorus_mul_splitTorus]; congr 1
  rw [Real.log_div hy.ne' hpos.ne']; push_cast; ring

theorem hasDerivAt_xIw : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) 1 0 := by
  have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
  have := (hasDerivAt_id (0 : ℝ)).div hden (by norm_num)
  convert this using 1
  all_goals first | rfl | simp

theorem hasDerivAt_uIw (y : ℝ) : HasDerivAt (fun t : ℝ => y / (1 + t ^ 2)) 0 0 := by
  have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (0 : ℝ) 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
  have := (hasDerivAt_const (0 : ℝ) y).div hden (by norm_num)
  convert this using 1
  all_goals first | rfl | simp

theorem hasDerivAt_psiK_xIw (κ : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (((t / (1 + t ^ 2) : ℝ)) : ℂ)))
      (2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_psiK_real κ y
  have h2 : HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (t : ℂ))) (2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ))
      ((0 : ℝ) / (1 + (0:ℝ) ^ 2)) := by simpa using h
  have h3 := h2.scomp (0 : ℝ) hasDerivAt_xIw
  rw [one_smul] at h3
  exact h3

theorem hasDerivAt_psiK_negI (κ : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (-(I * (t : ℂ))))) (2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ)) 0 := by
  unfold psiK
  have hre : ∀ t : ℝ, (κ * ((y : ℂ) * (-(I * (t : ℂ))))).re = κ.im * (y * t) := by
    intro t; simp [Complex.mul_re, Complex.mul_im]
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((2 * (κ * ((y : ℂ) * (-(I * (t : ℂ))))).re : ℝ) : ℂ))
      (2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ))
    convert h using 1
    · funext t; rw [hre]; simp only [id]; push_cast; ring
    · simp
  have := hlin.cexp
  convert this using 1
  simp

theorem hasDerivAt_psiK_negI_xIw (κ : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (-(I * (((t / (1 + t ^ 2) : ℝ)) : ℂ)))))
      (2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_psiK_negI κ y
  have h2 : HasDerivAt (fun t : ℝ => psiK κ ((y : ℂ) * (-(I * (t : ℂ))))) (2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ))
      ((0 : ℝ) / (1 + (0:ℝ) ^ 2)) := by simpa using h
  have h3 := h2.scomp (0 : ℝ) hasDerivAt_xIw
  rw [one_smul] at h3
  exact h3

theorem psiK_zero (κ : ℂ) : psiK κ 0 = 1 := by simp [psiK]

variable {n : ℕ} (F : Fin (n + 1) → GL (Fin 2) ℂ → ℂ) (κ : ℂ)
  (Ei : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Mi : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  (hN : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ), F p (unipotentGL2 x * h) = psiK κ x * F p h)
  (hE0 : Ei 0 = 1) (hE' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => Ei s i j) (Mi i j) 0)
  (fD : Fin (n + 1) → ℝ → ℂ) (hf : ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → HasDerivAt (fun s : ℝ => F p (aT s)) (fD p y) y)

include hE0 hE' fD hf in

theorem deriv_iwasawa_sum (p : Fin (n + 1)) (y : ℝ) (hy : 0 < y) (Ψ : ℝ → ℂ) (c : ℂ)
    (hΨ : HasDerivAt Ψ c 0) (hΨ0 : Ψ 0 = 1) :
    HasDerivAt (fun t : ℝ => ∑ p' : Fin (n + 1), Ei (Real.arctan t) p' p * (Ψ t * F p' (aT (y / (1 + t ^ 2)))))
      ((∑ p' : Fin (n + 1), Mi p' p * F p' (aT y)) + c * F p (aT y)) 0 := by
  have hterm : ∀ p' : Fin (n + 1), HasDerivAt (fun t : ℝ => Ei (Real.arctan t) p' p * (Ψ t * F p' (aT (y / (1 + t ^ 2)))))
      (Mi p' p * F p' (aT y) + (if p' = p then 1 else 0) * (c * F p' (aT y))) 0 := by
    intro p'
    have hE : HasDerivAt (fun t : ℝ => Ei (Real.arctan t) p' p) (Mi p' p * 1) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => Ei s p' p) (Mi p' p) (Real.arctan 0) := by rw [Real.arctan_zero]; exact hE' p' p
      have h2 := h1.scomp (0 : ℝ) (Real.hasDerivAt_arctan 0)
      convert h2 using 1 <;> first | rfl | simp
    have hFu : HasDerivAt (fun t : ℝ => F p' (aT (y / (1 + t ^ 2)))) 0 0 := by
      have h1 : HasDerivAt (fun s : ℝ => F p' (aT s)) (fD p' y) (y / (1 + (0:ℝ) ^ 2)) := by simpa using hf p' y hy
      have := h1.scomp (0 : ℝ) (hasDerivAt_uIw y)
      simp at this
      exact this
    have hprod := hE.mul (hΨ.mul hFu)
    convert hprod using 1
    simp [hE0, hΨ0, Matrix.one_apply]
  have hsum := HasDerivAt.sum fun p' (_ : p' ∈ Finset.univ) => hterm p'
  convert hsum using 1
  · funext t; simp [Finset.sum_apply]
  · rw [Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq']

end Iwasawa

section Lower

variable {n : ℕ} (F : Fin (n + 1) → GL (Fin 2) ℂ → ℂ) (κ : ℂ)
  (Ei : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Mi : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  (hN : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ), F p (unipotentGL2 x * h) = psiK κ x * F p h)
  (hE0 : Ei 0 = 1) (hE' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => Ei s i j) (Mi i j) 0)
  (fD : Fin (n + 1) → ℝ → ℂ) (hf : ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → HasDerivAt (fun s : ℝ => F p (aT s)) (fD p y) y)

include hN hE0 hE' fD hf in

theorem derivFm_torus
    (hK : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), Ei s p' p * F p' h)
    (p : Fin (n + 1)) (y : ℝ) (hy : 0 < y) (V : ℂ)
    (hV : HasDerivAt (fun t : ℝ => F p (aT y * archFlowMatrixComplex .Fm t)) V 0) :
    V = (∑ p' : Fin (n + 1), Mi p' p * F p' (aT y)) + 2 * Real.pi * Complex.I * ((2 * y * κ.re : ℝ) : ℂ) * F p (aT y) := by
  have hfun : (fun t : ℝ => F p (aT y * archFlowMatrixComplex .Fm t)) = fun t : ℝ =>
      ∑ p' : Fin (n + 1), Ei (Real.arctan t) p' p *
        (psiK κ ((y : ℂ) * (((t / (1 + t ^ 2) : ℝ)) : ℂ)) * F p' (aT (y / (1 + t ^ 2)))) := by
    funext t
    rw [flowFm, lowerUnipotent_real_iwasawa, ← mul_assoc, ← mul_assoc, aT_mul_unipotent y hy, mul_assoc (unipotentGL2 _),
      aT_mul_aIw y hy, hK p (Real.arctan t) _ (rotR (Real.arctan t)) (rotR_coe _)]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [hN]
  rw [hfun] at hV
  have h2 := deriv_iwasawa_sum F Ei Mi hE0 hE' fD hf p y hy
    (fun t => psiK κ ((y : ℂ) * (((t / (1 + t ^ 2) : ℝ)) : ℂ))) _ (hasDerivAt_psiK_xIw κ y) (by simp [psiK])
  exact hV.unique h2

include hN hE0 hE' fD hf in

theorem deriviFm_torus
    (hK : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), Ei s p' p * F p' h)
    (p : Fin (n + 1)) (y : ℝ) (hy : 0 < y) (V : ℂ)
    (hV : HasDerivAt (fun t : ℝ => F p (aT y * archFlowMatrixComplex .iFm t)) V 0) :
    V = (∑ p' : Fin (n + 1), Mi p' p * F p' (aT y)) + 2 * Real.pi * Complex.I * ((2 * y * κ.im : ℝ) : ℂ) * F p (aT y) := by
  have hfun : (fun t : ℝ => F p (aT y * archFlowMatrixComplex .iFm t)) = fun t : ℝ =>
      ∑ p' : Fin (n + 1), Ei (Real.arctan t) p' p *
        (psiK κ ((y : ℂ) * (-(I * (((t / (1 + t ^ 2) : ℝ)) : ℂ)))) * F p' (aT (y / (1 + t ^ 2)))) := by
    funext t
    rw [flowiFm, lowerUnipotent_imag_iwasawa, ← mul_assoc, ← mul_assoc, aT_mul_unipotent y hy, mul_assoc (unipotentGL2 _),
      aT_mul_aIw y hy, hK p (Real.arctan t) _ (rotS (Real.arctan t)) (rotS_coe _)]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [hN]
  rw [hfun] at hV
  have h2 := deriv_iwasawa_sum F Ei Mi hE0 hE' fD hf p y hy
    (fun t => psiK κ ((y : ℂ) * (-(I * (((t / (1 + t ^ 2) : ℝ)) : ℂ))))) _ (hasDerivAt_psiK_negI_xIw κ y) (by simp [psiK])
  exact hV.unique h2

end Lower

section Sums

variable {n : ℕ}

def extN (g : Fin (n + 1) → ℂ) (m : ℕ) : ℂ := if h : m < n + 1 then g ⟨m, h⟩ else 0

theorem sum_ite_val_eq (g : Fin (n + 1) → ℂ) (m : ℕ) :
    (∑ p' : Fin (n + 1), if (p' : ℕ) = m then g p' else 0) = extN g m := by
  unfold extN
  by_cases hm : m < n + 1
  · rw [dite_eq_left hm, Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      apply hb
      ext; simpa using h
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dite_eq_right hm]
    refine Finset.sum_eq_zero fun p' _ => ?_
    rw [ite_eq_right]
    intro h
    exact hm (h ▸ p'.isLt)

theorem mul_sum_ite_pred (g : Fin (n + 1) → ℂ) (p : Fin (n + 1)) (X : ℂ) :
    ((p : ℕ) : ℂ) * X * (∑ p' : Fin (n + 1), if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0) =
      ((p : ℕ) : ℂ) * X * extN g ((p : ℕ) - 1) := by
  rcases Nat.eq_zero_or_pos (p : ℕ) with hp | hp
  · simp [hp]
  · congr 1
    rw [← sum_ite_val_eq g ((p : ℕ) - 1)]
    refine Finset.sum_congr rfl fun p' _ => ?_
    congr 1
    apply propext
    omega

theorem sum_M1 (g : Fin (n + 1) → ℂ) (p : Fin (n + 1)) :
    (∑ p' : Fin (n + 1), (if (p' : ℕ) = (p : ℕ) + 1 then (1 : ℂ) else
        if (p : ℕ) = (p' : ℕ) + 1 then -(((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) else 0) * g p') =
      extN g ((p : ℕ) + 1) - ((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ)) * extN g ((p : ℕ) - 1) := by
  have hsplit : ∀ p' : Fin (n + 1),
      (if (p' : ℕ) = (p : ℕ) + 1 then (1 : ℂ) else if (p : ℕ) = (p' : ℕ) + 1 then -(((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) else 0) * g p' =
        (if (p' : ℕ) = (p : ℕ) + 1 then g p' else 0) +
          -(((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0) := by
    intro p'
    by_cases h1 : (p' : ℕ) = (p : ℕ) + 1
    · have h2 : ¬ ((p : ℕ) = (p' : ℕ) + 1) := by omega
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2]; ring
    · by_cases h2 : (p : ℕ) = (p' : ℕ) + 1
      · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]; ring
      · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]; ring
  rw [Finset.sum_congr rfl fun p' _ => hsplit p', Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_val_eq]
  have := mul_sum_ite_pred g p ((n : ℂ) + 1 - (p : ℕ))
  rw [show -(((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (∑ p' : Fin (n + 1), if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0) =
      -((((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (∑ p' : Fin (n + 1), if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0)) by ring,
    this]
  ring

theorem sum_M2 (g : Fin (n + 1) → ℂ) (p : Fin (n + 1)) :
    (∑ p' : Fin (n + 1), (if (p' : ℕ) = (p : ℕ) + 1 then Complex.I else
        if (p : ℕ) = (p' : ℕ) + 1 then Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) else 0) * g p') =
      Complex.I * extN g ((p : ℕ) + 1) + Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * extN g ((p : ℕ) - 1) := by
  have hsplit : ∀ p' : Fin (n + 1),
      (if (p' : ℕ) = (p : ℕ) + 1 then Complex.I else
          if (p : ℕ) = (p' : ℕ) + 1 then Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) else 0) * g p' =
        Complex.I * (if (p' : ℕ) = (p : ℕ) + 1 then g p' else 0) +
          Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0) := by
    intro p'
    by_cases h1 : (p' : ℕ) = (p : ℕ) + 1
    · have h2 : ¬ ((p : ℕ) = (p' : ℕ) + 1) := by omega
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2]; ring
    · by_cases h2 : (p : ℕ) = (p' : ℕ) + 1
      · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]; ring
      · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]; ring
  rw [Finset.sum_congr rfl fun p' _ => hsplit p', Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_ite_val_eq]
  have := mul_sum_ite_pred g p ((n : ℂ) + 1 - (p : ℕ))
  rw [show Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (∑ p' : Fin (n + 1), if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0) =
      Complex.I * ((((p : ℕ) : ℂ) * ((n : ℂ) + 1 - (p : ℕ))) * (∑ p' : Fin (n + 1), if (p : ℕ) = (p' : ℕ) + 1 then g p' else 0)) by ring,
    this]
  ring

end Sums

end IwasawaChartComplex

open IwasawaChartComplex Complex

/-! ## The complex place: the coupled Whittaker system -/

theorem gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
    (n : ℕ) (F : Fin (n + 1) → GL (Fin 2) ℂ → ℂ) (κ lam lam' : ℂ)
    (DF : Fin (n + 1) → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (DD : Fin (n + 1) → ArchDirComplex → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (hD : ∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => F p (h * archFlowMatrixComplex d t)) (DF p d h) 0)
    (hDD : ∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => DF p d (h * archFlowMatrixComplex d' t)) (DD p d' d h) 0)
    (hΩ : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h - Complex.I * DD p .H .iH h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h - Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h - Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h - Complex.I * DD p .E .iFm h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h - Complex.I * DD p .iE .iFm h)))) = lam * F p h)
    (hΩ' : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h + Complex.I * DD p .H .iH h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h + Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h + Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h + Complex.I * DD p .E .iFm h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h + Complex.I * DD p .iE .iFm h)))) = lam' * F p h)
    (hN : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ),
      F p (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * ((2 * (κ * x).re : ℝ) : ℂ)) * F p h)
    (hM : ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      F p (h * circleGL2 ζ) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * F p h)
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₁ s p' p * F p' h)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₂ s p' p * F p' h) :
    let f : ℕ → ℝ → ℂ := fun m y =>
      if hm : m < n + 1 then F ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0) := by
  intro f p

  have hfp : f (p : ℕ) = fun y => F p (aT y) := by
    funext y
    show (if hm : (p : ℕ) < n + 1 then F ⟨(p : ℕ), hm⟩ (splitTorusGL2Complex (((Real.log y / 2 : ℝ)) : ℂ)) else 0) = _
    rw [dite_eq_left p.isLt]; rfl
  have hfext : ∀ (m : ℕ) (y : ℝ), f m y = extN (fun p' => F p' (aT y)) m := fun _ _ => rfl
  have hN' : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ), F p (unipotentGL2 x * h) = psiK κ x * F p h := hN

  set fD : Fin (n + 1) → ℝ → ℂ := fun p y => ((1 / (2 * y) : ℝ)) • DF p .H (aT y) with hfDdef
  have hf1 : ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → HasDerivAt (fun s : ℝ => F p (aT s)) (fD p y) y :=
    fun p y hy => hasDerivAt_torus (F p) (DF p .H) (hD p .H) y hy
  have hG1 : ∀ y : ℝ, 0 < y → HasDerivAt (fun s : ℝ => DF p .H (aT s)) (((1 / (2 * y) : ℝ)) • DD p .H .H (aT y)) y :=
    fun y hy => hasDerivAt_torus (DF p .H) (DD p .H .H) (fun h => hDD p .H .H h) y hy
  set fDD : ℝ → ℂ := fun y => ((1 / (2 * y) : ℝ)) • (((1 / (2 * y) : ℝ)) • DD p .H .H (aT y)) +
    ((-(1 / (2 * y ^ 2)) : ℝ)) • DF p .H (aT y) with hfDDdef
  have hf2 : ∀ y : ℝ, 0 < y → HasDerivAt (fD p) (fDD y) y := by
    intro y hy
    have h1 : HasDerivAt (fun s : ℝ => (1 / (2 * s) : ℝ)) (-(1 / (2 * y ^ 2))) y := by
      have := ((hasDerivAt_id y).const_mul 2).inv (by positivity)
      convert this using 1
      · funext s; simp [one_div]
      · simp; field_simp
    have := h1.smul (hG1 y hy)
    convert this using 1
  have hderiv_f : ∀ y : ℝ, 0 < y → deriv (f (p : ℕ)) y = fD p y := by
    intro y hy; rw [hfp]; exact (hf1 p y hy).deriv
  have hderiv_fD : ∀ y : ℝ, 0 < y → HasDerivAt (deriv (f (p : ℕ))) (fDD y) y := by
    intro y hy
    refine (hf2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_f s hs
  refine ⟨fun y hy => ?_, fun y hy => (hderiv_fD y hy).differentiableAt.differentiableWithinAt, ?_⟩
  · rw [hfp]; exact (hf1 p y hy).differentiableAt.differentiableWithinAt
  intro y hy
  rw [(hderiv_fD y hy).deriv, hderiv_f y hy, hfp, hfext ((p : ℕ) + 1) y, hfext ((p : ℕ) - 1) y]
  beta_reduce

  set q : ℤ := (n : ℤ) - 2 * (p : ℕ) with hqdef
  have hq : ((q : ℤ) : ℂ) = (n : ℂ) - 2 * ((p : ℕ) : ℂ) := by rw [hqdef]; push_cast; ring
  have vDFiH : ∀ h, DF p .iH h = Complex.I * q * F p h := fun h => deriviH_of_weight (F p) q h _ (hM p) (hD p .iH h)
  have hMH := weight_derivH (F p) (DF p .H) q (hD p .H) (hM p)
  have hMiH := weight_deriviH (F p) (DF p .iH) q (hD p .iH) (hM p)
  have vDDiHH : DD p .iH .H (aT y) = Complex.I * q * DF p .H (aT y) :=
    deriviH_of_weight (DF p .H) q (aT y) _ hMH (hDD p .H .iH (aT y))
  have vDDiHiH : DD p .iH .iH (aT y) = Complex.I * q * DF p .iH (aT y) :=
    deriviH_of_weight (DF p .iH) q (aT y) _ hMiH (hDD p .iH .iH (aT y))
  have vDDHiH : DD p .H .iH (aT y) = Complex.I * q * DF p .H (aT y) := by
    have h1 := hDD p .iH .H (aT y)
    have h2 : HasDerivAt (fun t : ℝ => DF p .iH (aT y * archFlowMatrixComplex .H t)) (Complex.I * q * DF p .H (aT y)) 0 := by
      have := (hD p .H (aT y)).const_mul (Complex.I * q)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      exact vDFiH _
    exact h1.unique h2

  have cFm := covariant_deriv κ (F p) (DF p .Fm) .Fm (hD p .Fm) (hN' p)
  have ciFm := covariant_deriv κ (F p) (DF p .iFm) .iFm (hD p .iFm) (hN' p)
  have vDDEFm := derivE_torus κ (DF p .Fm) _ y hy cFm (hDD p .Fm .E (aT y))
  have vDDEiFm := derivE_torus κ (DF p .iFm) _ y hy ciFm (hDD p .iFm .E (aT y))
  have vDDiEFm := deriviE_torus κ (DF p .Fm) _ y hy cFm (hDD p .Fm .iE (aT y))
  have vDDiEiFm := deriviE_torus κ (DF p .iFm) _ y hy ciFm (hDD p .iFm .iE (aT y))

  have vDFFm := derivFm_torus F κ E₁ (fun i j => if (i : ℕ) = j + 1 then (1 : ℂ) else
      if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) hN' hE₁ hE₁' fD hf1 hK₁ p y hy _ (hD p .Fm (aT y))
  have vDFiFm := deriviFm_torus F κ E₂ (fun i j => if (i : ℕ) = j + 1 then Complex.I else
      if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) hN' hE₂ hE₂' fD hf1 hK₂ p y hy _ (hD p .iFm (aT y))
  have hS1 := sum_M1 (fun p' => F p' (aT y)) p
  have hS2 := sum_M2 (fun p' => F p' (aT y)) p
  beta_reduce at vDFFm vDFiFm
  rw [hS1] at vDFFm
  rw [hS2] at vDFiFm

  have hΩy := hΩ p (aT y)
  have hΩ'y := hΩ' p (aT y)
  rw [vDDHiH, vDDiHH, vDDiHiH, vDFiH, vDDEFm, vDDEiFm, vDDiEFm, vDDiEiFm, vDFFm, vDFiFm, hq] at hΩy hΩ'y

  set Sp : ℂ := extN (fun p' => F p' (aT y)) ((p : ℕ) + 1) with hSpdef
  set Sm : ℂ := extN (fun p' => F p' (aT y)) ((p : ℕ) - 1) with hSmdef

  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hy2 : (y : ℂ) ^ 2 * fDD y = -(1 / 2 : ℂ) * DF p .H (aT y) + (1 / 4 : ℂ) * DD p .H .H (aT y) := by
    simp only [hfDDdef, Complex.real_smul]
    push_cast
    field_simp
    ring
  have hy1 : (y : ℂ) * fD p y = (1 / 2 : ℂ) * DF p .H (aT y) := by
    simp only [hfDdef, Complex.real_smul]
    push_cast
    field_simp

  have hκ : κ = ((κ.re : ℝ) : ℂ) + ((κ.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im κ).symm
  have hκc : (starRingEnd ℂ) κ = ((κ.re : ℝ) : ℂ) - ((κ.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hκn : (((‖κ‖ ^ 2 : ℝ)) : ℂ) = ((κ.re : ℝ) : ℂ) ^ 2 + ((κ.im : ℝ) : ℂ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hI4 : Complex.I ^ 4 = 1 := by rw [show (4:ℕ) = 2 + 2 from rfl, pow_add, hI2]; ring
  push_cast at hΩy hΩ'y
  ring_nf at hΩy hΩ'y
  simp only [hI2, hI3, hI4] at hΩy hΩ'y
  constructor
  · linear_combination (-4 : ℂ) * hΩy + hy2 + ((n : ℂ) - 2 * ((p : ℕ) : ℂ) - 1) * hy1 +
      (8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * Sp) * hκ +
      (-(16 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2 * F p (aT y))) * hκn +
      (8 * (Real.pi : ℂ) * (y : ℂ) * ((κ.im : ℝ) : ℂ) * Sp) * hI2
  · linear_combination (-4 : ℂ) * hΩ'y + hy2 + (-(((n : ℂ) - 2 * ((p : ℕ) : ℂ)) + 1)) * hy1 +
      (-(8 * (Real.pi : ℂ) * Complex.I * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p : ℕ) : ℂ))) * (y : ℂ) * Sm)) * hκc +
      (-(16 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2 * F p (aT y))) * hκn +
      (8 * (Real.pi : ℂ) * (y : ℂ) * ((κ.im : ℝ) : ℂ) * (((p : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p : ℕ) : ℂ))) * Sm) * hI2

end AutomorphicForm

end
