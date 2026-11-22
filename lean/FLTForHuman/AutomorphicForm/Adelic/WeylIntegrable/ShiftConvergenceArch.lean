/-
  The archimedean atom: the Möbius shift against the atom integral.

  At an archimedean place the Rankin–Selberg local integral is the integral of the Möbius-shifted
  section against the atom profile

    `atom σ x = ((x - i) / √(1 + x²)) ^ k · (1 + x²) ^ (-(σ + 1/2))`         (real place),
    `atom σ z = z ^ a₀ · (star z) ^ b₀ · (1 + ‖z‖²) ^ (-(2σ + 1) - m/2)`      (complex place).

  Both rows say the same two things: the atom integral is *bounded* on the strip `1/2 < σ ≤ 1`, and
  the difference between the Möbius-transformed integral and the atom integral tends to `0` as `σ`
  tends to `1/2` from above.  This is the convergence half of the local functional equation at the
  archimedean place; the adic sibling of the same subject is
  `WeylIntegrable/ShiftConvergence.lean` (`…_weylShift_sub_integral_smoothAtom_adicCompletion`).

  Transcribed from the two pins below (pinned `aa2d8b3`, 206 + 175 lines), which are *not* copies of
  one another: the real row is a one-dimensional integral with the `((x - i)/√(1+x²))^k` weight and
  the complex row a two-dimensional one with the `z^a₀ (star z)^b₀` weight.  Both pins are
  all-public flattened files (15 + 13 declarations) and their declarations are all engines of the
  single headline, so the whole file is transcribed at the pins' names.

  Assumes the two premise rows of `ArchAtomValues.lean` (the `σ → 1/2+` convergence of the atom
  integrals) and `MeasureTheory/MoebiusIntegral.lean` (the change-of-variables formulas for the
  Möbius transform).

  ## Naming

  The pins' generated pipeline labels `ARCHW3R` / `ARCHW3C` are dropped; each copy keeps its own
  sub-namespace (`AtomReal`, `AtomComplex`) because the two copies share 10 last names (`atom`,
  `one_add_sq_pos`, `norm_atom`, `norm_atom_le`, `continuous_atom`, `integrable_atom`,
  `integrable_weighted`, `jacobian_identity`, `main`, `solution`) and not one of them has the same
  statement in the two copies (0 of the 10 statement hashes agree), so a single flat namespace would
  declare one public full name twice.  The pins' `p2m` proof scaffolding is not carried.

  ## Port deltas

  - no import added beyond the scaffold's five: `ArchAtomValues` already exports
    `integrable_rpow_neg_one_add_norm_sq` (via `JapaneseBracket`) and
    `integrable_inv_one_add_sq` (via `ImproperIntegrals`), the only two mathlib premises of the
    proofs that the scaffold's narrow list did not name.
  - the pins import `Mathlib` wholesale; this module does not.  The two `Mathlib` statements the
    proofs need beyond the scaffold's list are the two integrality lemmas above.
  - heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, never installed):
    silent at the project default (`200000`, i.e. no bump is needed and none is carried); the
    measured pair is **silent at 6000, first failure at 5000** (`AtomComplex.main`, at
    `«tactic execution»`); at **4000** `AtomReal.jacobian_identity` also falls, at `isDefEq`.
  - one proof step is re-spelled against mathlib v4.34: `AtomReal.jacobian_identity`'s last step
    closes with `ring_nf` where the pin's `ring` sufficed (under v4.34 `ring` reaches the same
    normal form only through its `ring_nf` fallback, which prints a `Try this:` info message and so
    would make the module non-silent).  Nothing else in the two copies changed.

  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchAtomValues
import FLTForHuman.MeasureTheory.MoebiusIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace AutomorphicForm.LocalIntertwining

/-! ### The real place: the one-dimensional atom -/

namespace AtomReal

def atom (k : ℤ) (σ x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

theorem norm_phase (x : ℝ) : ‖(((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have h1 : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp; ring
  have h2 : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'
  rw [norm_div, h1, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self h2]

theorem norm_atom (k : ℤ) (σ x : ℝ) : ‖atom k σ x‖ = (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
  rw [atom, norm_mul, norm_zpow, norm_phase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  congr 1
  simp

theorem norm_atom_le (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (x : ℝ) : ‖atom k σ x‖ ≤ (1 + x ^ 2)⁻¹ := by
  rw [norm_atom, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (by linarith)

theorem continuous_phase : Continuous fun x : ℝ => (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'

theorem continuous_atom (k : ℤ) (σ : ℝ) : Continuous (atom k σ) := by
  unfold atom
  refine Continuous.mul (continuous_phase.zpow₀ k fun x => Or.inl ?_) ?_
  · intro h
    have := norm_phase x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · refine Continuous.cpow (by fun_prop) continuous_const fun x => ?_
    exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

theorem integrable_atom (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) : Integrable (atom k σ) :=
  Integrable.mono' integrable_inv_one_add_sq (continuous_atom k σ).aestronglyMeasurable
    (ae_of_all _ (norm_atom_le k hσ))

theorem sq_le (c' d' x : ℝ) : (c' * x + d') ^ 2 ≤ (c' ^ 2 + d' ^ 2) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (c' - d' * x)]

theorem integrable_weighted (c' d' : ℝ) (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable fun x : ℝ => ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x := by
  set t : ℝ := σ - 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set K : ℝ := c' ^ 2 + d' ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (K ^ t)) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_atom k σ))
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.rpow_const (by fun_prop) fun x => Or.inr ht0
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_atom]
    have h1 : ((c' * x + d') ^ 2) ^ t ≤ K ^ t * (1 + x ^ 2) ^ t := by
      rw [← Real.mul_rpow hK0 (one_add_sq_pos x).le]
      exact Real.rpow_le_rpow (sq_nonneg _) (sq_le c' d' x) ht0
    have h2 : (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) = (1 + x ^ 2)⁻¹ := by
      rw [← Real.rpow_add (one_add_sq_pos x), ← Real.rpow_neg_one]
      congr 1; rw [ht]; ring
    calc ((c' * x + d') ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2))
        ≤ K ^ t * (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (one_add_sq_pos x).le _)
      _ = K ^ t * (1 + x ^ 2)⁻¹ := by rw [mul_assoc, h2]

theorem jacobian_identity (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) {σ : ℝ} (hσ : 1 / 2 < σ) (x : ℝ) :
    (((|a * d - b * c| / (a + x * c) ^ 2 : ℝ)) : ℂ)
        * (((((-c / Real.sqrt |a * d - b * c|) * ((b + x * d) / (a + x * c)) + d / Real.sqrt |a * d - b * c|) ^ 2)
              ^ (σ - 1 / 2) : ℝ) : ℂ)
      = (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))) := by
  set D : ℝ := |a * d - b * c| with hD
  have hD0 : 0 < D := abs_pos.mpr hdet
  set t : ℝ := a + x * c with ht
  by_cases ht0 : t = 0
  · have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [ht0]
    have h1 : ((|(0 : ℝ)| : ℝ) : ℂ) = 0 := by simp
    rw [h1, Complex.zero_cpow hne, mul_zero]
    simp
  · have hs : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hW : ((-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D) ^ 2 = D / t ^ 2 := by
      have e1 : (-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D = (a * d - b * c) / (t * Real.sqrt D) := by
        field_simp
        rw [ht]; ring
      rw [e1, div_pow, mul_pow, Real.sq_sqrt hD0.le]
      have h2 : (a * d - b * c) ^ 2 = D ^ 2 := by rw [hD, sq_abs]
      have hDne : D ≠ 0 := hD0.ne'
      rw [h2]
      field_simp
    rw [hW]
    have hq : 0 < D / t ^ 2 := div_pos hD0 (by positivity)
    rw [show ((σ : ℂ) + 1 / 2) = ((σ + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (-(2 * (σ : ℂ) + 1)) = ((-(2 * σ + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hD0.le, ← Complex.ofReal_cpow (abs_nonneg t), ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc D / t ^ 2 * (D / t ^ 2) ^ (σ - 1 / 2)
        = (D / t ^ 2) ^ (1 + (σ - 1 / 2)) := by rw [Real.rpow_add hq, Real.rpow_one]
      _ = (D / t ^ 2) ^ (σ + 1 / 2) := by congr 1; ring
      _ = D ^ (σ + 1 / 2) / (|t| ^ 2) ^ (σ + 1 / 2) := by rw [Real.div_rpow hD0.le (sq_nonneg t), sq_abs]
      _ = D ^ (σ + 1 / 2) * |t| ^ (-(2 * σ + 1)) := by
          rw [show (|t| ^ 2 : ℝ) = |t| ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
            ← Real.rpow_mul (abs_nonneg t), Real.rpow_neg (abs_nonneg t), div_eq_mul_inv]
          congr 2; ring_nf

theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (k : ℤ) :
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom k σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom k σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  constructor
  · refine ⟨∫ x : ℝ, (1 + x ^ 2)⁻¹, fun σ hσ _ => ?_⟩
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) integrable_inv_one_add_sq
      (ae_of_all _ (norm_atom_le k hσ.le))
  · have hD0 : 0 < |a * d - b * c| := abs_pos.mpr hdet
    have hs : Real.sqrt |a * d - b * c| ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hcd : (-c / Real.sqrt |a * d - b * c|) ≠ 0 ∨ (d / Real.sqrt |a * d - b * c|) ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not, div_eq_zero_iff, neg_eq_zero, div_eq_zero_iff] at h
      apply hdet
      rw [h.1.resolve_right hs, h.2.resolve_right hs]; ring
    have hA4 := AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
      (-c / Real.sqrt |a * d - b * c|) (d / Real.sqrt |a * d - b * c|) hcd k
    refine hA4.congr' (eventually_nhdsWithin_of_forall fun σ hσ => ?_)
    have hσ' : 1 / 2 < σ := hσ
    change ∫ x : ℝ, (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
        * atom k σ x = _
    have hsplit : (fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
        = fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x - atom k σ x := by
      funext x; push_cast; ring
    rw [hsplit, integral_sub (integrable_weighted _ _ k hσ') (integrable_atom k hσ'.le)]
    congr 1
    rw [← MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real a b c d hdet
      (fun u => (((((-c / Real.sqrt |a * d - b * c|) * u + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ)
        * atom k σ u)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← mul_assoc, jacobian_identity a b c d hdet hσ' x]

end AtomReal

/-! ### The complex place: the two-dimensional atom -/

namespace AtomComplex

def atom (a b m : ℕ) (σ : ℝ) (z : ℂ) : ℂ :=
  z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)

theorem one_add_sq_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

theorem exponent_cast (σ : ℝ) (m : ℕ) :
    (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2) = (((-(2 * σ + 1) - (m : ℝ) / 2 : ℝ)) : ℂ) := by
  push_cast; ring

theorem norm_atom (a b m : ℕ) (σ : ℝ) (z : ℂ) :
    ‖atom a b m σ z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2) := by
  rw [atom, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add, exponent_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos z), Complex.ofReal_re]

theorem norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h : ‖z‖ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg ‖z‖])
  calc ‖z‖ ^ n ≤ (Real.sqrt (1 + ‖z‖ ^ 2)) ^ n := pow_le_pow_left₀ (norm_nonneg _) h n
    _ = (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; ring

theorem norm_atom_le (a b m : ℕ) (habm : a + b ≤ m) (σ : ℝ) (z : ℂ) :
    ‖atom a b m σ z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
  have hX : 0 < 1 + ‖z‖ ^ 2 := one_add_sq_pos z
  have hX1 : 1 ≤ 1 + ‖z‖ ^ 2 := by linarith [sq_nonneg ‖z‖]
  rw [norm_atom]
  have h1 : ‖z‖ ^ (a + b) ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
    refine (norm_pow_le z (a + b)).trans (Real.rpow_le_rpow_of_exponent_le hX1 ?_)
    have : ((a + b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast habm
    linarith
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2)
      ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1) - (m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hX.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [← Real.rpow_add hX]; congr 1; ring

theorem norm_atom_le_two (a b m : ℕ) (habm : a + b ≤ m) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (z : ℂ) :
    ‖atom a b m σ z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) :=
  (norm_atom_le a b m habm σ z).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖z‖]) (by linarith))

theorem continuous_atom (a b m : ℕ) (σ : ℝ) : Continuous (atom a b m σ) := by
  unfold atom
  refine Continuous.mul (by fun_prop) ?_
  refine Continuous.cpow (by fun_prop) continuous_const fun z => ?_
  exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos z)

theorem integrable_bound (C : ℝ) : Integrable fun z : ℂ => C * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (this.congr (ae_of_all _ fun z => ?_)).const_mul C
  norm_num

theorem integrable_atom (a b m : ℕ) (habm : a + b ≤ m) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Integrable (atom a b m σ) :=
  (integrable_bound 1).mono' (continuous_atom a b m σ).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa only [one_mul] using norm_atom_le_two a b m habm hσ z)

theorem normSq_le (c' d' z : ℂ) : ‖c' * z + d'‖ ^ 2 ≤ (‖c'‖ ^ 2 + ‖d'‖ ^ 2) * (1 + ‖z‖ ^ 2) := by
  have h1 : ‖c' * z + d'‖ ≤ ‖c'‖ * ‖z‖ + ‖d'‖ := by
    refine (norm_add_le _ _).trans ?_; rw [norm_mul]
  have h2 : 0 ≤ ‖c'‖ * ‖z‖ + ‖d'‖ := by positivity
  calc ‖c' * z + d'‖ ^ 2 ≤ (‖c'‖ * ‖z‖ + ‖d'‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (‖c'‖ ^ 2 + ‖d'‖ ^ 2) * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖c'‖ - ‖d'‖ * ‖z‖)]

theorem integrable_weighted (c' d' : ℂ) (a b m : ℕ) (habm : a + b ≤ m) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable fun z : ℂ => ((((‖c' * z + d'‖ ^ 2) ^ (2 * σ - 1) : ℝ)) : ℂ) * atom a b m σ z := by
  set t : ℝ := 2 * σ - 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set K : ℝ := ‖c'‖ ^ 2 + ‖d'‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine Integrable.mono' (integrable_bound (K ^ t)) ?_ (ae_of_all _ fun z => ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_atom a b m σ))
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.rpow_const (by fun_prop) fun z => Or.inr ht0
  · have hX : 0 < 1 + ‖z‖ ^ 2 := one_add_sq_pos z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]
    have h1 : (‖c' * z + d'‖ ^ 2) ^ t ≤ K ^ t * (1 + ‖z‖ ^ 2) ^ t := by
      rw [← Real.mul_rpow hK0 hX.le]
      exact Real.rpow_le_rpow (sq_nonneg _) (normSq_le c' d' z) ht0
    have h2 : (1 + ‖z‖ ^ 2) ^ t * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) = (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hX]
      congr 1; rw [ht]; ring
    calc (‖c' * z + d'‖ ^ 2) ^ t * ‖atom a b m σ z‖
        ≤ K ^ t * (1 + ‖z‖ ^ 2) ^ t * (1 + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) :=
          mul_le_mul h1 (norm_atom_le a b m habm σ z) (norm_nonneg _)
            (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hX.le _))
      _ = K ^ t * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)) := by rw [mul_assoc, h2]

theorem jacobian_identity (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    ((‖a * d - b * c‖ ^ 2 / ‖a + z * c‖ ^ 4 : ℝ) : ℂ)
        * ((((‖(-c / ((Real.sqrt ‖a * d - b * c‖ : ℝ) : ℂ)) * ((b + z * d) / (a + z * c))
              + d / ((Real.sqrt ‖a * d - b * c‖ : ℝ) : ℂ)‖ ^ 2) ^ (2 * σ - 1) : ℝ)) : ℂ)
      = (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)
          * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))) := by
  set N : ℝ := ‖a * d - b * c‖ with hN
  have hN0 : 0 < N := norm_pos_iff.mpr hdet
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  set P : ℂ := a + z * c with hP
  have hexp1 : ((σ : ℂ) + 1 / 2) = ((σ + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hexp2 : (-(2 * (σ : ℂ) + 1)) = ((-(2 * σ + 1) : ℝ) : ℂ) := by push_cast; ring
  by_cases hP0 : P = 0
  · have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [hP0, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, Complex.ofReal_zero,
      zero_mul]
    rw [Complex.zero_cpow hne, mul_zero]
  · have hPn : 0 < ‖P‖ := norm_pos_iff.mpr hP0
    have hW : ‖(-c / (s : ℂ)) * ((b + z * d) / P) + d / (s : ℂ)‖ ^ 2 = N / ‖P‖ ^ 2 := by
      have e1 : (-c / (s : ℂ)) * ((b + z * d) / P) + d / (s : ℂ) = (a * d - b * c) / ((s : ℂ) * P) := by
        field_simp
        rw [hP]; ring
      rw [e1, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, ← hN, div_pow, mul_pow,
        hs, Real.sq_sqrt hN0.le]
      field_simp
    rw [hW]
    have hq : 0 < N / ‖P‖ ^ 2 := div_pos hN0 (by positivity)
    rw [hexp1, hexp2, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have h4 : N ^ 2 / ‖P‖ ^ 4 = (N / ‖P‖ ^ 2) ^ (2 : ℝ) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    calc N ^ 2 / ‖P‖ ^ 4 * (N / ‖P‖ ^ 2) ^ (2 * σ - 1)
        = (N / ‖P‖ ^ 2) ^ ((2 : ℝ) + (2 * σ - 1)) := by rw [h4, Real.rpow_add hq]
      _ = (N / ‖P‖ ^ 2) ^ (2 * σ + 1) := by congr 1; ring
      _ = N ^ (2 * σ + 1) / (‖P‖ ^ 2) ^ (2 * σ + 1) := by rw [Real.div_rpow hN0.le (sq_nonneg _)]
      _ = (N ^ 2) ^ (σ + 1 / 2) * (‖P‖ ^ 2) ^ (-(2 * σ + 1)) := by
          rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
            ← Real.rpow_mul hN0.le, Real.rpow_neg (sq_nonneg _), div_eq_mul_inv]
          congr 2; ring

theorem main (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (habm : a₀ + b₀ ≤ m) :
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ z, atom a₀ b₀ m σ z‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ z : ℂ, (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)
              * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom a₀ b₀ m σ ((b + z * d) / (a + z * c)))
          - ∫ z : ℂ, atom a₀ b₀ m σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  constructor
  · refine ⟨∫ z : ℂ, 1 * (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ)), fun σ hσ _ => ?_⟩
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun z => norm_nonneg _) (integrable_bound 1)
      (ae_of_all _ fun z => by simpa only [one_mul] using norm_atom_le_two a₀ b₀ m habm hσ.le z)
  · set s : ℝ := Real.sqrt ‖a * d - b * c‖ with hs
    have hN0 : 0 < ‖a * d - b * c‖ := norm_pos_iff.mpr hdet
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN0).ne'
    have hcd : (-c / (s : ℂ)) ≠ 0 ∨ (d / (s : ℂ)) ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not, div_eq_zero_iff, neg_eq_zero, div_eq_zero_iff] at h
      apply hdet
      rw [h.1.resolve_right hsC, h.2.resolve_right hsC]; ring
    have hA4 := AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half
      (-c / (s : ℂ)) (d / (s : ℂ)) hcd a₀ b₀ m habm
    refine hA4.congr' (eventually_nhdsWithin_of_forall fun σ hσ => ?_)
    have hσ' : 1 / 2 < σ := hσ
    change ∫ z : ℂ, ((((‖(-c / (s : ℂ)) * z + d / (s : ℂ)‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
        * atom a₀ b₀ m σ z = _
    have hsplit : (fun z : ℂ => ((((‖(-c / (s : ℂ)) * z + d / (s : ℂ)‖ ^ 2) ^ (2 * σ - 1) - 1 : ℝ)) : ℂ)
          * atom a₀ b₀ m σ z)
        = fun z : ℂ => ((((‖(-c / (s : ℂ)) * z + d / (s : ℂ)‖ ^ 2) ^ (2 * σ - 1) : ℝ)) : ℂ)
          * atom a₀ b₀ m σ z - atom a₀ b₀ m σ z := by
      funext z; push_cast; ring
    rw [hsplit, integral_sub (integrable_weighted _ _ a₀ b₀ m habm hσ') (integrable_atom a₀ b₀ m habm hσ'.le)]
    congr 1
    rw [← MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex a b c d hdet
      (fun u => ((((‖(-c / (s : ℂ)) * u + d / (s : ℂ)‖ ^ 2) ^ (2 * σ - 1) : ℝ)) : ℂ) * atom a₀ b₀ m σ u)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [← mul_assoc, jacobian_identity a b c d hdet hσ' z]

end AtomComplex

/-! ### The two headlines -/

theorem bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  exact AtomReal.main a b c d _hdet k

theorem bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ z, atom σ z‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ z : ℂ, (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + z * d) / (a + z * c)))
          - ∫ z : ℂ, atom σ z)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  exact AtomComplex.main a b c d _hdet a₀ b₀ m _habm

end AutomorphicForm.LocalIntertwining

end
