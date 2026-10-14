/-
The `CellPeriods` development: an open star-convex neighbourhood of `R.q`
inside any open set containing the compact radial region `R.K`.

The engine behind `AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset` --
the cell chart `U`, the polar-argument lemmas (`periodic_apply_arg`,
`r_arg_neg`, `continuousAt_r_arg`), the bounds `exists_bounds`, the scaled
star-shaped sets `Kscaled` with their openness, star-convexity, containment and
thickening conclusions, and `exists_Kscaled_subset`. Transcribed verbatim from the
pinned FLT `aa2d8b3` solution file; the pin's single `private` helper (`U`) stays
`private` and every pin-public declaration stays public. Public but unwired
(tier 3): the headline lives in
`FLTForHuman/AlgebraicCurve/RadialRegion/IsOpenStarConvex.lean`.

Namespace mapping. The pin wraps the development in the
`P2MW.S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset` namespace and
then in its own `AlgebraicCurve` namespace; that wrapper is dropped and the
redundant `AlgebraicCurve` segment is elided (the port root already ends in it), so
the pin's `...AlgebraicCurve.CellPeriods` becomes
`AlgebraicCurve.RadialRegion.CellPeriods` and its `...AlgebraicCurve.Cell`
becomes `AlgebraicCurve.RadialRegion.Cell`. The pin's `private def
_root_.AlgebraicCurve.Cell.U` is kept verbatim at its absolute name -- the
`hU`/`hKU`/`hUt` statements use the dot notation `C.U`, which resolves through
the `Cell` type's own namespace. The pin's `p2m_export` calls are dropped and its
`p2m_open` calls become ordinary `open` commands (the wrapper-qualified token is
elided).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean>
-/
import FLTForHuman.AlgebraicCurve.Defs.CellDissection
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

namespace AlgebraicCurve.RadialRegion


namespace Cell
open AlgebraicCurve.Cell AlgebraicCurve
variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
  [ChartedSpace ℂ (Place ℂ F)]

private def _root_.AlgebraicCurve.Cell.U (C : Cell F) : Set ℂ := C.ζ.target
-- pin: hU (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:16)
theorem hU (C : Cell F) : IsOpen C.U := C.ζ.open_target
-- pin: hKU (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:17)
theorem hKU (C : Cell F) : C.R.K ⊆ C.U := C.hKt
-- pin: hUt (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:18)
theorem hUt (C : Cell F) : C.U ⊆ C.ζ.target := fun _ h => h
end Cell

section Part_book_cell

namespace CellPeriods

open Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve
open scoped Real Topology Interval Manifold ContDiff

-- pin: periodic_apply_arg (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:28)
theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Loop

variable {c : ℂ} {r : ℝ → ℝ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)

end Loop

section Analysis

end Analysis

section Weight

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

end Weight

section CellIdentity

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end CellIdentity

end CellPeriods

end Part_book_cell

section Part_skel

namespace CellPeriods

open Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

-- pin: K_eq_image (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:87)
theorem K_eq_image : R.K = (fun p : ℝ × ℝ => R.q + ((p.2 * R.r p.1 : ℝ) : ℂ) * exp (p.1 * I)) ''
    (Icc 0 (2 * π) ×ˢ Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    have hz' : ‖z - R.q‖ ≤ R.r (arg (z - R.q)) := hz
    set φ₀ := arg (z - R.q) with hφ₀
    have hr0 : 0 < R.r φ₀ := R.hpos φ₀
    set t : ℝ := ‖z - R.q‖ / R.r φ₀ with ht
    have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) hr0.le
    have ht1 : t ≤ 1 := (div_le_one hr0).2 hz'

    set φ : ℝ := if φ₀ < 0 then φ₀ + 2 * π else φ₀ with hφ
    have hφI : φ ∈ Icc 0 (2 * π) := by
      have h1 := neg_pi_lt_arg (z - R.q)
      have h2 := arg_le_pi (z - R.q)
      simp only [hφ]
      split_ifs with h
      · constructor <;> linarith [Real.pi_pos]
      · constructor <;> linarith [Real.pi_pos]
    have hrφ : R.r φ = R.r φ₀ := by
      simp only [hφ]; split_ifs
      · exact R.hper φ₀
      · rfl
    have heφ : exp (φ * I) = exp (φ₀ * I) := by
      simp only [hφ]; split_ifs
      · rw [show ((φ₀ + 2 * π : ℝ) : ℂ) * I = φ₀ * I + 2 * π * I by push_cast; ring,
          exp_add, exp_two_pi_mul_I, mul_one]
      · rfl
    refine ⟨(φ, t), ⟨hφI, ht0, ht1⟩, ?_⟩
    show R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) = z
    rw [hrφ, heφ, ht, div_mul_cancel₀ _ hr0.ne']
    have := norm_mul_exp_arg_mul_I (z - R.q)
    linear_combination this
  · rintro ⟨⟨φ, t⟩, ⟨hφ, ht0, ht1⟩, rfl⟩
    dsimp only at hφ ht0 ht1
    show ‖R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q‖ ≤
      R.r (arg (R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q))
    rw [add_sub_cancel_left]
    have hr0 : 0 < R.r φ := R.hpos φ
    rcases ht0.lt_or_eq with ht | ht
    · have hpos : 0 < t * R.r φ := mul_pos ht hr0
      rw [periodic_apply_arg R.hper hpos, norm_mul, norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith
    · rw [← ht]
      simp only [zero_mul, ofReal_zero, norm_zero]
      exact (R.hpos _).le

-- pin: isCompact_K (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:136)
theorem isCompact_K : IsCompact R.K := by
  rw [K_eq_image]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  have hc := R.hcont
  fun_prop

end Region

section CellTop

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

end CellTop

section Flows

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Flows

end CellPeriods

end Part_skel

section Part_prims

namespace CellPeriods

open Complex Set Filter AlgebraicCurve Metric
open scoped Real Topology Manifold ContDiff

section RArg

variable {r : ℝ → ℝ} (hcont : Continuous r) (hper : Function.Periodic r (2 * π))

include hper in
-- pin: r_arg_neg (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:186)
theorem r_arg_neg (z : ℂ) (hz : z ≠ 0) : r (arg z) = r (arg (-z) + π) := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [arg_neg_eq_arg_add_pi_of_im_neg h, add_assoc, show (π + π : ℝ) = 2 * π by ring, hper]
  ·
    have hre : z.re ≠ 0 := by
      intro h'
      exact hz (Complex.ext h' h)
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
    rcases hre.lt_or_gt with hr | hr
    · rw [hz', ← ofReal_neg, arg_ofReal_of_neg hr, arg_ofReal_of_nonneg (by linarith), zero_add]
    · rw [hz', ← ofReal_neg, arg_ofReal_of_nonneg hr.le, arg_ofReal_of_neg (by linarith),
        show (π + π : ℝ) = 0 + 2 * π by ring, hper]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos h, sub_add_cancel]

include hcont hper in
-- pin: continuousAt_r_arg (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:201)
theorem continuousAt_r_arg {z : ℂ} (hz : z ≠ 0) : ContinuousAt (fun w => r (arg w)) z := by
  rcases mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · exact hcont.continuousAt.comp (continuousAt_arg h)
  · have heq : (fun w => r (arg w)) =ᶠ[𝓝 z] fun w => r (arg (-w) + π) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact r_arg_neg hper w hw
    refine (ContinuousAt.congr ?_ heq.symm)
    have h1 : ContinuousAt (fun w : ℂ => arg (-w)) z :=
      (continuousAt_arg h).comp (continuous_neg.continuousAt)
    exact hcont.continuousAt.comp (h1.add continuousAt_const)

include hcont hper in

-- pin: exists_bounds (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:214)
theorem exists_bounds (hpos : ∀ φ, 0 < r φ) :
    ∃ m M : ℝ, 0 < m ∧ (∀ φ, m ≤ r φ) ∧ ∀ φ, r φ ≤ M := by
  have hc : IsCompact (r '' Icc 0 (2 * π)) := isCompact_Icc.image hcont
  have hne : (r '' Icc 0 (2 * π)).Nonempty := ⟨r 0, 0, ⟨le_rfl, by positivity⟩, rfl⟩
  obtain ⟨m, ⟨φm, hφm, rfl⟩, hm⟩ := hc.exists_isMinOn hne continuousOn_id
  obtain ⟨M, ⟨φM, hφM, rfl⟩, hM⟩ := hc.exists_isMaxOn hne continuousOn_id
  have hred : ∀ φ, ∃ φ' ∈ Icc 0 (2 * π), r φ' = r φ := by
    intro φ
    refine ⟨toIcoMod Real.two_pi_pos 0 φ, ?_, ?_⟩
    · have := toIcoMod_mem_Ico Real.two_pi_pos 0 φ
      rw [zero_add] at this
      exact ⟨this.1, this.2.le⟩
    · rw [toIcoMod]
      exact hper.sub_zsmul_eq _
  refine ⟨r φm, r φM, hpos _, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨φ', hφ', h⟩ := hred φ
    rw [← h]; exact hm ⟨φ', hφ', rfl⟩
  · obtain ⟨φ', hφ', h⟩ := hred φ
    rw [← h]; exact hM ⟨φ', hφ', rfl⟩

end RArg

section Scaled

variable (R : AlgebraicCurve.RadialRegion)

-- pin: Kscaled (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:240)
def Kscaled (s : ℝ) : Set ℂ := {z | ‖z - R.q‖ < s * R.r (arg (z - R.q))}

-- pin: isOpen_Kscaled (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:242)
theorem isOpen_Kscaled {s : ℝ} (hs : 0 < s) : IsOpen (Kscaled R s) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ‖z - R.q‖ < s * R.r (arg (z - R.q)) := hz
  by_cases hzq : z = R.q
  ·
    obtain ⟨m, M, hm, hmr, -⟩ := exists_bounds R.hcont R.hper R.hpos
    have : ball R.q (s * m) ⊆ Kscaled R s := by
      intro w hw
      show ‖w - R.q‖ < s * R.r (arg (w - R.q))
      rw [mem_ball, dist_eq_norm] at hw
      exact hw.trans_le (by nlinarith [hmr (arg (w - R.q))])
    rw [hzq]
    exact Filter.mem_of_superset (ball_mem_nhds _ (mul_pos hs hm)) this
  ·
    have hne : z - R.q ≠ 0 := sub_ne_zero.2 hzq
    have hc : ContinuousAt (fun w => s * R.r (arg (w - R.q)) - ‖w - R.q‖) z := by
      have h0 : ContinuousAt (fun w : ℂ => w - R.q) z := continuousAt_id.sub continuousAt_const
      have h1 : ContinuousAt (fun w : ℂ => R.r (arg (w - R.q))) z :=
        ContinuousAt.comp (g := fun w => R.r (arg w)) (continuousAt_r_arg R.hcont R.hper hne) h0
      exact (continuousAt_const.mul h1).sub ((continuousAt_id.sub continuousAt_const).norm)
    have hpos : 0 < s * R.r (arg (z - R.q)) - ‖z - R.q‖ := by linarith
    have := hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    refine Filter.mem_of_superset this fun w hw => ?_
    show ‖w - R.q‖ < s * R.r (arg (w - R.q))
    have : 0 < s * R.r (arg (w - R.q)) - ‖w - R.q‖ := hw
    linarith

-- pin: q_mem_Kscaled (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:270)
theorem q_mem_Kscaled {s : ℝ} (hs : 0 < s) : R.q ∈ Kscaled R s := by
  show ‖R.q - R.q‖ < s * R.r (arg (R.q - R.q))
  rw [sub_self, norm_zero]
  exact mul_pos hs (R.hpos _)

-- pin: starConvex_Kscaled (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:275)
theorem starConvex_Kscaled {s : ℝ} (hs : 0 < s) : StarConvex ℝ R.q (Kscaled R s) := by
  intro z hz a t ha ht hat
  show ‖a • R.q + t • z - R.q‖ < s * R.r (arg (a • R.q + t • z - R.q))
  have hz' : ‖z - R.q‖ < s * R.r (arg (z - R.q)) := hz
  have heq : a • R.q + t • z - R.q = (t : ℂ) * (z - R.q) := by
    have ha' : a = 1 - t := by linarith
    rw [ha']
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [heq]
  rcases ht.lt_or_eq with ht0 | ht0
  · rw [arg_real_mul _ ht0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have ht1 : t ≤ 1 := by linarith
    have hr0 : 0 < s * R.r (arg (z - R.q)) := mul_pos hs (R.hpos _)
    nlinarith [norm_nonneg (z - R.q)]
  · rw [← ht0]
    simp only [ofReal_zero, zero_mul, norm_zero]
    exact mul_pos hs (R.hpos _)

-- pin: K_subset_Kscaled (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:295)
theorem K_subset_Kscaled {s : ℝ} (hs : 1 < s) : R.K ⊆ Kscaled R s := by
  intro z hz
  have hz' : ‖z - R.q‖ ≤ R.r (arg (z - R.q)) := hz
  show ‖z - R.q‖ < s * R.r (arg (z - R.q))
  have := R.hpos (arg (z - R.q))
  nlinarith

-- pin: Kscaled_subset_thickening (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:302)
theorem Kscaled_subset_thickening {s M : ℝ} (hs : 1 < s) (hM : ∀ φ, R.r φ ≤ M) {δ : ℝ}
    (hδ : (s - 1) * M < δ) : Kscaled R s ⊆ thickening δ R.K := by
  intro z hz
  have hz' : ‖z - R.q‖ < s * R.r (arg (z - R.q)) := hz
  rw [mem_thickening_iff]
  by_cases hzK : z ∈ R.K
  · refine ⟨z, hzK, ?_⟩
    rw [dist_self]
    have hM0 : 0 ≤ M := (R.hpos 0).le.trans (hM 0)
    nlinarith
  ·
    have hzK' : R.r (arg (z - R.q)) < ‖z - R.q‖ := by
      by_contra h
      exact hzK (not_lt.1 h)
    have hn0 : 0 < ‖z - R.q‖ := (R.hpos _).trans hzK'
    set ρ : ℝ := R.r (arg (z - R.q)) / ‖z - R.q‖ with hρ
    have hρ0 : 0 < ρ := div_pos (R.hpos _) hn0
    set z' : ℂ := R.q + (ρ : ℂ) * (z - R.q) with hz'def
    have harg : arg (z' - R.q) = arg (z - R.q) := by
      rw [hz'def, add_sub_cancel_left, arg_real_mul _ hρ0]
    have hnorm : ‖z' - R.q‖ = R.r (arg (z - R.q)) := by
      rw [hz'def, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0, hρ, div_mul_cancel₀ _ hn0.ne']
    refine ⟨z', ?_, ?_⟩
    · show ‖z' - R.q‖ ≤ R.r (arg (z' - R.q))
      rw [harg, hnorm]
    · rw [dist_eq_norm]
      have hzz : z - z' = ((1 - ρ : ℝ) : ℂ) * (z - R.q) := by
        rw [hz'def]; push_cast; ring
      have hρ1 : ρ ≤ 1 := (div_le_one hn0).2 hzK'.le
      rw [hzz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h1 : (1 - ρ) * ‖z - R.q‖ = ‖z - R.q‖ - R.r (arg (z - R.q)) := by
        rw [hρ]; field_simp
      rw [h1]
      have hM' := hM (arg (z - R.q))
      have hr0 := R.hpos (arg (z - R.q))
      nlinarith

-- pin: exists_Kscaled_subset (S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean:340)
theorem exists_Kscaled_subset {T : Set ℂ} (hT : IsOpen T) (hKT : R.K ⊆ T) :
    ∃ s : ℝ, 1 < s ∧ Kscaled R s ⊆ T := by
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_K R).exists_thickening_subset_open hT hKT
  obtain ⟨m, M, hm, hmr, hM⟩ := exists_bounds R.hcont R.hper R.hpos
  have hM0 : 0 < M := hm.trans_le ((hmr 0).trans (hM 0))
  have hs1 : 1 < 1 + δ / (2 * M) := by
    have := div_pos hδ (mul_pos two_pos hM0); linarith
  refine ⟨1 + δ / (2 * M), hs1, ?_⟩
  refine (Kscaled_subset_thickening R hs1 hM ?_).trans hthick
  rw [add_sub_cancel_left, div_mul_eq_mul_div, mul_comm δ, mul_div_assoc]
  have : (M : ℝ) * (δ / (2 * M)) = δ / 2 := by field_simp
  linarith [this]

end Scaled

section Prims

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Prims

end CellPeriods

end Part_prims

end AlgebraicCurve.RadialRegion
