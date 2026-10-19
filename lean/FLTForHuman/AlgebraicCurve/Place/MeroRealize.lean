/-
The meromorphic realisation of a place as a Laurent series, and the valuation subring
that turns that realisation into a chart: the engine under the third `localParam` leaf
of the Deligne–Serre cone. Given a degree-one place `v` with a prescribed uniformiser
`t`, the pin reads a formal power series off a coefficient sequence (`fps`, `S`),
extends the reading to a Hahn/Laurent series (`SL`) and proves the ring laws and the
order formula `meromorphicOrderAt (SL L) 0 = L.order`; `polyToLaurent` and
`isAlgebraic_of_apply_eq_ofPowerSeries` then supply the coefficient growth
(`bdd_powerSeriesPart`, through LP3b's majorant), the valuation subring `RSet`/`Rfield`
collects the elements whose realisation is meromorphic near `0`, and `main` assembles
the chart `G` with `G (f + g) = G f + G g`, `G (f * g) = G f * G g`, `G (algebraMap c) = c`,
`G t = id` and `meromorphicOrderAt (G f) 0 = v.ord f`. Statements are transcribed
verbatim from the pinned FLT proof (`anthropics/fermats-last-theorem`, `aa2d8b3`);
only proof bodies are adapted to mathlib `v4.34.0`.

The pin's prelim copy is imported, not restated — `Place.adicValuation_le_one_of_mem`,
`Place.adicValuation_eq_exp_neg_ord` (`Defs/Repartitions.lean`);
`Place.mem_of_ord_nonneg`, `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`);
`Place.evalAt_algebraMap`, `Place.evalAt_mul` (`Defs/PlaceEvaluation.lean`);
`Place.evalAt_zero`, `Place.evalAt_add` (`Defs/PlaceCalculus.lean`); and the rest of the
`Place` calculus in `Place/OrdCalculus.lean`. Also deliberately *not* copied: the pin's
file-wide `attribute [-instance]` (8 declarations) and `attribute [-simp]` (17 lemmas)
prelude, which exists because the pin's own `S_` files re-declare those instances and
coefficient lemmas; the port carries each of them exactly once, so no blanket narrowing
is needed. Role: tier 1, the engine half of the set — the internal node
`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex` — with 60 public
declarations (all but the `private le_radius_of_bound`), consumed by
`Place/LocalParamDatum.lean`.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean
-/
import FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.AlgebraicCurve.Place.TranscendentalOfOrdNeZero
import FLTForHuman.Analysis.PowerSeries.EisensteinAlgSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

noncomputable section

open Filter Topology Metric FormalMultilinearSeries Polynomial

namespace AlgebraicCurve

namespace Place

namespace MeroRealize

def Bdd (q : PowerSeries ℂ) : Prop :=
  ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n

theorem bdd_of_bound {q : PowerSeries ℂ} {C R : ℝ} (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) :
    Bdd q := by
  refine ⟨|C|, max |R| 1, abs_nonneg C, le_max_right _ _, fun n => (h n).trans ?_⟩
  calc C * R ^ n ≤ |C * R ^ n| := le_abs_self _
    _ = |C| * |R| ^ n := by rw [abs_mul, abs_pow]
    _ ≤ |C| * (max |R| 1) ^ n := by
        gcongr
        exact le_max_left _ _

theorem Bdd.zero : Bdd (0 : PowerSeries ℂ) :=
  ⟨0, 1, le_rfl, le_rfl, fun n => by simp⟩

theorem bound_mono {q : PowerSeries ℂ} {C R R' : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hRR' : R ≤ R')
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) (n : ℕ) :
    ‖PowerSeries.coeff n q‖ ≤ C * R' ^ n :=
  (h n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRR' n) hC)

theorem bound_X_pow_mul {q : PowerSeries ℂ} {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) (m n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.X ^ m * q)‖ ≤ C * R ^ n := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hmn
  · refine (h (n - m)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_right₀ hR (Nat.sub_le n m)
  · simpa using mul_nonneg hC (pow_nonneg (zero_le_one.trans hR) n)

def fps (q : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (fun n => PowerSeries.coeff n q)

def S (q : PowerSeries ℂ) : ℂ → ℂ := (fps q).sum

theorem S_eq_ofScalarsSum (q : PowerSeries ℂ) :
    S q = ofScalarsSum (E := ℂ) (fun n => PowerSeries.coeff n q) := rfl

theorem S_apply (q : PowerSeries ℂ) (u : ℂ) :
    S q u = ∑' n, PowerSeries.coeff n q * u ^ n := by
  rw [S_eq_ofScalarsSum, ofScalarsSum_eq_tsum]
  simp [smul_eq_mul]

theorem S_at_zero (q : PowerSeries ℂ) : S q 0 = PowerSeries.coeff 0 q := by
  rw [S_eq_ofScalarsSum, ofScalarsSum_zero]
  simp

@[scoped simp] theorem S_zero (u : ℂ) : S 0 u = 0 := by simp [S_apply]

theorem S_C (c u : ℂ) : S (PowerSeries.C c) u = c := by
  rw [S_apply, tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_C, hn]]
  simp

@[scoped simp] theorem S_one (u : ℂ) : S 1 u = 1 := by
  rw [← map_one PowerSeries.C, S_C]

theorem S_X_pow_mul (m : ℕ) (q : PowerSeries ℂ) (u : ℂ) :
    S (PowerSeries.X ^ m * q) u = u ^ m * S q u := by
  rw [S_apply, S_apply, ← tsum_mul_left]
  have hinj : Function.Injective (fun j : ℕ => j + m) := add_left_injective m
  rw [← hinj.tsum_eq (f := fun n => PowerSeries.coeff n (PowerSeries.X ^ m * q) * u ^ n)]
  · congr 1
    funext j
    simp only [PowerSeries.coeff_X_pow_mul, pow_add]
    ring
  · intro n hn
    rw [Function.mem_support, PowerSeries.coeff_X_pow_mul'] at hn
    by_cases hmn : m ≤ n
    · exact ⟨n - m, by simp only; omega⟩
    · simp [hmn] at hn

theorem norm_term_le {q : PowerSeries ℂ} {C R : ℝ} (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n)
    (u : ℂ) (n : ℕ) : ‖PowerSeries.coeff n q * u ^ n‖ ≤ C * (R * ‖u‖) ^ n := by
  rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h n) (pow_nonneg (norm_nonneg _) _)

theorem summable_norm_of_bound {q : PowerSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) {u : ℂ} (hu : ‖u‖ < R⁻¹) :
    Summable fun n => ‖PowerSeries.coeff n q * u ^ n‖ := by
  have h1 : R * ‖u‖ < 1 := by
    have := mul_lt_mul_of_pos_left hu hR
    rwa [mul_inv_cancel₀ hR.ne'] at this
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le h u n) ?_
  exact (summable_geometric_of_lt_one (mul_nonneg hR.le (norm_nonneg _)) h1).mul_left C

private theorem _root_.AlgebraicCurve.Place.MeroRealize.le_radius_of_bound {q : PowerSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) :
    ((Real.toNNReal R⁻¹ : NNReal) : ENNReal) ≤ (fps q).radius := by
  refine (fps q).le_radius_of_bound C fun n => ?_
  rw [fps, ofScalars_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hR.le)]
  calc ‖PowerSeries.coeff n q‖ * R⁻¹ ^ n ≤ C * R ^ n * R⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg (inv_nonneg.mpr hR.le) _)
    _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, mul_one]

theorem hasFPowerSeriesOnBall_of_bound {q : PowerSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) :
    HasFPowerSeriesOnBall (S q) (fps q) 0 (Real.toNNReal R⁻¹) := by
  have hpos : (0 : ENNReal) < Real.toNNReal R⁻¹ := by simpa using inv_pos.mpr hR
  exact ((fps q).hasFPowerSeriesOnBall (hpos.trans_le (le_radius_of_bound hR h))).mono hpos
    (le_radius_of_bound hR h)

theorem analyticAt_S {q : PowerSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n q‖ ≤ C * R ^ n) {u : ℂ} (hu : ‖u‖ < R⁻¹) :
    AnalyticAt ℂ (S q) u := by
  refine (hasFPowerSeriesOnBall_of_bound hR h).analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
    coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr hR.le)]
  exact hu

theorem S_add {q₁ q₂ : PowerSeries ℂ} {u : ℂ}
    (h₁ : Summable fun n => ‖PowerSeries.coeff n q₁ * u ^ n‖)
    (h₂ : Summable fun n => ‖PowerSeries.coeff n q₂ * u ^ n‖) :
    S (q₁ + q₂) u = S q₁ u + S q₂ u := by
  rw [S_apply, S_apply, S_apply, ← Summable.tsum_add h₁.of_norm h₂.of_norm]
  congr 1
  funext n
  rw [map_add, add_mul]

theorem S_mul {q₁ q₂ : PowerSeries ℂ} {u : ℂ}
    (h₁ : Summable fun n => ‖PowerSeries.coeff n q₁ * u ^ n‖)
    (h₂ : Summable fun n => ‖PowerSeries.coeff n q₂ * u ^ n‖) :
    S (q₁ * q₂) u = S q₁ u * S q₂ u := by
  rw [S_apply, S_apply, S_apply, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h₁ h₂]
  congr 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

def SL (L : LaurentSeries ℂ) (u : ℂ) : ℂ := u ^ L.order * S L.powerSeriesPart u

@[scoped simp] theorem SL_zero (u : ℂ) : SL 0 u = 0 := by simp [SL]

theorem single_mul_single_one (a b : ℤ) :
    (HahnSeries.single a (1 : ℂ) * HahnSeries.single b 1 : LaurentSeries ℂ) =
      HahnSeries.single (a + b) 1 := by
  rw [HahnSeries.single_mul_single, mul_one]

theorem single_natCast_one_eq (m : ℕ) :
    (HahnSeries.single (m : ℤ) (1 : ℂ) : LaurentSeries ℂ) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.X ^ m) := by
  rw [HahnSeries.ofPowerSeries_X_pow]

theorem zpow_mul_S_eq_of_eq {k₁ k₂ : ℤ} {q₁ q₂ : PowerSeries ℂ}
    (h : (HahnSeries.single k₁ (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ q₁ : LaurentSeries ℂ) =
      HahnSeries.single k₂ 1 * HahnSeries.ofPowerSeries ℤ ℂ q₂) {u : ℂ} (hu : u ≠ 0) :
    u ^ k₁ * S q₁ u = u ^ k₂ * S q₂ u := by
  wlog hle : k₁ ≤ k₂ generalizing k₁ k₂ q₁ q₂
  · exact (this h.symm (le_of_not_ge hle)).symm
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hle)
  have hk₂ : k₂ = k₁ + m := by omega
  have h1 : HahnSeries.ofPowerSeries ℤ ℂ q₁ = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.X ^ m * q₂) := by
    have h2 := congrArg (fun L => HahnSeries.single (-k₁) (1 : ℂ) * L) h
    rw [← mul_assoc, ← mul_assoc, single_mul_single_one, single_mul_single_one, hk₂,
      neg_add_cancel, neg_add_cancel_left, single_natCast_one_eq, ← map_mul,
      HahnSeries.single_zero_one, one_mul] at h2
    exact h2
  rw [HahnSeries.ofPowerSeries_injective h1, S_X_pow_mul, hk₂, zpow_add₀ hu, zpow_natCast]
  ring

theorem SL_eq_of_eq_single_mul {L : LaurentSeries ℂ} {k : ℤ} {q : PowerSeries ℂ}
    (hL : L = HahnSeries.single k 1 * HahnSeries.ofPowerSeries ℤ ℂ q) {u : ℂ} (hu : u ≠ 0) :
    SL L u = u ^ k * S q u := by
  unfold SL
  apply zpow_mul_S_eq_of_eq _ hu
  rw [LaurentSeries.single_order_mul_powerSeriesPart, ← hL]

theorem SL_C {c u : ℂ} (hu : u ≠ 0) : SL (HahnSeries.C c) u = c := by
  have h : (HahnSeries.C c : LaurentSeries ℂ) =
      HahnSeries.single 0 1 * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C c) := by
    rw [HahnSeries.ofPowerSeries_C, HahnSeries.single_zero_one, one_mul]
  rw [SL_eq_of_eq_single_mul h hu, zpow_zero, one_mul, S_C]

theorem SL_single_one {u : ℂ} (hu : u ≠ 0) : SL (HahnSeries.single 1 (1 : ℂ)) u = u := by
  have h : (HahnSeries.single 1 (1 : ℂ) : LaurentSeries ℂ) =
      HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℂ 1 := by
    rw [RingHom.map_one, mul_one]
  rw [SL_eq_of_eq_single_mul h hu, zpow_one, S_one, mul_one]

theorem eq_single_mul_of_le (L : LaurentSeries ℂ) {k : ℤ} (hk : k ≤ L.order) :
    L = HahnSeries.single k 1 *
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.X ^ (L.order - k).toNat * L.powerSeriesPart) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart L]
  rw [map_mul, ← single_natCast_one_eq, ← mul_assoc, single_mul_single_one,
    Int.toNat_of_nonneg (sub_nonneg.mpr hk), add_sub_cancel]

theorem SL_add {L₁ L₂ : LaurentSeries ℂ} (h₁ : Bdd L₁.powerSeriesPart)
    (h₂ : Bdd L₂.powerSeriesPart) :
    ∃ r > 0, ∀ u : ℂ, u ≠ 0 → ‖u‖ < r → SL (L₁ + L₂) u = SL L₁ u + SL L₂ u := by
  obtain ⟨C₁, R₁, hC₁, hR₁, hb₁⟩ := h₁
  obtain ⟨C₂, R₂, hC₂, hR₂, hb₂⟩ := h₂
  set R := max R₁ R₂ with hRdef
  have hR : 1 ≤ R := hR₁.trans (le_max_left _ _)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine ⟨R⁻¹, inv_pos.mpr hR0, fun u hu hur => ?_⟩
  set k := min L₁.order L₂.order with hkdef
  set q₁ := PowerSeries.X ^ (L₁.order - k).toNat * L₁.powerSeriesPart with hq₁
  set q₂ := PowerSeries.X ^ (L₂.order - k).toNat * L₂.powerSeriesPart with hq₂
  have e₁ : L₁ = HahnSeries.single k 1 * HahnSeries.ofPowerSeries ℤ ℂ q₁ :=
    eq_single_mul_of_le L₁ (min_le_left _ _)
  have e₂ : L₂ = HahnSeries.single k 1 * HahnSeries.ofPowerSeries ℤ ℂ q₂ :=
    eq_single_mul_of_le L₂ (min_le_right _ _)
  have e : L₁ + L₂ = HahnSeries.single k 1 * HahnSeries.ofPowerSeries ℤ ℂ (q₁ + q₂) := by
    rw [map_add, mul_add, ← e₁, ← e₂]
  have hbq₁ : ∀ n, ‖PowerSeries.coeff n q₁‖ ≤ C₁ * R ^ n := fun n =>
    bound_X_pow_mul hC₁ hR (bound_mono hC₁ (zero_le_one.trans hR₁) (le_max_left _ _) hb₁) _ n
  have hbq₂ : ∀ n, ‖PowerSeries.coeff n q₂‖ ≤ C₂ * R ^ n := fun n =>
    bound_X_pow_mul hC₂ hR (bound_mono hC₂ (zero_le_one.trans hR₂) (le_max_right _ _) hb₂) _ n
  rw [SL_eq_of_eq_single_mul e hu, SL_eq_of_eq_single_mul e₁ hu, SL_eq_of_eq_single_mul e₂ hu,
    S_add (summable_norm_of_bound hR0 hbq₁ hur) (summable_norm_of_bound hR0 hbq₂ hur), mul_add]

theorem SL_mul {L₁ L₂ : LaurentSeries ℂ} (h₁ : Bdd L₁.powerSeriesPart)
    (h₂ : Bdd L₂.powerSeriesPart) :
    ∃ r > 0, ∀ u : ℂ, u ≠ 0 → ‖u‖ < r → SL (L₁ * L₂) u = SL L₁ u * SL L₂ u := by
  obtain ⟨C₁, R₁, hC₁, hR₁, hb₁⟩ := h₁
  obtain ⟨C₂, R₂, hC₂, hR₂, hb₂⟩ := h₂
  set R := max R₁ R₂ with hRdef
  have hR : 1 ≤ R := hR₁.trans (le_max_left _ _)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine ⟨R⁻¹, inv_pos.mpr hR0, fun u hu hur => ?_⟩
  have e : L₁ * L₂ = HahnSeries.single (L₁.order + L₂.order) 1 *
      HahnSeries.ofPowerSeries ℤ ℂ (L₁.powerSeriesPart * L₂.powerSeriesPart) := by
    conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart L₁,
      ← LaurentSeries.single_order_mul_powerSeriesPart L₂]
    rw [map_mul, ← single_mul_single_one]
    ring
  have hb₁' : ∀ n, ‖PowerSeries.coeff n L₁.powerSeriesPart‖ ≤ C₁ * R ^ n :=
    bound_mono hC₁ (zero_le_one.trans hR₁) (le_max_left _ _) hb₁
  have hb₂' : ∀ n, ‖PowerSeries.coeff n L₂.powerSeriesPart‖ ≤ C₂ * R ^ n :=
    bound_mono hC₂ (zero_le_one.trans hR₂) (le_max_right _ _) hb₂
  rw [SL_eq_of_eq_single_mul e hu,
    S_mul (summable_norm_of_bound hR0 hb₁' hur) (summable_norm_of_bound hR0 hb₂' hur),
    zpow_add₀ hu]
  unfold SL
  ring

theorem analyticAt_SL {L : LaurentSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n L.powerSeriesPart‖ ≤ C * R ^ n) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ‖u‖ < R⁻¹) : AnalyticAt ℂ (SL L) u := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => w ^ L.order) u := (analyticAt_id (𝕜 := ℂ)).fun_zpow hu0
  exact h1.mul (analyticAt_S hR h hu)

theorem meromorphicAt_SL_zero {L : LaurentSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n L.powerSeriesPart‖ ≤ C * R ^ n) :
    MeromorphicAt (SL L) 0 :=
  ((MeromorphicAt.id 0).zpow L.order).mul
    (analyticAt_S hR h (by simpa using inv_pos.mpr hR)).meromorphicAt

theorem meromorphicOn_SL {L : LaurentSeries ℂ} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n L.powerSeriesPart‖ ≤ C * R ^ n) :
    MeromorphicOn (SL L) (ball (0 : ℂ) R⁻¹) := by
  intro u hu
  rw [mem_ball_zero_iff] at hu
  by_cases hu0 : u = 0
  · subst hu0
    exact meromorphicAt_SL_zero hR h
  · exact (analyticAt_SL hR h hu0 hu).meromorphicAt

theorem meromorphicOrderAt_zpow_zero (k : ℤ) :
    meromorphicOrderAt (fun u : ℂ => u ^ k) 0 = k := by
  have h1 : (fun u : ℂ => u ^ k) = (fun u : ℂ => u - 0) ^ k := by
    funext u; simp
  rw [h1, meromorphicOrderAt_zpow (by have h__af := (MeromorphicAt.id (0 : ℂ)); simp at h__af ⊢; exact h__af),
    meromorphicOrderAt_id_sub_const]
  simp

theorem meromorphicOrderAt_SL {L : LaurentSeries ℂ} (hL : L ≠ 0) (hb : Bdd L.powerSeriesPart) :
    meromorphicOrderAt (SL L) 0 = L.order := by
  obtain ⟨C, R, hC, hR1, h⟩ := hb
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hS : AnalyticAt ℂ (S L.powerSeriesPart) 0 :=
    analyticAt_S hR h (by simpa using inv_pos.mpr hR)
  have hS0 : S L.powerSeriesPart 0 ≠ 0 := by
    rw [S_at_zero, LaurentSeries.powerSeriesPart_coeff, Int.ofNat_zero, add_zero]
    exact fun h0 => hL (HahnSeries.coeff_order_eq_zero.mp h0)
  have hfun : SL L = (fun u : ℂ => u ^ L.order) * S L.powerSeriesPart := by
    funext u; rfl
  have hz : MeromorphicAt (fun u : ℂ => u ^ L.order) 0 := (MeromorphicAt.id 0).zpow L.order
  rw [hfun, meromorphicOrderAt_mul hz hS.meromorphicAt,
    meromorphicOrderAt_zpow_zero, hS.meromorphicOrderAt_eq, (hS.analyticOrderAt_eq_zero).mpr hS0]
  simp

theorem eventually_nhdsNE_zero {P : ℂ → Prop} {r : ℝ} (hr : 0 < r)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r → P u) : ∀ᶠ u in 𝓝[≠] (0 : ℂ), P u := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with u hu hne
  exact h u hne (by simpa using hu)

theorem eventually_SL_ne_zero {L : LaurentSeries ℂ} (hL : L ≠ 0) (hb : Bdd L.powerSeriesPart) :
    ∀ᶠ u in 𝓝[≠] (0 : ℂ), SL L u ≠ 0 := by
  obtain ⟨C, R, hC, hR1, h⟩ := id hb
  have hR : 0 < R := zero_lt_one.trans_le hR1
  refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_SL_zero hR h)).mp ?_
  rw [meromorphicOrderAt_SL hL hb]
  exact WithTop.coe_ne_top

theorem eventuallyEq_of_nhdsNE_zero {g₁ g₂ : ℂ → ℂ} {ρ : ℝ} (h₁ : MeromorphicOn g₁ (ball (0 : ℂ) ρ))
    (h₂ : MeromorphicOn g₂ (ball (0 : ℂ) ρ)) (h0 : g₁ =ᶠ[𝓝[≠] (0 : ℂ)] g₂) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ρ) : g₁ =ᶠ[𝓝[≠] z] g₂ := by
  have hρ : 0 < ρ := Metric.pos_of_mem_ball hz
  have hd : MeromorphicOn (g₁ - g₂) (ball (0 : ℂ) ρ) := h₁.sub h₂
  have h0' : meromorphicOrderAt (g₁ - g₂) 0 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (h0.mono fun u hu => by simp [hu])
  have hz' : meromorphicOrderAt (g₁ - g₂) z = ⊤ := by
    by_contra hne
    exact hd.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected hz
      (mem_ball_self hρ) hne h0'
  exact (meromorphicOrderAt_eq_top_iff.mp hz').mono fun u hu => sub_eq_zero.mp (by simpa using hu)

section FunctionField

variable {F : Type*} [Field F] [Algebra ℂ F]

def polyToLaurent : ℂ[X] →+* LaurentSeries ℂ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp Polynomial.coeToPowerSeries.ringHom

theorem polyToLaurent_C (c : ℂ) : polyToLaurent (Polynomial.C c) = HahnSeries.C c := by
  simp [polyToLaurent, Polynomial.coeToPowerSeries.ringHom_apply]

theorem polyToLaurent_X : polyToLaurent (X : ℂ[X]) = HahnSeries.single 1 1 := by
  simp [polyToLaurent, Polynomial.coeToPowerSeries.ringHom_apply]

theorem single_one_inv (k : ℤ) :
    (HahnSeries.single k (1 : ℂ) : LaurentSeries ℂ)⁻¹ = HahnSeries.single (-k) 1 :=
  inv_eq_of_mul_eq_one_right (by rw [single_mul_single_one, add_neg_cancel, HahnSeries.single_zero_one])

theorem single_one_zpow (n : ℤ) :
    (HahnSeries.single 1 (1 : ℂ) : LaurentSeries ℂ) ^ n = HahnSeries.single n 1 := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  | negSucc m =>
    rw [zpow_negSucc, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, single_one_inv,
      Int.negSucc_eq, Nat.cast_succ]

variable (φ : F →ₐ[ℂ] LaurentSeries ℂ) {t : F}

variable {φ} in
theorem injective_φ : Function.Injective φ := fun _ _ h =>
  (φ : F →+* LaurentSeries ℂ).injective h

variable {φ} in
theorem apply_algebraMap (c : ℂ) : φ (algebraMap ℂ F c) = HahnSeries.C c := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply']
  simp

theorem comp_eq_polyToLaurent (htr : Transcendental ℂ t) (hφt : φ t = HahnSeries.single 1 1) :
    (φ : F →+* LaurentSeries ℂ).comp
        ((algebraMap (Algebra.adjoin ℂ ({t} : Set F)) F).comp
          (Polynomial.algEquivOfTranscendental ℂ t htr : ℂ[X] →+* Algebra.adjoin ℂ ({t} : Set F)))
      = polyToLaurent := by
  set A := Algebra.adjoin ℂ ({t} : Set F) with hA
  set e := Polynomial.algEquivOfTranscendental ℂ t htr with he
  apply Polynomial.ringHom_ext
  · intro c
    have h1 : (e : ℂ[X] →+* A) (Polynomial.C c) = algebraMap ℂ A c := by
      rw [Polynomial.C_eq_algebraMap]
      exact e.commutes c
    rw [polyToLaurent_C, RingHom.comp_apply, RingHom.comp_apply, h1,
      ← IsScalarTower.algebraMap_apply, RingHom.coe_coe, apply_algebraMap]
  · have h1 : (e : ℂ[X] →+* A) X = ⟨t, Algebra.self_mem_adjoin_singleton ℂ t⟩ :=
      Polynomial.algEquivOfTranscendental_apply_X ℂ t htr
    rw [polyToLaurent_X, RingHom.comp_apply, RingHom.comp_apply, h1, RingHom.coe_coe, ← hφt]
    rfl

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isAlgebraic_of_apply_eq_ofPowerSeries (htr : Transcendental ℂ t)
    (hφt : φ t = HahnSeries.single 1 1)
    [Algebra.IsAlgebraic (IntermediateField.adjoin ℂ ({t} : Set F)) F]
    {g : F} {q : PowerSeries ℂ} (hg : φ g = HahnSeries.ofPowerSeries ℤ ℂ q) :
    IsAlgebraic ℂ[X] q := by
  have halg : IsAlgebraic (Algebra.adjoin ℂ ({t} : Set F)) g :=
    (Algebra.IsAlgebraic.isAlgebraic_iff (Algebra.adjoin ℂ ({t} : Set F))
      (IntermediateField.adjoin ℂ ({t} : Set F))).mpr (Algebra.IsAlgebraic.isAlgebraic g)
  obtain ⟨p, hp0, hp⟩ := halg
  set e := Polynomial.algEquivOfTranscendental ℂ t htr with he
  set P : ℂ[X][X] := p.map (e.symm : Algebra.adjoin ℂ ({t} : Set F) →+* ℂ[X]) with hP
  have hPp : P.map (e : ℂ[X] →+* Algebra.adjoin ℂ ({t} : Set F)) = p := by
    rw [hP, Polynomial.map_map]
    conv_rhs => rw [← Polynomial.map_id (p := p)]
    congr 1
    ext a
    simp
  have hP0 : P ≠ 0 := by
    intro h
    apply hp0
    rw [← hPp, h, Polynomial.map_zero]
  refine ⟨P, hP0, ?_⟩
  have h1 : Polynomial.eval₂ ((algebraMap (Algebra.adjoin ℂ ({t} : Set F)) F).comp
      (e : ℂ[X] →+* Algebra.adjoin ℂ ({t} : Set F))) g P = 0 := by
    rw [← Polynomial.eval₂_map, hPp]
    exact hp
  have h2 : (φ : F →+* LaurentSeries ℂ) (Polynomial.eval₂ ((algebraMap (Algebra.adjoin ℂ
      ({t} : Set F)) F).comp (e : ℂ[X] →+* Algebra.adjoin ℂ ({t} : Set F))) g P) = 0 := by
    rw [h1, map_zero]
  rw [Polynomial.hom_eval₂, comp_eq_polyToLaurent φ htr hφt, RingHom.coe_coe, hg] at h2
  have h3 : HahnSeries.ofPowerSeries ℤ ℂ
      (Polynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom) q P) = 0 := by
    rw [Polynomial.hom_eval₂]
    exact h2
  have h4 : Polynomial.eval₂ (Polynomial.coeToPowerSeries.ringHom) q P = 0 :=
    HahnSeries.ofPowerSeries_injective (by rw [h3, map_zero])
  exact h4

theorem bdd_powerSeriesPart (htr : Transcendental ℂ t) (hφt : φ t = HahnSeries.single 1 1)
    [Algebra.IsAlgebraic (IntermediateField.adjoin ℂ ({t} : Set F)) F] (f : F) :
    Bdd (φ f).powerSeriesPart := by
  by_cases hf : φ f = 0
  · rw [hf, LaurentSeries.powerSeriesPart_zero]
    exact Bdd.zero
  set o := (φ f).order with ho
  set pp := (φ f).powerSeriesPart with hpp
  have hdec : HahnSeries.single o 1 * HahnSeries.ofPowerSeries ℤ ℂ pp = φ f :=
    LaurentSeries.single_order_mul_powerSeriesPart (φ f)
  have hg : φ (f * t ^ (-o)) = HahnSeries.ofPowerSeries ℤ ℂ pp := by
    rw [map_mul, map_zpow₀, hφt, single_one_zpow, ← hdec, mul_comm, ← mul_assoc,
      single_mul_single_one, neg_add_cancel, HahnSeries.single_zero_one, one_mul]
  obtain ⟨C, R, hCR⟩ := PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex _
    (isAlgebraic_of_apply_eq_ofPowerSeries φ htr hφt hg)
  exact bdd_of_bound hCR

variable (ρ : ℝ)

def RSet : Set F :=
  {f | ∃ g : ℂ → ℂ, MeromorphicOn g (ball (0 : ℂ) ρ) ∧ ∀ᶠ u in 𝓝[≠] (0 : ℂ), SL (φ f) u = g u}

variable {φ ρ}

theorem mem_RSet_of_bound {f : F} {C R : ℝ} (hR : 0 < R)
    (h : ∀ n, ‖PowerSeries.coeff n (φ f).powerSeriesPart‖ ≤ C * R ^ n) (hρ : ρ ≤ R⁻¹) :
    f ∈ RSet φ ρ :=
  ⟨SL (φ f), (meromorphicOn_SL hR h).mono_set (Metric.ball_subset_ball hρ),
    Eventually.of_forall fun _ => rfl⟩

theorem t_mem_RSet (hφt : φ t = HahnSeries.single 1 1) : t ∈ RSet φ ρ := by
  refine ⟨fun u => u, fun x _ => MeromorphicAt.id x, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [hφt]
  exact SL_single_one hu

theorem algebraMap_mem_RSet (c : ℂ) : algebraMap ℂ F c ∈ RSet φ ρ := by
  refine ⟨fun _ => c, MeromorphicOn.const c, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [apply_algebraMap]
  exact SL_C hu

section closure

variable (hb : ∀ f : F, Bdd (φ f).powerSeriesPart)
include hb

theorem add_mem_RSet {f₁ f₂ : F} (h₁ : f₁ ∈ RSet φ ρ) (h₂ : f₂ ∈ RSet φ ρ) :
    f₁ + f₂ ∈ RSet φ ρ := by
  obtain ⟨g₁, hg₁, he₁⟩ := h₁
  obtain ⟨g₂, hg₂, he₂⟩ := h₂
  obtain ⟨r, hr, hadd⟩ := SL_add (hb f₁) (hb f₂)
  refine ⟨g₁ + g₂, hg₁.add hg₂, ?_⟩
  filter_upwards [he₁, he₂, eventually_nhdsNE_zero hr hadd] with u hu₁ hu₂ hu
  rw [map_add, hu, hu₁, hu₂, Pi.add_apply]

theorem mul_mem_RSet {f₁ f₂ : F} (h₁ : f₁ ∈ RSet φ ρ) (h₂ : f₂ ∈ RSet φ ρ) :
    f₁ * f₂ ∈ RSet φ ρ := by
  obtain ⟨g₁, hg₁, he₁⟩ := h₁
  obtain ⟨g₂, hg₂, he₂⟩ := h₂
  obtain ⟨r, hr, hmul⟩ := SL_mul (hb f₁) (hb f₂)
  refine ⟨g₁ * g₂, hg₁.mul hg₂, ?_⟩
  filter_upwards [he₁, he₂, eventually_nhdsNE_zero hr hmul] with u hu₁ hu₂ hu
  rw [map_mul, hu, hu₁, hu₂, Pi.mul_apply]

theorem inv_mem_RSet {f : F} (h : f ∈ RSet φ ρ) : f⁻¹ ∈ RSet φ ρ := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [inv_zero]
  obtain ⟨g, hg, he⟩ := h
  refine ⟨g⁻¹, hg.inv, ?_⟩
  obtain ⟨r, hr, hmul⟩ := SL_mul (hb f⁻¹) (hb f)
  have hφf : φ f ≠ 0 := (map_ne_zero_iff φ injective_φ).mpr hf
  filter_upwards [self_mem_nhdsWithin, he, eventually_nhdsNE_zero hr hmul,
    eventually_SL_ne_zero hφf (hb f)] with u hu0 hu hm hne
  rw [Pi.inv_apply, ← hu]
  apply eq_inv_of_mul_eq_one_left
  rw [← hm, ← map_mul, inv_mul_cancel₀ hf, map_one, ← HahnSeries.C_one]
  exact SL_C hu0

variable (ρ) in

def Rfield : IntermediateField ℂ F where
  carrier := RSet φ ρ
  mul_mem' := mul_mem_RSet hb
  one_mem' := by simpa using algebraMap_mem_RSet (φ := φ) (ρ := ρ) 1
  add_mem' := add_mem_RSet hb
  zero_mem' := by simpa using algebraMap_mem_RSet (φ := φ) (ρ := ρ) 0
  algebraMap_mem' := algebraMap_mem_RSet
  inv_mem' := fun _ => inv_mem_RSet hb

theorem mem_Rfield {f : F} : f ∈ Rfield ρ hb ↔ f ∈ RSet φ ρ := Iff.rfl

theorem Rfield_eq_top {n : ℕ}
    (b : Module.Basis (Fin n) (IntermediateField.adjoin ℂ ({t} : Set F)) F)
    (htm : t ∈ RSet φ ρ) (hbi : ∀ i, b i ∈ RSet φ ρ) : Rfield ρ hb = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hK : IntermediateField.adjoin ℂ ({t} : Set F) ≤ Rfield ρ hb :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr htm)
  rw [← b.sum_repr f]
  refine sum_mem fun i _ => ?_
  show ((b.repr f i : IntermediateField.adjoin ℂ ({t} : Set F)) : F) * b i ∈ Rfield ρ hb
  exact mul_mem (hK (b.repr f i).2) (hbi i)

end closure

end FunctionField

set_option linter.style.haveILetI false in
theorem main (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] (v : Place ℂ F) (t : F) (ht : v.ord t = 1) :
    ∃ (ρ : ℝ) (G : F → ℂ → ℂ), 0 < ρ ∧
      (∀ f : F, MeromorphicOn (G f) (Metric.ball (0 : ℂ) ρ)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ,
        (∀ f g : F, G (f + g) =ᶠ[𝓝[≠] z] G f + G g) ∧
        (∀ f g : F, G (f * g) =ᶠ[𝓝[≠] z] G f * G g) ∧
        (∀ c : ℂ, G (algebraMap ℂ F c) =ᶠ[𝓝[≠] z] fun _ => c) ∧
        (G t =ᶠ[𝓝[≠] z] fun u => u)) ∧
      ∀ f : F, f ≠ 0 → meromorphicOrderAt (G f) 0 = (v.ord f : WithTop ℤ) := by
  classical
  have htr : Transcendental ℂ t :=
    AlgebraicCurve.Place.transcendental_of_ord_ne_zero v (by rw [ht]; exact one_ne_zero)
  obtain ⟨x, -, hfin⟩ := hfg
  haveI := hfin
  haveI : FiniteDimensional (IntermediateField.adjoin ℂ ({t} : Set F)) F :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x htr
  obtain ⟨φ, hφt, hφo⟩ := AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one v
    (IsCurveOver.deg_eq_one_of_isAlgClosed v) t ht
  have hb : ∀ f : F, Bdd (φ f).powerSeriesPart := bdd_powerSeriesPart φ htr hφt
  set b := Module.finBasis (IntermediateField.adjoin ℂ ({t} : Set F)) F with hbdef
  have hRi : ∀ i, ∃ C R : ℝ, 0 < R ∧
      ∀ n, ‖PowerSeries.coeff n (φ (b i)).powerSeriesPart‖ ≤ C * R ^ n := fun i => by
    obtain ⟨C, R, -, hR1, h⟩ := hb (b i)
    exact ⟨C, R, zero_lt_one.trans_le hR1, h⟩
  choose C R hR0 hCR using hRi
  set Rm : ℝ := 1 + ∑ i, R i with hRm
  have hsum : 0 ≤ ∑ i, R i := Finset.sum_nonneg fun j _ => (hR0 j).le
  have hRm0 : 0 < Rm := by rw [hRm]; linarith
  have hRle : ∀ i, R i ≤ Rm := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hR0 j).le) (Finset.mem_univ i)
    rw [hRm]; linarith
  set ρ : ℝ := Rm⁻¹ with hρdef
  have hρ : 0 < ρ := inv_pos.mpr hRm0
  have hbi : ∀ i, b i ∈ RSet φ ρ := fun i =>
    mem_RSet_of_bound (hR0 i) (hCR i) (inv_anti₀ (hR0 i) (hRle i))
  have htop := Rfield_eq_top hb b (t_mem_RSet hφt) hbi
  have hall : ∀ f : F, ∃ g : ℂ → ℂ, MeromorphicOn g (ball (0 : ℂ) ρ) ∧
      ∀ᶠ u in 𝓝[≠] (0 : ℂ), SL (φ f) u = g u := fun f => by
    have hf : f ∈ Rfield ρ hb := by rw [htop]; exact IntermediateField.mem_top
    exact hf
  choose G hG hGe using hall
  refine ⟨ρ, G, hρ, hG, fun z hz => ⟨fun f g => ?_, fun f g => ?_, fun c => ?_, ?_⟩, fun f hf => ?_⟩
  · apply eventuallyEq_of_nhdsNE_zero (hG _) ((hG f).add (hG g)) _ hz
    obtain ⟨r, hr, hadd⟩ := SL_add (hb f) (hb g)
    filter_upwards [hGe (f + g), hGe f, hGe g, eventually_nhdsNE_zero hr hadd] with u h1 h2 h3 h4
    rw [← h1, map_add, h4, h2, h3, Pi.add_apply]
  · apply eventuallyEq_of_nhdsNE_zero (hG _) ((hG f).mul (hG g)) _ hz
    obtain ⟨r, hr, hmul⟩ := SL_mul (hb f) (hb g)
    filter_upwards [hGe (f * g), hGe f, hGe g, eventually_nhdsNE_zero hr hmul] with u h1 h2 h3 h4
    rw [← h1, map_mul, h4, h2, h3, Pi.mul_apply]
  · apply eventuallyEq_of_nhdsNE_zero (hG _) (MeromorphicOn.const c) _ hz
    filter_upwards [hGe (algebraMap ℂ F c), self_mem_nhdsWithin] with u h1 hu0
    rw [← h1, apply_algebraMap]
    exact SL_C hu0
  · apply eventuallyEq_of_nhdsNE_zero (hG _) (fun x _ => MeromorphicAt.id x) _ hz
    filter_upwards [hGe t, self_mem_nhdsWithin] with u h1 hu0
    rw [← h1, hφt]
    exact SL_single_one hu0
  · have hφf : φ f ≠ 0 := (map_ne_zero_iff φ injective_φ).mpr hf
    have he : G f =ᶠ[𝓝[≠] (0 : ℂ)] SL (φ f) := (hGe f).mono fun u hu => hu.symm
    rw [meromorphicOrderAt_congr he, meromorphicOrderAt_SL hφf (hb f), hφo]

end MeroRealize

end Place

end AlgebraicCurve
