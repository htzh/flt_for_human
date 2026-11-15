/-
  The Eisenstein piece: the archimedean integral bound, the induced section's continuity, the
  Bruhat-series Whittaker coefficient, and the additive-character integral identity.

  Four rows of the `EisensteinGeneral` layer, three of them the analytic core of the Eisenstein
  series' Fourier expansion:

  * `Arch.exists_norm_archIntegral_le`: the archimedean integral
    `∫_{u>0} u^z · exp (-c (u + r²/u))` is polynomially-times-exponentially bounded in `r` — the
    decay estimate the archimedean factors of a `FactorizationDatum` are built from.
  * `Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero`: an induced section
    that is continuous and nonzero somewhere forces both of its characters to be continuous.
  * `Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable`: for an induced
    `φ` whose Bruhat-cell translate is integrable against the additive Haar measure, the Whittaker
    coefficient of the Bruhat series `φ + ∑' ξ, φ(w n(ξ) ·)` is integrable, and the series is
    summable almost everywhere.
  * `Piece.integral_smul_add_mul_addChar_neg_mul_eq`: the additive-character change of variables
    `∫ y, f (a • (y + u)) ψ(-ξ y) = |α(a)|⁻¹ ψ(ξ u) ∫ z, f z ψ(-ξ a⁻¹ z)`.

  All four pins are single-headline files (one public `solution` each, over 9 / 6 / 7 / 1 private
  declarations), so this module is the four headlines plus the engines the order transcribes — all
  23 of them ported here, `private`, at subject names (the pins' `e2_` / `pc_` / `l1_` label
  prefixes are dropped; the pin-line-by-pin-line table is in `lean/tmp/af84/AF84D-REPORT.md`).

  Gates: `check_port --force` 4 ok / 0 mismatch / 0 missing / 0 own / 0 kw; `dedup.py --within` 0
  duplicate clusters; `move_dead.py` 0 declarations / 0 lines; `scaffold_audit.py` complete; axioms
  `[propext, Classical.choice, Quot.sound]` on the four rows and on all 23 engines.

  Heartbeat probe: silent at 12000, aborts at 6000 (`lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N`; the peak declaration is the `Arch` row). No in-file cap is carried —
  playbook §3.5, FR-0225.

  Local departures from the pins (v4.34), all recorded:
  * `haveI : (adelicAddHaar …).IsAddHaarMeasure` / `.Regular` / `IsFiniteMeasure …` → `have`
    (FR-0223, the linter's own `Try this:` block); the instance is still found.
  * `if_pos` / `if_neg` → `ite_eq_left` / `ite_eq_right` (v4.34 deprecations).
  * the Glue pin's two `private scoped instance`s (`:33`, `:37`) and its three `p2m_reactivate`
    calls (`:97`, `:100`, `:163`) are replaced by the named private theorems
    `nontrivial_adeleRing` / `countable_principalSubgroup`, introduced where needed with a
    class-typed `have` (FR-0223): `principalSubgroupEquiv` needs `Nontrivial (AdeleRing 𝓞 F F)` for
    `(algebraMap F _).injective` and `tsum_lintegral_translate_eq` needs both. No `scoped` instance
    leaks into importers.
  * the pins' `attribute [local instance] adeleBorel borelSpace_adeleBorel` lines are kept, per
    section — they are positive local instances, not `[-…]` walls.

  Transcribed from the four `S_` files below (pinned `aa2d8b3`, 233 + 189 + 165 + 125 lines).

  spec-pin: P2M/Sol/S_EisensteinGeneral_Arch_exists_norm_archIntegral_le.lean
  spec-pin: P2M/Sol/S_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero.lean
  spec-pin: P2M/Sol/S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable.lean
  spec-pin: P2M/Sol/S_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal

namespace EisensteinGeneral

namespace Arch

private theorem integrableOn_rpow_mul_exp_neg_mul (p b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-(b * u))) (Ioi 0) := by
  have h0 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ p) (Ioi 0) := by
    simpa using Real.GammaIntegral_convergent (by linarith : (0 : ℝ) < p + 1)
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(b * u)) * (b * u) ^ p) (Ioi 0) := by
    have h2 := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ p) 0 hb).mpr
      (by simpa using h0)
    simpa using h2
  have hbp : (0 : ℝ) < b ^ p := Real.rpow_pos_of_pos hb p
  have h3 : IntegrableOn (fun u : ℝ => (b ^ p)⁻¹ * (Real.exp (-(b * u)) * (b * u) ^ p)) (Ioi 0) :=
    h1.const_mul _
  refine h3.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu : (0 : ℝ) < u := hu
  beta_reduce
  rw [Real.mul_rpow hb.le hu.le]
  have hre : (b ^ p)⁻¹ * (Real.exp (-(b * u)) * (b ^ p * u ^ p))
      = (b ^ p)⁻¹ * b ^ p * (u ^ p * Real.exp (-(b * u))) := by ring
  rw [hre, inv_mul_cancel₀ hbp.ne', one_mul]

private theorem rpow_le_add_rpow_of_le_abs (u σ M₀ : ℝ) (hu : 0 < u) (h₁ : -M₀ ≤ σ) (h₂ : σ ≤ M₀) :
    u ^ σ ≤ u ^ M₀ + u ^ (-M₀) := by
  rcases le_total 1 u with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h₂
    have := Real.rpow_nonneg hu.le (-M₀)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hu h h₁
    have := Real.rpow_nonneg hu.le M₀
    linarith

private theorem two_mul_abs_le_add_sq_div (u r : ℝ) (hu : 0 < u) : 2 * |r| ≤ u + r ^ 2 / u := by
  have h : 2 * |r| - u ≤ r ^ 2 / u := by
    rw [le_div_iff₀ hu]
    nlinarith [sq_nonneg (u - |r|), sq_abs r, abs_nonneg r]
  linarith

private theorem exp_neg_mul_add_sq_div_le (a u r : ℝ) (ha : 0 < a) (hu : 0 < u) :
    Real.exp (-a * (u + r ^ 2 / u))
      ≤ Real.exp (-a * |r|) * Real.exp (-(a / 2 * u)) * Real.exp (-(a / 2 * (r ^ 2 / u))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_mul_abs_le_add_sq_div u r hu
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h)]

private theorem exp_neg_mul_pow_le (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : 0 < k) :
    Real.exp (-t) * t ^ k ≤ (k : ℝ) ^ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : t / k ≤ Real.exp (t / k) := by linarith [Real.add_one_le_exp (t / k)]
  have h2 : (t / k) ^ k ≤ Real.exp t := by
    calc (t / k) ^ k ≤ Real.exp (t / k) ^ k := by gcongr
      _ = Real.exp t := by
        rw [← Real.exp_nat_mul]; congr 1
        rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hk'.ne', mul_one]
  have h3 : t ^ k ≤ Real.exp t * (k : ℝ) ^ k := by
    rw [div_pow, div_le_iff₀ (pow_pos hk' k)] at h2
    exact h2
  calc Real.exp (-t) * t ^ k ≤ Real.exp (-t) * (Real.exp t * (k : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = (k : ℝ) ^ k := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

private theorem exp_neg_mul_sq_le (b u r : ℝ) (hb : 0 < b) (hu : 0 < u) (hr : r ≠ 0) (k : ℕ)
    (hk : 0 < k) :
    Real.exp (-(b * (r ^ 2 / u))) * (r ^ 2) ^ k ≤ (k : ℝ) ^ k / b ^ k * u ^ k := by
  have hr2 : (0 : ℝ) < r ^ 2 := lt_of_le_of_ne (sq_nonneg r) (pow_ne_zero 2 hr).symm
  have ht : (0 : ℝ) < b * (r ^ 2 / u) := by positivity
  have hbk : (0 : ℝ) < b ^ k := pow_pos hb k
  have h := exp_neg_mul_pow_le (b * (r ^ 2 / u)) ht k hk
  have hu' : u ^ k * (u ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero k hu.ne')
  have hb' : b ^ k * (b ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero k hb.ne')
  have hid : (r ^ 2) ^ k = (b * (r ^ 2 / u)) ^ k * (u ^ k * (b ^ k)⁻¹) := by
    calc (r ^ 2) ^ k = (r ^ 2) ^ k * (u ^ k * (u ^ k)⁻¹) * (b ^ k * (b ^ k)⁻¹) := by
          rw [hu', hb', mul_one, mul_one]
      _ = (b * (r ^ 2 / u)) ^ k * (u ^ k * (b ^ k)⁻¹) := by
          rw [mul_pow, div_pow, div_eq_mul_inv]; ring
  calc Real.exp (-(b * (r ^ 2 / u))) * (r ^ 2) ^ k
        = Real.exp (-(b * (r ^ 2 / u))) * (b * (r ^ 2 / u)) ^ k * (u ^ k * (b ^ k)⁻¹) := by
          rw [hid]; ring
    _ ≤ (k : ℝ) ^ k * (u ^ k * (b ^ k)⁻¹) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = (k : ℝ) ^ k / b ^ k * u ^ k := by rw [div_eq_mul_inv]; ring

private theorem rpow_neg_mul_sq_pow (r : ℝ) (hr : r ≠ 0) (k : ℕ) :
    |r| ^ (-((2 * k : ℕ) : ℝ)) * (r ^ 2) ^ k = 1 := by
  rw [Real.rpow_neg (abs_nonneg r), Real.rpow_natCast, pow_mul, sq_abs]
  exact inv_mul_cancel₀ (pow_ne_zero k (pow_ne_zero 2 hr))

private theorem rpow_mul_exp_neg_le (a u r σ M₀ : ℝ) (k : ℕ) (ha : 0 < a) (hu : 0 < u) (hr : r ≠ 0)
    (hk : 0 < k) (h₁ : -M₀ ≤ σ) (h₂ : σ ≤ M₀) :
    u ^ σ * Real.exp (-a * (u + r ^ 2 / u))
      ≤ Real.exp (-a * |r|) * (u ^ M₀ * Real.exp (-(a / 2 * u)))
        + Real.exp (-a * |r|) * ((k : ℝ) ^ k / (a / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
          * (u ^ ((k : ℝ) - M₀) * Real.exp (-(a / 2 * u))) := by
  have hb : (0 : ℝ) < a / 2 := half_pos ha
  have hpow := rpow_le_add_rpow_of_le_abs u σ M₀ hu h₁ h₂
  have hexp := exp_neg_mul_add_sq_div_le a u r ha hu
  have hρ0 : (0 : ℝ) ≤ |r| ^ (-((2 * k : ℕ) : ℝ)) := Real.rpow_nonneg (abs_nonneg r) _
  have hK0 : (0 : ℝ) ≤ (k : ℝ) ^ k / (a / 2) ^ k := by positivity
  have hnn : (0 : ℝ) ≤ a / 2 * (r ^ 2 / u) := by positivity

  have he₃ : Real.exp (-(a / 2 * (r ^ 2 / u))) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)

  have he₃' : Real.exp (-(a / 2 * (r ^ 2 / u)))
      ≤ |r| ^ (-((2 * k : ℕ) : ℝ)) * ((k : ℝ) ^ k / (a / 2) ^ k * u ^ k) := by
    have hsmall := exp_neg_mul_sq_le (a / 2) u r hb hu hr k hk
    have hone := rpow_neg_mul_sq_pow r hr k
    calc Real.exp (-(a / 2 * (r ^ 2 / u)))
          = |r| ^ (-((2 * k : ℕ) : ℝ)) * (Real.exp (-(a / 2 * (r ^ 2 / u))) * (r ^ 2) ^ k) := by
            rw [mul_left_comm, hone, mul_one]
      _ ≤ |r| ^ (-((2 * k : ℕ) : ℝ)) * ((k : ℝ) ^ k / (a / 2) ^ k * u ^ k) :=
            mul_le_mul_of_nonneg_left hsmall hρ0
  have hsplit : u ^ ((k : ℝ) - M₀) = u ^ (-M₀) * u ^ k := by
    rw [sub_eq_neg_add, Real.rpow_add hu, Real.rpow_natCast]
  have hE : (0 : ℝ) ≤ Real.exp (-a * |r|) * Real.exp (-(a / 2 * u)) := by positivity
  have hM : (0 : ℝ) ≤ u ^ M₀ := Real.rpow_nonneg hu.le M₀
  have hM' : (0 : ℝ) ≤ u ^ (-M₀) := Real.rpow_nonneg hu.le (-M₀)
  calc u ^ σ * Real.exp (-a * (u + r ^ 2 / u))
        ≤ (u ^ M₀ + u ^ (-M₀))
            * (Real.exp (-a * |r|) * Real.exp (-(a / 2 * u)) * Real.exp (-(a / 2 * (r ^ 2 / u)))) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (add_nonneg hM hM')
    _ = Real.exp (-a * |r|) * Real.exp (-(a / 2 * u)) * (u ^ M₀ * Real.exp (-(a / 2 * (r ^ 2 / u))))
          + Real.exp (-a * |r|) * Real.exp (-(a / 2 * u))
            * (u ^ (-M₀) * Real.exp (-(a / 2 * (r ^ 2 / u)))) := by ring
    _ ≤ Real.exp (-a * |r|) * Real.exp (-(a / 2 * u)) * (u ^ M₀ * 1)
          + Real.exp (-a * |r|) * Real.exp (-(a / 2 * u))
            * (u ^ (-M₀) * (|r| ^ (-((2 * k : ℕ) : ℝ)) * ((k : ℝ) ^ k / (a / 2) ^ k * u ^ k))) := by
          gcongr
    _ = Real.exp (-a * |r|) * (u ^ M₀ * Real.exp (-(a / 2 * u)))
          + Real.exp (-a * |r|) * ((k : ℝ) ^ k / (a / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
            * (u ^ ((k : ℝ) - M₀) * Real.exp (-(a / 2 * u))) := by
          rw [hsplit]; ring

private theorem const_mul_add_le_max (E K ρ I₁ I₂ : ℝ) (hE : 0 < E) (hK : 0 < K) (hρ : 0 ≤ ρ) :
    E * I₁ + E * (K * ρ) * I₂ ≤ (1 + |I₁| + K * |I₂|) * max 1 ρ * E := by
  have hX1 : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
  have hXρ : ρ ≤ max 1 ρ := le_max_right _ _
  have h1 : E * I₁ ≤ E * |I₁| * max 1 ρ := by
    calc E * I₁ ≤ E * |I₁| := mul_le_mul_of_nonneg_left (le_abs_self _) hE.le
      _ ≤ E * |I₁| * max 1 ρ := le_mul_of_one_le_right (by positivity) hX1
  have h2 : E * (K * ρ) * I₂ ≤ E * (K * |I₂|) * max 1 ρ := by
    calc E * (K * ρ) * I₂ ≤ E * (K * ρ) * |I₂| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = E * (K * |I₂|) * ρ := by ring
      _ ≤ E * (K * |I₂|) * max 1 ρ := mul_le_mul_of_nonneg_left hXρ (by positivity)
  have h3 : (0 : ℝ) ≤ max 1 ρ * E := by positivity
  nlinarith [h1, h2, h3]

theorem exists_norm_archIntegral_le (c : ℂ) (hc : 0 < c.re) (M : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (z : ℂ) (r : ℝ), |z.re| ≤ M → r ≠ 0 →
      ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by
  have ha : (0 : ℝ) < c.re := hc
  have hb : (0 : ℝ) < c.re / 2 := half_pos ha
  obtain ⟨M₀, hM₀pos, hMM₀⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ M ≤ M₀ :=
    ⟨|M| + 1, by positivity, by linarith [le_abs_self M]⟩
  obtain ⟨k, hk, hkM⟩ : ∃ k : ℕ, 0 < k ∧ M₀ < k :=
    ⟨⌈M₀⌉₊ + 1, Nat.succ_pos _, by rw [Nat.cast_add, Nat.cast_one]; linarith [Nat.le_ceil M₀]⟩
  have hI₁ := integrableOn_rpow_mul_exp_neg_mul M₀ (c.re / 2) hM₀pos hb
  have hI₂ := integrableOn_rpow_mul_exp_neg_mul ((k : ℝ) - M₀) (c.re / 2) (by linarith) hb
  have hK : (0 : ℝ) < (k : ℝ) ^ k / (c.re / 2) ^ k :=
    div_pos (pow_pos (by exact_mod_cast hk) k) (pow_pos hb k)
  refine ⟨1 + |∫ u in Ioi (0 : ℝ), u ^ M₀ * Real.exp (-(c.re / 2 * u))|
      + (k : ℝ) ^ k / (c.re / 2) ^ k
        * |∫ u in Ioi (0 : ℝ), u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u))|,
    c.re, 2 * k, by positivity, ha, ?_⟩
  intro z r hz hr
  obtain ⟨hz₁, hz₂⟩ := abs_le.mp hz
  have hz₁' : -M₀ ≤ z.re := by linarith
  have hz₂' : z.re ≤ M₀ := by linarith
  have hE : (0 : ℝ) < Real.exp (-c.re * |r|) := Real.exp_pos _
  have hρ : (0 : ℝ) ≤ |r| ^ (-((2 * k : ℕ) : ℝ)) := Real.rpow_nonneg (abs_nonneg r) _

  have hpt : ∀ u ∈ Ioi (0 : ℝ), ‖(u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
      ≤ Real.exp (-c.re * |r|) * (u ^ M₀ * Real.exp (-(c.re / 2 * u)))
        + Real.exp (-c.re * |r|) * ((k : ℝ) ^ k / (c.re / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
          * (u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u))) := by
    intro u hu
    have hu : (0 : ℝ) < u := hu
    have hw : (-c * (u + r ^ 2 / u) : ℂ) = -c * ((u + r ^ 2 / u : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
    have hre : (-c * ((u + r ^ 2 / u : ℝ) : ℂ)).re = -c.re * (u + r ^ 2 / u) := by
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, hw, Complex.norm_exp, hre]
    exact rpow_mul_exp_neg_le c.re u r z.re M₀ k ha hu hr hk hz₁' hz₂'

  have hg : IntegrableOn (fun u : ℝ =>
      Real.exp (-c.re * |r|) * (u ^ M₀ * Real.exp (-(c.re / 2 * u)))
        + Real.exp (-c.re * |r|) * ((k : ℝ) ^ k / (c.re / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
          * (u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u)))) (Ioi 0) :=
    (hI₁.const_mul (Real.exp (-c.re * |r|))).add
      (hI₂.const_mul (Real.exp (-c.re * |r|)
        * ((k : ℝ) ^ k / (c.re / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))))
  calc ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
      ≤ ∫ u in Ioi (0 : ℝ),
          (Real.exp (-c.re * |r|) * (u ^ M₀ * Real.exp (-(c.re / 2 * u)))
            + Real.exp (-c.re * |r|) * ((k : ℝ) ^ k / (c.re / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
              * (u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u)))) :=
        norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = Real.exp (-c.re * |r|) * (∫ u in Ioi (0 : ℝ), u ^ M₀ * Real.exp (-(c.re / 2 * u)))
          + Real.exp (-c.re * |r|) * ((k : ℝ) ^ k / (c.re / 2) ^ k * |r| ^ (-((2 * k : ℕ) : ℝ)))
            * ∫ u in Ioi (0 : ℝ), u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u)) := by
        rw [integral_add (hI₁.const_mul _) (hI₂.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ (1 + |∫ u in Ioi (0 : ℝ), u ^ M₀ * Real.exp (-(c.re / 2 * u))|
          + (k : ℝ) ^ k / (c.re / 2) ^ k
            * |∫ u in Ioi (0 : ℝ), u ^ ((k : ℝ) - M₀) * Real.exp (-(c.re / 2 * u))|)
          * max 1 (|r| ^ (-((2 * k : ℕ) : ℝ))) * Real.exp (-c.re * |r|) :=
        const_mul_add_le_max _ _ _ _ _ hE hK hρ


end Arch

namespace Piece

section InducedCharacter

variable {F : Type} [Field F] [NumberField F]

private noncomputable def diagGL2 (t₁ t₂ : (AdeleRing (𝓞 F) F)ˣ) : AdelicGL2 (𝓞 F) F :=
  ⟨Matrix.diagonal (fun i : Fin 2 => if i = 0 then (t₁ : AdeleRing (𝓞 F) F) else (t₂ : AdeleRing (𝓞 F) F)),
    Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then ((t₁⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      else ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = 0 <;> simp [hi],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases hi : i = 0 <;> simp [hi]⟩

private theorem diagGL2_mem_adelicBorel (t₁ t₂ : (AdeleRing (𝓞 F) F)ˣ) :
    diagGL2 t₁ t₂ ∈ adelicBorel (𝓞 F) F := by
  show (Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then (t₁ : AdeleRing (𝓞 F) F) else (t₂ : AdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagGL2 (t₁ t₂ : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagGL2 t₁ t₂, diagGL2_mem_adelicBorel t₁ t₂⟩ : ↥(adelicBorel (𝓞 F) F)) = t₁ := by
  apply Units.ext
  show (Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then (t₁ : AdeleRing (𝓞 F) F) else (t₂ : AdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t₁ : AdeleRing (𝓞 F) F)
  rw [Matrix.diagonal_apply_eq]
  simp

private theorem borelDiagSnd_diagGL2 (t₁ t₂ : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagGL2 t₁ t₂, diagGL2_mem_adelicBorel t₁ t₂⟩ : ↥(adelicBorel (𝓞 F) F)) = t₂ := by
  apply Units.ext
  show (Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then (t₁ : AdeleRing (𝓞 F) F) else (t₂ : AdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (t₂ : AdeleRing (𝓞 F) F)
  rw [Matrix.diagonal_apply_eq]
  simp

private theorem continuous_matrix_diagonal {X : Type} [TopologicalSpace X]
    (u₁ u₂ : X → AdeleRing (𝓞 F) F) (h₁ : Continuous u₁) (h₂ : Continuous u₂) :
    Continuous fun x => (Matrix.diagonal (fun i : Fin 2 => if i = 0 then u₁ x else u₂ x) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  by_cases hi : i = 0
  · simp only [ite_eq_left hi]
    exact h₁
  · simp only [ite_eq_right hi]
    exact h₂

private theorem continuous_diagGL2_mul (f₁ f₂ : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (g₀ : AdelicGL2 (𝓞 F) F) :
    Continuous fun t => diagGL2 (f₁ t) (f₂ t) * g₀ := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t => (Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then ((f₁ t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
        else ((f₂ t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      * ((g₀ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    exact (continuous_matrix_diagonal _ _ (Units.continuous_val.comp hf₁)
      (Units.continuous_val.comp hf₂)).mul continuous_const
  · show Continuous fun t => ((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      * (Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then (((f₁ t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
        else (((f₂ t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    exact continuous_const.mul
      (continuous_matrix_diagonal _ _ (Units.continuous_coe_inv.comp hf₁)
        (Units.continuous_coe_inv.comp hf₂))

end InducedCharacter

theorem continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
    (F : Type) [Field F]
    [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀) (hφ₀c : Continuous φ₀)
    (g₀ : AdelicGL2 (𝓞 F) F) (hne : φ₀ g₀ ≠ 0) :
    Continuous μ ∧ Continuous ν := by

  have hlaw : ∀ t₁ t₂ : (AdeleRing (𝓞 F) F)ˣ, φ₀ (diagGL2 t₁ t₂ * g₀)
      = ((etaFst μ α hα s₀ t₁ : ℂˣ) : ℂ) * ((etaSnd ν α hα s₀ t₂ : ℂˣ) : ℂ) * φ₀ g₀ := by
    intro t₁ t₂
    have h := hφ₀ (diagGL2 t₁ t₂) (diagGL2_mem_adelicBorel t₁ t₂) g₀
    rw [borelDiagFst_diagGL2, borelDiagSnd_diagGL2] at h
    exact h
  have hαpow : ∀ w : ℂ, Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ((((α t : ℝˣ) : ℝ) : ℂ)) ^ w :=
    fun w => (Complex.continuous_ofReal.comp hαc).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (hα t)
  have hαne : ∀ (w : ℂ) (t : (AdeleRing (𝓞 F) F)ˣ), ((((α t : ℝˣ) : ℝ) : ℂ)) ^ w ≠ 0 :=
    fun w t => Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (hα t).ne'))

  have hμval : ∀ t : (AdeleRing (𝓞 F) F)ˣ, ((μ t : ℂˣ) : ℂ)
      = φ₀ (diagGL2 t 1 * g₀)
        * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (s₀ + 1 / 2))⁻¹) := by
    intro t
    have h := hlaw t 1
    rw [map_one, Units.val_one, mul_one, etaFst_apply, Units.val_mul, cpowChar_apply_val] at h
    calc ((μ t : ℂˣ) : ℂ)
        = ((μ t : ℂˣ) : ℂ) * (φ₀ g₀ * ((((α t : ℝˣ) : ℝ) : ℂ)) ^ (s₀ + 1 / 2))
            * (φ₀ g₀ * ((((α t : ℝˣ) : ℝ) : ℂ)) ^ (s₀ + 1 / 2))⁻¹ :=
          (mul_inv_cancel_right₀ (mul_ne_zero hne (hαne _ t)) _).symm
      _ = φ₀ (diagGL2 t 1 * g₀)
            * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (s₀ + 1 / 2))⁻¹) := by
          rw [h, mul_inv]
          ring
  have hμc : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((μ t : ℂˣ) : ℂ) := by
    rw [show (fun t : (AdeleRing (𝓞 F) F)ˣ => ((μ t : ℂˣ) : ℂ))
        = fun t => φ₀ (diagGL2 t 1 * g₀)
            * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (s₀ + 1 / 2))⁻¹)
        from funext hμval]
    exact (hφ₀c.comp (continuous_diagGL2_mul (fun t => t) (fun _ => 1) continuous_id
      continuous_const g₀)).mul
      (continuous_const.mul ((hαpow _).inv₀ (hαne _)))

  have hνval : ∀ t : (AdeleRing (𝓞 F) F)ˣ, ((ν t : ℂˣ) : ℂ)
      = φ₀ (diagGL2 1 t * g₀)
        * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (-(s₀ + 1 / 2)))⁻¹) := by
    intro t
    have h := hlaw 1 t
    rw [map_one, Units.val_one, one_mul, etaSnd_apply, Units.val_mul, cpowChar_apply_val] at h
    calc ((ν t : ℂˣ) : ℂ)
        = ((ν t : ℂˣ) : ℂ) * (φ₀ g₀ * ((((α t : ℝˣ) : ℝ) : ℂ)) ^ (-(s₀ + 1 / 2)))
            * (φ₀ g₀ * ((((α t : ℝˣ) : ℝ) : ℂ)) ^ (-(s₀ + 1 / 2)))⁻¹ :=
          (mul_inv_cancel_right₀ (mul_ne_zero hne (hαne _ t)) _).symm
      _ = φ₀ (diagGL2 1 t * g₀)
            * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (-(s₀ + 1 / 2)))⁻¹) := by
          rw [h, mul_inv]
          ring
  have hνc : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((ν t : ℂˣ) : ℂ) := by
    rw [show (fun t : (AdeleRing (𝓞 F) F)ˣ => ((ν t : ℂˣ) : ℂ))
        = fun t => φ₀ (diagGL2 1 t * g₀)
            * ((φ₀ g₀)⁻¹ * (((((α t : ℝˣ) : ℝ) : ℂ)) ^ (-(s₀ + 1 / 2)))⁻¹)
        from funext hνval]
    exact (hφ₀c.comp (continuous_diagGL2_mul (fun _ => 1) (fun t => t) continuous_const
      continuous_id g₀)).mul
      (continuous_const.mul ((hαpow _).inv₀ (hαne _)))

  refine ⟨Units.continuous_iff.2 ⟨hμc, ?_⟩, Units.continuous_iff.2 ⟨hνc, ?_⟩⟩
  · simp only [Units.val_inv_eq_inv_val]
    exact hμc.inv₀ fun t => (μ t).ne_zero
  · simp only [Units.val_inv_eq_inv_val]
    exact hνc.inv₀ fun t => (ν t).ne_zero


end Piece

namespace Glue

section Periodization

open NumberField AutomorphicForm

attribute [local instance] adeleBorel borelSpace_adeleBorel

variable {F : Type} [Field F] [NumberField F]

private theorem nontrivial_adeleRing : Nontrivial (AdeleRing (𝓞 F) F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨⟨0, 1, fun h => zero_ne_one (α := w.Completion)
    (congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) h)⟩⟩

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

private noncomputable def principalSubgroupEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F := by
  have : Nontrivial (AdeleRing (𝓞 F) F) := nontrivial_adeleRing
  exact Equiv.ofBijective (fun β => ⟨algebraMap F _ β, β, rfl⟩)
    ⟨fun a b h => (algebraMap F (AdeleRing (𝓞 F) F)).injective (congrArg Subtype.val h),
     by rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩⟩

private theorem integrable_tsum_and_ae_summable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Countable ι] {f : ι → X → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun a => ∑' i, f i a) μ ∧ ∀ᵐ a ∂μ, Summable (fun i => f i a) := by
  have hf'' : ∀ i, AEMeasurable (fun a => ‖f i a‖ₑ) μ := fun i => (hf i).enorm
  have hhh : ∀ᵐ a ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  refine ⟨?_, hhh.mono fun a ha => ha.of_norm⟩
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i) ?_
    filter_upwards [hhh] with a ha
    exact (ha.of_norm).hasSum
  · have hlt : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    exact lt_of_le_of_lt (lintegral_mono fun a => enorm_tsum_le_tsum_enorm) hlt

private theorem tsum_lintegral_translate_eq (h : AdeleRing (𝓞 F) F → ℂ) :
    ∑' ξ : F, ∫⁻ x in adelicBox F, ‖h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)‖ₑ
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ y, ‖h y‖ₑ ∂(adelicAddHaar (𝓞 F) F) := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have : Nontrivial (AdeleRing (𝓞 F) F) := nontrivial_adeleRing
  have : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := countable_principalSubgroup
  rw [(isAddFundamentalDomain_adelicBox_adelicAddHaar F).lintegral_eq_tsum'' fun y => ‖h y‖ₑ]
  exact (principalSubgroupEquiv (F := F)).tsum_eq fun γ =>
    ∫⁻ x in adelicBox F, ‖h (γ +ᵥ x)‖ₑ ∂(adelicAddHaar (𝓞 F) F)

private theorem integrableOn_translate_add (h : AdeleRing (𝓞 F) F → ℂ)
    (hh : Integrable h (adelicAddHaar (𝓞 F) F)) (ξ : F) :
    IntegrableOn (fun x => h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
  have := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact (hh.comp_add_left (algebraMap F (AdeleRing (𝓞 F) F) ξ)).integrableOn

private theorem periodization (h : AdeleRing (𝓞 F) F → ℂ)
    (hh : Integrable h (adelicAddHaar (𝓞 F) F)) :
    Integrable (fun x => ∑' ξ : F, h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x))
        ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) ∧
      ∀ᵐ x ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)),
        Summable (fun ξ : F => h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) := by
  refine integrable_tsum_and_ae_summable
    (fun ξ => (integrableOn_translate_add h hh ξ).aestronglyMeasurable) ?_
  rw [tsum_lintegral_translate_eq h]
  exact hh.2.ne

end Periodization

section BruhatSeries

attribute [local instance] adeleBorel borelSpace_adeleBorel

theorem whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable (F : Type) [Field F]
    [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    WhittakerCoefficientIntegrable F (productionPins F) ψ
        (fun g' => φ g' + ∑' ξ' : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g ∧
      (letI := (productionPins F).nS
        ∀ᵐ x ∂(productionPins F).ν, Summable (fun ξ' : F =>
          φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))) := by
  obtain ⟨_, _, hsec⟩ := hφ
  obtain ⟨hP, hPae⟩ := periodization (F := F) _ hint
  have hsummand : ∀ (x : AdeleRing (𝓞 F) F) (ξ' : F),
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ')
          * (unipotentGL2 x * g))
        = φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ' + x) * g) := by
    intro x ξ'
    simp only [unipotentGL2_add, mul_assoc]
  refine ⟨?_, ?_⟩
  · show Integrable
        (fun x : AdeleRing (𝓞 F) F =>
          (φ (unipotentGL2 x * g) + ∑' ξ' : F,
              φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ')
                * (unipotentGL2 x * g)))
            * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x)))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
    unfold ProbabilityTheory.cond
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')
    refine Integrable.mul_bdd (c := 1) ?_ ?_ ?_
    · have h1 : Integrable (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g))
          ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) := by
        have : IsFiniteMeasure ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) :=
          isFiniteMeasure_restrict.mpr (adelicAddHaar_adelicBox_lt_top F).ne
        have hconst : (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) = fun _ => φ g :=
          funext fun x => isInducedSection_unipotent_mul hsec x g
        rw [hconst]
        exact integrable_const _
      have h2 : Integrable (fun x : AdeleRing (𝓞 F) F => ∑' ξ' : F,
            φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ')
              * (unipotentGL2 x * g)))
          ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) := by
        refine Integrable.congr hP (Filter.Eventually.of_forall fun x => ?_)
        exact tsum_congr fun ξ' => (hsummand x ξ').symm
      exact h1.add h2
    · exact (hψc.comp ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => (hψ _).le
  · show ∀ᵐ x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), Summable (fun ξ' : F =>
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ')
          * (unipotentGL2 x * g)))
    unfold ProbabilityTheory.cond
    refine Measure.ae_smul_measure ?_ _
    refine hPae.mono fun x hx => ?_
    exact hx.congr fun ξ' => (hsummand x ξ').symm

end BruhatSeries

end Glue

namespace Piece

section Coset

open NumberField AutomorphicForm

attribute [local instance] adeleBorel borelSpace_adeleBorel

variable {F : Type} [Field F] [NumberField F]

private theorem map_smul_adelicAddHaar (a : (AdeleRing (𝓞 F) F)ˣ) :
    Measure.map (fun x : AdeleRing (𝓞 F) F => a • x) (adelicAddHaar (𝓞 F) F)
      = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F := by
  have : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar
    infer_instance
  have hdef : DomMulAct.mk a⁻¹ • adelicAddHaar (𝓞 F) F
      = Measure.map (fun x : AdeleRing (𝓞 F) F => a • x) (adelicAddHaar (𝓞 F) F) := by
    show Measure.map (fun x : AdeleRing (𝓞 F) F => a⁻¹⁻¹ • x) _ = _
    rw [inv_inv]
  rw [← hdef, Measure.isAddLeftInvariant_eq_smul_of_regular
    (DomMulAct.mk a⁻¹ • adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F),
    addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]

end Coset

section ChangeOfVariables

open NumberField AutomorphicForm

attribute [local instance] adeleBorel borelSpace_adeleBorel

theorem integral_smul_add_mul_addChar_neg_mul_eq (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (u ξ : AdeleRing (𝓞 F) F) :
    ∫ y, f (a • (y + u)) * ψ (-(ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ * u)
        * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z)) ∂(adelicAddHaar (𝓞 F) F) := by
  have : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  let e : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F :=
    ((Homeomorph.addLeft u).trans (Homeomorph.smul a)).toMeasurableEquiv
  have he : ∀ y, e y = a • (u + y) := fun _ => rfl
  have hmap : Measure.map e (adelicAddHaar (𝓞 F) F)
      = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F := by
    have hcoe : (e : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F)
        = (fun x : AdeleRing (𝓞 F) F => a • x) ∘ (fun x : AdeleRing (𝓞 F) F => u + x) :=
      funext fun _ => rfl
    have hg : Measurable (fun x : AdeleRing (𝓞 F) F => a • x) := (continuous_const_smul a).measurable
    have hf : Measurable (fun x : AdeleRing (𝓞 F) F => u + x) :=
      (show Continuous (fun x : AdeleRing (𝓞 F) F => u + x) from
        continuous_const.add continuous_id).measurable
    rw [hcoe, ← Measure.map_map hg hf, map_add_left_eq_self, map_smul_adelicAddHaar]

  have h1 : ∀ y : AdeleRing (𝓞 F) F,
      f (e y) * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * e y - u)))
        = f (a • (y + u)) * ψ (-(ξ * y)) := by
    intro y
    rw [he, Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, Units.inv_mul_cancel_left,
      add_sub_cancel_left, add_comm u y]
  have h2 : ∀ z : AdeleRing (𝓞 F) F,
      f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
        = ψ (ξ * u) * (f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))) := by
    intro z
    have harg : -(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u))
        = ξ * u + -(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z) := by ring
    rw [harg, AddChar.map_add_eq_mul]
    ring
  calc ∫ y, f (a • (y + u)) * ψ (-(ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, f (e y) * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * e y - u)))
          ∂(adelicAddHaar (𝓞 F) F) := by
        simp only [h1]
    _ = ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
          ∂(Measure.map e (adelicAddHaar (𝓞 F) F)) :=
        (integral_map_equiv e (fun z => f z
          * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u))))).symm
    _ = ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
          ∂((distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F) := by
        rw [hmap]
    _ = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹
          • ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
              ∂(adelicAddHaar (𝓞 F) F) :=
        integral_smul_nnreal_measure _ _
    _ = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹
          • (ψ (ξ * u) * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))
              ∂(adelicAddHaar (𝓞 F) F)) := by
        simp only [h2]
        rw [integral_const_mul]
    _ = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ * u)
          * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))
              ∂(adelicAddHaar (𝓞 F) F) := by
        rw [NNReal.smul_def, Complex.real_smul]
        push_cast
        ring

end ChangeOfVariables


end Piece

end EisensteinGeneral
