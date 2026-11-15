/-
  SET-AF84D consumer: the Eisenstein archimedean core, read without the spectral parameter.

  **The rows.** `FLTForHuman/EisensteinGeneral/ArchIntegralBound.lean` carries the archimedean integral
  bound `Arch.exists_norm_archIntegral_le` and the additive-character change of variables
  `Piece.integral_smul_add_mul_addChar_neg_mul_eq`;
  `FLTForHuman/LanglandsTunnell/RankinSelberg/EulerPolyRecursion.lean` carries the ODE vanishing lemma
  `eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow`.

  **The readings.** Each row is stated with a parameter whose vanishing or specialisation makes it a
  *different* statement, and those are the forms the consumers use:

  * Zone 1 — **the change of variables with the character removed** (`ξ = 0`): the additive-character
    integral becomes the plain scaling identity `∫ y, f (a • (y+u)) = |α(a)|⁻¹ ∫ z, f z`. The character is
    what the row is *named* for; the identity is what it is *used* for at `ξ = 0`.
  * Zone 2 — **the archimedean bound past `|r| = 1`**: the row's `max 1 (|r|^(-N))` is `1` once `|r| ≥ 1`
    (a negative `rpow` of something at least `1` is at most `1`), so past the unit annulus the bound is
    purely exponential — no polynomial factor. That is the form the Euler-factor estimates spend.
  * Zone 3 — **the ODE lemma at `β = 1`**: a concrete `β` with `Re β > 0`, so the lemma is instantiated
    rather than merely quoted.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/EisensteinGeneralSetAF84DConsumer.lean` and never enters the build.
-/
import FLTForHuman.EisensteinGeneral.ArchIntegralBound
import FLTForHuman.LanglandsTunnell.RankinSelberg.EulerPolyRecursion

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal

namespace EisensteinGeneralSetAF84DConsumer

/-! ### Zone 1 — the additive-character identity at `ξ = 0` -/

/-- **Zone 1.** At `ξ = 0` the character drops out of both sides and the row reads as the scaling
identity for the additive Haar measure: `∫ y, f (a • (y + u)) = |α(a)|⁻¹ ∫ z, f z`. -/
theorem integral_smul_add_eq_inv_distribHaarChar_mul (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (f : AdeleRing (𝓞 F) F → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) :
    (∫ y, f (a • (y + u)) ∂(adelicAddHaar (𝓞 F) F))
      = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ *
          ∫ z, f z ∂(adelicAddHaar (𝓞 F) F) := by
  have h := EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq F ψ f a u 0
  simpa using h

/-! ### Zone 2 — the archimedean bound past the unit annulus -/

/-- **Zone 2.** Past `|r| = 1` the row's `max 1 (|r| ^ (-N))` is `1`, so the archimedean integral is
bounded by a pure exponential in `|r|` — the polynomial factor is gone. -/
theorem exists_exp_bound_of_one_le (c : ℂ) (hc : 0 < c.re) (M : ℝ) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧ ∀ (z : ℂ) (r : ℝ), |z.re| ≤ M → 1 ≤ |r| →
      ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * Real.exp (-c' * |r|) := by
  obtain ⟨C, c', N, hC, hc', h⟩ := EisensteinGeneral.Arch.exists_norm_archIntegral_le c hc M
  refine ⟨C, c', hC, hc', fun z r hz hr => ?_⟩
  have hmax : max 1 (|r| ^ (-(N : ℝ))) = 1 := by
    refine max_eq_left ?_
    refine Real.rpow_le_one_of_one_le_of_nonpos hr ?_
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  calc ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))‖
      ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := h z r hz (by
        have : 0 < |r| := lt_of_lt_of_le zero_lt_one hr
        exact abs_pos.mp this)
    _ = C * Real.exp (-c' * |r|) := by rw [hmax, mul_one]

/-! ### Zone 3 — the ODE lemma at `β = 1` -/

/-- **Zone 3.** The vanishing lemma at the concrete exponential rate `β = 1`. -/
theorem eq_zero_of_deriv_eq_div_add_one_mul_of_isBigO_pow (α : ℂ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + 1) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 :=
  LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow α 1 (by norm_num) f hf
    hfeq C N hgrowth

end EisensteinGeneralSetAF84DConsumer
