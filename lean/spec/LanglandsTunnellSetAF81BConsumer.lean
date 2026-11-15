/-
  Consumer zone for `WORKORDER-AF81B` — the partial Rankin–Selberg `GL₂ × GL₂` Euler product,
  read at `K = ℚ`, `S = ∅` and the constant Hecke data `a = a' = 2`, `b = b' = 1`.

  The row under test is
  `LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow`:
  for Hecke data `a b a' b'` bounded by `‖· v‖ ≤ |v| ^ κ`, some half-plane `re s > σ₀` carries the
  multiplicative, differentiable, non-vanishing Euler product `∏'_{v ∉ S} P_v(|v| ^ (-s))⁻¹` of the
  Rankin–Selberg polynomial.  The instantiation is chosen so that every object in it is computable:

  * `S = ∅`, so the row's product runs over *all* places of `ℚ`;
  * the Satake data `a = 2`, `b = 1` is the double-root case `X² - 2 X + 1 = (X - 1)²`: both
    parameters of the first representation are `1`, and both of the second are `1` as well.  At that
    data the degree-six Euler polynomial collapses to `(1 - X)⁴` (Zone 1), the fourth power of the
    degree-one factor at `z = 1`, so the whole Rankin–Selberg product is the fourth power of the
    Dedekind zeta Euler product;
  * `κ = 1` discharges the row's polynomial bound from `|v| ≥ 2` — the port's own
    `NumberField.ZetaEuler.two_le_absNorm_spectrum` (Zone 3).

  Zones: 1 the polynomial's factorization, 2 the pin's root existence and root bound at the same
  data, 3 the row's three clauses at the point `s = σ₀ + 1` of the half-plane it asserts, and 4 the
  composition — reading the row's factor through Zone 1 turns all three clauses into statements
  about `(1 - |v| ^ (-s))⁴`.  No `#check`; every step is a real application, so deleting the module
  breaks this file.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF81BConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.RankinSelberg.EulerPolyProduct

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField Polynomial
open scoped BigOperators

namespace LanglandsTunnellSetAF81BConsumer

/-- The set of places the row removes: none — the full Rankin–Selberg Euler product. -/
private abbrev noPlaces : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅

/-- The Satake parameter `a = 2` at every place: the sum of the two parameters `1, 1`. -/
private def aTwo : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} → ℂ := fun _ => 2

/-- The Satake parameter `b = 1` at every place: the product of the two parameters `1, 1`. -/
private def bOne : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} → ℂ := fun _ => 1

/-! ### Zone 1: the Euler polynomial at the double root `1` is a perfect fourth power -/

/-- At `a = a' = 2`, `b = b' = 1` the pinned polynomial's four Rankin–Selberg linear factors all
coincide, so its value at `x` is `(1 - x)⁴`. -/
theorem eval_rsEulerPoly_eq_two_one (x : ℂ) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly 2 1 2 1 0).eval x = (1 - x) ^ 4 := by
  have h := LanglandsTunnell.RankinSelberg.eval_rsEulerPoly_eq (1 : ℂ) 1 1 1 x
  rw [show (1 : ℂ) + 1 = 2 by norm_num, mul_one] at h
  rw [h]
  ring

/-! ### Zone 2: the pin's quadratic split and root bound at the same data -/

/-- The pin's root existence at the double root: some `α, β` sum to `2` and multiply to `1`. -/
theorem exists_roots_two_one : ∃ α β : ℂ, α + β = 2 ∧ α * β = 1 :=
  LanglandsTunnell.RankinSelberg.exists_roots 2 1

/-- The pin's root bound at that data: every root of `X² - 2X + 1` has norm at most `3`. -/
theorem norm_le_three_of_add_mul {α β : ℂ} (h1 : α + β = 2) (h2 : α * β = 1) : ‖α‖ ≤ 3 := by
  have h := LanglandsTunnell.RankinSelberg.norm_root_le h1 h2
  have h3 : max 1 (‖(2 : ℂ)‖ + ‖(1 : ℂ)‖) = 3 := by norm_num [Complex.norm_ofNat]
  rw [h3] at h
  exact h

/-! ### Zone 3: the row at `S = ∅`, `a = a' = 2`, `b = b' = 1`, `κ = 1` -/

/-- The polynomial bound the row assumes, met at `‖a v‖ = 2 ≤ |v| ^ 1`: a height-one prime of `𝓞 ℚ`
has absolute norm at least `2`. -/
private theorem norm_aTwo_le_rpow_one (v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces}) :
    ‖aTwo v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) := by
  have h2 := NumberField.ZetaEuler.two_le_absNorm_spectrum ℚ v.1
  have h2' : (2 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast h2
  rw [Real.rpow_one]
  simpa only [aTwo, Complex.norm_ofNat] using h2'

/-- The same bound at `‖b v‖ = 1`. -/
private theorem norm_bOne_le_rpow_one (v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces}) :
    ‖bOne v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) := by
  have h2 := NumberField.ZetaEuler.two_le_absNorm_spectrum ℚ v.1
  have h2' : (2 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast h2
  rw [Real.rpow_one]
  have hone : ‖bOne v‖ = 1 := by simp only [bOne, norm_one]
  rw [hone]
  linarith

/-- The row's four-fold hypothesis, at the constant data. -/
private theorem hbdConcrete :
    ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      ‖aTwo v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) ∧
        ‖bOne v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) ∧
          ‖aTwo v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) ∧
            ‖bOne v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) :=
  fun v =>
    ⟨norm_aTwo_le_rpow_one v, norm_bOne_le_rpow_one v, norm_aTwo_le_rpow_one v,
      norm_bOne_le_rpow_one v⟩

/-- The row itself, instantiated: some half-plane carries the whole product. -/
private theorem rowAtEmpty :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) :=
  LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
    ℚ noPlaces aTwo bOne aTwo bOne 1 hbdConcrete

/-- The half-plane's abscissa, read off the row's existential. -/
private def sigmaZero : ℝ := Classical.choose rowAtEmpty

/-- The row's three clauses at `sigmaZero`. -/
private theorem sigmaZero_spec :
    (∀ s : ℂ, sigmaZero < s.re →
      Multipliable (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | sigmaZero < s.re} ∧
      (∀ s : ℂ, sigmaZero < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) :=
  Classical.choose_spec rowAtEmpty

/-- A point strictly inside the half-plane the row asserts. -/
private def sOne : ℂ := ((sigmaZero + 1 : ℝ) : ℂ)

/-- `sOne` really is inside it. -/
private theorem lt_sOne_re : sigmaZero < sOne.re := by
  rw [sOne, Complex.ofReal_re]
  linarith

/-- The multiplicity clause at `s = σ₀ + 1`. -/
theorem multipliable_at_sOne :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} =>
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-sOne)))⁻¹) :=
  sigmaZero_spec.1 sOne lt_sOne_re

/-- The differentiability clause on the whole half-plane. -/
theorem differentiableOn_tprod :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | sigmaZero < s.re} :=
  sigmaZero_spec.2.1

/-- The non-vanishing clause at `s = σ₀ + 1`. -/
theorem tprod_ne_zero_at_sOne :
    (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (aTwo v) (bOne v) (aTwo v) (bOne v) 0).eval
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-sOne)))⁻¹) ≠ 0 :=
  sigmaZero_spec.2.2 sOne lt_sOne_re

/-! ### Zone 4: the row's factors, written as the fourth power of the degree-one factor -/

/-- The multiplicity clause after Zone 1: the product of `((1 - |v| ^ (-s))⁴)⁻¹` is multiplicative
at `s = σ₀ + 1`. -/
theorem multipliable_inv_fourth_power :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} =>
      ((1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-sOne)) ^ 4)⁻¹) := by
  have h := multipliable_at_sOne
  simp only [aTwo, bOne] at h
  exact h.congr fun v => by rw [eval_rsEulerPoly_eq_two_one]

/-- The non-vanishing clause after Zone 1, at the row's own product: the fourth power of the
degree-one Euler product of `ζ_ℚ` over all places does not vanish at `s = σ₀ + 1`. -/
theorem tprod_inv_fourth_power_ne_zero :
    (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      ((1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-sOne)) ^ 4)⁻¹) ≠ 0 := by
  have h := tprod_ne_zero_at_sOne
  simp only [aTwo, bOne] at h
  rw [← tprod_congr fun v =>
    congrArg (fun z : ℂ => z⁻¹) (eval_rsEulerPoly_eq_two_one _)]
  exact h

/-- The differentiability clause after Zone 1, on the row's half-plane. -/
theorem differentiableOn_inv_fourth_power :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      ((1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) ^ 4)⁻¹) {s : ℂ | sigmaZero < s.re} := by
  have h := differentiableOn_tprod
  simp only [aTwo, bOne] at h
  exact h.congr fun s _ =>
    tprod_congr fun v =>
      congrArg (fun z : ℂ => z⁻¹) (eval_rsEulerPoly_eq_two_one _).symm

end LanglandsTunnellSetAF81BConsumer
