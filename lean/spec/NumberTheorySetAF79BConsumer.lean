/-
  Consumer zone for `WORKORDER-AF79B` — the full Euler product of the Dedekind zeta function,
  read at `K = ℚ`, `S = ∅`, `s = 2`.

  The row under test is
  `NumberField.ZetaEuler.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one`:
  for a number field `M`, a finite set `S` of places and `z` with `‖z v‖ ≤ 1`, the product
  `∏'_{v ∉ S} (1 - z v * |v|^{-s})⁻¹` is multiplicable, differentiable on `re s > 1`, and non-zero
  there.  Here every clause is read at the concrete point `S = ∅`, `z ≡ 1`, `s = 2`, where the
  product under the row is the honest Euler product of `ζ_ℚ(s) = ∏_p (1 - p^{-s})⁻¹`.

  Zone 1 reads the prelude's product decomposition `dedekindZeta_eq_prod_mul_tprod` (at `s = 2`,
  `T = ∅`, where the finite product is empty) and so identifies `ζ_ℚ(2)` with the truncated product.
  Zone 2 reads `tendsto_norm_tprod_atTop` as an eventual lower bound for that product's norm.  Zone 3
  reads the row's three conjuncts — multiplicability, differentiability, non-vanishing — at `s = 2`,
  and Zone 4 composes the non-vanishing clause with Zone 1 to get `ζ_ℚ(2) ≠ 0` at the row's terms.

  `lake env lean spec/NumberTheorySetAF79BConsumer.lean` — 0 errors, 0 warnings, no `#check`.
-/
import FLTForHuman.NumberTheory.LSeries.DedekindZetaEulerProduct

open Filter Topology IsDedekindDomain NumberField
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace NumberTheorySetAF79BConsumer

open NumberField.ZetaEuler

/-- The set of places the row removes: none — the full Euler product. -/
private abbrev noPlaces : Finset (HeightOneSpectrum (𝓞 ℚ)) := ∅

/-- The row's hypothesis on the perturbation `z`, met at the degenerate point `z ≡ 1`: the Euler
factor itself, with no Dirichlet character in front of it. -/
private def zOne : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} → ℂ := 1

/-! ### Zone 1: the prelude's product decomposition at `s = 2` -/

/-- `ζ_ℚ(2)` is the empty finite product times the full infinite product over the places of `ℚ`. -/
theorem dedekindZeta_two_eq_prod_mul_tprod :
    NumberField.dedekindZeta ℚ (2 : ℂ) =
      (∏ v ∈ noPlaces, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹) *
        ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ :=
  dedekindZeta_eq_prod_mul_tprod ℚ (by norm_num) noPlaces

/-- At `T = ∅` the finite product is `1`, so the decomposition *is* the Euler product. -/
theorem dedekindZeta_two_eq_tprod :
    NumberField.dedekindZeta ℚ (2 : ℂ) =
      ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ := by
  simpa [noPlaces] using dedekindZeta_two_eq_prod_mul_tprod

/-! ### Zone 2: the truncated product blows up towards `s = 1` -/

/-- The norm of the truncated product tends to infinity as `σ → 1⁺`. -/
theorem tendsto_norm_tprod_atTop_Q :
    Tendsto (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖) (𝓝[>] 1) atTop :=
  tendsto_norm_tprod_atTop ℚ noPlaces

/-- Consumed as an eventual bound: the truncated product is `≥ 1` in norm near `1` from above. -/
theorem eventually_one_le_norm_tprod :
    ∀ᶠ σ : ℝ in 𝓝[>] 1,
      1 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ :=
  tendsto_norm_tprod_atTop_Q.eventually (eventually_ge_atTop 1)

/-! ### Zone 3: the row's three conjuncts at `S = ∅`, `z ≡ 1`, `s = 2` -/

/-- The multiplicability clause at `s = 2`: the Euler factors of `ζ_ℚ(2)` are multipliable. -/
theorem multipliable_at_two :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces} =>
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹ := by
  have h := (multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    ℚ noPlaces zOne fun v => by simp [zOne]).1 (2 : ℂ) (by norm_num)
  simpa only [zOne, Pi.one_apply, one_mul] using h

/-- The differentiability clause on the whole half-plane `re s > 1`. -/
theorem differentiableOn_tprod_Q :
    DifferentiableOn ℂ
      (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) {s : ℂ | 1 < s.re} := by
  have h := (multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    ℚ noPlaces zOne fun v => by simp [zOne]).2.1
  simpa only [zOne, Pi.one_apply, one_mul] using h

/-- The non-vanishing clause at `s = 2`. -/
theorem tprod_at_two_ne_zero :
    (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ noPlaces},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)))⁻¹) ≠ 0 := by
  have h := (multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    ℚ noPlaces zOne fun v => by simp [zOne]).2.2 (2 : ℂ) (by norm_num)
  simpa only [zOne, Pi.one_apply, one_mul] using h

/-! ### Zone 4: the two roads meet — `ζ_ℚ(2) ≠ 0` at the row's own terms -/

/-- The row's non-vanishing clause, transported through the prelude's decomposition: the same
`ζ_ℚ(2)` that Zone 1 writes as a product is non-zero. -/
theorem dedekindZeta_two_ne_zero : NumberField.dedekindZeta ℚ (2 : ℂ) ≠ 0 := by
  rw [dedekindZeta_two_eq_tprod]
  exact tprod_at_two_ne_zero

end NumberTheorySetAF79BConsumer
