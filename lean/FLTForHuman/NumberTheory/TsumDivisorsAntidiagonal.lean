/-
  Two generic rearrangements of `tsum`s over `ℕ+ × ℕ+` and the divisor
  antidiagonal.

  `tsum_prod_eq_tsum_antidiagonal` rewrites a sum over the product `ℕ+ × ℕ+` as a
  sum over `n.divisorsAntidiagonal`, and `tsum_tsum_eq_tsum_antidiagonal` is its
  iterated form for bounded factors and `‖r‖ < 1`. They generalise mathlib's
  `tsum_prod_pow_eq_tsum_sigma` (the `σ` special case) and are the double-sum
  rearrangement at the heart of the Lambert-series identity.

  This is generic analytic number theory, not modular forms, so it gets its own
  module rather than being exported from `ModularForms/EisensteinSeries.lean`
  (where it is a `private` consumer). The pin writes the lemmas `private` in the
  `CardC` namespace of `P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean`
  (pinned `aa2d8b3`); the statements are the pin's copies.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Topology

/-- A sum over `ℕ+ × ℕ+` whose summand factors as `F a * G b * b ^ e * r ^ (a*b)`
equals the sum over the divisor antidiagonal. -/
lemma tsum_prod_eq_tsum_antidiagonal {F G : ℕ → ℂ} {r : ℂ} (e : ℕ) (h : ℕ+ × ℕ+ → ℂ)
    (hs : Summable h)
    (hh : ∀ p, h p = F p.1 * ((((p.2 : ℕ) : ℂ)) ^ e * (G p.2 * r ^ ((p.2 : ℕ) * p.1)))) :
    ∑' p : ℕ+ × ℕ+, h p =
      ∑' n : ℕ+, (∑ x ∈ (n : ℕ).divisorsAntidiagonal, F x.1 * G x.2 * ((x.2 : ℕ) : ℂ) ^ e) *
        r ^ (n : ℕ) := by
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  have hs' : Summable (fun x : Σ n : ℕ+, ((n : ℕ)).divisorsAntidiagonal =>
      h (sigmaAntidiagonalEquivProd x)) := (Equiv.summable_iff _).mpr hs
  rw [hs'.tsum_sigma]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype, Finset.sum_mul, Finset.univ_eq_attach,
    ← Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : x.1.1 * x.1.2 = n := (Nat.mem_divisorsAntidiagonal.mp x.2).1
  have e1 : ((sigmaAntidiagonalEquivProd ⟨n, x⟩).1 : ℕ) = x.1.1 := rfl
  have e2 : ((sigmaAntidiagonalEquivProd ⟨n, x⟩).2 : ℕ) = x.1.2 := rfl
  rw [hh, e1, e2, mul_comm x.1.2 x.1.1, hx]
  ring

/-- The iterated form of `tsum_prod_eq_tsum_antidiagonal`, for factors bounded by
`1` and `‖r‖ < 1`. -/
lemma tsum_tsum_eq_tsum_antidiagonal {F G : ℕ → ℂ} (hF : ∀ c, ‖F c‖ ≤ 1) (hG : ∀ m, ‖G m‖ ≤ 1)
    {r : ℂ} (hr : ‖r‖ < 1) (e : ℕ) :
    ∑' c : ℕ+, F c * ∑' m : ℕ+, (((m : ℕ) : ℂ)) ^ e * (G m * r ^ ((m : ℕ) * c)) =
      ∑' n : ℕ+, (∑ x ∈ (n : ℕ).divisorsAntidiagonal, F x.1 * G x.2 * ((x.2 : ℕ) : ℂ) ^ e) *
        r ^ (n : ℕ) := by
  let h : ℕ+ × ℕ+ → ℂ := fun p => F p.1 * ((((p.2 : ℕ) : ℂ)) ^ e * (G p.2 * r ^ ((p.2 : ℕ) * p.1)))
  have hr' : ‖(‖r‖ : ℝ)‖ < 1 := by simpa using hr
  have hs : Summable h := by
    refine Summable.of_norm_bounded (summable_prod_mul_pow e hr') fun p => ?_
    simp only [h, norm_mul, norm_pow, Complex.norm_natCast]
    calc ‖F ↑p.1‖ * ((p.2 : ℝ) ^ e * (‖G ↑p.2‖ * ‖r‖ ^ ((p.2 : ℕ) * (p.1 : ℕ))))
        ≤ 1 * ((p.2 : ℝ) ^ e * (1 * ‖r‖ ^ ((p.2 : ℕ) * (p.1 : ℕ)))) := by
          gcongr
          · exact hF _
          · exact hG _
      _ = (p.2 : ℝ) ^ e * ‖r‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by rw [mul_comm (p.2 : ℕ)]; ring
  rw [← tsum_prod_eq_tsum_antidiagonal e h hs (fun p => rfl), hs.tsum_prod]
  exact tsum_congr fun c => (tsum_mul_left).symm
