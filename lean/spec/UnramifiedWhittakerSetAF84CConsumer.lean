/-
  SET-AF84C consumer: the unramified Whittaker model, read at `y = 0`.

  **The rows.** `FLTForHuman/RepTheory/LocalLanglands/WhittakerRecursion.lean` carries three rows of the
  local unramified Whittaker model: the diagonal's action by the torus factor, the summability of the
  pointwise product of two Hecke recursion sequences with a power, and the Rankin–Selberg identity
  between that sum and the Euler polynomial `rsEulerPoly lam (N*om) lam' (N*om')`.

  **The readings.** The third row's identity is `(∑' m, seq m) * poly.eval (y/N²) = 1 - om·om'·(y/N)²`.
  At `y = 0` the geometric factor collapses and, because `0^0 = 1` and `0^m = 0` for `m ≥ 1`, so does the
  sum. So the two rows together *evaluate the Euler polynomial at the origin*:

  * Zone 1 — the summability row at `y = 0`, where its norm hypothesis holds trivially (`‖0‖ = 0` and
    `N ≠ 0` give `0 < ‖N‖²`).
  * Zone 2 — the recursion product's `tsum` at `y = 0` is `1`: only the `m = 0` term survives, and
    `heckeRecursionSeq N lam om 0 = 1`.
  * Zone 3 — the composition: the Euler polynomial's constant value is `1`, i.e.
    `(rsEulerPoly lam (N*om) lam' (N*om') 0).eval 0 = 1`. This is a fact about `rsEulerPoly` that
    neither row states, and it is exactly the normalisation the local zeta integral needs at the origin.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/UnramifiedWhittakerSetAF84CConsumer.lean` and never enters the build.
-/
import FLTForHuman.RepTheory.LocalLanglands.WhittakerRecursion

set_option autoImplicit false

noncomputable section

open MeasureTheory Polynomial
open scoped Classical

namespace UnramifiedWhittakerSetAF84CConsumer

open UnramifiedWhittaker

/-- `N ≠ 0` makes the summability row's norm hypothesis hold at `y = 0`. -/
private theorem zero_bound (N lam om lam' om' : ℂ) (hN : N ≠ 0) :
    ‖(0 : ℂ)‖ * (max 1 (‖lam‖ + ‖N * om‖)) * (max 1 (‖lam'‖ + ‖N * om'‖)) < ‖N‖ ^ 2 := by
  have h : 0 < ‖N‖ ^ 2 := by positivity
  simpa using h

/-! ### Zone 1 — summability at `y = 0` -/

/-- **Zone 1.** The summability row at `y = 0`: the recursion product is summable there, because the
norm hypothesis is `0 < ‖N‖²`. -/
theorem summable_at_zero (N lam om lam' om' : ℂ) (_hN : N ≠ 0) :
    Summable (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * (0 : ℂ) ^ m) :=
  summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow N lam om lam' om' _hN 0
    (zero_bound N lam om lam' om' _hN)

/-! ### Zone 2 — the recursion product's sum at `y = 0` is `1` -/

/-- **Zone 2.** At `y = 0` only the `m = 0` term of the recursion product survives, and both sequences
start at `1`. -/
theorem tsum_at_zero (N lam om lam' om' : ℂ) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * (0 : ℂ) ^ m) = 1 := by
  rw [tsum_eq_single 0]
  · simp [heckeRecursionSeq]
  · intro m hm
    rw [zero_pow hm, mul_zero]

/-! ### Zone 3 — the Euler polynomial at the origin -/

/-- **Zone 3.** Composing the two rows at `y = 0`: the Rankin–Selberg Euler polynomial takes the value
`1` at the origin. This is a fact about `rsEulerPoly` that neither row states. -/
theorem eval_zero_rsEulerPoly (N lam om lam' om' : ℂ) (hN : N ≠ 0) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval 0 = 1 := by
  have h := tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval N lam om lam' om'
    hN 0 (summable_at_zero N lam om lam' om' hN)
  rw [tsum_at_zero N lam om lam' om'] at h
  simpa using h

end UnramifiedWhittakerSetAF84CConsumer
