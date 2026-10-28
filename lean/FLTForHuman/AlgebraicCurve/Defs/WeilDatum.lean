/-
The Weil-datum structure behind the divisorial Weil pairing, after FLT's
`Definitions/Def_AlgebraicCurve_WeilDatum.lean` (81 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilDatum.lean>).

A `WeilDatum K F n` is a pair of degree-`n` divisors `D₁`, `D₂` with functions `f₁`, `f₂` whose
orders are `n D₁`, `n D₂` and whose supports are disjoint and rational; `pairing` is the value
`evalFun f₁ D₂ / evalFun f₂ D₁`, and `symm` / `addLeft` are the swap and the addition laws the
pairing's bilinearity is built from. The statements are the pin's verbatim; the pin's `import
Mathlib` is replaced by `Defs/PlaceEvaluation.lean` (for `Divisor.evalFun`) and `Defs/Place.lean`
(for `Place.IsRational`, `Place.ord_mul`).

spec-pin: Definitions/Def_AlgebraicCurve_WeilDatum.lean
spec-pin: Theorems/Thm_AlgebraicCurve_WeilDatum_symm_pairing.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_WeilDatum_symm_pairing.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.Place

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in

structure WeilDatum (n : ℕ) where

  D₁ : Divisor K F

  D₂ : Divisor K F

  f₁ : F

  f₂ : F
  f₁_ne_zero : f₁ ≠ 0
  f₂_ne_zero : f₂ ≠ 0

  ord_f₁ : ∀ v : Place K F, v.ord f₁ = n * D₁ v

  ord_f₂ : ∀ v : Place K F, v.ord f₂ = n * D₂ v

  disjoint : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0

  rational : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

def pairing : K :=
  Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁

def symm : WeilDatum K F n where
  D₁ := d.D₂
  D₂ := d.D₁
  f₁ := d.f₂
  f₂ := d.f₁
  f₁_ne_zero := d.f₂_ne_zero
  f₂_ne_zero := d.f₁_ne_zero
  ord_f₁ := d.ord_f₂
  ord_f₂ := d.ord_f₁
  disjoint := fun v => (d.disjoint v).symm
  rational := fun v hv => d.rational v hv.symm

/-- **Swapping the divisors inverts the pairing**: the Weil datum's `symm` replaces the
pairing by its inverse. Statement from
`Theorems/Thm_AlgebraicCurve_WeilDatum_symm_pairing.lean`; the proof is `inv_div` on the
two unfoldings of `pairing`, as in the pin's `S_` file. -/
theorem symm_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by
  simp only [pairing, symm]
  exact (inv_div _ _).symm

def addLeft (d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (_hf : d.f₂ = d'.f₂) :
    WeilDatum K F n where
  D₁ := d.D₁ + d'.D₁
  D₂ := d.D₂
  f₁ := d.f₁ * d'.f₁
  f₂ := d.f₂
  f₁_ne_zero := mul_ne_zero d.f₁_ne_zero d'.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ := fun v => by
    rw [v.ord_mul d.f₁_ne_zero d'.f₁_ne_zero, d.ord_f₁ v, d'.ord_f₁ v, Finsupp.add_apply,
      mul_add]
  ord_f₂ := d.ord_f₂
  disjoint := fun v => by
    rcases eq_or_ne (d.D₂ v) 0 with h2 | h2
    · exact Or.inr h2
    · refine Or.inl ?_
      rw [Finsupp.add_apply, (d.disjoint v).resolve_right h2,
        (d'.disjoint v).resolve_right (hD ▸ h2), add_zero]
  rational := fun v hv => by
    rcases hv with h1 | h2
    · rw [Finsupp.add_apply] at h1
      rcases eq_or_ne (d.D₁ v) 0 with hd | hd
      · exact d'.rational v (Or.inl fun hd' => h1 (by rw [hd, hd', add_zero]))
      · exact d.rational v (Or.inl hd)
    · exact d.rational v (Or.inr h2)

end WeilDatum

end AlgebraicCurve
