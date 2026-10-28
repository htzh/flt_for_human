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

The module also carries the **support block** the pairing's laws consume — the eight lemmas from
`ord_f₁_eq_zero_of_mem_support` to `evalFun_f₂_ne_zero` — at the pin's canonical names and
statements. The pin states them three times: publicly in
`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`, and privately with a `'`
suffix in the two `S_` files of the small pairing laws and with an `_i` suffix in the big
`pairing_eq_of_isPrincipal_sub` file. The port writes the block once, here, and the rows import it
(SET 6 §4.3).

spec-pin: Definitions/Def_AlgebraicCurve_WeilDatum.lean
spec-pin: Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean
spec-pin: Theorems/Thm_AlgebraicCurve_WeilDatum_addLeft_pairing.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_WeilDatum_addLeft_pairing.lean
spec-pin: Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_WeilDatum_pairing_ne_zero.lean
spec-pin: Theorems/Thm_AlgebraicCurve_WeilDatum_symm_pairing.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_WeilDatum_symm_pairing.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
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

/-- The support of `D₂` is the zero locus of `f₁`: `f₁` is a unit at every place of `D₂`'s
support. (`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean:119`.) -/
theorem ord_f₁_eq_zero_of_mem_support {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

/-- The support of `D₁` is the zero locus of `f₂`. -/
theorem ord_f₂_eq_zero_of_mem_support {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

/-- Every place of `D₁`'s support is rational. -/
theorem rational_of_mem_support_left {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

/-- Every place of `D₂`'s support is rational. -/
theorem rational_of_mem_support_right {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

/-- `f₁` has a nonzero value at every place of `D₂`'s support. -/
theorem evalAt_f₁_ne_zero {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.evalAt d.f₁ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_right hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support hv)

/-- `f₂` has a nonzero value at every place of `D₁`'s support. -/
theorem evalAt_f₂_ne_zero {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.evalAt d.f₂ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_left hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support hv)

/-- The evaluation of `f₁` against `D₂` is nonzero. -/
theorem evalFun_f₁_ne_zero : Divisor.evalFun d.f₁ d.D₂ ≠ 0 :=
  Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₁_ne_zero hv

/-- The evaluation of `f₂` against `D₁` is nonzero. -/
theorem evalFun_f₂_ne_zero : Divisor.evalFun d.f₂ d.D₁ ≠ 0 :=
  Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₂_ne_zero hv

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

/-- **The pairing is multiplicative in the left arguments when the right ones agree.**
Statement from `Theorems/Thm_AlgebraicCurve_WeilDatum_addLeft_pairing.lean`; the pin's
`S_` proof, with the `'`-suffixed prelude replaced by the support block above
(`evalFun_mul` on `D₂`, `evalFun_add` on `D₁ + D₂`). -/
theorem addLeft_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by
  have hnum : Divisor.evalFun (d.f₁ * d'.f₁) d.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun d'.f₁ d.D₂ := by
    refine Divisor.evalFun_mul (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => ?_) (fun v hv => ?_)
    · exact v.mem_of_ord_nonneg d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support hv).ge
    · exact v.mem_of_ord_nonneg d'.f₁_ne_zero
        (d'.ord_f₁_eq_zero_of_mem_support (hD ▸ hv)).ge
  have hden : Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ d'.D₁ := by
    refine Divisor.evalFun_add d.f₂ (fun v hv => d.evalAt_f₂_ne_zero hv) (fun v hv => ?_)
    exact hf ▸ d'.evalAt_f₂_ne_zero hv
  show Divisor.evalFun (d.f₁ * d'.f₁) d.D₂ / Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = d.pairing * d'.pairing
  simp only [WeilDatum.pairing]
  rw [hnum, hden, div_mul_div_comm, hD, hf]

/-- **The pairing never vanishes.**  Statement from
`Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_ne_zero.lean`; the pin's one-line proof
off the the support block. -/
theorem pairing_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (d : WeilDatum K F n) : d.pairing ≠ 0 :=
  div_ne_zero d.evalFun_f₁_ne_zero d.evalFun_f₂_ne_zero

end WeilDatum

end AlgebraicCurve
