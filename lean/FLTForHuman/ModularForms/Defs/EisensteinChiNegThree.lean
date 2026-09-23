/-
  The `χ₋₃` Eisenstein vocabulary.

  `chiNegThree` is the nontrivial Dirichlet character mod `3` (as a `ℤ`-valued
  function), `sigmaChi` its divisor sum, `e1Chi3` the `q`-series
  `1 + 6∑σ_χ(n)qⁿ` and `e1Chi3In R` its base change. `E1Chi3IsModular` records
  that this `q`-series is the expansion of a weight-1 modular form on `Γ₁(3)`.

  Transcribed verbatim from `Definitions/Def_ModularForm_EisensteinChiNegThree.lean`
  (pinned `aa2d8b3`). It is self-contained (mathlib `PowerSeries` and the
  modular-form vocabulary only). The weight-2 lattice vocabulary that consumes
  `e1Chi3In` is `Defs/IntegralLattice.lean`.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

namespace EisensteinWeightOne

/-- The nontrivial character mod `3`, `ℤ`-valued. -/
def chiNegThree (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- `∑_{d ∣ n} χ₋₃(d)`. -/
def sigmaChi (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, chiNegThree d

/-- The `q`-series `1 + 6∑σ_χ(n)qⁿ`. -/
def e1Chi3 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * sigmaChi n

/-- The base change of `e1Chi3` to `R`. -/
noncomputable def e1Chi3In (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) e1Chi3

open CongruenceSubgroup in

/-- `e1Chi3` is the `q`-expansion of a weight-1 modular form on `Γ₁(3)`. -/
def E1Chi3IsModular : Prop :=
  ∃ f : ModularForm (Gamma1 3) 1, ∀ z : UpperHalfPlane,
    f z = ∑' n : ℕ,
      ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))

end EisensteinWeightOne
