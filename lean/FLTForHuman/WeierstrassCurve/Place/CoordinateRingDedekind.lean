/-
The shared coordinate-ring pair: the Dedekind-domain instance for the coordinate
ring of an elliptic curve, and the `XYIdeal` normal form of a nonzero prime ideal.

Canonical sources: the pinned FLT `aa2d8b3` `Theorems/` wrappers

* `Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean`,
* `Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean`

with their `S_` files
`P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean` and
`P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean`.  The
statements are transcribed verbatim from the wrappers (the pin's
`P2M.Dup.` prefix on `exists_eq_XYIdeal` is dropped: the checker matches by last
name).  Only the proof bodies are adapted to mathlib `v4.34.0`.

Assumes from lower modules: `WeierstrassCurve/Place/Dictionary.lean` — the
`XYIdeal` dictionary (`XYIdeal_isMaximal`, `XYIdeal_ne_bot`), the normal form
`exists_eq_XYIdeal_of_isMaximal`, and the Dedekind route
`isDedekindDomain_of_Δ_ne_zero`.  The pin's route to the instance
(`isDedekindDomain_of_isAlgClosed'`, 187 lines, a principal-ideal argument at
every maximal ideal) is not needed: the port's landed route is equivalent and
green, so only the statement is transcribed.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean>
-/
import FLTForHuman.WeierstrassCurve.Place.Dictionary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- The pin's `isMaximal_of_isPrime_of_ne_bot` (its `S_` file, 4 lines): a nonzero
prime ideal of the coordinate ring is maximal.  The pin proves it from
`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap` plus its
`IsPrime.to_maximal_ideal (Ideal.under_ne_bot F[X] hP)`; in mathlib `v4.34.0` the
contraction lemma is `Ideal.IsIntegral.under_ne_bot` (it now carries the
`[IsDomain W.CoordinateRing]` side condition, which is available) and the PID
step is unchanged. -/
private theorem isMaximal_of_isPrime_of_ne_bot (P : Ideal W.CoordinateRing) [P.IsPrime]
    (hP : P ≠ ⊥) : P.IsMaximal := by
  haveI : Module.Finite F[X] W.CoordinateRing :=
    Module.Finite.of_basis (CoordinateRing.basis W)
  haveI : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := F[X]) (S := W.CoordinateRing) P <|
    IsPrime.to_maximal_ideal (Ideal.IsIntegral.under_ne_bot F[X] hP)

/-- The pin's `P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal`
(`Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean:8`):
a nonzero prime ideal of the coordinate ring is the `XYIdeal` of some point.  The
pin's private `isMaximal_of_isPrime_of_ne_bot` supplies the maximality the ported
`exists_eq_XYIdeal_of_isMaximal` consumes. -/
theorem exists_eq_XYIdeal {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K]
    {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by
  obtain ⟨a, b, hab, hPab⟩ :=
    exists_eq_XYIdeal_of_isMaximal P (isMaximal_of_isPrime_of_ne_bot P hP)
  exact ⟨a, b, hab, hPab.symm⟩

/-- The pin's `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain`
(`Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean:8`).
The port proves it through the landed `isDedekindDomain_of_Δ_ne_zero` rather than
the pin's `isDedekindDomain_of_isAlgClosed'`. -/
theorem isDedekindDomain {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K)
    [W.IsElliptic] : IsDedekindDomain W.toAffine.CoordinateRing :=
  isDedekindDomain_of_Δ_ne_zero (W := W.toAffine) W.isUnit_Δ.ne_zero

end CoordinateRing
end Affine
end WeierstrassCurve
