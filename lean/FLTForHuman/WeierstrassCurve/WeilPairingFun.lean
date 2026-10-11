/-
The function-field (ad hoc) Weil pairing `weilPairing0` of an affine Weierstrass
curve, after the pinned FLT `Definitions/Def_EllipticCurve_WeilPairingFun.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_WeilPairingFun.lean>),
69 lines / 13 declarations.

`placeIdeal P` is the ideal of the place of a nonzero point (`⊤` at the origin);
`fibIdeal n Q` is the product of the `placeIdeal`s over the set of `n`-division
points of `Q`, and `weilNum` is its principal generator when there is one.
`weilFun n T = weilNum n T / weilNum n 0` is the Miller function, and
`weilPairing0 n S T` extracts the scalar `c` with
`transEquiv S (weilFun n T) = c * weilFun n T` when it exists (and `1` otherwise);
`transEquiv_weilFun` and `weilPairing0_of_not` are the two definitional
branches. This is the definition consumed by the `ModularCurve.FullLevel` /
`LevelComponent` packages; the general divisorial construction is a separate
node (`Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`).

Assumes `FLTForHuman.WeierstrassCurve.Place.PointPlace` — the pin's `placeOf`
and `transEquiv` (the needed slice of
`Definitions/Def_EllipticCurve_FunctionFieldPullback.lean`); see that module's
header and `CARRY-FORWARD.md` for the deferred surface.

Statements are transcribed verbatim from the pin (only proof bodies adapted to
mathlib `v4.34.0`; `dif_pos`/`dif_neg` become `dite_eq_left`/`dite_eq_right`);
the pin's names, namespaces and kinds are kept.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_WeilPairingFun.lean>
-/
import FLTForHuman.WeierstrassCurve.Place.PointPlace
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

section WeilPairingDefs

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

open Classical in

noncomputable def placeIdeal (P : (W⁄K).Point) : Ideal (W⁄K).CoordinateRing :=
  if hP : P = 0 then ⊤ else (placeOf W K P hP).asIdeal

theorem placeIdeal_zero : placeIdeal W K 0 = ⊤ := dite_eq_left rfl

theorem placeIdeal_of_ne_zero {P : (W⁄K).Point} (hP : P ≠ 0) :
    placeIdeal W K P = (placeOf W K P hP).asIdeal := dite_eq_right hP

def fibSet (n : ℤ) (Q : (W⁄K).Point) : Set (W⁄K).Point := {P | n • P = Q}

@[simp] theorem mem_fibSet {n : ℤ} {Q P : (W⁄K).Point} : P ∈ fibSet W K n Q ↔ n • P = Q := Iff.rfl

open Classical in

noncomputable def fibIdeal (n : ℤ) (Q : (W⁄K).Point) : Ideal (W⁄K).CoordinateRing :=
  if h : (fibSet W K n Q).Finite then ∏ P ∈ h.toFinset, placeIdeal W K P else ⊤

theorem fibIdeal_eq {n : ℤ} {Q : (W⁄K).Point} (h : (fibSet W K n Q).Finite) :
    fibIdeal W K n Q = ∏ P ∈ h.toFinset, placeIdeal W K P := by
  rw [fibIdeal, dite_eq_left h]

open Classical in

noncomputable def weilNum (n : ℤ) (T : (W⁄K).Point) : (W⁄K).CoordinateRing :=
  if h : (fibIdeal W K n T).IsPrincipal then @Submodule.IsPrincipal.generator _ _ _ _ _ _ h else 1

theorem span_weilNum {n : ℤ} {T : (W⁄K).Point} (h : (fibIdeal W K n T).IsPrincipal) :
    Ideal.span {weilNum W K n T} = fibIdeal W K n T := by
  rw [weilNum, dite_eq_left h]
  exact @Ideal.span_singleton_generator _ _ _ h

noncomputable def weilFun (n : ℤ) (T : (W⁄K).Point) : (W⁄K).FunctionField :=
  algebraMap _ (W⁄K).FunctionField (weilNum W K n T) / algebraMap _ (W⁄K).FunctionField (weilNum W K n 0)

open Classical in

noncomputable def weilPairing0 [IsAlgClosed K] [W.IsElliptic] (n : ℤ) (S T : (W⁄K).Point) : Kˣ :=
  if h : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T
  then h.choose else 1

theorem transEquiv_weilFun [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (weilPairing0 W K n S T : K) * weilFun W K n T := by
  rw [weilPairing0, dite_eq_left h]
  exact h.choose_spec

theorem weilPairing0_of_not [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ¬ ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    weilPairing0 W K n S T = 1 := by
  rw [weilPairing0, dite_eq_right h]

end WeilPairingDefs

end WeierstrassCurve.Affine

#print axioms WeierstrassCurve.Affine.transEquiv_weilFun
#print axioms WeierstrassCurve.Affine.weilPairing0_of_not
