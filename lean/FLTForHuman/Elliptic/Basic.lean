/-
Shared elliptic-curve setup for the FLT fragments in this project.

This module holds the definitions and instances that several fragments need
before any proof work starts. It imports mathlib only.

Origin: the pieces here are the parts of the FLT development that are pure
plumbing over mathlib. See `logs/card-torsion-port.md` for the trace and the ground rules.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Module.Torsion.Basic

open scoped WeierstrassCurve.Affine

namespace FLTForHuman.Elliptic

/-- The point group of `W` base changed to the algebra `S`, written `W⟮S⟯`.
FLT declares the same notation under `WeierstrassCurve.Affine`. -/
scoped notation3:max W' "⟮" S "⟯" =>
  WeierstrassCurve.Affine.Point (WeierstrassCurve.Affine.baseChange W' S)

/-- Base change preserves nonsingularity: if `W` is elliptic over `R` then so is
its base change to any `R`-algebra `A`.

mathlib proves this for `W.map f`; instance search does not find the
`baseChange` form on its own because it will not unfold the definition, so the
FLT development states it explicitly (`Def_WeierstrassCurve_EDSEngine.lean`,
`instIsEllipticBaseChange`) and we keep that one line. -/
instance instIsEllipticBaseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs <| (W.map (algebraMap R A)).IsElliptic

end FLTForHuman.Elliptic
