/-
The point/place dictionary of an affine Weierstrass curve, together with the
translation automorphism of its function field — the slice of the pinned FLT
`Definitions/Def_EllipticCurve_FunctionFieldPullback.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean>)
that the `weilPairing0` construction (`WeilPairingFun.lean`) consumes.

It carries the pin's `Point.xc`/`Point.yc` coordinate accessors and their
lemmas, `placeOf` (a nonzero rational point as a height-one spectrum of the
coordinate ring, built on the port's `CoordinateRing.heightOneSpectrumOfEquation`),
and `transEquiv` (the translation-by-`S` automorphism of the function field,
re-derived from the port's `translationAlgEquivOf`, `Velu/Engine.lean`; the
pin's `transPull`/`pointPull`/`pointHom` route to it is not transcribed).

The rest of that pin node — `genericX`/`genericY`, `genericPoint`, `pointHom`,
`pointPull`, `transPull`, `negPull`/`negEquiv`, `mulPull` and their lemmas — is
**not** ported here; the deferred surface is registered in `CARRY-FORWARD.md`.
This module is the boundary slice, not a whole-node port.

Statements are transcribed verbatim from the pin (only proof bodies adapted to
mathlib `v4.34.0`; `dif_pos`/`dif_neg` become `dite_eq_left`/`dite_eq_right`);
the pin's declaration names, namespaces and kinds are kept.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Engine
import FLTForHuman.WeierstrassCurve.Place.Dictionary

set_option autoImplicit false

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

namespace Point

variable {S : Type*} [CommRing S] {V : Affine S}

def xc : V.Point → S
  | 0 => 0
  | some x _ _ => x

def yc : V.Point → S
  | 0 => 0
  | some _ y _ => y

@[simp] lemma xc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).xc = x := rfl

@[simp] lemma yc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).yc = y := rfl

lemma nonsingular_xc_yc {P : V.Point} (hP : P ≠ 0) : V.Nonsingular P.xc P.yc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

lemma eq_some_xc_yc {P : V.Point} (hP : P ≠ 0) :
    P = some P.xc P.yc (nonsingular_xc_yc hP) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

end Point

section Places

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

noncomputable def placeOf (P : (W⁄K).Point) (hP : P ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing :=
  CoordinateRing.heightOneSpectrumOfEquation (Point.nonsingular_xc_yc hP).left

omit [DecidableEq K] in
@[simp] theorem placeOf_asIdeal (P : (W⁄K).Point) (hP : P ≠ 0) :
    (placeOf W K P hP).asIdeal = CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) := rfl

variable [IsAlgClosed K] [W.IsElliptic]

/-- Translation by the rational point `S` on the function field. The pin builds
this from `transPull`; the port's route is `translationAlgEquivOf`
(`Velu/Engine.lean`), the same automorphism. -/
noncomputable def transEquiv (S : (W⁄K).Point) :
    (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  match S with
  | .zero => AlgEquiv.refl
  | .some x y h =>
      haveI : (W⁄K).IsElliptic := by
        dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
      translationAlgEquivOf (isElliptic_Δ_ne_zero (W := W⁄K)) h.left

end Places

end WeierstrassCurve.Affine
