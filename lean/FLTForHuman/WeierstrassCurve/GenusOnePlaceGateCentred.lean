/-
The Weierstrass genus-one place gate, centred, with Abel's theorem.

Over an algebraically closed field `F`, for an elliptic affine Weierstrass curve
`W` whose coordinate ring is Dedekind and whose function field has principal
divisors, there is a `GenusOnePlaceGate W` — a bijection between `W.Point` and the
degree-one places of the function field — which is *centred* (the classes of
`X - x` and `Y - y` are non-units at the place of `(x, y)`) and which satisfies
Abel's theorem (a degree-zero divisor is principal iff its divisor sum is zero).

This is the capstone of the genus-one silo.  Its statement is the pin's
`Theorems/` wrapper verbatim; its proof is the pin's `solution` body
(`P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
lines 2252–2288), adapted to mathlib `v4.34.0`.  The gate instance is built from
the geometric point↔place bijection; the `IsCentred` fields are the two non-unit
statements at `geomPlaceOfPoint (Point.some x y h)`; the `AbelTheorem` field is
the `GeomAbelTheorem` instance supplied by `HasPrincipalDivisors`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean>
-/
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGate
import FLTForHuman.WeierstrassCurve.Place.RRSpace
import FLTForHuman.WeierstrassCurve.Place.UnitIdeal

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

theorem exists_genusOnePlaceGate_isCentred_and_abelTheorem
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [IsDedekindDomain W.CoordinateRing] [AlgebraicCurve.HasPrincipalDivisors F W.FunctionField] :
    ∃ g : WeierstrassCurve.Affine.GenusOnePlaceGate W,
      @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g
        ∧ @WeierstrassCurve.Affine.AbelTheorem F _ _ W g := by

  let g : WeierstrassCurve.Affine.GenusOnePlaceGate W :=
    { pointEquivPlace := WeierstrassCurve.Affine.geomPointEquivPlace
      deg_eq_one := fun v => by
        obtain ⟨P, rfl⟩ := WeierstrassCurve.Affine.geomPlaceOfPoint_surjective
          (WeierstrassCurve.Affine.isElliptic_Δ_ne_zero (W := W)) v
        exact WeierstrassCurve.Affine.deg_geomPlaceOfPoint P }
  letI := g
  refine ⟨g, ⟨?_, ?_⟩, ⟨?_⟩⟩
  ·
    intro x y h
    change algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (WeierstrassCurve.Affine.geomPlaceOfPoint (Point.some x y h)).toValuationSubring.nonunits
    rw [WeierstrassCurve.Affine.geomPlaceOfPoint_some, WeierstrassCurve.Affine.placeOfEquation,
      AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring, ValuationSubring.mem_nonunits_iff]
    refine (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.mp ?_
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem,
      WeierstrassCurve.Affine.CoordinateRing.heightOneSpectrumOfEquation_asIdeal]
    exact Ideal.subset_span (Set.mem_insert _ _)
  ·
    intro x y h
    change algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (WeierstrassCurve.Affine.geomPlaceOfPoint (Point.some x y h)).toValuationSubring.nonunits
    rw [WeierstrassCurve.Affine.geomPlaceOfPoint_some, WeierstrassCurve.Affine.placeOfEquation,
      AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring, ValuationSubring.mem_nonunits_iff]
    refine (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.mp ?_
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem,
      WeierstrassCurve.Affine.CoordinateRing.heightOneSpectrumOfEquation_asIdeal]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  ·
    intro D hD
    exact WeierstrassCurve.Affine.GeomAbelTheorem.isPrincipal_iff_geomDivisorSum_eq_zero D hD

end WeierstrassCurve.Affine

end
