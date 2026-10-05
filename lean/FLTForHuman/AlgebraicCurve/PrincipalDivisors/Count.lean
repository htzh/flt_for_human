/-
The Dedekind `count`/`spanSingleton` bridge used by the Weierstrass
unit-ideal/Abel block: the count of a principal fractional ideal is minus the
log of the valuation, the count-form reassembly of the height-one
factorization, and the resulting `ord = count` identity at a height-one
spectrum.

Transcribed verbatim from the pinned FLT `aa2d8b3`:
`P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
(lines 1823–1888), whose only consumer in the port is
`FLTForHuman/WeierstrassCurve/Place/UnitIdeal.lean`.  The two blocks live here,
in the generic `FractionalIdeal` / `AlgebraicCurve.Place` namespaces, rather than
in a Weierstrass module: they are Dedekind theory about an arbitrary fraction
ring, not mathematics about a curve.

`ord_ofHeightOneSpectrum_eq_count` is stated at the pin's binders and proved
directly through this module's `count_spanSingleton` and the already-ported
`AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq`.  The pin proves it
by rewriting through `ord_ofHeightOneSpectrum_eq_neg_log`, whose general ported
copy currently lives in the downstream `WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`;
inlining its three-line uniformizer step here keeps this module free of that
heavy dependency and avoids a second declaration of the same name (importing both
modules would clash).  The duplication is a `3`-line proof, not mathematics.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean>
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]

theorem count_spanSingleton (w : HeightOneSpectrum R) {f : L} (hf : f ≠ 0) :
    count L w (spanSingleton R⁰ f) = -log (w.valuation L f) := by
  classical
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ f
  have hn : n ≠ 0 := by
    rintro rfl
    exact hf (IsLocalization.mk'_zero (M := R⁰) (S := L) d)
  have hd : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2

  have hI : spanSingleton R⁰ (IsLocalization.mk' L n d) =
      spanSingleton R⁰ ((algebraMap R L) (d : R))⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [count_well_defined L w (spanSingleton_ne_zero_iff.mpr hf) hI]

  rw [HeightOneSpectrum.valuation_of_mk',
    log_div (w.intValuation_ne_zero n hn) (w.intValuation_ne_zero (d : R) hd),
    w.intValuation_if_neg hn, w.intValuation_if_neg hd, log_exp, log_exp]
  ring

theorem finprod_heightOneSpectrum_count {I : FractionalIdeal R⁰ L} (hI : I ≠ 0) :
    (∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ L) ^ count L w I) = I := by
  classical
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  calc (∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ L) ^ count L w I)
      = ∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ L) ^
          ((Associates.mk w.asIdeal).count (Associates.mk J).factors -
            (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) :=
        finprod_congr fun w => by rw [count_well_defined L w hI haJ]
    _ = I := finprod_heightOneSpectrum_factorization hI haJ

theorem eq_of_count_eq {I J : FractionalIdeal R⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum R, count L w I = count L w J) : I = J := by
  rw [← finprod_heightOneSpectrum_count hI, ← finprod_heightOneSpectrum_count hJ]
  exact finprod_congr fun w => by rw [h w]

end FractionalIdeal

namespace AlgebraicCurve

namespace Place

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
variable [Algebra K R] [Algebra K L] [IsScalarTower K R L]

theorem ord_ofHeightOneSpectrum_eq_count (w : HeightOneSpectrum R) {f : L} (hf : f ≠ 0) :
    (ofHeightOneSpectrum (K := K) w).ord f
      = FractionalIdeal.count L w (FractionalIdeal.spanSingleton R⁰ f) := by
  rw [FractionalIdeal.count_spanSingleton w hf]
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hval : w.valuation L (algebraMap R L π) = exp (-1 : ℤ) := by
    rw [w.valuation_of_algebraMap]
    exact hπ
  exact (ofHeightOneSpectrum (K := K) w).ord_eq_neg_log_of_valuationSubring_eq
    (w.valuation L) rfl hval hf

end Place

end AlgebraicCurve

end
