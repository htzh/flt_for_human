/-
  A function with nonzero order at a place is transcendental over the constants: the
  second of the three `localParam` leaves of the Deligne–Serre cone. The proof is the
  classical one: an algebraic element is integral, so lies in every valuation ring
  (`mem_of_isAlgebraic`, from `mem_of_eval_monic_eq_zero` applied to the image of the
  minimal polynomial), and an element of the valuation ring is a unit times a
  nonnegative power of a uniformiser, hence has order zero (`ord_coe_unit`).

  Statements are transcribed verbatim from the pinned FLT proof
  (`anthropics/fermats-last-theorem`, `aa2d8b3`); only proof bodies are adapted to
  mathlib `v4.34.0`. The pin's imports of
  `Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean` are the port's already:
  `Place.mem_of_eval_monic_eq_zero` (`Defs/PlacesOverDVR.lean`), and
  `Place.ord_coe_unit`, `Place.ord_zero`, `Place.algebraMap_mem'`
  (`Defs/Place.lean`). Two public declarations
  (`AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic'` and the headline) plus one
  `private` helper, as in the pin.

  Role: tier 1 and a premise of the third `localParam` leaf
  (`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`, WORKORDER-LP4).

  spec-pin: Theorems/Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace AlgebraicCurve

namespace Place

namespace TranscendentalOfOrdNeZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mem_of_isAlgebraic (v : Place K F) {x : F} (hx : IsAlgebraic K x) :
    x ∈ v.toValuationSubring := by
  have hint : IsIntegral K x := hx.isIntegral
  refine v.mem_of_eval_monic_eq_zero (P := (minpoly K x).map (algebraMap K F))
    ((minpoly.monic hint).map _) (fun i => ?_) ?_
  · rw [coeff_map]; exact v.algebraMap_mem' _
  · rw [eval_map_algebraMap, minpoly.aeval]

end TranscendentalOfOrdNeZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_eq_zero_of_isAlgebraic' {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0, v.ord_zero]
  · let u : v.toValuationSubringˣ :=
      { val := ⟨x, TranscendentalOfOrdNeZero.mem_of_isAlgebraic v hx⟩
        inv := ⟨x⁻¹, TranscendentalOfOrdNeZero.mem_of_isAlgebraic v hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u

end Place

end AlgebraicCurve

namespace AlgebraicCurve

-- pin: AlgebraicCurve.Place.transcendental_of_ord_ne_zero (Theorems/Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean:9)
theorem Place.transcendental_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t :=
  fun h => ht (Place.ord_eq_zero_of_isAlgebraic' v h)

end AlgebraicCurve
