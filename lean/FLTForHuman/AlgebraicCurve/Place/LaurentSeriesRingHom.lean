/-
The place/order dictionary of the Laurent-series model, at the ring-hom spelling.

`Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` states, for an algebra map
`ι : F →ₐ[K] LaurentSeries K` that is not order-trivial, that there are a place `w` of `F`
and a positive integer `γ` with `w.ord x * γ = (ι x).order` for every `x`.  Downstream
modules sometimes only have a ring hom `f : F →+* LaurentSeries K` together with the
statement that `f` sends constants to `HahnSeries.C` — the `ℂ`-algebra structure on
`LaurentSeries K` is a Mathlib diamond (`HahnSeries.instAlgebra` versus
`HahnSeries.powerSeriesAlgebra`), so an algebra map produced in one module cannot be passed
to a consumer elaborated under the other spelling.  This file states the dictionary for the
ring-hom spelling, which needs no `LaurentSeries`-side algebra instance at all: the lift to
`HahnSeries ℚ K` is built from `f`, the ram-bound dictionary applies to it, and the scaling
`γ` is recovered from the order at a uniformiser.

The pin's statement
`AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` is the wrapper
`Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean` of
`P2M/Sol/S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean`
(pinned `aa2d8b3`; public mirror
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean>).
This is the port's own spelling of its proof, not a transcription of that statement, so the
declaration carries an `own:` row in `spec/decl_markers.tsv`.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean
-/
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Place

/- The `K`-algebra structure on `HahnSeries ℚ K` is a diamond in `Mathlib`
(`HahnSeries.instAlgebra` versus `HahnSeries.powerSeriesAlgebra`); the ram-bound dictionary
below is stated with the former, so this file pins it locally. -/
attribute [local instance 2000] HahnSeries.instAlgebra

/-- A ring hom `F →+* LaurentSeries K` that sends constants to `HahnSeries.C` is a rescaled
order map: there are a place `w` of `F` and a positive integer `γ` with
`w.ord x * γ = (f x).order` for every `x`. -/
theorem exists_ord_mul_eq_order_of_ringHom
    {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
    (f : F →+* LaurentSeries K)
    (hf : ∀ c : K, f (algebraMap K F c) = HahnSeries.C c)
    (h : ∃ x : F, (f x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (f x).order := by
  let φ : F →ₐ[K] HahnSeries ℚ K :=
    { toRingHom := (HahnSeries.puiseuxRamEmb one_pos).comp f
      commutes' := by
        intro c
        show HahnSeries.puiseuxRamEmb one_pos (f (algebraMap K F c)) =
          algebraMap K (HahnSeries ℚ K) c
        rw [hf c, HahnSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact HahnSeries.embDomainRingHom_C }
  have horder : ∀ x : F, (φ x).order = ((f x).order : ℚ) := by
    intro x
    show (HahnSeries.puiseuxRamEmb one_pos (f x)).order = _
    rw [LaurentSeriesModel.order_puiseuxRamEmb one_pos, HahnSeries.ramScale_apply]
    simp
  have hRB : ∀ x : F, HahnSeries.HasRamBound 1 (φ x) := fun x =>
    LaurentSeriesModel.hasRamBound_puiseuxRamEmb one_pos (f x)
  obtain ⟨x₀, hx₀⟩ := h
  have hnt : ∃ x : F, (φ x).order ≠ 0 := by
    refine ⟨x₀, ?_⟩
    rw [horder]
    exact_mod_cast hx₀
  obtain ⟨w, g, hg, hgw⟩ :=
    exists_ord_mul_eq_order_of_hasRamBound (K := K) (L := K) (F := F) (d := 1) φ
      one_pos hRB hnt
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hordπ : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hgval : g = ((f (π : F)).order : ℚ) := by
    have h1 := hgw (π : F)
    rw [hordπ, horder] at h1
    simpa using h1
  have hpos : 0 < (f (π : F)).order := by
    rw [hgval] at hg
    exact_mod_cast hg
  refine ⟨w, ((f (π : F)).order).toNat, by omega, fun x => ?_⟩
  have h1 := hgw x
  rw [hgval, horder] at h1
  have h2 : w.ord x * (f (π : F)).order = (f x).order := by exact_mod_cast h1
  rw [Int.toNat_of_nonneg hpos.le]
  exact h2

end Place

end AlgebraicCurve
