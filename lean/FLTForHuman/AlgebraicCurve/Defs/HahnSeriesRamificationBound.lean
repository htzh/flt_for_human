/-
The ramified-embedding vocabulary of a Puiseux/Hahn-series function field, after FLT's
`Definitions/Def_HahnSeries_RamificationBound.lean` (42 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HahnSeries_RamificationBound.lean>).

`ramScale e` embeds the integer exponents into `ℚ` as `k ↦ k / e`; `puiseuxRamEmb` carries a Hahn
series over `ℤ` to one over `ℚ` along that embedding; `HasRamBound e y` says every support point of
`y` is integral over `e` (`y.support ⊆ (1/e)ℤ`); and `puiseuxRamSubfield` is the image of that
embedding as a subfield. It is the vocabulary of the ramified Hahn-series place construction
(`Place.exists_ord_mul_eq_order_of_hasRamBound`). The statements are the pin's verbatim; the
module needs only mathlib's Hahn-series algebra.

spec-pin: Definitions/Def_HahnSeries_RamificationBound.lean
-/
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.CharP.IntermediateField

set_option autoImplicit false

noncomputable section

namespace HahnSeries

variable {K : Type*} [Field K]

def ramScale (e : ℕ) : ℤ →+ ℚ where
  toFun k := (k : ℚ) / e
  map_zero' := by simp
  map_add' a b := by simp only [Int.cast_add]; rw [add_div]

@[simp] theorem ramScale_apply (e : ℕ) (k : ℤ) : ramScale e k = (k : ℚ) / e := rfl

theorem ramScale_injective {e : ℕ} (he : 0 < e) : Function.Injective (ramScale e) := by
  intro a b hab
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  simp only [ramScale_apply, div_eq_div_iff he' he'] at hab
  exact_mod_cast mul_right_cancel₀ he' hab

theorem ramScale_le_iff {e : ℕ} (he : 0 < e) (a b : ℤ) :
    ramScale e a ≤ ramScale e b ↔ a ≤ b := by
  have he' : (0 : ℚ) < e := Nat.cast_pos.mpr he
  simp only [ramScale_apply, div_le_div_iff_of_pos_right he', Int.cast_le]

def puiseuxRamEmb {e : ℕ} (he : 0 < e) : HahnSeries ℤ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (ramScale e) (ramScale_injective he) (ramScale_le_iff he)

def HasRamBound (e : ℕ) (y : HahnSeries ℚ K) : Prop :=
  y.support ⊆ Set.range (fun k : ℤ => (k : ℚ) / e)

variable (K) in

def puiseuxRamSubfield {e : ℕ} (he : 0 < e) : Subfield (HahnSeries ℚ K) :=
  (puiseuxRamEmb (K := K) he).fieldRange

end HahnSeries

end
