/-
The value/centre dictionary at a `Place` and the realisation core of the
place-realisation development: `Place.HasValueAt` and its add/mul/neg/inv/div/pow
lemmas, `compSubring`, `value`, `centre`, `compValuationSubring`,
`exists_unique_valueHom`, `exists_place_centre_comap_eq`, the transcendental/adjoin
block, and the `eq_of_forall_mem_nonunits_iff` place-identity lemmas.

It was split out of `FLTForHuman/AlgebraicCurve/Place/ValuationSubringCore.lean`
(itself split from `Place/IsPrimeOverValuationSubring.lean`); the `Place`-free half
now lives in `FLTForHuman/NumberTheory/ValuationSubring/Domination.lean`, which this
module imports. See the reuse note
`lean/topics/algebraicCurve/TOPIC-valuation-subring-core.md`.

This module is public but **tier 3** (unwired): it is built and importable, but it
is deliberately not listed in the statement checker's `PORT_FILES`; its surface is
recorded in `lean/spec/UNWIRED-PUBLIC.md`. Every declaration carries a `-- pin:`
comment naming its line in the pin original.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean
-/

import FLTForHuman.NumberTheory.ValuationSubring.Domination
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are kept literal, as in `Defs/PlacesOverDVR.lean`.
set_option linter.style.haveILetI false

open Polynomial
open IsLocalRing
open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

-- pin: AlgebraicCurve.Place.algebraMap_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:153)
theorem _root_.AlgebraicCurve.Place.algebraMap_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring := w.algebraMap_mem' a


-- pin: AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:157)
theorem _root_.AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using w.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]


-- pin: AlgebraicCurve.Place.mul_mem_nonunits (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:169)
theorem _root_.AlgebraicCurve.Place.mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx


-- pin: AlgebraicCurve.Place.mem_of_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:181)
theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)


-- pin: AlgebraicCurve.Place.mem_nonunits_iff_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:191)
theorem _root_.AlgebraicCurve.Place.mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_pos h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'


-- pin: AlgebraicCurve.Place.HasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:207)
def _root_.AlgebraicCurve.Place.HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

-- pin: hasValueAt_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:211)
theorem hasValueAt_iff (f : F) (a : K) :
    w.HasValueAt f a ↔ f - algebraMap K F a ∈ w.toValuationSubring.nonunits := Iff.rfl

-- pin: AlgebraicCurve.Place.hasValueAt_iff_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:214)
theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_ord_pos {f : F} {a : K} (h : f ≠ algebraMap K F a) :
    w.HasValueAt f a ↔ 0 < w.ord (f - algebraMap K F a) :=
  w.mem_nonunits_iff_ord_pos (sub_ne_zero.mpr h)

-- pin: AlgebraicCurve.Place.hasValueAt_of_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:219)
theorem _root_.AlgebraicCurve.Place.hasValueAt_of_ord_pos {f : F} {a : K} (h : 0 < w.ord (f - algebraMap K F a)) :
    w.HasValueAt f a := by
  have hne : f ≠ algebraMap K F a := by
    intro hfa; rw [hfa, sub_self] at h; simp at h
  exact (w.hasValueAt_iff_ord_pos hne).mpr h


-- pin: AlgebraicCurve.Place.hasValueAt_algebraMap (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:227)
theorem _root_.AlgebraicCurve.Place.hasValueAt_algebraMap (a : K) : w.HasValueAt (algebraMap K F a) a := by
  simp [HasValueAt, ZeroMemClass.zero_mem]


-- pin: AlgebraicCurve.Place.hasValueAt_zero_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:232)
theorem _root_.AlgebraicCurve.Place.hasValueAt_zero_iff (f : F) : w.HasValueAt f 0 ↔ f ∈ w.toValuationSubring.nonunits := by
  simp [HasValueAt]


-- pin: AlgebraicCurve.Place.mem_of_hasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:237)
theorem _root_.AlgebraicCurve.Place.mem_of_hasValueAt {f : F} {a : K} (h : w.HasValueAt f a) : f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (w.algebraMap_mem a)

namespace HasValueAt
variable {w} in

-- pin: AlgebraicCurve.Place.HasValueAt.unique (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:245)
theorem _root_.AlgebraicCurve.Place.HasValueAt.unique {f : F} {a b : K} (ha : w.HasValueAt f a) (hb : w.HasValueAt f b) :
    a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((w.algebraMap_mem_nonunits_iff _).mp h)

end HasValueAt
namespace HasValueAt
variable {w} in
-- pin: AlgebraicCurve.Place.HasValueAt.add (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:256)
theorem _root_.AlgebraicCurve.Place.HasValueAt.add {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HasValueAt, map_add]
  convert this using 1
  ring

end HasValueAt
namespace HasValueAt
variable {w} in
-- pin: AlgebraicCurve.Place.HasValueAt.neg (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:267)
theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) := by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
namespace HasValueAt
variable {w} in
-- pin: AlgebraicCurve.Place.HasValueAt.mul (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:277)
theorem _root_.AlgebraicCurve.Place.HasValueAt.mul {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (w.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hg (w.algebraMap_mem a)
  have := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert this using 1
  ring

end HasValueAt
namespace HasValueAt
variable {w} in

-- pin: AlgebraicCurve.Place.HasValueAt.pow (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:293)
theorem _root_.AlgebraicCurve.Place.HasValueAt.pow {f : F} {a : K} (hf : w.HasValueAt f a) (n : ℕ) :
    w.HasValueAt (f ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using w.hasValueAt_algebraMap 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hf

end HasValueAt
namespace HasValueAt
variable {w} in

-- pin: AlgebraicCurve.Place.HasValueAt.inv (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:306)
theorem _root_.AlgebraicCurve.Place.HasValueAt.inv {f : F} {a : K} (hf : w.HasValueAt f a) (ha : a ≠ 0) :
    w.HasValueAt f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
    exact ha (hf.unique this)
  have hfu : f ∉ w.toValuationSubring.nonunits := fun hfn =>
    ha (hf.unique ((w.hasValueAt_zero_iff f).mpr hfn))
  have hfinv : f⁻¹ ∈ w.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (mul_mem hfinv (w.algebraMap_mem _))
  have := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ w.toValuationSubring.nonunits
  convert this using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

end HasValueAt
namespace HasValueAt
variable {w} in

-- pin: AlgebraicCurve.Place.HasValueAt.div (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:333)
theorem _root_.AlgebraicCurve.Place.HasValueAt.div {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b)
    (hb : b ≠ 0) : w.HasValueAt (f / g) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hf.mul (hg.inv hb)

end HasValueAt

-- pin: AlgebraicCurve.Place.hasValueAt_iff_residue (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:341)
theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_residue {f : F} (hf : f ∈ w.toValuationSubring) (a : K) :
    w.HasValueAt f a ↔
      residue w.toValuationSubring ⟨f, hf⟩ = algebraMap K w.ResidueField a := by
  have e : algebraMap K w.ResidueField a =
      residue w.toValuationSubring (algebraMap K w.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl


-- pin: AlgebraicCurve.Place.exists_hasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:351)
theorem _root_.AlgebraicCurve.Place.exists_hasValueAt (hw : Function.Surjective (algebraMap K w.ResidueField)) {f : F}
    (hf : f ∈ w.toValuationSubring) : ∃ a : K, w.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (w.hasValueAt_iff_residue hf a).mpr ha.symm⟩


-- pin: AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:358)
theorem _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K w.ResidueField] : Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2


-- pin: surjective_algebraMap_residueField_of_deg_eq_one (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:365)
theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  w.surjective_algebraMap_residueField_of_isAlgClosed

variable (A : ValuationSubring K)

-- pin: AlgebraicCurve.Place.compSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:372)
def _root_.AlgebraicCurve.Place.compSubring : Subring F where
  carrier := {f | ∃ a : A, w.HasValueAt f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simpa using ha.mul hb⟩
  one_mem' := ⟨1, by simpa using w.hasValueAt_algebraMap 1⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using w.hasValueAt_algebraMap 0⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by simpa using ha.neg⟩

variable {A} in
-- pin: mem_compSubring_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:388)
theorem mem_compSubring_iff {f : F} : f ∈ w.compSubring A ↔ ∃ a : A, w.HasValueAt f a :=
  Iff.rfl

variable {A} in
-- pin: AlgebraicCurve.Place.mem_compSubring_of_hasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:392)
theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_hasValueAt {f : F} {a : K} (ha : a ∈ A) (h : w.HasValueAt f a) :
    f ∈ w.compSubring A :=
  ⟨⟨a, ha⟩, h⟩


-- pin: AlgebraicCurve.Place.compSubring_le (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:398)
theorem _root_.AlgebraicCurve.Place.compSubring_le : w.compSubring A ≤ w.toValuationSubring.toSubring := by
  rintro f ⟨a, ha⟩
  exact w.mem_of_hasValueAt ha


-- pin: AlgebraicCurve.Place.mem_compSubring_of_mem_nonunits (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:404)
theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_mem_nonunits {f : F} (hf : f ∈ w.toValuationSubring.nonunits) :
    f ∈ w.compSubring A :=
  ⟨0, by simpa [w.hasValueAt_zero_iff] using hf⟩


-- pin: AlgebraicCurve.Place.algebraMap_mem_compSubring_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:410)
theorem _root_.AlgebraicCurve.Place.algebraMap_mem_compSubring_iff (a : K) : algebraMap K F a ∈ w.compSubring A ↔ a ∈ A := by
  constructor
  · rintro ⟨b, hb⟩
    rw [(w.hasValueAt_algebraMap a).unique hb]
    exact b.2
  · intro ha
    exact ⟨⟨a, ha⟩, w.hasValueAt_algebraMap a⟩


-- pin: AlgebraicCurve.Place.value (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:420)
def _root_.AlgebraicCurve.Place.value : w.compSubring A →+* A where
  toFun f := Classical.choose f.2
  map_one' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).one_mem).unique (by
      simpa using w.hasValueAt_algebraMap 1)
  map_mul' f g := Subtype.ext <|
    (Classical.choose_spec (mul_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).mul (Classical.choose_spec g.2))
  map_zero' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).zero_mem).unique (by
      simpa using w.hasValueAt_algebraMap 0)
  map_add' f g := Subtype.ext <|
    (Classical.choose_spec (add_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).add (Classical.choose_spec g.2))


-- pin: AlgebraicCurve.Place.hasValueAt_value (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:437)
theorem _root_.AlgebraicCurve.Place.hasValueAt_value (f : w.compSubring A) : w.HasValueAt (f : F) (w.value A f : K) :=
  Classical.choose_spec f.2

variable {A} in
-- pin: AlgebraicCurve.Place.value_eq_of_hasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:442)
theorem _root_.AlgebraicCurve.Place.value_eq_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F) a) :
    w.value A f = a :=
  Subtype.ext ((w.hasValueAt_value A f).unique h)

variable {A} in

-- pin: ord_sub_value_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:449)
theorem ord_sub_value_pos {f : w.compSubring A} (hf : (f : F) ≠ algebraMap K F (w.value A f)) :
    0 < w.ord ((f : F) - algebraMap K F (w.value A f)) :=
  (w.hasValueAt_iff_ord_pos hf).mp (w.hasValueAt_value A f)

variable {A} in
-- pin: value_eq_of_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:454)
theorem value_eq_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : w.value A f = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_of_ord_pos h)

-- pin: AlgebraicCurve.Place.value_algebraMap (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:458)
theorem _root_.AlgebraicCurve.Place.value_algebraMap (a : A) :
    w.value A ⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap (a : K))

-- pin: AlgebraicCurve.Place.value_surjective (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:463)
theorem _root_.AlgebraicCurve.Place.value_surjective : Function.Surjective (w.value A) :=
  fun a => ⟨_, w.value_algebraMap A a⟩

variable {A} in

-- pin: AlgebraicCurve.Place.value_eq_zero_of_mem_nonunits (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:469)
theorem _root_.AlgebraicCurve.Place.value_eq_zero_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : w.value A f = 0 :=
  w.value_eq_of_hasValueAt (by simpa [w.hasValueAt_zero_iff] using hf)


-- pin: AlgebraicCurve.Place.centre (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:475)
def _root_.AlgebraicCurve.Place.centre : Ideal (w.compSubring A) := (maximalIdeal A).comap (w.value A)

-- pin: centre_isPrime (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:478)
scoped instance centre_isPrime : (w.centre A).IsPrime := Ideal.comap_isPrime _ _

-- pin: centre_isMaximal (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:480)
scoped instance centre_isMaximal : (w.centre A).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (w.value_surjective A)

variable {A} in
-- pin: AlgebraicCurve.Place.mem_centre_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:484)
theorem _root_.AlgebraicCurve.Place.mem_centre_iff (f : w.compSubring A) : f ∈ w.centre A ↔ w.value A f ∈ maximalIdeal A :=
  Iff.rfl

variable {A} in
-- pin: AlgebraicCurve.Place.mem_centre_iff_of_hasValueAt (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:489)
theorem _root_.AlgebraicCurve.Place.mem_centre_iff_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F) a) :
    f ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, w.value_eq_of_hasValueAt h]

variable {A} in

-- pin: mem_centre_iff_of_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:496)
theorem mem_centre_iff_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : f ∈ w.centre A ↔ a ∈ maximalIdeal A :=
  w.mem_centre_iff_of_hasValueAt (w.hasValueAt_of_ord_pos h)

variable {A} in

-- pin: AlgebraicCurve.Place.mem_centre_of_mem_nonunits (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:502)
theorem _root_.AlgebraicCurve.Place.mem_centre_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : f ∈ w.centre A := by
  rw [mem_centre_iff, w.value_eq_zero_of_mem_nonunits hf]
  exact Ideal.zero_mem _

variable {A} in
-- pin: mem_centre_of_ord_pos (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:509)
theorem mem_centre_of_ord_pos {f : w.compSubring A} (hf : 0 < w.ord (f : F)) : f ∈ w.centre A :=
  w.mem_centre_of_mem_nonunits ((w.mem_nonunits_iff_ord_pos (by rintro h; simp [h] at hf)).mpr hf)

-- pin: AlgebraicCurve.Place.algebraMap_mem_centre_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:512)
theorem _root_.AlgebraicCurve.Place.algebraMap_mem_centre_iff (a : A) :
    (⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ : w.compSubring A)
        ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, value_algebraMap]


-- pin: AlgebraicCurve.Place.mem_compSubring_or_inv_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:519)
theorem _root_.AlgebraicCurve.Place.mem_compSubring_or_inv_mem (hw : Function.Surjective (algebraMap K w.ResidueField))
    (f : F) : f ∈ w.compSubring A ∨ f⁻¹ ∈ w.compSubring A := by
  by_cases hf : f ∈ w.toValuationSubring
  · obtain ⟨c, hc⟩ := w.exists_hasValueAt hw hf
    by_cases hcA : c ∈ A
    · exact Or.inl ⟨⟨c, hcA⟩, hc⟩
    · right

      have hcA' : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
        exact hc0 (hc.unique this)
      have hfu : f ∉ w.toValuationSubring.nonunits := by
        intro hfn
        exact hc0 (hc.unique ((w.hasValueAt_zero_iff f).mpr hfn))
      have hfinv : f⁻¹ ∈ w.toValuationSubring := by
        by_contra hne
        exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
      refine ⟨⟨c⁻¹, hcA'⟩, ?_⟩

      have hprod : (f - algebraMap K F c) * (f⁻¹ * algebraMap K F c⁻¹)
          ∈ w.toValuationSubring.nonunits :=
        w.mul_mem_nonunits hc (mul_mem hfinv (w.algebraMap_mem _))
      have := neg_mem hprod
      show f⁻¹ - algebraMap K F (c⁻¹ : K) ∈ w.toValuationSubring.nonunits
      convert this using 1
      have hcF : algebraMap K F c ≠ 0 := by simpa using hc0
      rw [map_inv₀]
      field_simp
      ring
  ·
    right
    refine w.mem_compSubring_of_mem_nonunits A ?_
    exact (ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hf)


-- pin: AlgebraicCurve.Place.compValuationSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:558)
def _root_.AlgebraicCurve.Place.compValuationSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    ValuationSubring F :=
  ValuationSubring.ofSubring (w.compSubring A) (w.mem_compSubring_or_inv_mem A hw)

@[scoped simp]
-- pin: compValuationSubring_toSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:564)
theorem compValuationSubring_toSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    (w.compValuationSubring A hw).toSubring = w.compSubring A := rfl

-- pin: mem_compValuationSubring_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:567)
theorem mem_compValuationSubring_iff (hw : Function.Surjective (algebraMap K w.ResidueField))
    (f : F) : f ∈ w.compValuationSubring A hw ↔ f ∈ w.compSubring A := Iff.rfl

-- pin: mem_compSubring_of_isIntegral (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:570)
theorem mem_compSubring_of_isIntegral (hw : Function.Surjective (algebraMap K w.ResidueField))
    {S : Subring F} (hS : S ≤ w.compSubring A) {f : F} (hf : IsIntegral S f) :
    f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  let V := w.compValuationSubring A hw
  let i : S →+* V := Subring.inclusion hS
  have hint : IsIntegral V f := by
    refine ⟨p.map i, hp.map i, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

-- pin: AlgebraicCurve.Place.mem_compSubring_of_isIntegral' (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:584)
theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_isIntegral' [IsAlgClosed K] {S : Subring F} (hS : S ≤ w.compSubring A)
    {f : F} (hf : IsIntegral S f) : f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  have hSO : ∀ s : S, (s : F) ∈ w.toValuationSubring := fun s => w.compSubring_le A (hS s.2)

  have hfO : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := p.map S.subtype) (hp.map _) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      exact hSO _
    · rw [Polynomial.eval_map]
      exact hpf

  let vS : S →+* A := (w.value A).comp (Subring.inclusion hS)
  let ιS : S →+* w.toValuationSubring := S.subtype.codRestrict _ hSO
  have hres : (residue w.toValuationSubring).comp ιS =
      ((algebraMap K w.ResidueField).comp (algebraMap A K)).comp vS := by
    ext s
    change residue w.toValuationSubring ⟨s, hSO s⟩ =
      algebraMap K w.ResidueField ((w.value A ⟨s, hS s.2⟩ : A) : K)
    exact (w.hasValueAt_iff_residue (hSO s) _).mp (w.hasValueAt_value A ⟨s, hS s.2⟩)
  set r : w.ResidueField := residue w.toValuationSubring ⟨f, hfO⟩ with hr
  let Q : Polynomial A := p.map vS
  have hQ : Q.Monic := hp.map _
  have hzero : Polynomial.eval₂ ιS ⟨f, hfO⟩ p = 0 := by
    apply Subtype.val_injective
    change w.toValuationSubring.subtype (Polynomial.eval₂ ιS ⟨f, hfO⟩ p) = ((0 : w.toValuationSubring) : F)
    rw [Polynomial.hom_eval₂]
    exact hpf
  have hrootκ : Polynomial.eval₂ (algebraMap K w.ResidueField) r (Q.map (algebraMap A K)) = 0 := by
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map, ← hres, hr, ← Polynomial.hom_eval₂, hzero,
      map_zero]

  have hint : IsIntegral K r := ⟨Q.map (algebraMap A K), hQ.map _, hrootκ⟩
  obtain ⟨c, hc⟩ : r ∈ (algebraMap K w.ResidueField).range :=
    minpoly.mem_range_of_degree_eq_one K r
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))

  have hcroot : Polynomial.eval₂ (algebraMap A K) c Q = 0 := by
    apply (algebraMap K w.ResidueField).injective
    rw [Polynomial.hom_eval₂, ← Polynomial.eval₂_map, hc, hrootκ, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (⟨Q, hQ, hcroot⟩ : IsIntegral A c)

  refine ⟨y, (w.hasValueAt_iff_residue hfO _).mpr ?_⟩
  rw [← hr, ← hc, ← hy]
  rfl


-- pin: exists_unique_valueHom (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:632)
theorem exists_unique_valueHom [IsAlgClosed K] (g : F) (B₀ : Subring F)
    (hint : ∀ b : B₀,
      ∃ p : Polynomial (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})),
        p.Monic ∧
          Polynomial.eval₂ (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})).subtype
            (b : F) p = 0)
    (hw : ∃ a : A, g - algebraMap K F (a : K) ∈ w.toValuationSubring.nonunits) :
    ∃! φ : B₀ →+* A, ∀ b : B₀,
      (b : F) - algebraMap K F ((φ b : A) : K) ∈ w.toValuationSubring.nonunits := by

  obtain ⟨a₀, ha₀⟩ := hw
  have hg : g ∈ w.compSubring A := w.mem_compSubring_of_hasValueAt a₀.2 ha₀
  have hS : Subring.closure (algebraMap K F '' (A : Set K) ∪ {g}) ≤ w.compSubring A := by
    rw [Subring.closure_le]
    rintro y (⟨c, hc, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff A c).mpr hc
    · exact hg
  have hB₀ : B₀ ≤ w.compSubring A := fun b hb => w.mem_compSubring_of_isIntegral' A hS (hint ⟨b, hb⟩)

  refine ⟨(w.value A).comp (Subring.inclusion hB₀), fun b => w.hasValueAt_value A ⟨b, hB₀ b.2⟩, ?_⟩

  intro ψ hψ
  refine RingHom.ext fun b => ?_
  have h1 : w.HasValueAt (b : F) ((ψ b : A) : K) := hψ b
  have h2 : ψ b = w.value A ⟨b, hB₀ b.2⟩ := Subtype.ext (h1.unique (w.hasValueAt_value A ⟨b, hB₀ b.2⟩))
  exact h2

variable {A} in

-- pin: AlgebraicCurve.Place.residue_comp_value_surjective (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:661)
theorem _root_.AlgebraicCurve.Place.residue_comp_value_surjective {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) :
    Function.Surjective
      (((IsLocalRing.residue A).comp (w.value A)).comp (Subring.inclusion hB)) := by
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨⟨algebraMap K F a, hconst a⟩, ?_⟩
  change IsLocalRing.residue A (w.value A ⟨algebraMap K F a, hB (hconst a)⟩) = _
  rw [w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap (a : K))]

variable {A} in

-- pin: AlgebraicCurve.Place.ker_residue_comp_value (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:674)
theorem _root_.AlgebraicCurve.Place.ker_residue_comp_value {B : Subring F} (hB : B ≤ w.compSubring A) :
    RingHom.ker (((IsLocalRing.residue A).comp (w.value A)).comp (Subring.inclusion hB)) =
      (w.centre A).comap (Subring.inclusion hB) := by
  ext b
  rw [RingHom.mem_ker, Ideal.mem_comap, mem_centre_iff, RingHom.comp_apply, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff]

variable {A} in
-- pin: centre_comap_isMaximal (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:683)
theorem centre_comap_isMaximal {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) :
    ((w.centre A).comap (Subring.inclusion hB)).IsMaximal := by
  rw [← w.ker_residue_comp_value hB]
  exact RingHom.ker_isMaximal_of_surjective _ (w.residue_comp_value_surjective hB hconst)

variable {A} in

-- pin: sub_value_mem_centre_comap (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:691)
theorem sub_value_mem_centre_comap {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) (b : B) :
    b - ⟨algebraMap K F (w.value A ⟨b, hB b.2⟩ : K), hconst _⟩ ∈
      (w.centre A).comap (Subring.inclusion hB) := by
  rw [Ideal.mem_comap, mem_centre_iff]
  simp only [map_sub]
  have h1 : w.value A (Subring.inclusion hB ⟨algebraMap K F (w.value A ⟨b, hB b.2⟩ : K), hconst _⟩)
      = w.value A ⟨b, hB b.2⟩ :=
    w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap _)
  have h2 : w.value A (Subring.inclusion hB b) = w.value A ⟨b, hB b.2⟩ := rfl
  rw [h1, h2, sub_self]
  exact Ideal.zero_mem _

variable {A} in

-- pin: AlgebraicCurve.Place.algebraMap_mem_centre_comap_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:706)
theorem _root_.AlgebraicCurve.Place.algebraMap_mem_centre_comap_iff {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) (a : A) :
    (⟨algebraMap K F a, hconst a⟩ : B) ∈ (w.centre A).comap (Subring.inclusion hB) ↔
      a ∈ maximalIdeal A := by
  rw [Ideal.mem_comap]
  exact w.algebraMap_mem_centre_iff A a

end Place

end AlgebraicCurve

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

-- pin: ofValuationSubringOver (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1037)
def ofValuationSubringOver (O : ValuationSubring F) (hO : ∀ r : R, algebraMap R F r ∈ O)
    (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O) : Place K F where
  toValuationSubring := O
  algebraMap_mem' := hK
  ne_top' := hne
  isPrincipalIdealRing' := O.isPrincipalIdealRing_of_dedekind_le hO hne

@[scoped simp]
-- pin: ofValuationSubringOver_toValuationSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1045)
theorem ofValuationSubringOver_toValuationSubring (O : ValuationSubring F)
    (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O) :
    (ofValuationSubringOver O hO hne hK).toValuationSubring = O := rfl

-- pin: mem_nonunits_ofValuationSubringOver_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1049)
theorem mem_nonunits_ofValuationSubringOver_iff (O : ValuationSubring F)
    (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O)
    {B : Subring F} {𝔭 : Ideal B} (hdom : ∀ b : B, (b : F) ∈ O.nonunits ↔ b ∈ 𝔭) (b : B) :
    (b : F) ∈ (ofValuationSubringOver O hO hne hK).toValuationSubring.nonunits ↔ b ∈ 𝔭 :=
  hdom b

end Place

end AlgebraicCurve

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- pin: eq_zero_of_X_sub_C_dvd_C (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1477)
theorem eq_zero_of_X_sub_C_dvd_C {R : Type*} [CommRing R] {a₀ a : R}
    (h : (Polynomial.X - Polynomial.C a₀) ∣ Polynomial.C a) : a = 0 := by
  obtain ⟨g, hg⟩ := h
  have := congrArg (Polynomial.eval a₀) hg
  simpa using this

-- pin: exists_place_centre_comap_eq (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1483)
theorem exists_place_centre_comap_eq [IsAlgClosed K] (A : ValuationSubring K) {j : F}
    (hj : Transcendental K j) [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F]
    {B : Subring F} (hconst : ∀ a : A, algebraMap K F a ∈ B) (hjB : j ∈ B)
    (hint : ∀ b : B,
      IsIntegral (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})) (b : F))
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮A : ∀ a : A, (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (a₀ : A) (hja : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔮) :
    ∃ (w : Place K F) (hB : B ≤ w.compSubring A),
      (w.centre A).comap (Subring.inclusion hB) = 𝔮 ∧ w.HasValueAt j a₀ := by
  classical

  set S : Subring F := Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})
    with hSdef
  have hSB : S ≤ B := by
    rw [hSdef, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    exacts [hconst a, hjB]
  haveI : IsIntegrallyClosed S := A.isIntegrallyClosed_closure hj
  have hjS : j ∈ S := Subring.subset_closure (Or.inr rfl)
  have hcS : ∀ a : A, algebraMap K F a ∈ S := fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)

  let e := A.polynomialEquivClosure hj
  have heX : (e Polynomial.X : F) = j := by
    rw [ValuationSubring.polynomialEquivClosure_apply, Polynomial.aeval_X]
  have heC : ∀ a : A, (e (Polynomial.C a) : F) = algebraMap K F a := fun a => by
    rw [ValuationSubring.polynomialEquivClosure_apply, Polynomial.aeval_C]
    rfl
  have hegen : e (Polynomial.X - Polynomial.C a₀) = ⟨j, hjS⟩ - ⟨algebraMap K F a₀, hcS a₀⟩ := by
    apply Subtype.ext
    rw [map_sub]
    push_cast
    rw [heX, heC]
  let p₀ : Ideal (Polynomial A) := Ideal.span {Polynomial.X - Polynomial.C a₀}
  haveI hp₀ : p₀.IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (Polynomial.quotientSpanXSubCAlgEquiv a₀).toMulEquiv.isDomain_iff.mpr inferInstance
  let p : Ideal S := p₀.map e.toRingHom
  haveI hp : p.IsPrime := Ideal.map_isPrime_of_equiv e
  have hp_span : p = Ideal.span {(⟨j, hjS⟩ : S) - ⟨algebraMap K F a₀, hcS a₀⟩} := by
    change Ideal.map e.toRingHom (Ideal.span _) = _
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun y => Ideal.span {y}) hegen
  let q : Ideal S := 𝔮.comap (Subring.inclusion hSB)
  have hpq : p ≤ q := by
    rw [hp_span, Ideal.span_le, Set.singleton_subset_iff]
    change Subring.inclusion hSB (⟨j, hjS⟩ - ⟨algebraMap K F a₀, hcS a₀⟩) ∈ 𝔮
    rw [map_sub]
    exact hja

  obtain ⟨𝔭, h𝔭𝔮, h𝔭, h𝔭p⟩ :=
    Subring.exists_ideal_le_comap_eq_of_isIntegral hSB hint hpq 𝔮 rfl
  haveI := h𝔭

  have hj𝔭 : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔭 := by
    have : (⟨j, hjS⟩ : S) - ⟨algebraMap K F a₀, hcS a₀⟩ ∈ 𝔭.comap (Subring.inclusion hSB) := by
      rw [h𝔭p, hp_span]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap, map_sub] at this
    exact this

  have hbot : ∀ a : A, (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔭 → a = 0 := by
    intro a ha
    have h1 : (⟨algebraMap K F a, hcS a⟩ : S) ∈ 𝔭.comap (Subring.inclusion hSB) := by
      rw [Ideal.mem_comap]
      exact ha
    rw [h𝔭p, hp_span, Ideal.mem_span_singleton'] at h1

    obtain ⟨g, hg⟩ := h1
    have h3 : e (Polynomial.C a) = ⟨algebraMap K F a, hcS a⟩ := Subtype.ext (heC a)
    have h4 : e.symm g * (Polynomial.X - Polynomial.C a₀) = Polynomial.C a := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hegen, h3, hg]
    exact eq_zero_of_X_sub_C_dvd_C ⟨e.symm g, by rw [mul_comm]; exact h4.symm⟩

  have hj_ne : j - algebraMap K F a₀ ≠ 0 := by
    intro h
    apply hj
    rw [sub_eq_zero] at h
    rw [h]
    exact isAlgebraic_algebraMap (a₀ : K)
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hj𝔭
    exact hj_ne (by simpa using congrArg Subtype.val hj𝔭)

  obtain ⟨O, hle, hdom⟩ := Subring.exists_valuationSubring_dominating 𝔭
  have hne : O ≠ ⊤ := Subring.ne_top_of_dominating hdom h𝔭ne
  have hK : ∀ c : K, algebraMap K F c ∈ O :=
    Subring.algebraMap_mem_of_dominating A hconst hle hdom hbot

  let R := integralClosure (Algebra.adjoin K ({j} : Set F)) F
  haveI : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hj
  haveI : IsFractionRing R F := isFractionRing_integralClosure_adjoin hj
  have hO : ∀ r : R, algebraMap R F r ∈ O := fun r =>
    integralClosure_adjoin_le_valuationSubring O hK (hle hjB) r
  let w : Place K F := Place.ofValuationSubringOver O hO hne hK

  have hval : w.HasValueAt j a₀ := by
    have := (hdom (⟨j, hjB⟩ - ⟨algebraMap K F a₀, hconst a₀⟩)).mpr hj𝔭
    simp at this
    exact this

  have hS_le : S ≤ w.compSubring A := by
    rw [hSdef, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff A _).mpr a.2
    · exact w.mem_compSubring_of_hasValueAt a₀.2 hval
  have hB : B ≤ w.compSubring A := fun b hb => w.mem_compSubring_of_isIntegral' A hS_le (hint ⟨b, hb⟩)
  refine ⟨w, hB, ?_, hval⟩

  have h𝔭𝔓 : 𝔭 ≤ (w.centre A).comap (Subring.inclusion hB) := fun x hx =>
    w.mem_centre_of_mem_nonunits ((hdom x).mpr hx)
  ext b
  obtain ⟨a, hab⟩ := ValuationSubring.exists_sub_constants_mem hconst hjB hint 𝔭 hbot a₀ hj𝔭 b
  have hab' : b - ⟨algebraMap K F a, hconst a⟩ ∈ 𝔭 := hab
  have key : ∀ (I : Ideal B), 𝔭 ≤ I →
      (b ∈ I ↔ (⟨algebraMap K F a, hconst a⟩ : B) ∈ I) := by
    intro I hI
    constructor
    · intro hb
      have := I.sub_mem hb (hI hab')
      rwa [sub_sub_cancel] at this
    · intro ha
      have := I.add_mem (hI hab') ha
      rwa [sub_add_cancel] at this
  rw [key _ h𝔭𝔓, key _ h𝔭𝔮, w.algebraMap_mem_centre_comap_iff hB hconst, h𝔮A]

end Place

end AlgebraicCurve

namespace AlgebraicCurve

namespace Place

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

-- pin: finite_residueField_of_adjoin_simple_eq_top_of_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1627)
theorem finite_residueField_of_adjoin_simple_eq_top_of_mem {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E)
    (hxv : x ∈ v.toValuationSubring) : Module.Finite K v.ResidueField := by
  classical

  haveI : IsDedekindDomain (Algebra.adjoin K ({x} : Set E)) := isDedekindDomain_adjoin_singleton hx
  haveI : FaithfulSMul (Algebra.adjoin K ({x} : Set E)) E :=
    (faithfulSMul_iff_algebraMap_injective _ E).mpr Subtype.val_injective
  haveI : IsFractionRing (Algebra.adjoin K ({x} : Set E)) E := by
    refine IsFractionRing.of_field (Algebra.adjoin K ({x} : Set E)) E (fun z => ?_)
    have hz : z ∈ IntermediateField.adjoin K ({x} : Set E) := by
      rw [htop]
      exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  set O := v.toValuationSubring with hOdef

  have hO : ∀ r : Algebra.adjoin K ({x} : Set E), algebraMap _ E r ∈ O := by
    intro r
    have hle : Algebra.adjoin K ({x} : Set E) ≤
        { O.toSubring with algebraMap_mem' := v.algebraMap_mem' } :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxv)
    exact hle r.2
  have hne : O ≠ ⊤ := v.ne_top'

  let xO : O := ⟨x, hxv⟩
  let xbar : v.ResidueField := IsLocalRing.residue O xO
  have hcomp : (IsLocalRing.residue O).comp (algebraMap K O) = algebraMap K v.ResidueField :=
    RingHom.ext fun _ => rfl
  have hres_aeval : ∀ p : K[X], IsLocalRing.residue O (Polynomial.aeval xO p) =
      Polynomial.aeval xbar p := fun p => by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp]
  have hcoe_aeval : ∀ p : K[X], ((Polynomial.aeval xO p : O) : E) = Polynomial.aeval x p :=
    fun p => by
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K O E) xO p

    exact this.symm
  let e := Polynomial.algEquivOfTranscendental K x hx
  have hcoe_e : ∀ p : K[X], ((e p : Algebra.adjoin K ({x} : Set E)) : E) = Polynomial.aeval x p :=
    fun p => by
    rw [Polynomial.algEquivOfTranscendental_apply, Polynomial.aeval_subalgebra_coe]

  have hOe : ∀ p : K[X], (⟨((e p : Algebra.adjoin K ({x} : Set E)) : E), hO (e p)⟩ : O) =
      Polynomial.aeval xO p := fun p => Subtype.ext (by rw [hcoe_aeval, hcoe_e])

  obtain ⟨f, hf𝔭, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (O.centreOver_ne_bot hO hne)
  obtain ⟨g, rfl⟩ := e.surjective f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [h, map_zero])
  have hgbar : Polynomial.aeval xbar g = 0 := by
    rw [← hres_aeval, IsLocalRing.residue_eq_zero_iff, ← hOe,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact (O.mem_centreOver_iff hO).mp hf𝔭
  have halg : IsAlgebraic K xbar := ⟨g, hg0, hgbar⟩
  have hint : IsIntegral K xbar := halg.isIntegral
  haveI : FiniteDimensional K K⟮xbar⟯ := IntermediateField.adjoin.finiteDimensional hint

  have htop' : K⟮xbar⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    have hz : (z : E) ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E
        (O.centreHeightOneSpectrum hO hne) := by
      rw [← O.eq_valuationSubringAtPrime_centre hO hne]
      exact z.2
    obtain ⟨a, s, hs, hz'⟩ := hz
    obtain ⟨ga, rfl⟩ := e.surjective a
    obtain ⟨gs, rfl⟩ := e.surjective s

    have hsn : ((e gs : Algebra.adjoin K ({x} : Set E)) : E) ∉ O.nonunits := fun h =>
      hs ((O.mem_centreOver_iff hO).mpr h)
    have hres_s : IsLocalRing.residue O (Polynomial.aeval xO gs) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ← hOe, ← ValuationSubring.coe_mem_nonunits_iff]
      exact hsn
    have hs0 : ((e gs : Algebra.adjoin K ({x} : Set E)) : E) ≠ 0 := fun h =>
      hsn (h ▸ (zero_mem O.nonunits))

    have hmul : z * Polynomial.aeval xO gs = Polynomial.aeval xO ga := by
      rw [← hOe, ← hOe]
      apply Subtype.ext
      change (z : E) * _ = _
      push_cast
      rw [hz']
      exact inv_mul_cancel_right₀ hs0 _
    have hzq : IsLocalRing.residue O z =
        Polynomial.aeval xbar ga / Polynomial.aeval xbar gs := by
      rw [eq_div_iff (by rwa [← hres_aeval]), ← hres_aeval, ← hres_aeval, ← map_mul, hmul]
    rw [hzq]
    refine div_mem ?_ ?_ <;>
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)

  have : FiniteDimensional K (⊤ : IntermediateField K v.ResidueField) := by
    rw [← htop']
    infer_instance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional



-- pin: finite_residueField_of_adjoin_simple_eq_top (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1733)
theorem finite_residueField_of_adjoin_simple_eq_top {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E) :
    Module.Finite K v.ResidueField := by
  by_cases hxv : x ∈ v.toValuationSubring
  · exact finite_residueField_of_adjoin_simple_eq_top_of_mem hx htop v hxv
  ·
    have hxinv : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hxv
    have hx' : Transcendental K x⁻¹ := fun h => hx (by simpa using h.inv)
    have htop' : IntermediateField.adjoin K ({x⁻¹} : Set E) = ⊤ := by
      rw [IntermediateField.adjoin_simple_inv_eq x, htop]
    exact finite_residueField_of_adjoin_simple_eq_top_of_mem hx' htop' v hxinv

-- pin: finiteResidue_of_adjoin_simple_eq_top (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1745)
theorem finiteResidue_of_adjoin_simple_eq_top {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E) : v.FiniteResidue :=
  ⟨finite_residueField_of_adjoin_simple_eq_top hx htop v⟩

end Place

end AlgebraicCurve

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- pin: AlgebraicCurve.Place.eq_of_forall_mem_nonunits_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1788)
theorem _root_.AlgebraicCurve.Place.eq_of_forall_mem_nonunits_iff (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R F] [IsFractionRing R F] {v₁ v₂ : Place K F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring)
    (h₂ : ∀ r : R, algebraMap R F r ∈ v₂.toValuationSubring)
    (h : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring.nonunits ↔
      algebraMap R F r ∈ v₂.toValuationSubring.nonunits) : v₁ = v₂ :=
  Place.ext (ValuationSubring.eq_of_forall_mem_nonunits_iff h₁ v₁.ne_top' h₂ v₂.ne_top' h)


-- pin: eq_of_forall_mem_nonunits_iff_of_surjective (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1798)
theorem eq_of_forall_mem_nonunits_iff_of_surjective (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R F] [IsFractionRing R F] {v₁ v₂ : Place K F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring)
    (h₂ : ∀ r : R, algebraMap R F r ∈ v₂.toValuationSubring)
    {ι : Type*} (f : ι → F) (hsurj : ∀ r : R, ∃ i, f i = algebraMap R F r)
    (h : ∀ i, f i ∈ v₁.toValuationSubring.nonunits ↔ f i ∈ v₂.toValuationSubring.nonunits) :
    v₁ = v₂ :=
  eq_of_forall_mem_nonunits_iff R h₁ h₂ fun r => by
    obtain ⟨i, hi⟩ := hsurj r
    rw [← hi]
    exact h i

variable (K) in

-- pin: integralClosure_adjoin_le_of_forall_isIntegral_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1812)
theorem integralClosure_adjoin_le_of_forall_isIntegral_mem {j : F} {S : Subring F}
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hj : j ∈ S)
    (hS : ∀ x : F, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0) → x ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ S := by

  let S' : Subalgebra K F := { S with algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ S' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj)
  let φ : Algebra.adjoin K ({j} : Set F) →+* S :=
    (Subalgebra.val _).toRingHom.codRestrict S (fun y => hle y.2)

  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  refine hS r ⟨p.map φ, hp.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpr

-- pin: exists_eq_of_integralClosure_adjoin (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1827)
theorem exists_eq_of_integralClosure_adjoin {j : F} {B : Type*} (π : B → F) {S : Subring F}
    (hrange : ∀ x, x ∈ S ↔ ∃ b, π b = x)
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hj : j ∈ S)
    (hS : ∀ x : F, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0) → x ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) :
    ∃ b, π b = algebraMap (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F r :=
  (hrange r).mp (integralClosure_adjoin_le_of_forall_isIntegral_mem K hK hj hS r)

end Place

end AlgebraicCurve
