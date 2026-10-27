/-
The place-descent cluster of the constant-field-extension wave: FLT's
`AlgebraicCurve.Place` nodes over `F ⊆ F' = K'·F`, after the pin

* `P2M/Sol/S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean`
* `P2M/Sol/S_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean`

(and the `Theorems/` wrappers of the same stems), pinned `aa2d8b3`,
<https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b3/P2M/Sol>.

The module carries the eight public headlines and, as its prelude, the pin-private
engines the cluster rests on: the two layer-0 roots of the pin's `Place` files
(`Place.rowMain`, `Place.exists_comap_eq_toValuationSubring`), the `ord`-iff block
of the `comap`-lift file, the tensor-product/centring block of the
`valuation_sub_lt_one` files, and `Place.mem_range_algebraMap_of_forall_ord_eq_zero_core`.

Blocks the pin repeats across files are written once here. Imported, not re-proved
(workorder §3): `Place.ord_nonneg_of_mem`, `Place.ord_nonneg_of_mem_vs`,
`Place.mem_toValuationSubring_of_ord_nonneg_alt`, `Place.mem_of_ord_nonneg`,
`Place.mem_vs_of_ord_nonneg` (the pin's no-nonzero `mem_of_ord_nonneg`),
`Place.exists_ord_pos`, `Place.ord_coe_unit`, `Place.isRational_of_isCurveOver`,
`Place.LocalDerivation.isUnit_add_of_mem_maximalIdeal` (the pin's
`isUnit_add_of_mem_maximalIdeal`), `AlgebraicCurve.ConstantFieldExtension.transcendental_algebraMap`
(D4: the port's form is stronger), `AlgebraicCurve.linearIndependent_of_constantFieldExtension`,
`AlgebraicCurve.RegularProlongation.linearIndependent_pow_iff_transcendental`,
`AlgebraicCurve.finiteDimensional_adjoin_of_transcendental`, and
`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`.

Deviations from the pin are API drift only (playbook §4): the pin's
`include`/`omit` section-variable scaffolding becomes explicit binders where the
statements allow it (`omit` is kept only where the pin itself needs it to keep an
unused instance out of a helper's type), `Ideal.comap` is used in place of the
`Ideal.under` abbrev, and `haveI`/`letI` are spelled `have`/`let` to satisfy the
port's `haveILetI` linter. No statement changes.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.lean   -- comparable copy
# The two shared prelude pieces `mem_maximalIdeal_of_ord_pos` and
# `exists_sub_algebraMap_mem_maximalIdeal` are declared in the pin's P3/P4/P5 files,
# not in any of the eight; this one supplies both.
spec-pin: P2M/Sol/S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.lean   -- comparable copy
-/

import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.ResidueTheorem.KFamily
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree
import FLTForHuman.AlgebraicCurve.P1.Dictionary
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.Algebra.IsSeparableFrobenius
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.RatFunc.IntermediateField

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial AlgebraicCurve
open scoped TensorProduct IntermediateField nonZeroDivisors

namespace AlgebraicCurve

namespace Place

/-! ## The pin-private `ord` prelude of the `comap`-lift file

The 17- and 55-line blocks of
`S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean`,
shared with the pin's `exists_derivation` file and written once here. -/

section OrdPrelude

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

/-- A member of the valuation subring whose inverse is not a member has order at
least one. -/
theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := v.ord_nonneg_of_mem_vs h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

/-- Membership in the valuation subring is non-negativity of the order.  The pin
declares this without a non-zero hypothesis; it is the `Place.mem_iff_ord_nonneg_vs`
companion of `Place.mem_vs_of_ord_nonneg`. -/
theorem mem_iff_ord_nonneg_vs (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨v.ord_nonneg_of_mem_vs, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

end OrdPrelude

/-! ## The two layer-0 roots

`Place.rowMain` (the pin's 137-line `exists_ord_algebraMap_eq_mul_ord` file) and
`Place.exists_comap_eq_toValuationSubring` (the pin's 93-line file), both private
engines of the headlines below. -/

section RowMain

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F']

/-- The order along an integral extension is a positive multiple of the order
below: the pin's `Place.rowMain`. -/
private theorem rowMain (w : Place K F') (v : Place K F)
    (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by
  have hmem : ∀ {f : F}, f ∈ v.toValuationSubring → algebraMap F F' f ∈ w.toValuationSubring :=
    fun {f} h => by
      rw [hv] at h
      exact (ValuationSubring.mem_comap).mp h
  have hmem' : ∀ {f : F}, algebraMap F F' f ∈ w.toValuationSubring → f ∈ v.toValuationSubring :=
    fun {f} h => by
      rw [hv]
      exact (ValuationSubring.mem_comap).mpr h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπF' : algebraMap F F' (π : F) ≠ 0 := by simpa using hπF

  have he0 : 0 ≤ w.ord (algebraMap F F' (π : F)) :=
    w.ord_nonneg_of_mem_vs (hmem π.2)
  have hepos : 0 < w.ord (algebraMap F F' (π : F)) := by
    rcases eq_or_lt_of_le he0 with h0 | h
    · exfalso
      have hinv : (algebraMap F F' (π : F))⁻¹ ∈ w.toValuationSubring :=
        w.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hπF')
          (by rw [w.ord_inv, ← h0, neg_zero])
      have hinv' : (π : F)⁻¹ ∈ v.toValuationSubring := hmem' (by rwa [map_inv₀])
      have h1 := v.ord_nonneg_of_mem_vs hinv'
      rw [v.ord_inv, v.ord_coe_irreducible hπ] at h1
      omega
    · exact h

  have hunit : ∀ u : v.toValuationSubringˣ,
      w.ord (algebraMap F F' ((u : v.toValuationSubring) : F)) = 0 := by
    intro u
    have h1 : 0 ≤ w.ord (algebraMap F F' ((u : v.toValuationSubring) : F)) :=
      w.ord_nonneg_of_mem_vs (hmem (u : v.toValuationSubring).2)
    have h2 : 0 ≤ w.ord (algebraMap F F' ((↑(u⁻¹) : v.toValuationSubring) : F)) :=
      w.ord_nonneg_of_mem_vs (hmem (↑(u⁻¹) : v.toValuationSubring).2)
    have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
      simp [ne_eq, ZeroMemClass.coe_eq_zero]
    have hu0' : ((↑(u⁻¹) : v.toValuationSubring) : F) ≠ 0 := by
      simp [ne_eq, ZeroMemClass.coe_eq_zero]
    have hprod : ((u : v.toValuationSubring) : F) * ((↑(u⁻¹) : v.toValuationSubring) : F) = 1 := by
      have := u.mul_inv
      rw [Subtype.ext_iff] at this
      push_cast at this
      exact this
    have hsum : w.ord (algebraMap F F' ((u : v.toValuationSubring) : F))
        + w.ord (algebraMap F F' ((↑(u⁻¹) : v.toValuationSubring) : F)) = 0 := by
      rw [← w.ord_mul ((map_ne_zero (algebraMap F F')).mpr hu0)
        ((map_ne_zero (algebraMap F F')).mpr hu0'), ← map_mul, hprod, map_one, w.ord_one]
    omega
  refine ⟨(w.ord (algebraMap F F' (π : F))).toNat, by omega, fun f => ?_⟩
  rw [Int.toNat_of_nonneg he0]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  conv_lhs => rw [hu]
  rw [map_mul, map_zpow₀, w.ord_mul ((map_ne_zero (algebraMap F F')).mpr hu0) (zpow_ne_zero _ hπF'),
    hunit u, zero_add, w.ord_zpow, mul_comm]

end RowMain

section ExistsComap

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- A place of `F` lifts to a place of the finite separable extension `F'` with
the same valuation subring below: the pin's
`Place.exists_comap_eq_toValuationSubring`. -/
private theorem exists_comap_eq_toValuationSubring_core (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by
  classical
  let A : Type _ := v.toValuationSubring
  let : Algebra A F' := ((algebraMap F F').comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let C : Type _ := integralClosure A F'
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A F F'
  have : IsFractionRing C F' := integralClosure.isFractionRing_of_finite_extension F F'
  let : Algebra K C := ((algebraMap A C).comp (algebraMap K A)).toAlgebra
  have hAC : ∀ a : A, algebraMap C F' (algebraMap A C a) = algebraMap F F' (a : F) := fun a => rfl
  have : IsScalarTower K C F' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap K F' a = algebraMap C F' (algebraMap A C (algebraMap K A a))
    rw [hAC, Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply])

  have hinj : Function.Injective (algebraMap A C) := by
    intro a b h
    have h' := congrArg (algebraMap C F') h
    rw [hAC, hAC] at h'
    exact Subtype.ext ((algebraMap F F').injective h')
  obtain ⟨P, hPmax, hP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal A) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
  have hPne : P ≠ ⊥ := by
    intro hbot
    apply IsDiscreteValuationRing.not_a_field A
    rw [← hP, hbot]
    exact Ideal.comap_bot_of_injective (algebraMap A C) hinj
  let w₀ : HeightOneSpectrum C := ⟨P, hPmax.isPrime, hPne⟩
  refine ⟨ofHeightOneSpectrum (K := K) w₀, ?_⟩
  ext f
  rw [ValuationSubring.mem_comap, ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff]
  constructor
  · intro hle
    by_contra hfA
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfA (zero_mem _)
    have hinvA : f⁻¹ ∈ v.toValuationSubring :=
      (v.toValuationSubring.mem_or_inv_mem f).resolve_left hfA

    have hnu : (⟨f⁻¹, hinvA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
      have hb' : f⁻¹ * (b : F) = 1 := by simpa [Subtype.ext_iff] using hb
      have hbf : (b : F) = f := by
        have := congrArg (fun z => f * z) hb'
        simpa [← mul_assoc, mul_inv_cancel₀ hf0] using this
      exact hfA (hbf ▸ b.2)
    have hP' : algebraMap A C ⟨f⁻¹, hinvA⟩ ∈ P := by
      have h2 : (⟨f⁻¹, hinvA⟩ : A) ∈ P.under A := by rw [hP]; exact hnu
      exact Ideal.mem_comap.mp h2
    have hlt : w₀.valuation F' (algebraMap F F' f⁻¹) < 1 := by
      rw [show algebraMap F F' f⁻¹ = algebraMap C F' (algebraMap A C ⟨f⁻¹, hinvA⟩) from
        (hAC ⟨f⁻¹, hinvA⟩).symm]
      exact (w₀.valuation_lt_one_iff_mem _).mpr hP'
    rw [map_inv₀, map_inv₀] at hlt
    have hx0 : w₀.valuation F' (algebraMap F F' f) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero (algebraMap F F')).mpr hf0)
    have : 1 < w₀.valuation F' (algebraMap F F' f) := (inv_lt_one₀ (zero_lt_iff.mpr hx0)).mp hlt
    exact absurd hle (not_le.mpr this)
  · intro hfA
    rw [show algebraMap F F' f = algebraMap C F' (algebraMap A C ⟨f, hfA⟩) from (hAC ⟨f, hfA⟩).symm]
    exact w₀.valuation_le_one _

end ExistsComap

end Place

/-! ## The layer-0 headlines -/

theorem Place.deg_eq_one_iff_surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  unfold Place.deg
  rw [show Function.Surjective (algebraMap K v.ResidueField)
        ↔ Function.Bijective (algebraMap K v.ResidueField) from
      ⟨fun h => ⟨(algebraMap K v.ResidueField).injective, h⟩, fun h => h.2⟩]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap

theorem Place.inertiaDeg_eq_one_of_isRational {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational)
    (hv : (w.restrict F).IsRational) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [(Place.isRational_iff_deg_eq_one _).1 hv,
    (Place.isRational_iff_deg_eq_one _).1 hw, one_mul] at h
  exact h

theorem Place.sum_ramificationIndex_eq_finrank {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
  rw [← Place.sum_ramificationIndex_mul_inertiaDeg (F' := F') v]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [w.inertiaDeg_eq_one_of_isRational (hrat w hw) ((Place.mem_fiber.mp hw).symm ▸ hv),
    Nat.cast_one, mul_one]

end AlgebraicCurve

/-! ## The constant-field place lift

`AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension` (the
pin's 615-line file): a place of `F` lifts uniquely to a place of `F' = K'·F` whose
comap is it and whose order agrees on `F`.  The engine is the `ConstantFieldPlaceLift`
block below: tensor-product digit expansion of `F'` over `K'`, and the linear
disjointness of the `K'`-span of `F` from `1`. -/

namespace ConstantFieldPlaceLift

section Basic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Equal orders at a point and its inverse force order zero. -/
theorem ord_eq_zero_of_mem_of_inv_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have a := v.ord_nonneg_of_mem_vs h1
  have b := v.ord_nonneg_of_mem_vs h2
  rw [v.ord_inv] at b
  omega

/-- A wrapper of `ord_eq_zero_of_mem_of_inv_mem` along a further algebra map. -/
theorem ord_algebraMap_eq_zero {L : Type*} [Field L] [Algebra F L] {K' : Type*} [Field K']
    [Algebra K' L] (w : Place K' L) {f : F}
    (h1 : algebraMap F L f ∈ w.toValuationSubring)
    (h2 : algebraMap F L f⁻¹ ∈ w.toValuationSubring) : w.ord (algebraMap F L f) = 0 :=
  ord_eq_zero_of_mem_of_inv_mem w h1 (by simpa using h2)

end Basic

section Psi

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

/-- The `K'`-span of the place's valuation subring, transported into `F'`. -/
noncomputable def Psi : (ι →₀ P.toValuationSubring) →+ F' :=
  Finsupp.liftAddHom fun j =>
    (AddMonoidHom.mulLeft (algebraMap K' F' (B j))).comp
      ((algebraMap F F' : F →+* F').toAddMonoidHom.comp
        P.toValuationSubring.subtype.toAddMonoidHom)

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_single (j : ι) (o : P.toValuationSubring) :
    Psi F' B P (Finsupp.single j o) = algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  simp [Psi]

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_apply (w : ι →₀ P.toValuationSubring) :
    Psi F' B P w = w.sum fun j o => algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  rw [Psi, Finsupp.liftAddHom_apply]
  rfl

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_smul (s : P.toValuationSubring) (w : ι →₀ P.toValuationSubring) :
    Psi F' B P (s • w) = algebraMap F F' (s : F) * Psi F' B P w := by
  induction w using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [smul_add, map_add, map_add, ih, Finsupp.smul_single, Psi_single, Psi_single, mul_add,
      smul_eq_mul, MulMemClass.coe_mul, map_mul]
    ring

/-- A single tensor `d ⊗ o` as an element of the span. -/
noncomputable def pureW (d : K') (o : P.toValuationSubring) : ι →₀ P.toValuationSubring :=
  (B.repr d).mapRange (fun a => algebraMap K P.toValuationSubring a * o) (by simp)

theorem Psi_pureW (d : K') (o : P.toValuationSubring) :
    Psi F' B P (pureW B P d o) = algebraMap K' F' d * algebraMap F F' (o : F) := by
  rw [Psi_apply, pureW, Finsupp.sum_mapRange_index (fun j => by simp)]
  conv_rhs => rw [← B.linearCombination_repr d, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MulMemClass.coe_mul, Place.coe_algebraMap, map_mul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring

theorem Psi_mul_mem_range (w₁ w₂ : ι →₀ P.toValuationSubring) :
    ∃ w, Psi F' B P w = Psi F' B P w₁ * Psi F' B P w₂ := by
  classical
  refine ⟨∑ i ∈ w₁.support, ∑ j ∈ w₂.support, pureW B P (B i * B j) (w₁ i * w₂ j), ?_⟩
  rw [map_sum, Psi_apply F' B P w₁, Finsupp.sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Psi_apply F' B P w₂, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Psi_pureW, map_mul, MulMemClass.coe_mul, map_mul]
  ring

/-- The image of `Psi` as a subring of `F'`. -/
noncomputable def rangePsi : Subring F' where
  carrier := Set.range (Psi F' B P)
  mul_mem' := by
    rintro _ _ ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
    exact Psi_mul_mem_range F' B P w₁ w₂
  one_mem' := ⟨pureW B P 1 1, by simp [Psi_pureW]⟩
  add_mem' := by
    rintro _ _ ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨-w, map_neg _ _⟩

theorem mem_rangePsi_iff {y : F'} : y ∈ rangePsi F' B P ↔ ∃ w, Psi F' B P w = y := Iff.rfl

theorem algebraMap_mem_rangePsi (d : K') : algebraMap K' F' d ∈ rangePsi F' B P :=
  ⟨pureW B P d 1, by simp [Psi_pureW]⟩

theorem algebraMap_coe_mem_rangePsi (o : P.toValuationSubring) :
    algebraMap F F' (o : F) ∈ rangePsi F' B P :=
  ⟨pureW B P 1 o, by simp [Psi_pureW]⟩

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_mem {S : Type*} [SetLike S F'] [SubringClass S F'] (V : S)
    (hK : ∀ d : K', algebraMap K' F' d ∈ V)
    (hO : ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ V)
    (w : ι →₀ P.toValuationSubring) : Psi F' B P w ∈ V := by
  rw [Psi_apply]
  exact sum_mem fun j _ => mul_mem (hK _) (hO _)

/-- The fraction subalgebra of `F'` that `Psi` generates. -/
noncomputable def fracPsi : Subalgebra K' F' where
  carrier := {y | ∃ w, ∃ s : P.toValuationSubring, (s : F) ≠ 0 ∧
    y * algebraMap F F' (s : F) = Psi F' B P w}
  mul_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    obtain ⟨w, hw⟩ := Psi_mul_mem_range F' B P w₁ w₂
    refine ⟨w, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [hw, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  one_mem' := ⟨pureW B P 1 1, 1, by simp, by simp [Psi_pureW]⟩
  add_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    refine ⟨s₂ • w₁ + s₁ • w₂, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_add, Psi_smul, Psi_smul, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  algebraMap_mem' d := ⟨pureW B P d 1, 1, by simp, by simp [Psi_pureW]⟩

theorem mem_fracPsi_iff {y : F'} : y ∈ fracPsi F' B P ↔ ∃ w, ∃ s : P.toValuationSubring,
    (s : F) ≠ 0 ∧ y * algebraMap F F' (s : F) = Psi F' B P w := Iff.rfl

theorem algebraMap_mem_fracPsi (f : F) : algebraMap F F' f ∈ fracPsi F' B P := by
  rcases P.toValuationSubring.mem_or_inv_mem f with h | h
  · exact ⟨pureW B P 1 ⟨f, h⟩, 1, by simp, by simp [Psi_pureW]⟩
  · rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero]; exact (fracPsi F' B P).zero_mem
    · refine ⟨pureW B P 1 1, ⟨f⁻¹, h⟩, by simpa using hf, ?_⟩
      simp [Psi_pureW, mul_inv_cancel₀ ((_root_.map_ne_zero (algebraMap F F')).mpr hf)]

theorem exists_mul_Psi_eq (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {z : F'} (hz : z ≠ 0) :
    ∃ w₁ w₂, Psi F' B P w₂ ≠ 0 ∧ z * Psi F' B P w₂ = Psi F' B P w₁ := by
  have hzmem : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hzmem
  obtain ⟨r, hr, s, hs, rfl⟩ := hzmem
  have hle : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ fracPsi F' B P :=
    Algebra.adjoin_le (by rintro _ ⟨f, rfl⟩; exact algebraMap_mem_fracPsi F' B P f)
  obtain ⟨w₁, s₁, hs₁, h₁⟩ := hle hr
  obtain ⟨w₂, s₂, hs₂, h₂⟩ := hle hs
  have hr0 : r ≠ 0 := by rintro rfl; simp at hz
  have hs0 : s ≠ 0 := by rintro rfl; simp at hz
  refine ⟨s₂ • w₁, s₁ • w₂, ?_, ?_⟩
  · rw [Psi_smul, ← h₂]
    exact mul_ne_zero (by simpa using hs₁) (mul_ne_zero hs0 (by simpa using hs₂))
  · rw [Psi_smul, Psi_smul, ← h₁, ← h₂]
    field_simp

end Psi

/-- Adding a small term to a unit stays a unit. -/
theorem ne_zero_and_inv_mem_of_add {L : Type*} [Field L] (V : ValuationSubring L) {a m p : L}
    (ha : a ∈ V) (hai : a⁻¹ ∈ V) (ha0 : a ≠ 0) (hm : m ∈ V) (hp : p ∈ V) (hpi : p⁻¹ ∉ V) :
    a + p * m ≠ 0 ∧ (a + p * m)⁻¹ ∈ V := by
  have hva : V.valuation a = 1 := by
    refine le_antisymm ((V.valuation_le_one_iff a).2 ha) ?_
    have h := (V.valuation_le_one_iff _).2 hai
    rw [map_inv₀] at h
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))).1 h
  have hvp : V.valuation p < 1 :=
    lt_of_le_of_ne ((V.valuation_le_one_iff p).2 hp)
      (fun h => hpi (by rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]))
  have hvm : V.valuation m ≤ 1 := (V.valuation_le_one_iff m).2 hm
  have hlt : V.valuation (p * m) < V.valuation a := by
    rw [map_mul, hva]
    calc V.valuation p * V.valuation m ≤ V.valuation p * 1 := by gcongr
      _ = V.valuation p := mul_one _
      _ < 1 := hvp
  have hve : V.valuation (a + p * m) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hva]
  refine ⟨(Valuation.ne_zero_iff _).1 (by rw [hve]; exact one_ne_zero), ?_⟩
  rw [← V.valuation_le_one_iff, map_inv₀, hve, inv_one]

section Decomp

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

/-- In the residue field of a place of a curve, every element of the valuation
subring has a residue that lifts to the constants. -/
theorem exists_digit [IsAlgClosed K] [IsCurveOver K F] {π : P.toValuationSubring}
    (hπ : Irreducible π) (o : P.toValuationSubring) :
    ∃ a : K, ∃ o' : P.toValuationSubring,
      o = algebraMap K P.toValuationSubring a + π * o' ∧ (o = 0 → o' = 0) := by
  rcases eq_or_ne o 0 with rfl | ho
  · exact ⟨0, 0, by simp, fun _ => rfl⟩
  have : Module.Finite K P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue P.toValuationSubring o)
  have hmem : o - algebraMap K P.toValuationSubring a ∈
      IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
      IsScalarTower.algebraMap_apply K P.toValuationSubring P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨a, b, by rw [mul_comm, hb]; ring, fun h => absurd h ho⟩

/-- The digit expansion of `Psi w` along the order of a uniformiser. -/
theorem decomp [IsAlgClosed K] [IsCurveOver K F] {π : P.toValuationSubring} (hπ : Irreducible π)
    (w : ι →₀ P.toValuationSubring) (hw : w ≠ 0) :
    ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
      Psi F' B P w = algebraMap F F' (π : F) ^ k *
        (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') := by
  classical
  choose dig rest hdr hr0 using exists_digit P hπ
  have hrest0 : rest 0 = 0 := hr0 0 rfl
  have step : ∀ w : ι →₀ P.toValuationSubring,
      Psi F' B P w = algebraMap K' F' (∑ j ∈ w.support, dig (w j) • B j) +
        algebraMap F F' (π : F) * Psi F' B P (w.mapRange rest hrest0) := by
    intro w
    rw [Psi_apply F' B P (w.mapRange _ _),
      Finsupp.sum_mapRange_index (fun j => by simp)]
    rw [Psi_apply]
    simp only [Finsupp.sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hdr (w j)]
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, Place.coe_algebraMap, map_add, map_mul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K K' F',
      ← IsScalarTower.algebraMap_apply K F F']
    ring
  suffices h : ∀ (n : ℕ) (w : ι →₀ P.toValuationSubring) (j₁ : ι), w j₁ ≠ 0 →
      P.ord ((w j₁ : P.toValuationSubring) : F) < n →
      ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
        Psi F' B P w = algebraMap F F' (π : F) ^ k *
          (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') by
    obtain ⟨j₁, hj₁⟩ : ∃ j₁, w j₁ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (Finsupp.ext h)
    exact h ((P.ord ((w j₁ : P.toValuationSubring) : F)).toNat + 1) w j₁ hj₁ (by omega)
  intro n
  induction n with
  | zero =>
    intro w j₁ _ hlt
    have := P.ord_nonneg_of_mem_vs (w j₁).2
    push_cast at hlt
    omega
  | succ n ih =>
    intro w j₁ hj₁ hlt
    by_cases hdig : ∃ j ∈ w.support, dig (w j) ≠ 0
    · refine ⟨0, ∑ j ∈ w.support, dig (w j) • B j, w.mapRange rest hrest0, ?_, ?_⟩
      · intro hd
        obtain ⟨j, hj, hne⟩ := hdig
        exact hne (linearIndependent_iff'.1 B.linearIndependent w.support (fun j => dig (w j))
          hd j hj)
      · rw [pow_zero, one_mul]
        exact step w
    · push Not at hdig
      have hd0 : ∑ j ∈ w.support, dig (w j) • B j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hdig j hj, zero_smul]
      have hj₁s : j₁ ∈ w.support := Finsupp.mem_support_iff.2 hj₁
      have hwj : ((w j₁ : P.toValuationSubring) : F) = (π : F) * (rest (w j₁) : F) := by
        conv_lhs => rw [hdr (w j₁)]
        rw [hdig j₁ hj₁s]
        simp
      have hr : rest (w j₁) ≠ 0 := by
        intro h
        apply hj₁
        apply Subtype.ext
        rw [hwj, h]
        simp
      have hw' : (w.mapRange rest hrest0) j₁ ≠ 0 := by
        rwa [Finsupp.mapRange_apply]
      have hord : P.ord (((w.mapRange rest hrest0) j₁ : P.toValuationSubring) : F) < n := by
        rw [Finsupp.mapRange_apply]
        have hr0' : ((rest (w j₁) : P.toValuationSubring) : F) ≠ 0 := fun h => hr (Subtype.ext h)
        have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
        have := P.ord_mul hπ0 hr0'
        rw [← hwj, P.ord_coe_irreducible hπ] at this
        push_cast at hlt
        omega
      obtain ⟨k, d, w'', hd, heq⟩ := ih (w.mapRange rest hrest0) j₁ hw' hord
      refine ⟨k + 1, d, w'', hd, ?_⟩
      rw [step w, hd0, map_zero, zero_add, heq]
      ring

end Decomp

section LinDisj

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F'] [IsAlgClosed K] [CharZero K]

/-- Linear disjointness of the `K'`-span from `1` over an algebraically closed
`K`: the pin's private linear-algebra engine. -/
theorem sum_ne_of_not_mem_span
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} (c : ι → K') (s : Finset ι) (o : ι → F) (y : F)
    (hy : y ∉ Submodule.span K (Set.range o)) :
    ∑ j ∈ s, algebraMap K' F' (c j) * algebraMap F F' (o j) ≠ algebraMap F F' y := by
  classical
  intro heq
  set M := Submodule.span K (Set.range o) with hM
  let bM := Module.Basis.ofVectorSpace K M
  let v : Module.Basis.ofVectorSpaceIndex K M → F := fun l => (bM l : F)
  have hv : LinearIndependent K v :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hspan : Submodule.span K (Set.range v) = M := by
    change Submodule.span K (Set.range (M.subtype ∘ bM)) = M
    rw [Set.range_comp, Submodule.span_image, bM.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hyv : y ∉ Submodule.span K (Set.range v) := by rwa [hspan]
  have hLI := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg'
    hgen (hv.option hyv)
  have ho : ∀ j, o j ∈ M := fun j => Submodule.subset_span ⟨j, rfl⟩
  let R : ι → (Module.Basis.ofVectorSpaceIndex K M →₀ K) := fun j => bM.repr ⟨o j, ho j⟩
  have hR : ∀ j, ∀ T : Finset (Module.Basis.ofVectorSpaceIndex K M), (R j).support ⊆ T →
      ∑ l ∈ T, algebraMap K F (R j l) * v l = o j := by
    intro j T hT
    have h1 := bM.linearCombination_repr ⟨o j, ho j⟩
    rw [Finsupp.linearCombination_apply] at h1
    have h2 := congrArg (M.subtype) h1
    rw [map_finsuppSum, Finsupp.sum_of_support_subset _ hT _ (fun l _ => by simp)] at h2
    have h3 : ∑ x ∈ T, M.subtype ((R j) x • bM x) = o j := h2
    rw [← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Module.Basis.ofVectorSpaceIndex K M),
      ∀ j ∈ s, (R j).support ⊆ T :=
    ⟨s.biUnion fun j => (R j).support, fun j hj =>
      Finset.subset_biUnion_of_mem (fun j => (R j).support) hj⟩
  let κ : Option (Module.Basis.ofVectorSpaceIndex K M) → K' :=
    fun i => Option.casesOn' i (-1) (fun l => ∑ j ∈ s, R j l • c j)
  have hinner : ∑ l ∈ T, (∑ j ∈ s, R j l • c j) • algebraMap F F' (v l) =
      ∑ j ∈ s, algebraMap K' F' (c j) * algebraMap F F' (o j) := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hR j T (hT j hj), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring
  have hsum : ∑ i ∈ Finset.insertNone T,
      κ i • algebraMap F F' (Option.casesOn' i y v) = 0 := by
    rw [Finset.sum_insertNone]
    simp only [κ, Option.casesOn'_none, Option.casesOn'_some]
    rw [hinner, heq, neg_one_smul, neg_add_cancel]
  have := linearIndependent_iff'.1 hLI (Finset.insertNone T) κ hsum none (by simp)
  simp [κ] at this

end LinDisj

end ConstantFieldPlaceLift

open ConstantFieldPlaceLift in
theorem AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : AlgebraicCurve.Place K F) :
    ∃ P' : AlgebraicCurve.Place K' F',
      P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, P'.ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : AlgebraicCurve.Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q' = P' := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : P.ord (π : F) = 1 := P.ord_coe_irreducible hπ
  have hπinv : (π : F)⁻¹ ∉ P.toValuationSubring := by
    intro h
    have := P.ord_nonneg_of_mem_vs h
    rw [P.ord_inv, hπ1] at this
    omega
  let B := Module.Basis.ofVectorSpace K K'

  have memO : ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ Q'.toValuationSubring := by
    intro Q' hQ o
    have : (o : F) ∈ Q'.toValuationSubring.comap (algebraMap F F') := by rw [hQ]; exact o.2
    exact ValuationSubring.mem_comap.1 this
  have pinv : ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      (algebraMap F F' (π : F))⁻¹ ∉ Q'.toValuationSubring := by
    intro Q' hQ h
    have h2 : (π : F)⁻¹ ∈ Q'.toValuationSubring.comap (algebraMap F F') :=
      ValuationSubring.mem_comap.2 (by rwa [map_inv₀])
    rw [hQ] at h2
    exact hπinv h2

  have ordPsi : ∀ w : _ →₀ P.toValuationSubring, w ≠ 0 → ∃ k : ℕ, ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Psi F' B P w ≠ 0 ∧
        Q'.ord (Psi F' B P w) = k * Q'.ord (algebraMap F F' (π : F)) := by
    intro w hw
    obtain ⟨k, d, w', hd, heq⟩ := decomp F' B P hπ w hw
    refine ⟨k, fun Q' hQ => ?_⟩
    have hunit := ne_zero_and_inv_mem_of_add Q'.toValuationSubring
      (a := algebraMap K' F' d) (m := Psi F' B P w') (p := algebraMap F F' (π : F))
      (Q'.algebraMap_mem' d) (by rw [← map_inv₀]; exact Q'.algebraMap_mem' d⁻¹)
      (by simpa using hd)
      (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w')
      (memO Q' hQ π) (pinv Q' hQ)
    have hmem : algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w' ∈
        Q'.toValuationSubring :=
      add_mem (Q'.algebraMap_mem' d)
        (mul_mem (memO Q' hQ π)
          (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w'))
    have hpk : algebraMap F F' (π : F) ^ k ≠ 0 := pow_ne_zero _ ((_root_.map_ne_zero _).2 hπ0)
    refine ⟨by rw [heq]; exact mul_ne_zero hpk hunit.1, ?_⟩
    rw [heq, Q'.ord_mul hpk hunit.1, ord_eq_zero_of_mem_of_inv_mem Q' hmem hunit.2,
      ← zpow_natCast, Q'.ord_zpow]
    ring

  have ordAny : ∀ z : F', z ≠ 0 → ∃ m : ℤ, ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord z = m * Q'.ord (algebraMap F F' (π : F)) := by
    intro z hz
    obtain ⟨w₁, w₂, hne, hzw⟩ := exists_mul_Psi_eq F' B P hgen hz
    have hw₂ : w₂ ≠ 0 := by rintro rfl; exact hne (map_zero _)
    have hw₁ : w₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hzw
      exact mul_ne_zero hz hne hzw
    obtain ⟨k₁, h₁⟩ := ordPsi w₁ hw₁
    obtain ⟨k₂, h₂⟩ := ordPsi w₂ hw₂
    refine ⟨k₁ - k₂, fun Q' hQ => ?_⟩
    have e₁ := (h₁ Q' hQ).2
    have e₂ := (h₂ Q' hQ).2
    have := Q'.ord_mul hz hne
    rw [hzw, e₁, e₂] at this
    linarith

  have eOne : ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord (algebraMap F F' (π : F)) = 1 := by
    intro Q' hQ
    obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible Q'.toValuationSubring
    have hπ'0 : (π' : F') ≠ 0 := fun h => hπ'.ne_zero (Subtype.ext h)
    obtain ⟨m, hm⟩ := ordAny (π' : F') hπ'0
    have h := hm Q' hQ
    rw [Q'.ord_coe_irreducible hπ'] at h
    have hnn : 0 ≤ Q'.ord (algebraMap F F' (π : F)) := Q'.ord_nonneg_of_mem_vs (memO Q' hQ π)
    exact Int.eq_one_of_dvd_one hnn ⟨m, by rw [mul_comm]; exact h⟩
  have ordEq : ∀ Q' : AlgebraicCurve.Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ f : F, Q'.ord (algebraMap F F' f) = P.ord f := by
    intro Q' hQ f
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf hπ
    have hu0 : algebraMap F F' ((u : P.toValuationSubring) : F) ≠ 0 := by
      rw [_root_.map_ne_zero]
      exact fun h => u.ne_zero (Subtype.ext h)
    have hzp : algebraMap F F' (π : F) ^ P.ord f ≠ 0 := zpow_ne_zero _ ((_root_.map_ne_zero _).2 hπ0)
    have huinv : (algebraMap F F' ((u : P.toValuationSubring) : F))⁻¹ ∈ Q'.toValuationSubring := by
      have hmul : ((u : P.toValuationSubring) : F) *
          (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) = 1 := by
        rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
      rw [← map_inv₀, ← eq_inv_of_mul_eq_one_right hmul]
      exact memO Q' hQ _
    conv_lhs => rw [hu, map_mul, map_zpow₀]
    rw [Q'.ord_mul hu0 hzp, Q'.ord_zpow, eOne Q' hQ,
      ord_eq_zero_of_mem_of_inv_mem Q' (memO Q' hQ u) huinv]
    ring

  have uniq : ∀ Q₁ Q₂ : AlgebraicCurve.Place K' F',
      Q₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q₁ = Q₂ := by
    intro Q₁ Q₂ h1 h2
    apply Place.ext
    ext z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    obtain ⟨m, hm⟩ := ordAny z hz
    rw [Place.mem_iff_ord_nonneg_vs (v := Q₁) z, Place.mem_iff_ord_nonneg_vs (v := Q₂) z, hm Q₁ h1,
      hm Q₂ h2, eOne Q₁ h1, eOne Q₂ h2]

  have hπA : algebraMap F F' (π : F) ∈ rangePsi F' B P := algebraMap_coe_mem_rangePsi F' B P π
  have hI : Ideal.span {(⟨algebraMap F F' (π : F), hπA⟩ : rangePsi F' B P)} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨w, hw⟩ := a.2
    have ha' : Psi F' B P w * algebraMap F F' (π : F) = 1 := by
      have := congrArg Subtype.val ha
      simpa [hw] using this
    have hy : (π : F)⁻¹ ∉ Submodule.span K (Set.range fun j => ((w j : P.toValuationSubring) : F)) := by
      let OK : Submodule K F :=
        { carrier := P.toValuationSubring
          add_mem' := fun ha hb => add_mem ha hb
          zero_mem' := zero_mem _
          smul_mem' := fun c x hx => by
            rw [Algebra.smul_def]
            exact mul_mem (P.algebraMap_mem' c) hx }
      have hle : Submodule.span K (Set.range fun j => ((w j : P.toValuationSubring) : F)) ≤ OK :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (w j).2)
      exact fun h => hπinv (hle h)
    have hPsi : Psi F' B P w =
        ∑ j ∈ w.support, algebraMap K' F' (B j) *
          algebraMap F F' ((w j : P.toValuationSubring) : F) := by
      rw [Psi_apply]
      rfl
    refine sum_ne_of_not_mem_span hfg hfg' hgen B w.support
      (fun j => ((w j : P.toValuationSubring) : F)) _ hy ?_
    rw [← hPsi, map_inv₀]
    exact eq_inv_of_mul_eq_one_left ha'
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  have hAV' : ∀ y, y ∈ rangePsi F' B P → y ∈ V := fun y hy => hAV hy
  have hπV : algebraMap F F' (π : F) ∈ V := hAV' _ hπA
  have hnu : algebraMap F F' (π : F) ∈ V.nonunits :=
    hIV ⟨⟨_, hπA⟩, Ideal.mem_span_singleton_self _, rfl⟩
  have hπVinv : (algebraMap F F' (π : F))⁻¹ ∉ V := by
    have := (V.inv_mem_nonunits_iff (x := (algebraMap F F' (π : F))⁻¹)).1
      (by rw [inv_inv]; exact hnu)
    exact this.resolve_left (inv_ne_zero ((_root_.map_ne_zero _).2 hπ0))

  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  obtain ⟨x', -, hfin'⟩ := hfg'
  have := hfin'
  obtain ⟨P', hP'⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K') x' (RingHom.id F') V (fun a => hAV' _ (algebraMap_mem_rangePsi F' B P a))
    ⟨_, hπVinv⟩
  have hmemP' : ∀ z, z ∈ P'.toValuationSubring ↔ z ∈ V := fun z => by
    rw [hP', ValuationSubring.mem_comap, RingHom.id_apply]

  have hover : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring := by
    ext f
    rw [ValuationSubring.mem_comap, hmemP']
    refine ⟨fun hfV => ?_, fun hf => hAV' _ (algebraMap_coe_mem_rangePsi F' B P ⟨f, hf⟩)⟩
    by_contra hfO
    have hf0 : f ≠ 0 := by rintro rfl; exact hfO (zero_mem _)
    have hn : P.ord f < 0 := by
      by_contra h
      push Not at h
      exact hfO ((Place.mem_iff_ord_nonneg_vs (v := P) f).2 h)
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf0 hπ
    have hui : (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) *
        ((u : P.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    set n := P.ord f with hn'
    have key : (π : F)⁻¹ = (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) * f *
        (π : F) ^ ((-n - 1).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      conv_rhs => rw [hu]
      calc (π : F)⁻¹ = 1 * ((π : F) ^ n * (π : F) ^ (-n - 1)) := by
            rw [← zpow_add₀ hπ0, show n + (-n - 1) = -1 by ring, zpow_neg_one, one_mul]
        _ = _ := by rw [← hui]; ring
    apply hπVinv
    rw [← map_inv₀, key, map_mul, map_mul, map_pow]
    exact mul_mem (mul_mem (hAV' _ (algebraMap_coe_mem_rangePsi F' B P _)) hfV) (pow_mem hπV _)
  exact ⟨P', hover, ordEq P' hover, fun Q' hQ' => uniq Q' P' hQ' hover⟩

/-! ## Constants are base over an algebraically closed field

`AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed`
(the pin's 401-line file), with the pin's field-theory engine written private here:
the Frobenius index of a rational function field, and the core
`Place.mem_range_algebraMap_of_forall_ord_eq_zero_core`.  The pin's
`isSeparable_of_finrank_fieldRange_frobenius_eq` is imported, not re-proved
(`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`). -/

namespace AlgebraicCurve

section FieldTheory

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem finrank_toSubfield (E : IntermediateField K F) :
    Module.finrank E.toSubfield F = Module.finrank E F :=
  Algebra.finrank_eq_of_equiv_equiv
    (⟨⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩,
      fun _ _ => rfl, fun _ _ => rfl⟩ : E.toSubfield ≃+* E)
    (RingEquiv.refl F) (by ext x; rfl)

private noncomputable def ratFuncHom (y : F) (hy : Transcendental K y) : RatFunc K →ₐ[K] F :=
  (K⟮y⟯.val).comp (RatFunc.algEquivOfTranscendental y hy : RatFunc K →ₐ[K] K⟮y⟯)

private theorem ratFuncHom_X (y : F) (hy : Transcendental K y) : ratFuncHom y hy RatFunc.X = y := by
  simp [ratFuncHom]

private theorem map_top_ratFuncHom (y : F) (hy : Transcendental K y) :
    (⊤ : IntermediateField K (RatFunc K)).map (ratFuncHom y hy) = K⟮y⟯ := by
  rw [← RatFunc.adjoin_X, IntermediateField.adjoin_map, Set.image_singleton, ratFuncHom_X]

private theorem map_adjoin_X_pow_ratFuncHom (y : F) (hy : Transcendental K y) (m : ℕ) :
    K⟮(RatFunc.X : RatFunc K) ^ m⟯.map (ratFuncHom y hy) = K⟮y ^ m⟯ := by
  rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow, ratFuncHom_X]

private theorem finrank_adjoin_X_pow' (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K⟮(RatFunc.X : RatFunc K) ^ m⟯ (RatFunc K) = m := by
  rw [RatFunc.finrank_eq_max_natDegree,
    show (RatFunc.X : RatFunc K) ^ m = algebraMap K[X] (RatFunc K) (Polynomial.X ^ m) by
      rw [map_pow, RatFunc.algebraMap_X],
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_one, Nat.max_eq_left (Nat.zero_le m)]

private theorem le_finrank_adjoin_of_pow_eq (y : F) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ F] (m : ℕ) {x : F} (hxy : y ^ m = x) :
    m ≤ Module.finrank K⟮x⟯ F := by
  subst hxy
  have hle : K⟮y ^ m⟯ ≤ K⟮y⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self K y) m)
  have hrel : IntermediateField.relfinrank K⟮y ^ m⟯ K⟮y⟯ = m := by
    rw [← map_adjoin_X_pow_ratFuncHom y hy m, ← map_top_ratFuncHom y hy,
      IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right,
      finrank_adjoin_X_pow']
  have hmul := IntermediateField.relfinrank_mul_finrank_top hle
  rw [hrel] at hmul
  have hpos : 0 < Module.finrank K⟮y⟯ F := Module.finrank_pos
  calc m = m * 1 := (mul_one m).symm
    _ ≤ m * Module.finrank K⟮y⟯ F := Nat.mul_le_mul_left m hpos
    _ = Module.finrank K⟮y ^ m⟯ F := hmul

private theorem fieldRange_frobenius_ratFunc (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectRing K p] :
    (frobenius (RatFunc K) p).fieldRange = K⟮(RatFunc.X : RatFunc K) ^ p⟯.toSubfield := by
  have : CharP (RatFunc K) p := (Algebra.charP_iff K (RatFunc K) p).mp inferInstance
  have halg : ∀ g : K[X], algebraMap K[X] (RatFunc K) g = Polynomial.aeval (RatFunc.X : RatFunc K) g :=
    fun g => by rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    change (frobenius (RatFunc K) p) r ∈ K⟮(RatFunc.X : RatFunc K) ^ p⟯
    have key : ∀ f : K[X], (algebraMap K[X] (RatFunc K) f) ^ p ∈ K⟮(RatFunc.X : RatFunc K) ^ p⟯ := by
      intro f
      have hf : (algebraMap K[X] (RatFunc K) f) ^ p
          = Polynomial.aeval ((RatFunc.X : RatFunc K) ^ p) (f.map (frobenius K p)) := by
        rw [← map_pow, ← Polynomial.map_frobenius_expand, Polynomial.map_expand, halg,
          Polynomial.expand_aeval]
      rw [hf]
      refine IntermediateField.algebra_adjoin_le_adjoin K _ ?_
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨_, rfl⟩
    rw [frobenius_def]
    have h := div_mem (key r.num) (key r.denom)
    rwa [← div_pow, RatFunc.num_div_denom] at h
  · rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro z (⟨c, rfl⟩ | hz)
    · refine ⟨algebraMap K (RatFunc K) ((frobeniusEquiv K p).symm c), ?_⟩
      rw [frobenius_def, ← map_pow, ← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨RatFunc.X, rfl⟩

private theorem finrank_fieldRange_frobenius_ratFunc (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectRing K p] :
    Module.finrank (frobenius (RatFunc K) p).fieldRange (RatFunc K) = p := by
  rw [fieldRange_frobenius_ratFunc K p, finrank_toSubfield, finrank_adjoin_X_pow']

private theorem finrank_fieldRange_frobenius_eq_of_transcendental (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP F p] [PerfectRing K p] (y : F) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ F] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  have : CharP (RatFunc K) p := (Algebra.charP_iff K (RatFunc K) p).mp inferInstance
  set ψ : RatFunc K →+* F := (ratFuncHom y hy).toRingHom with hψ
  have hcomm : ψ.comp (frobenius (RatFunc K) p) = (frobenius F p).comp ψ :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, frobenius_def, map_pow]

  have hB : (⊤ : Subfield (RatFunc K)).map ψ = K⟮y⟯.toSubfield := by
    have h := congrArg IntermediateField.toSubfield (map_top_ratFuncHom y hy)
    rwa [IntermediateField.toSubfield_map, IntermediateField.top_toSubfield] at h
  set C : Subfield F := ((frobenius (RatFunc K) p).fieldRange).map ψ with hC
  have hCB : C ≤ K⟮y⟯.toSubfield := by
    rw [← hB]
    rintro _ ⟨r, -, rfl⟩
    exact ⟨r, trivial, rfl⟩
  have hCA : C ≤ (frobenius F p).fieldRange := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, rfl⟩ := RingHom.mem_fieldRange.mp hr
    exact ⟨ψ s, by rw [frobenius_def, frobenius_def, map_pow]⟩
  have T1 := Subfield.relfinrank_mul_finrank_top hCB
  have T2 := Subfield.relfinrank_mul_finrank_top hCA

  have S3 : Subfield.relfinrank C (frobenius F p).fieldRange
      = Module.finrank K⟮y⟯.toSubfield F := by
    have hC' : C = (K⟮y⟯.toSubfield).map (frobenius F p) := by
      rw [hC, RingHom.fieldRange_eq_map, Subfield.map_map, hcomm, ← Subfield.map_map, hB]
    rw [hC', RingHom.fieldRange_eq_map (frobenius F p), Subfield.relfinrank_map_map,
      Subfield.relfinrank_top_right]

  have S4 : Subfield.relfinrank C K⟮y⟯.toSubfield = p := by
    rw [hC, ← hB, Subfield.relfinrank_map_map, Subfield.relfinrank_top_right]
    exact finrank_fieldRange_frobenius_ratFunc K p
  have hpos : 0 < Module.finrank K⟮y⟯.toSubfield F := by
    rw [finrank_toSubfield]
    exact Module.finrank_pos
  have h := T1.trans T2.symm
  rw [S3, S4, mul_comm p] at h
  exact (Nat.eq_of_mul_eq_mul_left hpos h).symm
end FieldTheory

section R2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem transcendental_of_pow_eq {x y : F} {m : ℕ} (hx : Transcendental K x) (h : y ^ m = x) :
    Transcendental K y :=
  fun halg => hx (h ▸ halg.pow m)

end R2

namespace Place

/-- The pin's core engine: an element of a one-variable function field whose order
vanishes at every place is a constant, over an algebraically closed constant field.
The `hpole` input supplies a place of negative order at every transcendental element
of a finite separable extension (`Place.exists_ord_neg_of_transcendental_of_isSeparable`
below). -/
private theorem mem_range_algebraMap_of_forall_ord_eq_zero_core {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K]
    (hfin : ∀ z : F, Transcendental K z → FiniteDimensional K⟮z⟯ F)
    (hpole : ∀ z : F, Transcendental K z → FiniteDimensional K⟮z⟯ F →
      Algebra.IsSeparable K⟮z⟯ F → ∃ v : Place K F, v.ord z < 0)
    {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by
  classical
  by_contra hxK
  have hxt : Transcendental K x := fun halg =>
    hxK (minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))

  have pole : ∀ z : F, Transcendental K z → (∀ v : Place K F, v.ord z = 0) →
      Algebra.IsSeparable K⟮z⟯ F → False := by
    intro z hz hz0 hsep
    obtain ⟨v, hv⟩ := hpole z hz (hfin z hz) hsep
    rw [hz0 v] at hv
    exact lt_irrefl 0 hv
  obtain ⟨p, hchar⟩ := CharP.exists F
  by_cases hp : p = 0
  ·
    subst hp
    have := hchar
    have : CharZero F := CharP.charP_to_charZero F
    have : CharZero K⟮x⟯ := (algebraMap K⟮x⟯ F).charZero
    have := hfin x hxt
    have : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite _ _
    exact pole x hxt hx Algebra.IsAlgebraic.isSeparable_of_perfectField
  ·
    have := hchar
    have hpp : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero F p).resolve_right hp⟩
    have : CharP K p := (Algebra.charP_iff K F p).mpr hchar
    have : ExpChar K p := ExpChar.prime hpp.out
    have step : ∀ n : ℕ, ∃ y : F, y ^ p ^ n = x := by
      intro n
      induction n with
      | zero => exact ⟨x, by rw [pow_zero, pow_one]⟩
      | succ n ih =>
        obtain ⟨y, hy⟩ := ih
        have hyt : Transcendental K y := transcendental_of_pow_eq hxt hy
        have hy0 : ∀ v : Place K F, v.ord y = 0 := fun v => by
          have h := hx v
          rw [← hy, ← zpow_natCast, v.ord_zpow] at h
          exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast pow_ne_zero n hpp.out.ne_zero)
        have := hfin y hyt
        by_contra hne
        push Not at hne
        have hyp : y ∉ (frobenius F p).fieldRange := by
          intro hmem
          obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp hmem
          rw [frobenius_def] at hz
          apply hne z
          rw [pow_succ', pow_mul, hz, hy]
        have hdeg := finrank_fieldRange_frobenius_eq_of_transcendental (K := K) p y hyt
        have hsep : Algebra.IsSeparable K⟮y⟯ F :=
          Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq p hdeg
            ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩ hyp
        exact pole y hyt hy0 hsep

    have := hfin x hxt
    obtain ⟨y, hy⟩ := step (Module.finrank K⟮x⟯ F)
    have hyt : Transcendental K y := transcendental_of_pow_eq hxt hy
    have := hfin y hyt
    have hle := le_finrank_adjoin_of_pow_eq y hyt _ hy
    exact absurd hle (not_le.mpr (Nat.lt_pow_self hpp.out.one_lt))

/-- A transcendental element of a finite extension of a one-variable function field
has a place of negative order. -/
theorem exists_ord_neg_of_transcendental_of_isSeparable {K F : Type*} [Field K] [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ v : Place K F, v.ord x < 0 := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hφ : (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval x : Polynomial K →ₐ[K] F) := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    exact fun h => hp (hinj (by rw [h, map_zero]))
  set ψ : RatFunc K →ₐ[K] F := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ_def
  have hψX : ψ RatFunc.X = x := by
    rw [hψ_def, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X, Polynomial.aeval_X,
      map_one, div_one]
  let : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm

  have hEle : IntermediateField.adjoin K ({x} : Set F) ≤ ψ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨RatFunc.X, hψX⟩)
  have : Module.Finite (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add g h _ _ hg hh => exact Submodule.add_mem _ hg hh
    | smul e g _ hg =>
      obtain ⟨r, hr⟩ := hEle e.2
      have hsm : e • g = r • g := by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        have he' : algebraMap (IntermediateField.adjoin K ({x} : Set F)) F e = (e : F) := rfl
        rw [he', ← hr]
      rw [hsm]
      exact Submodule.smul_mem _ r hg

  have haev : ∀ p : Polynomial K,
      Polynomial.aeval x p ∈ IntermediateField.adjoin K ({x} : Set F) := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K x)
  have hle : ψ.fieldRange ≤ IntermediateField.adjoin K ({x} : Set F) := by
    intro y hy
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    rw [hψ_def, RatFunc.liftAlgHom_apply]
    exact div_mem (haev z.num) (haev z.denom)
  have hfr : ψ.fieldRange = IntermediateField.adjoin K ({x} : Set F) := le_antisymm hle hEle
  let eKx : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    (AlgEquiv.ofInjectiveField ψ).trans (IntermediateField.equivOfEq hfr)
  have : Algebra.IsSeparable (RatFunc K) F := by
    refine Algebra.IsSeparable.of_equiv_equiv eKx.symm.toRingEquiv (RingEquiv.refl F) ?_
    refine RingHom.ext fun z => ?_
    show ψ (eKx.symm z) = algebraMap (IntermediateField.adjoin K ({x} : Set F)) F z
    have h1 : ψ (eKx.symm z) = ((eKx (eKx.symm z) : IntermediateField.adjoin K ({x} : Set F)) : F) :=
      rfl
    rw [h1, eKx.apply_symm_apply, IntermediateField.algebraMap_apply]

  obtain ⟨vinf, hvinf⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  obtain ⟨w, hw⟩ := exists_comap_eq_toValuationSubring_core (K := K) (F' := F) vinf
  obtain ⟨e, he0, htrans⟩ := rowMain w vinf hw.symm
  refine ⟨w, ?_⟩
  have hX := htrans RatFunc.X
  have hordX : vinf.ord RatFunc.X = -1 := by
    rw [AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      vinf hvinf RatFunc.X_ne_zero, RatFunc.intDegree_X]
  have hmapX : algebraMap (RatFunc K) F RatFunc.X = x := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hψX
  rw [hmapX, hordX] at hX
  rw [hX, mul_neg_one, Left.neg_neg_iff]
  exact_mod_cast he0

end Place

end AlgebraicCurve

open AlgebraicCurve.Place in
theorem AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (j : F)
    (hj : Transcendental K j) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    {x : F} (hx : ∀ v : AlgebraicCurve.Place K F, v.ord x = 0) :
    x ∈ (algebraMap K F).range := by
  have _ := hj
  exact mem_range_algebraMap_of_forall_ord_eq_zero_core
    (fun z hz => AlgebraicCurve.finiteDimensional_adjoin_of_transcendental j hz)
    (fun z hz _ _ => exists_ord_neg_of_transcendental_of_isSeparable z hz)
    hx

/-! ## Rigidity of the centred place

`AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension`
(the pin's 429-line file) and
`AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension`
(the pin's 205-line file), with the tensor-product/centring block the two share
written once here (`mulMap`, `evalMap`, `mulMap_injective`, `exists_centred`).
The general place and span lemmas of that block are public, at the pin's own
names (`mem_of_valuation_lt_one`, `eq_zero_of_valuation_algebraMap_lt_one`,
`centre_unique`, `span_eq_top_of_adjoin_eq_top`), which the pin states publicly
in both files; the tensor-product engine stays `private`. -/

namespace AlgebraicCurve.CentredPlaceRigidity

section General

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]

theorem mem_of_valuation_lt_one (P : Place E FE) {y : FE}
    (hy : P.toValuationSubring.valuation y < 1) : y ∈ P.toValuationSubring :=
  (ValuationSubring.valuation_le_one_iff _ _).mp hy.le

private theorem adicValuation_lt_one_of_valuation_lt_one (P : Place E FE) {y : FE}
    (hy : P.toValuationSubring.valuation y < 1) : P.adicValuation y < 1 := by
  have hmem := mem_of_valuation_lt_one P hy
  have h := (ValuationSubring.valuation_lt_one_iff P.toValuationSubring ⟨y, hmem⟩).mpr hy
  exact (P.mem_maximalIdeal_iff_adicValuation_lt_one ⟨y, hmem⟩).mp h

private theorem ord_ne_zero_of_valuation_lt_one (P : Place E FE) {y : FE} (hy0 : y ≠ 0)
    (hy : P.toValuationSubring.valuation y < 1) : P.ord y ≠ 0 := fun h =>
  (adicValuation_lt_one_of_valuation_lt_one P hy).ne
    ((P.ord_eq_zero_iff_adicValuation_eq_one hy0).mp h)

theorem eq_zero_of_valuation_algebraMap_lt_one (P : Place E FE) {c : E}
    (hc : P.toValuationSubring.valuation (algebraMap E FE c) < 1) : c = 0 := by
  by_contra h
  have hu : IsUnit (algebraMap E P.toValuationSubring c) := (IsUnit.mk0 c h).map _
  have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hu
  rw [Place.coe_algebraMap] at h1
  exact hc.ne h1

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F FE]

theorem centre_unique (P : Place E FE) {σ τ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (σ f)) < 1)
    (hτ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (τ f)) < 1) :
    σ = τ := by
  ext f
  have h : P.toValuationSubring.valuation (algebraMap E FE (τ f - σ f)) < 1 := by
    have := Valuation.map_sub P.toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (σ f)) (algebraMap F FE f - algebraMap E FE (τ f))
    rw [sub_sub_sub_cancel_left, ← map_sub] at this
    exact this.trans_lt (max_lt (hσ f) (hτ f))
  exact (sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)).symm

end General

section Span

theorem span_eq_top_of_adjoin_eq_top {E L M : Type*} [Field E] [Field L] [Field M]
    [Algebra E L] [Algebra L M] [Algebra E M] [IsScalarTower E L M] {ι : Type*} [Finite ι]
    (b : ι → M)
    (hmul : ∀ i j, b i * b j ∈ Submodule.span L (Set.range b))
    (h1 : (1 : M) ∈ Submodule.span L (Set.range b))
    {T : Set M} (hT : T ⊆ Submodule.span L (Set.range b))
    (hgen : IntermediateField.adjoin E T = ⊤) :
    Submodule.span L (Set.range b) = ⊤ := by
  set S := Submodule.span L (Set.range b) with hS
  have : FiniteDimensional L S := FiniteDimensional.span_of_finite L (Set.finite_range b)
  have hmul' : ∀ s ∈ S, ∀ s' ∈ S, s * s' ∈ S := by
    refine Submodule.mul_le.mp ?_
    rw [hS, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hmul i j
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [inv_zero]; exact S.zero_mem
    let m : S →ₗ[L] S :=
      { toFun := fun y => ⟨s * y, hmul' s hs y y.2⟩
        map_add' := fun y y' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r y => Subtype.ext (by simp) }
    have hinj : Function.Injective m := fun y y' h =>
      Subtype.ext (mul_left_cancel₀ hs0 (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨1, h1⟩
    have hy' : s * y = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  let S' : IntermediateField E M :=
    { carrier := S
      mul_mem' := fun ha hb => hmul' _ ha _ hb
      one_mem' := h1
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [IsScalarTower.algebraMap_apply E L M, Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem _ h1
      inv_mem' := hinv }
  have hle : (⊤ : IntermediateField E M) ≤ S' := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr hT
  exact eq_top_iff.mpr fun y _ => hle (IntermediateField.mem_top (x := y))

end Span

section Setup

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE]

variable (K F E FE) in
noncomputable def mulMap : E ⊗[K] F →ₐ[E] FE :=
  Algebra.TensorProduct.lift (Algebra.ofId E FE) (IsScalarTower.toAlgHom K F FE)
    (fun _ _ => Commute.all _ _)

theorem mulMap_tmul (c : E) (f : F) :
    mulMap K F E FE (c ⊗ₜ f) = algebraMap E FE c * algebraMap F FE f := rfl

noncomputable def evalMap (e : F →ₐ[K] E) : E ⊗[K] F →ₐ[E] E :=
  Algebra.TensorProduct.lift (AlgHom.id E E) e (fun _ _ => Commute.all _ _)

theorem evalMap_tmul (e : F →ₐ[K] E) (c : E) (f : F) : evalMap e (c ⊗ₜ f) = c * e f := rfl

theorem mulMap_injective
    (hli : LinearIndependent E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i))) :
    Function.Injective (mulMap K F E FE) := by
  classical
  let bE := Algebra.TensorProduct.basis E (Module.Basis.ofVectorSpace K F)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hrepr : Finsupp.linearCombination E bE (bE.repr z) = z := bE.linearCombination_repr z
  have hcomp : ((mulMap K F E FE).toLinearMap : E ⊗[K] F →ₗ[E] FE) ∘ bE =
      fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i) := by
    funext i
    simp [bE, Algebra.TensorProduct.basis_apply, mulMap_tmul]
  have h0 : Finsupp.linearCombination E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i))
      (bE.repr z) = 0 := by
    rw [← hcomp, ← Finsupp.apply_linearCombination, hrepr]
    exact hz
  have hc : bE.repr z = 0 := hli (by rw [map_zero]; exact h0)
  rw [← hrepr, hc, map_zero]

/-- An alg-hom `F →ₐ[K] E` is the centre of a place of `FE` over the constant
extension: the pin's `exists_centred`. -/
theorem exists_centred [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) :
    ∃ P : Place E FE, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have hinj : Function.Injective (mulMap K F E FE) :=
    mulMap_injective (AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg
      hfgE hgen (Module.Basis.ofVectorSpace K F).linearIndependent)
  let ε : (E ⊗[K] F) ≃ₐ[E] (mulMap K F E FE).range := AlgEquiv.ofInjective _ hinj
  let θ : (mulMap K F E FE).range →ₐ[E] E :=
    (evalMap e).comp (ε.symm : (mulMap K F E FE).range →ₐ[E] E ⊗[K] F)
  let I : Ideal (mulMap K F E FE).range := RingHom.ker θ.toRingHom
  have hI : I ≠ ⊤ := RingHom.ker_ne_top θ.toRingHom
  obtain ⟨B, hRB, hIB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := (mulMap K F E FE).range.toSubring) I hI
  have hEB : ∀ c : E, algebraMap E FE c ∈ B := fun c =>
    hRB ((mulMap K F E FE).range.algebraMap_mem c)

  have hval : ∀ f : F, mulMap K F E FE (1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f)) =
      algebraMap F FE f - algebraMap E FE (e f) := fun f => by
    rw [map_sub, AlgHom.commutes, mulMap_tmul, map_one, one_mul]
  have hmemR : ∀ f : F, algebraMap F FE f - algebraMap E FE (e f) ∈ (mulMap K F E FE).range :=
    fun f => (AlgHom.mem_range _).mpr ⟨_, hval f⟩
  have hcen : ∀ f : F, B.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
    intro f
    rw [← ValuationSubring.mem_nonunits_iff]
    refine hIB ⟨⟨_, hmemR f⟩, ?_, rfl⟩
    show θ ⟨_, hmemR f⟩ = 0
    have hsymm : ε.symm ⟨_, hmemR f⟩ = 1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (hval f).symm
    change evalMap e (ε.symm ⟨_, hmemR f⟩) = 0
    rw [hsymm, map_sub, evalMap_tmul, one_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]

  obtain ⟨x, hx, hxfin⟩ := id hfg
  have := hxfin
  have hxE : Transcendental E (algebraMap F FE x) :=
    AlgebraicCurve.ConstantFieldExtension.transcendental_algebraMap (K := K) (F := F) (x := x) hfgE hgen
  have htne : algebraMap F FE x - algebraMap E FE (e x) ≠ 0 := fun h =>
    hxE (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap (e x))
  have hBtop : B ≠ ⊤ := by
    intro hB
    have hmem := (ValuationSubring.mem_nonunits_iff (A := B)).mpr (hcen x)
    rcases (ValuationSubring.mem_nonunits_iff_or (A := B)).mp hmem with h0 | hinv
    · exact htne h0
    · exact hinv (hB ▸ ValuationSubring.mem_top _)

  obtain ⟨x₀, -, hx₀fin⟩ := id hfgE
  have := hx₀fin
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨P, hP⟩ := Place.exists_of_valuationSubring (K := E) x₀ B hEB hBtop
  exact ⟨P, fun f => by rw [hP]; exact hcen f⟩

end Setup

end AlgebraicCurve.CentredPlaceRigidity

open AlgebraicCurve.CentredPlaceRigidity in
theorem AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) (P Q : AlgebraicCurve.Place E FE)
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1)
    (hQ : ∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    P = Q := by
  classical
  obtain ⟨x, hx, hfin⟩ := id hfg
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  have : FiniteDimensional Kx F := hfin
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hxKx : x ∈ Kx := IntermediateField.subset_adjoin K _ (Set.mem_singleton x)

  set x' : FE := algebraMap F FE x with hx'def
  have hx' : Transcendental E x' :=
    AlgebraicCurve.ConstantFieldExtension.transcendental_algebraMap (K := K) (F := F) (x := x) hfgE hgen
  set a : E := e x with hadef
  have ht0 : x' - algebraMap E FE a ≠ 0 := fun h =>
    hx' (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap a)
  let γ : RatFunc E ≃ₐ[E] E⟮x'⟯ := RatFunc.algEquivOfTranscendental x' hx'
  let ψ : RatFunc E →ₐ[E] FE := (IntermediateField.val _).comp (γ : RatFunc E →ₐ[E] E⟮x'⟯)
  let : Algebra (RatFunc E) FE := ψ.toRingHom.toAlgebra
  have : IsScalarTower E (RatFunc E) FE :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have hψ : ∀ r, algebraMap (RatFunc E) FE r = ψ r := fun r => rfl
  have hψX : algebraMap (RatFunc E) FE RatFunc.X = x' := by
    rw [hψ]
    exact RatFunc.algEquivOfTranscendental_X x' hx'
  have hψC : ∀ c : E, algebraMap (RatFunc E) FE (RatFunc.C c) = algebraMap E FE c := fun c => by
    have h : RatFunc.C c = algebraMap E (RatFunc E) c := by rw [RatFunc.algebraMap_eq_C]
    rw [h, ← IsScalarTower.algebraMap_apply]

  have hcoef : ∀ c : Kx, ∃ r : RatFunc E,
      algebraMap (RatFunc E) FE r = algebraMap F FE (c : F) := by
    intro c
    have hmem : algebraMap F FE (c : F) ∈ E⟮x'⟯ := by
      let φ : F →ₐ[K] FE := IsScalarTower.toAlgHom K F FE
      have h1 : φ (c : F) ∈ (IntermediateField.adjoin K ({x} : Set F)).map φ := ⟨c, c.2, rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
      have hle : IntermediateField.adjoin K ({φ x} : Set FE) ≤
          IntermediateField.restrictScalars K E⟮x'⟯ :=
        IntermediateField.adjoin_le_iff.mpr
          (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self E x'))
      exact hle h1
    refine ⟨γ.symm ⟨_, hmem⟩, ?_⟩
    rw [hψ]
    change ((γ (γ.symm ⟨_, hmem⟩) : E⟮x'⟯) : FE) = _
    rw [AlgEquiv.apply_symm_apply]
  set n : ℕ := Module.finrank Kx F with hndef
  let b := Module.finBasis Kx F
  let b' : Fin n → FE := fun i => algebraMap F FE (b i)
  have hT : ∀ f : F, algebraMap F FE f ∈ Submodule.span (RatFunc E) (Set.range b') := by
    intro f
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hcoef (b.repr f i)
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul, ← hr, ← Algebra.smul_def]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span (RatFunc E) (Set.range b') = ⊤ :=
    span_eq_top_of_adjoin_eq_top (E := E) b'
      (fun i j => by simpa only [b', ← map_mul] using hT (b i * b j))
      (by simpa only [map_one] using hT 1)
      (T := Set.range (algebraMap F FE)) (by rintro _ ⟨f, rfl⟩; exact hT f) hgen
  have : Module.Finite (RatFunc E) FE :=
    Module.finite_def.mpr (by rw [← hspan]; exact Submodule.fg_span (Set.finite_range b'))
  have hrank : Module.finrank (RatFunc E) FE ≤ n := by
    have h := finrank_range_le_card (R := RatFunc E) b'
    rw [Fintype.card_fin] at h
    change Module.finrank (RatFunc E) (Submodule.span (RatFunc E) (Set.range b')) ≤ n at h
    rwa [hspan, finrank_top] at h
  have : Algebra.IsIntegral (RatFunc E) FE := Algebra.IsIntegral.of_finite _ _
  have : CharZero (RatFunc E) :=
    charZero_of_injective_algebraMap (algebraMap E (RatFunc E)).injective
  have : Algebra.IsSeparable (RatFunc E) FE := Algebra.IsSeparable.of_integral _ _

  let v₀ : Place E (RatFunc E) := RationalFunctionField.placeOfPoint E a
  let Z : Finset (Place E FE) := v₀.fiber FE
  have hzero : ∀ P' : Place E FE,
      P'.toValuationSubring.valuation (x' - algebraMap E FE a) < 1 → P' ∈ Z := by
    intro P' hP'
    rw [Place.mem_fiber]
    rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty E (P'.restrict (RatFunc E)) with
      ⟨c, hc⟩ | hinf
    · rw [hc]
      by_contra hne
      have hca : c ≠ a := fun h => hne (by rw [h])
      have hordw : (RationalFunctionField.placeOfPoint E c).ord
          (RatFunc.X - RatFunc.C a : RatFunc E) = 0 := by
        have h := RationalFunctionField.ord_placeOfPoint_algebraMap c (Polynomial.X_sub_C_ne_zero a)
        rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at h
        rw [h, Polynomial.rootMultiplicity_X_sub_C, ite_eq_right (by simpa using hca), Nat.cast_zero]
      have hordP : P'.ord (x' - algebraMap E FE a) = 0 := by
        have h := P'.ord_restrict (RatFunc.X - RatFunc.C a : RatFunc E)
        rw [hc, hordw, mul_zero, map_sub, hψX, hψC] at h
        exact h
      exact ord_ne_zero_of_valuation_lt_one P' ht0 hP' hordP
    · exfalso
      have hxmem : x' ∈ P'.toValuationSubring := by
        have h := add_mem (mem_of_valuation_lt_one P' hP') (P'.algebraMap_mem' a)
        rwa [sub_add_cancel] at h
      have hX : (RatFunc.X : RatFunc E) ∈ (P'.restrict (RatFunc E)).toValuationSubring := by
        rw [Place.mem_restrict_iff, hψX]
        exact hxmem
      rw [hinf, RationalFunctionField.placeInfty_toValuationSubring,
        Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hX
      exact absurd hX (by norm_num)
  have hcardZ : Z.card ≤ n := by
    have hv₀ : v₀.IsRational := Place.isRational_of_isCurveOver (K := E) v₀
    have hsum := Place.sum_ramificationIndex_eq_finrank (F' := FE) v₀ hv₀
      (fun w _ => Place.isRational_of_isCurveOver (K := E) w)
    have h1 : (Z.card : ℤ) ≤ ∑ w ∈ Z, (w.ramificationIndex (RatFunc E) : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      rw [Nat.cast_one, Nat.one_le_cast]
      exact w.ramificationIndex_pos (F := RatFunc E)
    have h2 : (Z.card : ℤ) ≤ (n : ℤ) := by
      rw [hsum] at h1
      exact h1.trans (by exact_mod_cast hrank)
    exact_mod_cast h2

  let : Algebra Kx E := (e.comp Kx.val).toRingHom.toAlgebra
  have : IsScalarTower K Kx E :=
    IsScalarTower.of_algebraMap_eq fun c => ((e.comp Kx.val).commutes c).symm
  have : CharZero Kx := charZero_of_injective_algebraMap (algebraMap K Kx).injective
  have : Algebra.IsSeparable Kx F := Algebra.IsSeparable.of_integral _ _
  have hcardH : Fintype.card (F →ₐ[Kx] E) = n := AlgHom.card Kx F E
  have hHx : ∀ σ : F →ₐ[Kx] E, σ x = a := fun σ => by
    have h := σ.commutes ⟨x, hxKx⟩
    rw [IntermediateField.algebraMap_apply] at h
    exact h
  have hex : ∀ σ : F →ₐ[Kx] E, ∃ P' : Place E FE, ∀ f : F,
      P'.toValuationSubring.valuation
        (algebraMap F FE f - algebraMap E FE (σ.restrictScalars K f)) < 1 :=
    fun σ => exists_centred hfg hfgE hgen (σ.restrictScalars K)
  choose Pl hPl using hex
  have hPl_inj : Function.Injective Pl := fun σ τ h => by
    apply AlgHom.restrictScalars_injective K
    refine centre_unique (Pl σ) (hPl σ) ?_
    rw [h]
    exact hPl τ
  have hPlZ : ∀ σ, Pl σ ∈ Z := fun σ => hzero (Pl σ) (by
    have h := hPl σ x
    rwa [AlgHom.restrictScalars_apply, hHx σ] at h)

  have himg : Finset.univ.image Pl = Z := by
    apply Finset.eq_of_subset_of_card_le
    · intro P' hP'
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hP'
      exact hPlZ σ
    · rw [Finset.card_image_of_injective _ hPl_inj, Finset.card_univ, hcardH]
      exact hcardZ
  have hPZ : P ∈ Z := hzero P (hP x)
  have hQZ : Q ∈ Z := hzero Q (hQ x)
  rw [← himg] at hPZ hQZ
  obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hPZ
  obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp hQZ
  have hσe : σ.restrictScalars K = e := centre_unique P (by rw [← hσ]; exact hPl σ) hP
  have hτe : τ.restrictScalars K = e := centre_unique Q (by rw [← hτ]; exact hPl τ) hQ
  have hστ : σ = τ := AlgHom.restrictScalars_injective K (hσe.trans hτe.symm)
  rw [← hσ, ← hτ, hστ]

/-! ## A transcendental element has a place of negative order (char 0) -/

theorem AlgebraicCurve.Place.exists_ord_neg_of_transcendental {K F : Type*} [Field K] [CharZero K]
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ v : AlgebraicCurve.Place K F, v.ord x < 0 := by
  have : CharZero ↥(IntermediateField.adjoin K ({x} : Set F)) := inferInstance
  have : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ _
  exact AlgebraicCurve.Place.exists_ord_neg_of_transcendental_of_isSeparable x hx

/-! ## The point ↔ place dictionary of the constant extension

`AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension`
(the pin's 205-line file): every alg-hom `F →ₐ[K] E` is the centre of a unique
place of `FE`, and conversely. -/

namespace AlgebraicCurve.PointPlaceDictionary

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE]

/-- Every element of the valuation subring of a place of the constant extension
whose constants are all integral is centred at some alg-hom `F →ₐ[K] E`. -/
private theorem exists_centre_of_forall_mem [IsAlgClosed E] [IsCurveOver E FE] (P : Place E FE)
    (hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) :
    ∃ e : F →ₐ[K] E, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have : Module.Finite E P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral E P.ResidueField := Algebra.IsIntegral.of_finite E P.ResidueField
  have hbij : Function.Bijective (algebraMap E P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ρ : E ≃+* P.ResidueField := RingEquiv.ofBijective (algebraMap E P.ResidueField) hbij
  let ι : F →+* P.toValuationSubring := (algebraMap F FE).codRestrict P.toValuationSubring hP
  let r : F →+* P.ResidueField := (IsLocalRing.residue P.toValuationSubring).comp ι
  have hρ : ∀ c : E, ρ c = IsLocalRing.residue _ (algebraMap E P.toValuationSubring c) :=
    fun c => rfl
  have hr : ∀ a : K, r (algebraMap K F a) = ρ (algebraMap K E a) := by
    intro a
    rw [hρ]
    change IsLocalRing.residue _ (ι (algebraMap K F a)) = _
    congr 1
    apply Subtype.ext
    change algebraMap F FE (algebraMap K F a) = (algebraMap E P.toValuationSubring _ : FE)
    rw [Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let e : F →ₐ[K] E :=
    { ρ.symm.toRingHom.comp r with
      commutes' := fun a => by
        change ρ.symm (r (algebraMap K F a)) = algebraMap K E a
        rw [hr, RingEquiv.symm_apply_apply] }
  refine ⟨e, fun f => ?_⟩
  have he : ρ (e f) = r f := by
    change ρ (ρ.symm (r f)) = r f
    exact ρ.apply_symm_apply _
  have hmem : (⟨algebraMap F FE f, hP f⟩ - algebraMap E P.toValuationSubring (e f) :
      P.toValuationSubring) ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hρ, he, sub_eq_zero]
    rfl
  have := (ValuationSubring.valuation_lt_one_iff _ _).mp hmem
  simpa [Place.coe_algebraMap] using this

end AlgebraicCurve.PointPlaceDictionary

open AlgebraicCurve.PointPlaceDictionary in
theorem AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    (∀ e : F →ₐ[K] E, ∃! P : AlgebraicCurve.Place E FE, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) ∧
    (∀ P : AlgebraicCurve.Place E FE, (∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) →
      ∃ e : F →ₐ[K] E, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) := by
  refine ⟨fun e => ?_, fun P hP => exists_centre_of_forall_mem P hP⟩
  obtain ⟨P, hP⟩ := AlgebraicCurve.CentredPlaceRigidity.exists_centred hfg hfgE hgen e
  exact ⟨P, hP, fun Q hQ =>
    AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE
      hfgE hgen e Q P hQ hP⟩

/-! ## The shared `maximalIdeal` block

The 7- and 22-line pieces of the pin's `Basic` sections (shared by its
`mem_span_range`, `exists_derivation` and `isPrincipal` files) that the port does
not already carry.  `mem_of_ord_nonneg` is the port's `Place.mem_vs_of_ord_nonneg`
(no non-zero hypothesis) / `Place.mem_of_ord_nonneg` (with one), and
`isUnit_add_of_mem_maximalIdeal` is the port's generic
`Place.LocalDerivation.isUnit_add_of_mem_maximalIdeal`; neither is re-proved here. -/

namespace AlgebraicCurve.Place

section MaximalIdeal

variable {k L : Type*} [Field k] [Field L] [Algebra k L] {w : Place k L}

/-- A member of the valuation subring of positive order lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_ord_pos {Y : w.toValuationSubring} (h : 0 < w.ord (Y : L)) :
    Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, rfl⟩ := hu
  have := w.ord_coe_unit u
  omega

/-- In the residue field of a place of a curve over an algebraically closed field,
every element of the valuation subring differs from a constant by a maximally
small term. -/
theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed k] [IsCurveOver k L]
    (X : w.toValuationSubring) :
    ∃ a : k, X - algebraMap k w.toValuationSubring a ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
  have : Module.Finite k w.ResidueField := IsCurveOver.finiteResidue w
  have : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue w.toValuationSubring X)
  refine ⟨a, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
    IsScalarTower.algebraMap_apply k w.toValuationSubring w.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

end MaximalIdeal

/-! ## The two layer-0 roots as public headlines

The pin writes each of these as a public `theorem solution` over a private engine of the same
file (`Place.rowMain` in both, disambiguated here).  The engines are the module's private blocks
above; the headlines are the pin's statements, one line each. -/

section Layer0Nodes

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F']

/-- Pin `Place.exists_ord_algebraMap_eq_mul_ord`: along an integral map, the order at `w` of the
image of `f` is `e · ord_v f` for a ramification index `e > 0`. -/
theorem exists_ord_algebraMap_eq_mul_ord (w : Place K F') (v : Place K F)
    (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f :=
  rowMain w v hv

end Layer0Nodes

section Layer0ComapNode

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- Pin `Place.exists_comap_eq_toValuationSubring`: every place of `F` is the comap of a place of
a finite separable extension `F'`. -/
theorem exists_comap_eq_toValuationSubring (v : Place K F) :
    ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring :=
  exists_comap_eq_toValuationSubring_core v

end Layer0ComapNode

end AlgebraicCurve.Place
