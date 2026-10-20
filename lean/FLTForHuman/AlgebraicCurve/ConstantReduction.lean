/-
  A *constant reduction* of a place: a valuation subring `integers` of `F` meeting
  the image of `L` exactly in the valuation subring `A`, with a residue map onto an
  extension `Fbar` of `A`'s residue field, together with the induced map on places
  `Place L F → Place (ResidueField A) Fbar` which is degree-preserving and
  compatible with principal divisors. `IsGood` records the genus drop
  `genusFF (ResidueField A) Fbar = genusFF L F`.

  The port of the pin definition module

      `AlgebraicCurve.ConstantReduction`

  (`Definitions/Def_AlgebraicCurve_ConstantReduction.lean` — 127 pin lines),
  transcribed verbatim: the structure, the `IsGood` predicate, and the twelve
  lemmas/definitions of the `ConstantReduction` namespace which push divisors,
  `degZero` and `Pic0` along the place map. Namespace `AlgebraicCurve`, field order
  and binder spelling unchanged; the pin's `import Mathlib` /
  `Def_AlgebraicCurve_DivisorClassGroup` / `Def_AlgebraicCurve_Repartitions` become
  the port's `Defs/Divisor.lean` and `Defs/Repartitions.lean`, which home the same
  declarations (`Place`, `Divisor`, `Pic0`, `genusFF`). Nothing is promoted.

  The mathematics. If `D` is principal, `D = div f` for some `f ≠ 0`, then
  `exists_smul_mem` produces a constant `c` with `c • f` integral and nonzero
  residue, so `div(residue (c • f)) = mapDomain placeMap (div (c • f))` by
  `mapDomain_placeMap`, and `div (c • f) = div f` because `ord (algebraMap c) = 0`
  for `c ≠ 0` (`ord_algebraMap`, `ord_smul`). Hence `mapDomain placeMap` preserves
  principal divisors and degree (`degree_mapDomain`), so it descends to
  `Pic0 →+ Pic0` (`pic0Map`).

  Assumes: `FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean` (the pin's
  `Def_AlgebraicCurve_Repartitions.lean` and, through it,
  `Def_AlgebraicCurve_DivisorClassGroup.lean`) and mathlib `v4.34.0`.

  spec-pin: Definitions/Def_AlgebraicCurve_ConstantReduction.lean
  Drift against `v4.34.0` and against the pin's imports.

  * the pin's `import Mathlib` / `Def_AlgebraicCurve_DivisorClassGroup` /
    `Def_AlgebraicCurve_Repartitions` become the port's
    `Defs/Repartitions.lean` (which carries `genusFF`; it imports `Defs/Divisor.lean`,
    which carries `Place`, `Divisor` and `Pic0` — the pin's `DivisorClassGroup` lines
    179–247 and `Repartitions`) plus two mathlib valuation modules. No statement moves.
  * the pin's `set_option linter.unusedVariables false in` above `def IsGood` is carried
    verbatim. `IsGood`'s binder `R` is unused *by design* (the pin suppresses it too), and
    neither of Lean's own two suggestions is admissible here: removing `R` changes the
    API (a three-argument `def` becomes a nullary one) and renaming it `_R` changes the
    checked statement text — the checker reports `MISMATCH … port: (_R :
    ConstantReduction A F Fbar) : Prop`. This is the module's one stop-and-report item.
  * docstrings are added throughout (they are outside the checked statement, which the
    checker cuts at the first top-level `:=`).

-/

import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- A constant reduction of a place: a valuation subring of `F` prolonging `A`,
with a residue map onto `Fbar`, a degree-preserving map on places, and the
compatibility of that map with principal divisors. -/
structure ConstantReduction where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  deg_placeMap : ∀ P, (placeMap P).deg = P.deg

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in
/-- The genus drop of a constant reduction: the residue field has the same genus. -/
def IsGood (R : ConstantReduction A F Fbar) : Prop :=
  genusFF (ResidueField A) Fbar = genusFF L F

/-- `IsGood` is the genus equality by definition. -/
theorem isGood_iff (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  Iff.rfl

variable (R : ConstantReduction A F Fbar)

/-- The order of a nonzero constant is zero. -/
theorem ord_algebraMap (P : Place L F) {c : L} (hc : c ≠ 0) : P.ord (algebraMap L F c) = 0 := by
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap L F c, P.algebraMap_mem' c⟩, ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

/-- Rescaling by a nonzero constant does not change the order. -/
theorem ord_smul (P : Place L F) {c : L} (hc : c ≠ 0) (f : F) : P.ord (c • f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap P hc, zero_add]

/-- `mapDomain placeMap` carries principal divisors to principal divisors. -/
theorem mapDomain_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  exact ⟨R.residue ⟨c • f, hc⟩, hres, fun Q =>
    R.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P => by rw [hDf P]; exact (ord_smul P hc0 f).symm) Q⟩

/-- `mapDomain placeMap` preserves the degree. -/
theorem degree_mapDomain (D : Divisor L F) :
    Divisor.degree (Finsupp.mapDomain R.placeMap D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, R.deg_placeMap]

/-- `mapDomain placeMap` carries degree-zero divisors to degree-zero divisors. -/
theorem mapDomain_mem_degZero {D : Divisor L F}
    (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [R.degree_mapDomain, hD]

/-- The induced additive map on divisors. -/
def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.mapDomain.addMonoidHom R.placeMap

/-- `divMap` is `mapDomain placeMap`. -/
@[simp]
theorem divMap_apply (D : Divisor L F) : R.divMap D = Finsupp.mapDomain R.placeMap D := rfl

/-- The induced additive map on degree-zero divisors. -/
def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.domRestrict (Divisor.degZero (K := L) (F := F))).codRestrict _ fun D => R.mapDomain_mem_degZero D.2

/-- The coercion of `degZeroMap` is `mapDomain placeMap`. -/
@[simp]
theorem coe_degZeroMap (D : Divisor.degZero (K := L) (F := F)) :
    (R.degZeroMap D : Divisor (ResidueField A) Fbar) = Finsupp.mapDomain R.placeMap (D : Divisor L F) :=
  rfl

/-- The induced additive map on `Pic0`. -/
def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.mapDomain_mem_principal hD)

/-- `pic0Map` commutes with `Pic0.mk`. -/
theorem pic0Map_mk (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) :=
  rfl

end ConstantReduction

end AlgebraicCurve
