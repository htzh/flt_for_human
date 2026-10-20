/-
  A *regular prolongation* of a valuation subring `A` of a field `L` along a field
  extension `L → F`: a valuation subring `integers` of `F` that meets the image of
  `L` exactly in `A` (`algebraMap_mem_iff`), with a residue map onto an extension
  `Fbar` of `A`'s residue field which is surjective, whose kernel is the maximal
  ideal, which restricts to `A`'s own residue map on constants
  (`residue_algebraMap`), and which can be made nonzero at any `f ≠ 0` by rescaling
  with a constant of `L` (`exists_smul_mem`). It is the valuation-theoretic input
  of the Gauss prolongation of places.

  The port of the pin definition module

      `AlgebraicCurve.RegularProlongation`

  (`Definitions/Def_AlgebraicCurve_RegularProlongation.lean` — 84 pin lines), the
  structure, the `RegularProlongation` namespace's three lemmas and the trailing
  `ConstantReduction` bridge, transcribed verbatim: same names, same namespace
  `AlgebraicCurve`, same field order and binder spelling, the pin's `@[reducible]`
  and `@[simp]` attributes kept. The mathematics of the three lemmas is the
  unit/maximal-ideal dictionary (`isUnit_of_residue_ne_zero`,
  `residue_ne_zero_of_isUnit`) and the observation that a rescaled element's residue
  cannot vanish for the zero constant (`smul_const_ne_zero`). The bridge
  (`ConstantReduction.toRegularProlongation` and its two `@[simp]` projections)
  reads a pin `AlgebraicCurve.ConstantReduction` as a regular prolongation; it is
  part of the pin's global simp configuration and is homed here because the
  Gauss-prolongation consumers need the pair.

  Assumes: `FLTForHuman/AlgebraicCurve/ConstantReduction.lean` (the pin's
  `Definitions/Def_AlgebraicCurve_ConstantReduction.lean`), and mathlib `v4.34.0`.

  spec-pin: Definitions/Def_AlgebraicCurve_RegularProlongation.lean
  Drift against `v4.34.0`: none in the structure or the three lemmas. The pin's two
  `import` lines become `ConstantReduction.lean` plus four mathlib modules; docstrings
  are added (outside the checked statement). The pin's `@[reducible]` on
  `toRegularProlongation` and its two `@[simp]` attributes are kept.

-/

import FLTForHuman.AlgebraicCurve.ConstantReduction
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maximal

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- A valuation subring of `F` prolonging the valuation subring `A` of `L`, with a
residue map onto `Fbar` compatible with `A`'s residue field and with `A`'s residue
map on constants. -/
structure RegularProlongation where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

namespace RegularProlongation

variable {A F Fbar}
variable (R : RegularProlongation A F Fbar)

/-- An element of the integers whose residue is nonzero is a unit: the maximal ideal
is exactly the kernel of the residue map. -/
theorem isUnit_of_residue_ne_zero {f : R.integers} (hf : R.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal R.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← R.ker_residue] at hmem
  exact hmem

/-- A unit of the integers has nonzero residue. -/
theorem residue_ne_zero_of_isUnit {f : R.integers} (hf : IsUnit f) : R.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker R.residue := h0
  rw [R.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

/-- Rescaling a nonzero `f` by a constant `c` whose residue is nonzero forces `c ≠ 0`. -/
theorem smul_const_ne_zero {f : F} {c : L} (hc : c • f ∈ R.integers)
    (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

end RegularProlongation

namespace ConstantReduction

variable {A F Fbar}

/-- A constant reduction is a regular prolongation: the same integers, residue map
and structure fields, forgetting the place map. -/
@[reducible] def toRegularProlongation (R : ConstantReduction A F Fbar) : RegularProlongation A F Fbar where
  integers := R.integers
  residue := R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem

/-- The integers of the regular prolongation are the constant reduction's. -/
@[simp] theorem toRegularProlongation_integers (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.integers = R.integers := rfl

/-- The residue map of the regular prolongation is the constant reduction's. -/
@[simp] theorem toRegularProlongation_residue (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.residue = R.residue := rfl

end ConstantReduction

end AlgebraicCurve

end
