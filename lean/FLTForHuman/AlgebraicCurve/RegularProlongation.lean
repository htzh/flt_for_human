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

spec-pin: Definitions/Def_AlgebraicCurve_RegularProlongation.lean
spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean   -- comparable copy
-/

import FLTForHuman.AlgebraicCurve.ConstantReduction
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max

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

/-! ## The pointwise dictionary for a regular prolongation

The pin's `S_` file carries its two private preliminaries
(`coeff_mem_of_aeval_mem_integers`, the Gauss-lemma coefficient criterion, and
`aux_mem_integers_iff`, the dictionary against a common denominator) in the same
file as the headline; they are transcribed here as private lemmas of the same
namespace. -/

namespace RegularProlongation

open IsLocalRing Polynomial

theorem coeff_mem_of_aeval_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (c : Polynomial L) (hc : Polynomial.aeval (x : F) c ∈ R.integers) (i : ℕ) :
    c.coeff i ∈ A := by
  classical
  by_cases hci : c.coeff i = 0
  · exact hci ▸ A.zero_mem
  have hi : i ∈ c.support := Polynomial.mem_support_iff.mpr hci

  obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image c.support
    (fun j => A.valuation (c.coeff j)) ⟨i, hi⟩
  have hcj₀ : c.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀

  suffices hAj₀ : c.coeff j₀ ∈ A by
    rw [← A.valuation_le_one_iff] at hAj₀ ⊢
    exact (hj₀max i hi).trans hAj₀
  by_contra hnA

  set s : L := (c.coeff j₀)⁻¹ with hs
  have hsnon : s ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hnA)
  have hsA : s ∈ A := (A.valuation_le_one_iff s).mp (A.mem_nonunits_iff.mp hsnon).le
  have hsres : IsLocalRing.residue A ⟨s, hsA⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (A.coe_mem_nonunits_iff.mp hsnon)

  have hcoeff : ∀ j, s * c.coeff j ∈ A := by
    intro j
    by_cases hj : j ∈ c.support
    · have hv := hj₀max j hj
      rw [← A.valuation_le_one_iff, map_mul, hs, map_inv₀]
      have hvj₀ : A.valuation (c.coeff j₀) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hcj₀
      calc (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j)
          ≤ (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j₀) :=
            mul_le_mul_right hv _
        _ = 1 := inv_mul_cancel₀ hvj₀
    · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]; exact A.zero_mem

  set c' : Polynomial A := c.support.sum
    (fun j => Polynomial.C ⟨s * c.coeff j, hcoeff j⟩ * Polynomial.X ^ j) with hc'
  have hc'map : c'.map A.subtype = s • c := by
    rw [hc']; ext j
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_smul, smul_eq_mul]
    rw [Finset.sum_ite_eq c.support j]
    by_cases hj : j ∈ c.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hc'j₀ : c'.coeff j₀ = 1 := by
    rw [hc']
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq c.support j₀, ite_eq_left hj₀]
    exact Subtype.ext (show s * c.coeff j₀ = 1 from by rw [hs, inv_mul_cancel₀ hcj₀])

  set cbar : Polynomial (ResidueField A) := c'.map (IsLocalRing.residue A) with hcbar
  have hcbar0 : cbar ≠ 0 := by
    intro h0
    have : cbar.coeff j₀ = 0 := by rw [h0]; simp
    rw [hcbar, Polynomial.coeff_map, hc'j₀, map_one] at this
    exact one_ne_zero this

  let φ : A →+* R.integers :=
    { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hresφ : R.residue.comp φ = (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) := by
    ext a; exact R.residue_algebraMap a

  have hresEval : R.residue (Polynomial.eval₂ φ x c') =
      Polynomial.aeval (R.residue x) cbar := by
    calc R.residue (Polynomial.eval₂ φ x c')
        = Polynomial.eval₂ (R.residue.comp φ) (R.residue x) c' :=
          Polynomial.hom_eval₂ c' φ R.residue x
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
            (R.residue x) c' := by rw [hresφ]
      _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue x)
            (c'.map (IsLocalRing.residue A)) := by rw [← Polynomial.eval₂_map]
      _ = Polynomial.aeval (R.residue x) cbar := by rw [hcbar, Polynomial.aeval_def]
  have hne0 : R.residue (Polynomial.eval₂ φ x c') ≠ 0 := by
    rw [hresEval]
    exact fun h => hx ⟨cbar, hcbar0, h⟩

  have hfactor : (Polynomial.eval₂ φ x c' : R.integers) = φ ⟨s, hsA⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((Polynomial.eval₂ φ x c' : R.integers) : F) =
      algebraMap L F s * Polynomial.aeval (x : F) c
    have h1 : ((Polynomial.eval₂ φ x c' : R.integers) : F) =
        Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (↑x) c' := by
      have hsub : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype := by
        ext a; rfl
      rw [← hsub]
      exact Polynomial.hom_eval₂ c' φ R.integers.subtype x
    rw [h1, ← Polynomial.eval₂_map, ← Polynomial.aeval_def, hc'map, map_smul,
      Algebra.smul_def]
  apply hne0
  rw [hfactor, map_mul]
  have hresφs : R.residue (φ ⟨s, hsA⟩) = 0 := by
    change (R.residue.comp φ) ⟨s, hsA⟩ = 0
    rw [hresφ]
    change algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨s, hsA⟩) = 0
    rw [hsres, map_zero]
  rw [hresφs, zero_mul]

private theorem aux_mem_integers_iff
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hf : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hf⟩))
    (q : L[X]) (hqf : aeval f q ≠ 0)
    (qA : Polynomial A) (hqAmap : qA.map A.subtype = q)
    (hqbar : qA.map (IsLocalRing.residue A) ≠ 0)
    (e : F) (p : L[X]) (hep : e * aeval f q = aeval f p) :
    e ∈ R.integers ↔ ∀ j, p.coeff j ∈ A := by
  classical
  let φ : A →+* R.integers :=
    { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hresφ : R.residue.comp φ =
      (algebraMap (IsLocalRing.ResidueField A) Fbar).comp (IsLocalRing.residue A) :=
    RingHom.ext fun a => R.residue_algebraMap a
  have hsubφ : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype :=
    RingHom.ext fun _ => rfl
  set qO : R.integers := Polynomial.eval₂ φ ⟨f, hf⟩ qA with hqO
  have hqO_coe : (qO : F) = aeval f q := by
    rw [hqO]
    calc ((Polynomial.eval₂ φ ⟨f, hf⟩ qA : R.integers) : F)
        = Polynomial.eval₂ (R.integers.subtype.comp φ) f qA :=
          Polynomial.hom_eval₂ qA φ R.integers.subtype ⟨f, hf⟩
      _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f qA := by rw [hsubφ]
      _ = Polynomial.eval₂ (algebraMap L F) f (qA.map A.subtype) :=
          (Polynomial.eval₂_map A.subtype (algebraMap L F) f).symm
      _ = aeval f q := by rw [hqAmap, Polynomial.aeval_def]
  have hqmem : aeval f q ∈ R.integers := hqO_coe ▸ qO.2
  have hqO_res : R.residue qO =
      aeval (R.residue ⟨f, hf⟩) (qA.map (IsLocalRing.residue A)) := by
    rw [hqO]
    calc R.residue (Polynomial.eval₂ φ ⟨f, hf⟩ qA)
        = Polynomial.eval₂ (R.residue.comp φ) (R.residue ⟨f, hf⟩) qA :=
          Polynomial.hom_eval₂ qA φ R.residue ⟨f, hf⟩
      _ = Polynomial.eval₂ ((algebraMap (IsLocalRing.ResidueField A) Fbar).comp
            (IsLocalRing.residue A))
            (R.residue ⟨f, hf⟩) qA := by rw [hresφ]
      _ = Polynomial.eval₂ (algebraMap (IsLocalRing.ResidueField A) Fbar) (R.residue ⟨f, hf⟩)
            (qA.map (IsLocalRing.residue A)) := by rw [← Polynomial.eval₂_map]
      _ = aeval (R.residue ⟨f, hf⟩) (qA.map (IsLocalRing.residue A)) :=
          (Polynomial.aeval_def _ _).symm
  have hqO_unit : IsUnit qO := by
    apply R.isUnit_of_residue_ne_zero
    rw [hqO_res]
    exact fun habs => hqbar ((transcendental_iff.mp htr) _ habs)
  have hqinv : (aeval f q)⁻¹ ∈ R.integers := by
    obtain ⟨u, hu⟩ := hqO_unit
    have huF : ((u : R.integers) : F) = aeval f q := by rw [hu]; exact hqO_coe
    have huinv : ((↑u⁻¹ : R.integers) : F) = (aeval f q)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h1 : ((↑u⁻¹ : R.integers) * (↑u : R.integers) : R.integers) = 1 :=
        Units.inv_mul u
      calc ((↑u⁻¹ : R.integers) : F) * aeval f q
          = ((↑u⁻¹ : R.integers) : F) * ((↑u : R.integers) : F) := by rw [huF]
        _ = (((↑u⁻¹ : R.integers) * (↑u : R.integers) : R.integers) : F) := by
            exact_mod_cast rfl
        _ = ((1 : R.integers) : F) := by rw [h1]
        _ = 1 := by exact_mod_cast rfl
    rw [← huinv]; exact (↑u⁻¹ : R.integers).2
  constructor
  · intro heR
    have hpmem : aeval f p ∈ R.integers := hep ▸ mul_mem heR hqmem
    exact fun j =>
      coeff_mem_of_aeval_mem_integers A R ⟨f, hf⟩ htr p hpmem j
  · intro hpA
    have hpmem : aeval f p ∈ R.integers := by
      rw [aeval_eq_sum_range]
      refine sum_mem fun j _ => ?_
      rw [Algebra.smul_def]
      exact mul_mem ((R.algebraMap_mem_iff _).mpr (hpA j)) (pow_mem hf j)
    have heq : e = (aeval f p) * (aeval f q)⁻¹ := by
      rw [← hep, mul_inv_cancel_right₀ hqf]
    rw [heq]; exact mul_mem hpmem hqinv

set_option linter.unusedVariables false in
/-- **The pointwise dictionary for a regular prolongation.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue.lean`;
the pin's `S_` proof is transcribed. -/
theorem mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (htr₁ : Transcendental (IsLocalRing.ResidueField A) (R₁.residue ⟨f, hf₁⟩))
    (htr₂ : Transcendental (IsLocalRing.ResidueField A) (R₂.residue ⟨f, hf₂⟩))
    (e : F) (he : e ∈ IntermediateField.adjoin L ({f} : Set F)) :
    e ∈ R₁.integers ↔ e ∈ R₂.integers := by
  classical
  rcases eq_or_ne e 0 with rfl | hene
  · simp only [zero_mem]
  obtain ⟨r, s, hers⟩ := (IntermediateField.mem_adjoin_simple_iff L e).mp he
  have hsf : aeval f s ≠ 0 := fun h => hene (by rw [hers, h, div_zero])
  obtain ⟨c, hcmem, hcres⟩ := R₁.exists_smul_mem (aeval f s) hsf
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hcmem hcres
  set q : L[X] := C c * s with hqdef
  have hcq : aeval f q = c • aeval f s := by
    simp only [hqdef, map_mul, aeval_C, Algebra.smul_def]
  have hqf : aeval f q ≠ 0 := hcq ▸ smul_ne_zero hc0 hsf
  have hqmem₁ : aeval f q ∈ R₁.integers := hcq ▸ hcmem
  have hqres₁ : R₁.residue ⟨aeval f q, hqmem₁⟩ ≠ 0 := by
    intro h; apply hcres
    have heq : (⟨aeval f q, hqmem₁⟩ : R₁.integers) = ⟨c • aeval f s, hcmem⟩ := Subtype.ext hcq
    rw [← heq]; exact h
  have hqA : ∀ j, q.coeff j ∈ A := fun j =>
    coeff_mem_of_aeval_mem_integers A R₁ ⟨f, hf₁⟩ htr₁ q hqmem₁ j

  set qA : Polynomial A :=
    q.support.sum (fun j => C ⟨q.coeff j, hqA j⟩ * X ^ j) with hqAdef
  have hqAmap : qA.map A.subtype = q := by
    ext j
    simp only [hqAdef, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq q.support j]
    by_cases hj : j ∈ q.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hqbar_ne : qA.map (IsLocalRing.residue A) ≠ 0 := by
    intro hqz
    apply hqres₁
    let φ₁ : A →+* R₁.integers :=
      { toFun := fun a => ⟨algebraMap L F a, (R₁.algebraMap_mem_iff a).mpr a.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
    have hresφ₁ : R₁.residue.comp φ₁ =
        (algebraMap (IsLocalRing.ResidueField A) Fb₁).comp (IsLocalRing.residue A) :=
      RingHom.ext fun a => R₁.residue_algebraMap a
    have heq' : (⟨aeval f q, hqmem₁⟩ : R₁.integers) = Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA := by
      apply Subtype.ext
      have hsub : R₁.integers.subtype.comp φ₁ = (algebraMap L F).comp A.subtype :=
        RingHom.ext fun _ => rfl
      calc aeval f q
          = aeval f (qA.map A.subtype) := by rw [hqAmap]
        _ = Polynomial.eval₂ (algebraMap L F) f (qA.map A.subtype) := Polynomial.aeval_def _ _
        _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f qA :=
            Polynomial.eval₂_map A.subtype (algebraMap L F) f
        _ = Polynomial.eval₂ (R₁.integers.subtype.comp φ₁) f qA := by rw [hsub]
        _ = ((Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA : R₁.integers) : F) :=
            (Polynomial.hom_eval₂ qA φ₁ R₁.integers.subtype ⟨f, hf₁⟩).symm
    rw [heq']
    calc R₁.residue (Polynomial.eval₂ φ₁ ⟨f, hf₁⟩ qA)
        = Polynomial.eval₂ (R₁.residue.comp φ₁) (R₁.residue ⟨f, hf₁⟩) qA :=
          Polynomial.hom_eval₂ qA φ₁ R₁.residue ⟨f, hf₁⟩
      _ = aeval (R₁.residue ⟨f, hf₁⟩) (qA.map (IsLocalRing.residue A)) := by
          rw [hresφ₁, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
      _ = 0 := by rw [hqz, map_zero]

  set p : L[X] := C c * r with hpdef
  have hep : e * aeval f q = aeval f p := by
    simp only [hqdef, hpdef, map_mul, aeval_C, hers]
    field_simp
  exact (aux_mem_integers_iff A R₁ f hf₁ htr₁ q hqf qA hqAmap hqbar_ne e p hep).trans
        (aux_mem_integers_iff A R₂ f hf₂ htr₂ q hqf qA hqAmap hqbar_ne e p hep).symm

end RegularProlongation

end AlgebraicCurve

end
