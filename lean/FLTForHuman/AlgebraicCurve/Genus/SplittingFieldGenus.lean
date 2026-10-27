/-
The genus formula for the function field of a Kummer splitting field.

Let `L` be an algebraically closed field of characteristic zero, `F` a function field
of one variable over `L` (a transcendental `x` with `L⟮x⟯ / F` finite), `q` a prime and
`f : F` an element that is not a `q`-th power in `F` and whose order at every place is
divisible by `q`.  Then the splitting field `F'` of `X ^ q - C f` over `F` satisfies
`genusFF L F' - 1 = q * (genusFF L F - 1)`: the Kummer cover of degree `q` is
unramified everywhere, so Hurwitz's formula
`2 g' - 2 = [F' : F] * (2 g - 2) + Σ_w (e_w - 1) * deg w` degenerates to
`2 g' - 2 = q * (2 g - 2)`.

The proof chooses a root `α` of `X ^ q - C f` in `F'`.  Kummer theory gives both
`F⟮α⟯ = ⊤` and `[F' : F] = q` (the exponent is prime, `f` is not a `q`-th power, and
`F` contains the `q`-th roots of unity because it is algebraically closed), and the
ramification index of every place of `F'` over a place `v` of `F` is `1` because
`q ∣ v.ord f` and the cover is tame in characteristic zero.  Hurwitz's degree formula
for the Kähler different then gives the identity for the two `genus` values, which are
the `genusFF` values once Riemann–Roch and constants-are-base hold for both function
fields.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean

spec-pin: Theorems/Thm_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.Hurwitz
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.OrderArithmetic
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false

noncomputable section

set_option linter.style.haveILetI false

open AlgebraicCurve Polynomial
open scoped IntermediateField

namespace AlgebraicCurve

namespace KummerGenusReduction

universe u v w

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

/-- Transcendentality is preserved by the inclusion into an extension: the pin's
`transcendental_algebraMap`, a restatement of `transcendental_algebraMap_iff`. -/
theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

/-- Finiteness of `L⟮x⟯ / F` transports to `L⟮x'⟯ / F'` for `x'` the image of `x`: the
pin's `finiteDimensional_adjoin_algebraMap`. -/
theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
    [FiniteDimensional F F'] :
    FiniteDimensional L⟮algebraMap F F' x⟯ F' := by
  haveI := hfin
  let φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  haveI : Module.Finite L⟮x⟯ F' := Module.Finite.trans F F'
  have hmap : L⟮x⟯.map φ = L⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮x⟯ ≃ₐ[L] L⟮algebraMap F F' x⟯ :=
    (L⟮x⟯.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  refine Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext y
  rfl

end Cover

end KummerGenusReduction

/-- **The genus of a Kummer splitting field.**  With `α ^ q = f` in the splitting field
`F'` of `X ^ q - C f`, `F⟮α⟯ = ⊤`, and `q ∣ v.ord f` at every place of `F`, the genus of
the function field of `F'` satisfies `genusFF L F' - 1 = q * (genusFF L F - 1)`.  The
cover is tame and unramified (its ramification indices are all `1`), so Hurwitz's
degree formula for the different reduces to `2 g' - 2 = [F' : F] (2 g - 2)`, and
Kummer theory gives `[F' : F] = q`. -/
theorem genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by
  classical
  obtain ⟨x, hx, hfin⟩ := hF
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap L F).injective
  haveI hCF : IsCurveOver L F := by
    haveI := hfin
    haveI : CharZero L⟮x⟯ := charZero_of_injective_algebraMap (algebraMap L L⟮x⟯).injective
    haveI : Algebra.IsSeparable L⟮x⟯ F := Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable L F x hx hfin inferInstance
  haveI hEF : Algebra.EssFiniteType L F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfin
  haveI hCan : HasCanonicalDivisor (K := L) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hDC : ∀ v : Place L F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  haveI : FiniteDimensional F F' := IsSplittingField.finiteDimensional F' (X ^ q - C f)
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  haveI : Algebra.IsSeparable F F' := inferInstance
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hq hf
  have hζ : (primitiveRoots q F).Nonempty := by
    haveI : NeZero (q : L) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
    exact ⟨algebraMap L F ζ, (mem_primitiveRoots hq.pos).mpr
      (hζ.map_of_injective (algebraMap L F).injective)⟩
  have hrank : Module.finrank F F' = q := finrank_of_isSplittingField_X_pow_sub_C hζ hirr F'
  set α : F' := rootOfSplitsXPowSubC (NeZero.pos q) f F' with hαdef
  have hα : α ^ q = algebraMap F F' f := rootOfSplitsXPowSubC_pow f F'
  have htop : F⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hζ hirr hα

  set x' : F' := algebraMap F F' x with hx'def
  have hx' : Transcendental L x' := KummerGenusReduction.transcendental_algebraMap hx
  have hfin' : FiniteDimensional L⟮x'⟯ F' :=
    KummerGenusReduction.finiteDimensional_adjoin_algebraMap x hfin
  haveI hCF' : IsCurveOver L F' := by
    haveI := hfin'
    haveI : CharZero L⟮x'⟯ := charZero_of_injective_algebraMap (algebraMap L L⟮x'⟯).injective
    haveI : Algebra.IsSeparable L⟮x'⟯ F' := Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable L F' x' hx' hfin' inferInstance
  haveI hEF' : Algebra.EssFiniteType L F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hx' hfin'
  haveI hCan' : HasCanonicalDivisor (K := L) (F := F') := hasCanonicalDivisor_of_isCurveOver
  haveI hDC' : ∀ w : Place L F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  have he : ∀ w : Place L F', w.ramificationIndex F = 1 := fun w =>
    Place.ramificationIndex_eq_one_of_forall_dvd_ord hf hα htop hdvd w
      (Place.isRational_of_isCurveOver w)
  have htame : ∀ w : Place L F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    rw [he w, Nat.cast_one]
    exact one_ne_zero
  have hreg := localUnitDerivativeRegular_of_isCurveOver (K := L) (F' := F')

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄L])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_of_isCurveOver (K := L) (F := F')
    (riemannRoch_and_constantsAreBase (K := L) (F := F')).2).1
  have hω₀' : KaehlerDifferential.map L L F F' ω₀ ≠ 0 :=
    map_ne_zero_of_tame hreg htame w₀ hω₀

  have hK := degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase (K := L) (F := F)).1
    (riemannRoch_and_constantsAreBase (K := L) (F := F)).2 hω₀
  have hK' := degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase (K := L) (F := F')).1
    (riemannRoch_and_constantsAreBase (K := L) (F := F')).2 hω₀'
  have hRH := two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame hω₀ hω₀' hK hK'
  have hsum : ∑ᶠ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := by
    have : ∀ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := fun w => by
      rw [he w]
      simp
    simp_rw [this, finsum_zero]
  rw [hsum, add_zero, hrank] at hRH

  rw [genus_eq_genusFF (riemannRoch_and_constantsAreBase (K := L) (F := F)).1
      (weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
        (riemannRoch_and_constantsAreBase (K := L) (F := F)).1
        (stichtenothGenusExists_of_isCurveOver (K := L) (F := F)
          (riemannRoch_and_constantsAreBase (K := L) (F := F)).2))
      (riemannRoch_and_constantsAreBase (K := L) (F := F)).2,
    genus_eq_genusFF (riemannRoch_and_constantsAreBase (K := L) (F := F')).1
      (weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
        (riemannRoch_and_constantsAreBase (K := L) (F := F')).1
        (stichtenothGenusExists_of_isCurveOver (K := L) (F := F')
          (riemannRoch_and_constantsAreBase (K := L) (F := F')).2))
      (riemannRoch_and_constantsAreBase (K := L) (F := F')).2] at hRH
  have h2 : (2 : ℤ) * ((genusFF L F' : ℤ) - 1) = 2 * (q * ((genusFF L F : ℤ) - 1)) := by
    linear_combination hRH
  exact mul_left_cancel₀ two_ne_zero h2

end AlgebraicCurve

end
