/-
`IsCurveOver` from a single transcendental generator, after FLT's
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean` (57 ln),
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean`
(19 ln) and
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean`
(20 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean>).

The three public headlines are their wrappers verbatim.  The first assembles the
three curve axioms from the prerequisites — principal divisors
(`PrincipalDivisors/IsSeparable.lean`), the Kähler rank
(`Defs/KaehlerTranscendental.lean`) and the finite residue-field extension
(`Place/FiniteResidue.lean`) — after transporting the `K(x)`-tower to the
`RatFunc K`-tower.  The second is the perfect-field corollary: the ported
`exists_separating_transcendental_of_perfectField` supplies a separating `t`.
The third is the pin's `_of_isSeparable` alias of the first: the pin states it
with explicit `(x : F)`, `(hx : …)` binders over the same hypothesis list, and its
`S_` proof is the one-line application of `isCurveOver_of_transcendental`.  Both
statements are kept — the wire diffs statement text, and the pin publishes both
names.  (`IsCurveOver/SeparatingTranscendental.lean` cannot host it: it is a
`Defs`-only leaf below the principal-divisor machinery this file builds on.)

Mathlib search negatives (recorded): `IsCurveOver` is FLT's class, so there is no
mathlib `instance`; the only reusable inputs are `RatFunc.algEquivOfTranscendental`
and the transport lemmas (`IsScalarTower.of_algebraMap_eq`,
`Module.Finite.of_equiv_equiv`, `Algebra.IsSeparable.of_equiv_equiv`).

  spec-pin: Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean   -- comparable copy
  spec-pin: Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean   -- comparable copy
  spec-pin: Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean   -- comparable copy
  spec-pin: Theorems/Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental.lean   -- comparable copy

spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean
spec-pin: Theorems/Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.IsSeparable
import FLTForHuman.AlgebraicCurve.Place.FiniteResidue
import FLTForHuman.AlgebraicCurve.IsCurveOver.PerfectField
import FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental
import FLTForHuman.AlgebraicCurve.P1.UnitFinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve IntermediateField

namespace AlgebraicCurve

/-- **`IsCurveOver` from a transcendental generator.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental.lean`. -/
theorem isCurveOver_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by
  have hprin : HasPrincipalDivisors K F :=
    AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable htr hfd hsep
  have hkae : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
    AlgebraicCurve.kaehlerRankOne_of_transcendental htr hsep
  have hfin : ∀ v : Place K F, Module.Finite K v.ResidueField := by
    haveI := hfd
    haveI := hsep
    set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr with he
    letI : Algebra (RatFunc K) F :=
      ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
    have hsq : RingHom.comp (algebraMap (RatFunc K) F)
          (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
        = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
      refine RingHom.ext fun a => ?_
      show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
      rw [e.apply_symm_apply]
    haveI : IsScalarTower K (RatFunc K) F :=
      IsScalarTower.of_algebraMap_eq fun a => by
        show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
        rw [e.commutes, ← IsScalarTower.algebraMap_apply]
    haveI : FiniteDimensional (RatFunc K) F :=
      Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
    haveI : Algebra.IsSeparable (RatFunc K) F :=
      Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
    intro v
    haveI h1 : Module.Finite (v.restrict (RatFunc K)).ResidueField v.ResidueField :=
      Place.finite_residueField_of_finiteDimensional (F := RatFunc K) v
    haveI h2 : Module.Finite K (v.restrict (RatFunc K)).ResidueField :=
      (AlgebraicCurve.instIsCurveOverRatFunc K).finiteResidue _
    exact Module.Finite.trans (v.restrict (RatFunc K)).ResidueField v.ResidueField
  exact { toHasPrincipalDivisors := hprin, finiteResidue := hfin, kaehler_free_rank_one := hkae }

/-- **`IsCurveOver` from a separating transcendental generator.**  Statement from
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable.lean`,
which spells the binders explicitly (`(x : F)`, `(hx : …)`); the pin's `S_` file
proves it by the one-line application below. -/
theorem isCurveOver_of_transcendental_of_isSeparable (K F : Type*) [Field K] [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F :=
  isCurveOver_of_transcendental hx hfin hsep

/-- **`IsCurveOver` from a transcendental generator over a perfect field.**
Verbatim from
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean`. -/
theorem isCurveOver_of_transcendental_of_perfectField {K F : Type*} [Field K] [Field F]
    [Algebra K F] [PerfectField K] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F := by
  obtain ⟨t, ht, htfd, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr hfd
  exact isCurveOver_of_transcendental ht htfd htsep

/-- **`IsCurveOver` from a transcendental generator over an algebraically closed
field.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental.lean`,
whose `S_` file proves it by the one-line application below from the
perfect-field corollary (`IsAlgClosed` is `PerfectField`, mathlib's
`IsAlgClosed.perfectField`). -/
theorem isCurveOver_of_isAlgClosed_of_transcendental {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    IsCurveOver K F :=
  isCurveOver_of_transcendental_of_perfectField hx inferInstance

/-- **The pointwise dictionary, `IsCurveOver` form.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional.lean`;
the forward direction is the separating-generator theorem
(`IsCurveOver/SeparatingTranscendental.lean`), the backward one
`isCurveOver_of_transcendental` above. -/
theorem isCurveOver_iff_exists_transcendental_finiteDimensional {K : Type*} {F : Type*}
    [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] :
    IsCurveOver K F ↔ ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧
      Algebra.IsSeparable K⟮t⟯ F := by
  constructor
  · intro h
    exact IsCurveOver.exists_separating_transcendental
  · rintro ⟨t, htr, hfd, hsep⟩
    exact isCurveOver_of_transcendental htr hfd hsep


end AlgebraicCurve

end
