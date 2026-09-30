/-
The curve-level prerequisite `IsCurveOver.exists_separating_transcendental`, after
FLT's
`P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean` (229 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean>).

The public target `IsCurveOver.exists_separating_transcendental` is spelled from its
`Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean:13`
wrapper; the support lemmas (`kaehlerAdjoinBasis`,
`kaehlerOfSeparatingTranscendentalBasis`, `finrank_kaehler_eq_card_of_separating`,
its `'` variant, and the `trdeg` chain) are the pin's public declarations from the
same `S_` file, in its own declaration order.

This module is the refactor round's home for the block that H2 re-provisioned
`private` inside `RiemannRoch/Assembly.lean:73–170` (see
`logs/riemann-roch-friction.md` § Set H2).  The only adaptation forced by the port's
mathlib is that `Basis` lives in `Module`; `open Module` restores the pin's spelling
so the statements diff verbatim.
-/
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open KaehlerDifferential Algebra IntermediateField Module
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve

universe u₁ u₂

variable {K : Type u₁} {F : Type u₂} [Field K] [Field F] [Algebra K F]

variable {ι : Type*} {v : ι → F}

def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :
    Basis ι (IntermediateField.adjoin K (Set.range v))
      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] := by

  let Kv : IntermediateField K F := IntermediateField.adjoin K (Set.range v)

  letI : Algebra (MvPolynomial ι K) Kv :=
    ((algebraMap (Algebra.adjoin K (Set.range v)) Kv).comp
      (hv.aevalEquiv : MvPolynomial ι K →+* Algebra.adjoin K (Set.range v))).toAlgebra

  haveI : IsScalarTower K (MvPolynomial ι K) Kv :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K Kv a
        = algebraMap (Algebra.adjoin K (Set.range v)) Kv (hv.aevalEquiv (algebraMap K _ a))
      rw [AlgEquiv.commutes]; rfl

  haveI : IsFractionRing (MvPolynomial ι K) Kv :=
    IsFractionRing.of_ringEquiv_left hv.aevalEquiv.toRingEquiv (fun _ => rfl)

  haveI : Algebra.FormallyEtale (MvPolynomial ι K) Kv :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι K))

  exact ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange Kv).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) Kv)

def kaehlerOfSeparatingTranscendentalBasis (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] : Basis ι F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range v)) F :=
    Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerAdjoinBasis hv).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range v)) F)

theorem finrank_kaehler_eq_card_of_separating {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F] :
    Module.finrank F Ω[F⁄K] = s.card := by
  rw [Module.finrank_eq_card_basis (kaehlerOfSeparatingTranscendentalBasis hs),
    Fintype.card_coe]

theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}
    (hs : AlgebraicIndependent K ((↑) : s → F))
    [hsep : Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F] :
    Module.finrank F Ω[F⁄K] = s.card := by

  have heq : IntermediateField.adjoin K (s : Set F)
      = IntermediateField.adjoin K (Set.range ((↑) : s → F)) := by
    rw [Subtype.range_coe]
  let e : (IntermediateField.adjoin K (s : Set F)) ≃ₐ[K]
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) :=
    IntermediateField.equivOfEq heq

  haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun x => rfl)
  exact finrank_kaehler_eq_card_of_separating hs

namespace IsCurveOver

theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :
    1 ≤ Algebra.trdeg K F := by
  have hna : ¬ Algebra.IsAlgebraic K F := by
    intro halg
    haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
    exact false_of_nontrivial_of_subsingleton Ω[F⁄K]
  haveI : Algebra.Transcendental K F := Algebra.transcendental_iff_not_isAlgebraic.mpr hna
  exact Cardinal.one_le_iff_pos.mpr (trdeg_pos K F)

theorem trdeg_eq_one [PerfectField K] [IsCurveOver K F]
    (htrdeg : Algebra.trdeg K F ≤ 1) :
    Algebra.trdeg K F = 1 :=
  le_antisymm htrdeg one_le_trdeg

theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F ≤ 1 := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  haveI := hsep
  have hcard : s.card = 1 := by
    rw [← finrank_kaehler_eq_card_of_separating' hs.1, IsCurveOver.finrank_kaehler]

  have htr := hs.cardinalMk_eq_trdeg
  rw [Cardinal.mk_coe_finset, hcard, Nat.cast_one] at htr
  exact htr.symm.le

theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] : Algebra.trdeg K F = 1 :=
  IsCurveOver.trdeg_eq_one trdeg_le_one

theorem exists_separating_transcendental {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by

  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F

  have hcard : s.card = 1 := by
    have htr := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, IsCurveOver.trdeg_eq_one_of_perfectField] at htr
    exact_mod_cast htr

  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard

  have htr : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun x => (Finset.mem_singleton.mp x.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff (ι := (↑({t} : Finset F)))).mp h1

  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  haveI hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)

  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

end IsCurveOver

end AlgebraicCurve

end
