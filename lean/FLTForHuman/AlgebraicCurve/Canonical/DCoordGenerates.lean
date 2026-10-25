/-
Every place of a curve over a perfect field has a generating `dCoord`.

`Place.DCoordGenerates` is the per-place hypothesis the canonical-divisor and different
engines assume: `D v.uniformizer` spans `Ω[F⁄K]`. This module discharges it from
`IsCurveOver K F` for a perfect `K`, one step per model predicate of
`Canonical/ValSubringKaehler.lean`:

* `dCoordGenerates_of_valSubringKaehlerSpanTop`: the span hypothesis itself is the
  statement, at the place;
* the perfect-field supply of separability: a finite residue field over a perfect `K` is
  separable, which is what turns `ValSubringKaehlerFinite` into the span;
* `dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField` and
  `…_of_valSubringDedekindModel_of_perfectField`: the same, from the two later model
  predicates;
* `hasSeparatingTranscendental_of_isCurveOver_of_perfectField`: `IsCurveOver` supplies the
  separating transcendental of `Canonical/AffineChart.lean`;
* and the headline `dCoordGenerates_of_isCurveOver`, verbatim from
  `Theorems/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean`.

After FLT's `P2M/Sol/S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean` and the middle
of `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`, pinned at `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean>.

Assumes `Canonical/AffineChart.lean` and `Canonical/ValSubringKaehler.lean`.

spec-pin: Theorems/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean   -- comparable copy
spec-pin: P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Canonical.AffineChart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain Polynomial IsLocalRing KaehlerDifferential IntermediateField
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.Place

namespace AlgebraicCurve

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :
    v.DCoordGenerates := by
  constructor
  rw [eq_top_iff,
    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)
      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),
    Submodule.span_le]
  rintro _ ⟨f, rfl⟩

  have hDf : KaehlerDifferential.D K v.toValuationSubring f
      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top
  rw [← hspan v] at hDf
  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘
        KaehlerDifferential.D K v.toValuationSubring) f
      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)
        (Submodule.span v.toValuationSubring _) :=
    Submodule.mem_map_of_mem hDf
  rw [Submodule.map_span, Set.image_singleton,
    v.kaehlerMap_subring_D_uniformizer] at hmap

  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap

end AbstractEngine

section PerPlaceSupply

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

open scoped AlgebraicCurve.Place in
private theorem isSeparable_residueField_of_perfectField_of_finiteResidue
    [PerfectField K] (v : Place K F) [v.FiniteResidue] :
    Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) := by
  haveI : Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Place.FiniteResidue.finite
  haveI : Algebra.IsAlgebraic K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.IsAlgebraic.of_finite K _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Place

theorem isSeparable_residueField_forall_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue] :
    ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
  fun v => v.isSeparable_residueField_of_perfectField_of_finiteResidue

end PerPlaceSupply

section IsSeparableEngines

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable
    [∀ v : Place K F, Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringKaehlerSpanTop K F :=
  valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable hfin)

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable
    [∀ v : Place K F, Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable hfin) v

end IsSeparableEngines

section PerfectFieldEngines

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  haveI : ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
    isSeparable_residueField_forall_of_perfectField
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable hfin v

end PerfectFieldEngines

end AlgebraicCurve

namespace AlgebraicCurve

section S12ChainWires

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hmodel : ValSubringFiniteTypeModel K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField
    (valSubringKaehlerFinite_of_finiteTypeModel hmodel) v

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_valSubringDedekindModel_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hmodel : ValSubringDedekindModel K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField
    (valSubringFiniteTypeModel_of_dedekindModel hmodel) v

open scoped AlgebraicCurve.Place in
theorem Place.dCoordGenerates_of_hasSeparatingTranscendental_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hsep : HasSeparatingTranscendental K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringDedekindModel_of_perfectField
    (valSubringDedekindModel_of_hasSeparatingTranscendental hsep) v

open _root_.IntermediateField in
theorem hasSeparatingTranscendental_of_isCurveOver_of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact ⟨t, htr, hfd, hsep,
    IntermediateField.finiteDimensional_adjoin_inv t,
    IntermediateField.isSeparable_adjoin_inv t⟩

/-- **Every place has a generating `dCoord`.** The pin's
`S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.solution`: the separating
transcendental supplied by `IsCurveOver.exists_separating_transcendental` closes
the model-predicate chain above. Verbatim from
`Theorems/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean`. The port
already carried the whole chain as the `hasCanonicalDivisor` effort's machinery,
so only this headline is new. -/
theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates :=
  fun v => Place.dCoordGenerates_of_hasSeparatingTranscendental_of_perfectField
    (hasSeparatingTranscendental_of_isCurveOver_of_perfectField (K := K) (F := F)) v

end S12ChainWires

end AlgebraicCurve

end
