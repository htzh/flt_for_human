/-
Ω is one-dimensional over `F` at a place: `dπ` generates it, every differential has a
coordinate in that generator, and for a separating uniformiser the coordinate of an
integral element is integral. After FLT's
`P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean` (1,422 ln) and
the coefficient layer
`P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean` (28 ln),
`P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean` (26 ln) and
`P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean` (576 ln),
pinned at `aa2d8b3`:

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean>.

The first file inlines its whole `s12` prelude (61 private helpers, ≈670 lines);
every one already has a public home in the port's
`AlgebraicCurve/Canonical/HasCanonicalDivisor.lean` (`ValSubringKaehlerSpanTop`,
`valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12`,
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`,
`Place.exists_mem_D_eq_smul_dCoord_s12`,
`Place.exists_unit_D_eq_smul_dCoord_s12`,
`isLocalization_centerIdeal_of_isDedekindDomain`, …). This module imports that
home rather than re-proving it and lands the headline at its `Theorems/` wrapper
statement.

The last three files are the pin's coefficient layer, absorbed here because they are
the same subject: `Place.diffCoeff t ω` is the `g` with `g • dt = ω` (and `0` when
there is none), so the three theorems are the three faces of `Ω` being free of rank
one where `Dt ≠ 0` — existence (`Dt` spans `Ω`), uniqueness (`Dt ≠ 0`), and
integrality: `d/dt` maps the valuation ring into itself, i.e. the local different is
effective. The pin proves the last one by hand in a `RatFunc` tower (its private
`engine`, ≈250 lines, over the `Dict` block that is public here as
`Defs/PlaceDictionary.lean`); in the port that engine is
`exists_mem_D_eq_smul_D_of_isCurveOver` plus the `IsCurveOver` supply
(`finiteDimensional_adjoin_of_transcendental`, `isCurveOver_of_transcendental`), and
the `RatFunc` transport disappears — the headline's own hypotheses already give `t`
as a separating generator. Only the coefficient vocabulary (lines 27–37) is
transcribed from `Definitions/Def_AlgebraicCurve_Differentials.lean`; that file's
other halves are homed under their own pin files (`regularDifferentials`,
`IsRegularAt`, `pullbackAlong`).

spec-pin: Definitions/Def_AlgebraicCurve_Differentials.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Place.SeparableUniformiser
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import Mathlib.RingTheory.Kaehler.Basic

set_option autoImplicit false

-- The separating-uniformiser instance is introduced locally, as in the pin's proofs.
set_option linter.style.haveILetI false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

/-- At a place `v` with `v.ord π = 1`, the Kähler differential of an integral `x`
is an integral multiple of `D π` (the pin
`exists_mem_D_eq_smul_D_of_isCurveOver`; statement from its `Theorems/` wrapper). -/
theorem exists_mem_D_eq_smul_D_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) {π : F} (hπ : v.ord π = 1) {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F π :=
  exists_mem_D_eq_smul_D_of_isCurveOver_s12 v hπ hx

namespace Place

/-! ### The coefficient against a uniformiser

The pin states these in a section, so the binder block is the section's; the same
here, to keep the checked text identical. -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in
/-- The coordinate of `ω` against `d t`: the `g` with `g • d t = ω`, and `0` when
there is none.  The pin's `Place.diffCoeff`
(`Definitions/Def_AlgebraicCurve_Differentials.lean:27`), body verbatim. -/
def diffCoeff (t : F) (ω : Ω[F⁄K]) : F :=
  if h : ∃ g : F, ω = g • D K F t then h.choose else 0

theorem diffCoeff_smul_D {t : F} {ω : Ω[F⁄K]} (h : ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω • D K F t = ω := by
  rw [diffCoeff, dite_eq_left h]
  exact h.choose_spec.symm

theorem diffCoeff_of_not_exists {t : F} {ω : Ω[F⁄K]} (h : ¬ ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω = 0 := by
  rw [diffCoeff, dite_eq_right h]

/-- The canonical coefficient `v.differentialCoeff` (the `dCoord` case) is this one
at `t = v.uniformizer`; the bridge that keeps the port on a single coefficient.
Port glue, not a pin statement. -/
theorem diffCoeff_uniformizer_eq_differentialCoeff (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] (ω : Ω[F⁄K]) : diffCoeff v.uniformizer ω = v.differentialCoeff ω := by
  obtain ⟨g, hg⟩ := v.exists_eq_smul_dCoord ω
  exact (v.differentialCoeff_unique
    (diffCoeff_smul_D (t := v.uniformizer) (ω := ω) ⟨g, hg⟩).symm).symm

end Place

end AlgebraicCurve

/-! ### The coefficient exists and is unique

A uniformiser `t` is separating (`Place.isSeparable_adjoin_of_ord_eq_one`, from
`ord t = 1`), so `d t` is transcendental and spans `Ω`; that is existence. The same
`d t ≠ 0` makes the coefficient unique. -/

theorem AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω := by
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero (by rw [ht]; exact one_ne_zero))
  have hω : ω ∈ Submodule.span F {KaehlerDifferential.D K F t} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, hg.symm⟩

theorem AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g := by
  have hDt : KaehlerDifferential.D K F t ≠ 0 := by
    haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
    exact KaehlerDifferential.D_ne_zero_of_transcendental K t
      (v.transcendental_of_ord_ne_zero (by rw [ht]; exact one_ne_zero))
  have hmul : AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t)
      • KaehlerDifferential.D K F t = g • KaehlerDifferential.D K F t :=
    AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, rfl⟩
  have hzero : (AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) - g)
      • KaehlerDifferential.D K F t = 0 := by
    rw [sub_smul, hmul, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hDt

/-! ### The coefficient of an integral element is integral

`d/dt` maps the valuation ring into itself: the local different at a separating
unifomiser is effective. The pin proves this by hand in a `RatFunc` tower (its
private `engine`); here it is `exists_mem_D_eq_smul_D_of_isCurveOver` plus the
`IsCurveOver` supply, with the two uniformisers compared by
`exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12`. -/

theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F] {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) := by
  have htr : Transcendental K t :=
    v.transcendental_of_ord_ne_zero (by rw [ht]; exact one_ne_zero)
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x htr
  have hDt : KaehlerDifferential.D K F t ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K t htr
  haveI : AlgebraicCurve.IsCurveOver K F :=
    AlgebraicCurve.isCurveOver_of_transcendental htr hfd inferInstance
  haveI : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  haveI : v.DCoordGenerates :=
    AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop
      (AlgebraicCurve.valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12) v
  obtain ⟨c, hc, hDf⟩ :=
    AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver v (π := v.uniformizer)
      v.ord_uniformizer (v.mem_vs_of_ord_nonneg hf)
  obtain ⟨u, hu0, hDtu⟩ :=
    AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12
      v v.uniformizer t v.ord_uniformizer ht
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hDtu
    exact hDt hDtu
  have hDf' : KaehlerDifferential.D K F f = (c / u) • KaehlerDifferential.D K F t := by
    rw [hDf, hDtu, smul_smul, div_mul_cancel₀ c hu]
  have hcoef : AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f) = c / u := by
    rw [hDf']
    exact AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht (c / u)
  rw [hcoef]
  rcases eq_or_ne c 0 with rfl | hc0
  · simp [zero_div, v.ord_zero]
  · rw [div_eq_mul_inv, v.ord_mul hc0 (inv_ne_zero hu), v.ord_inv, hu0, neg_zero, add_zero]
    exact v.ord_nonneg_of_mem hc
