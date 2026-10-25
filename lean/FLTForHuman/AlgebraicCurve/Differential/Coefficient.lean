/-
The coefficient of a differential against a chosen local generator at a place.

`Ω[F⁄K]` is one-dimensional over `F` at a place `v`, so a uniformiser `t` turns every
differential into a unique coefficient `diffCoeff t ω` with `diffCoeff t ω • Dt = ω` (`0`
when no such coefficient exists). The three faces of that freeness of rank one are here:
existence (`Dt` spans `Ω`, so a coordinate exists: `diffCoeff_smul_D_of_ord_eq_one`),
uniqueness (`Dt ≠ 0`, so `diffCoeff t` is the two-sided inverse of `ω ↦ ω • Dt`:
`diffCoeff_smul_D_eq_of_ord_eq_one`), and integrality — for a separating uniformiser the
coefficient of an integral element is integral (`ord_diffCoeff_D_nonneg_of_isSeparable`),
i.e. the local different at `v` is effective; over a perfect `K` the separability
hypothesis is free (`ord_diffCoeff_D_nonneg_of_perfectField`), because `ord t = 1` already
separates (`Place.isSeparable_adjoin_of_ord_eq_one`).

The coefficient is the general one, against an arbitrary uniformiser `t`; the canonical
`Place.differentialCoeff` of `Defs/CanonicalDivisor.lean` is its `dCoord` case, and
`diffCoeff_uniformizer_eq_differentialCoeff` relates the two — the two spellings are the
same term, so the tree carries one coefficient API. What the existence half rests on is
`exists_mem_D_eq_smul_D_of_isCurveOver`, i.e. `dπ` spans `Ω` at a place, which
`Canonical/ValSubringKaehler.lean` supplies through
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`.

After FLT's `Definitions/Def_AlgebraicCurve_Differentials.lean` (lines 27–37, the
coefficient vocabulary) and the five `S_` files below, pinned at `aa2d8b3`:

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean>.

Assumes `Defs/CanonicalDivisor.lean` (`uniformizer`, `dCoord`, `differentialCoeff`),
`Defs/KaehlerTranscendental.lean` (`span_D_eq_top_of_transcendental`,
`D_ne_zero_of_transcendental`), `Place/SeparableUniformiser.lean` (separability of a
uniformiser) and `Canonical/ValSubringKaehler.lean` with `Canonical/DCoordGenerates.lean`
(generation at a place).

spec-pin: Definitions/Def_AlgebraicCurve_Differentials.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean   -- comparable copy
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
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F π := by
  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField (K := K) (F := F)
  haveI : v.DCoordGenerates := Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v
  obtain ⟨c, hc, hDx⟩ := v.exists_mem_D_eq_smul_dCoord hspan hx
  obtain ⟨w, hw0, hw, hDπ⟩ := v.exists_unit_D_eq_smul_dCoord hspan hπ
  refine ⟨c / w, ?_, ?_⟩
  · rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_div]; exact zero_mem _
    · exact v.mem_vs_of_ord_nonneg (by
        rw [div_eq_mul_inv, v.ord_mul hc0 (inv_ne_zero hw0), v.ord_inv, hw, neg_zero, add_zero]
        exact v.ord_nonneg_of_mem_vs hc)
  · rw [hDx, hDπ, smul_smul, div_mul_cancel₀ _ hw0]

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
The two are not two definitions related by a factor: `v.dCoord` is
`D K F v.uniformizer` by definition, so the two spellings are the same term and the
statement holds by `rfl`. Port glue, not a pin statement. -/
theorem diffCoeff_uniformizer_eq_differentialCoeff (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] (ω : Ω[F⁄K]) : diffCoeff v.uniformizer ω = v.differentialCoeff ω :=
  rfl

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
`exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver`.

The second declaration is the same statement with the separability hypothesis
discharged: `ord t = 1` already separates (`Place.isSeparable_adjoin_of_ord_eq_one`),
so the instance is derived from the pin's own hypotheses. It is the form the
`ordDiff` consumers state, so it belongs here, next to the theorem it instantiates. -/

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
      (AlgebraicCurve.valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField) v
  obtain ⟨c, hc, hDf⟩ :=
    AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver v (π := v.uniformizer)
      v.ord_uniformizer (v.mem_vs_of_ord_nonneg hf)
  obtain ⟨u, hu0, hDtu⟩ :=
    AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
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

/-- **The same integrality without the separability hypothesis.** Over a perfect `K`
a uniformiser is separating (`Place.isSeparable_adjoin_of_ord_eq_one`), so the
instance of `ord_diffCoeff_D_nonneg_of_isSeparable` follows from the pin's own
hypotheses. Verbatim from
`Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean`. -/
theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable x v ht hf
