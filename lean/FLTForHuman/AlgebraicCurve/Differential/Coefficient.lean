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

The order of the differential of a function is the third subject: `ordDiff (D f) = ord f - 1`
at a place where `f` has nonzero order, and `D f` regular wherever `f` has no pole — the
sharp form of the different's effectivity in characteristic zero. The other half of the same
definition module is here too: `IsRegularDiff` (nonnegative
order at every place), the submodule `regularDiffs` spanned by those, and the two trivial
membership lemmas. That the span adds nothing — `mem_regularDiffs_iff` — is the pin's next
node and is proved where its prelude lives; the definition stays with the vocabulary it
belongs to.

The coefficient is the general one, against an arbitrary uniformiser `t`; the canonical
`Place.differentialCoeff` of `Defs/CanonicalDivisor.lean` is its `dCoord` case, and
`diffCoeff_uniformizer_eq_differentialCoeff` relates the two — the two spellings are the
same term, so the tree carries one coefficient API. What the existence half rests on is
`exists_mem_D_eq_smul_D_of_isCurveOver`, i.e. `dπ` spans `Ω` at a place, which
`Canonical/ValSubringKaehler.lean` supplies through
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`.

The same three faces are stated a second time with weaker hypotheses, at any element of
nonzero order over a field of characteristic zero (no perfectness, no `ord t = 1`):
`exists_eq_smul_D_of_ord_ne_zero`, `diffCoeff_smul_D_of_ord_ne_zero`,
`diffCoeff_smul_D_eq`. The two families are incomparable (a perfect field need not have
characteristic zero), and the second is cheap: in characteristic zero separability is
free, so none of the `p`-th-power machinery of the uniformiser case is involved. That
section also carries `ordDiff_zero`, `ordDiff_D_uniformizer` and `ordDiff_smul` for both a
characteristic-zero and a perfect base field, with `ordDiff_smul_D_uniformizer` as the
common body of the first two. The last member of the family, the integrality headline
`ord_diffCoeff_D_nonneg` of characteristic zero, is the end of the file: the pin builds a
`RatFunc` tower for it, and `PerfectField.ofCharZero` makes it the perfect-field node.

After FLT's `Definitions/Def_AlgebraicCurve_Differentials.lean` (lines 27–37, the
coefficient vocabulary) and the five `S_` files below, pinned at `aa2d8b3`:

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField.lean>.

For the nonzero-order family, the six files below. Every one of them copies the same
eight-declaration prelude; the port writes that prelude once, here:

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_eq_smul_D_of_ord_ne_zero.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul_of_perfectField.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean>.

and the two files of the `D f` cluster (`ordDiff_D_eq_ord_sub_one`,
`ordDiff_eq_ord_diffCoeff`, which are one text, plus the `ordDiff_D_nonneg` node and three
supporting lemmas the pair shares):

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean>.

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
spec-pin: Theorems/Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_eq_smul_D_of_ord_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_eq_smul_D_of_ord_ne_zero.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul_of_perfectField.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_D_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_D_nonneg.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
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

/-! ### The order of a differential

The pin's `Place.ordDiff` is the order of the coefficient of `ω` against a
uniformiser. The port keeps one uniformiser (`Place.uniformizer`, the single home of the
`Classical.choose` in `Defs/CanonicalDivisor.lean`), so the pin's
`uniformizer_alt` is that element and `ordDiff` reads the coefficient at it: the two
pin declarations are the port's spellings of `uniformizer` and `diffCoeff`, not new
objects. Because `Place.differentialCoeff` is `diffCoeff v.uniformizer` definitionally
(`diffCoeff_uniformizer_eq_differentialCoeff`), `v.ordDiff ω` is `v.ordDifferential ω` —
the bridge the pin proves in
`S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean:185`
(`ordDiff_eq_ordDifferential`) is `rfl` here. -/

variable (v : Place K F)

/-- The pin's `Place.uniformizer_alt` (`Definitions/Def_AlgebraicCurve_Differentials.lean:18`):
a uniformiser, which the port already has once. -/
def uniformizer_alt : F := v.uniformizer

/-- Pin `Place.ord_uniformizer_alt`
(`Definitions/Def_AlgebraicCurve_Differentials.lean:21`). -/
theorem ord_uniformizer_alt (h : ∃ t : F, v.ord t = 1) : v.ord v.uniformizer_alt = 1 := by
  obtain ⟨_, _⟩ := h
  exact v.ord_uniformizer

/-- Pin `Place.ordDiff` (`Definitions/Def_AlgebraicCurve_Differentials.lean:39`): the order
of a differential at `v`, read through the coefficient against the uniformiser. -/
def ordDiff (ω : Ω[F⁄K]) : ℤ := v.ord (diffCoeff v.uniformizer_alt ω)

/-- Pin `Place.ordDiff_def` (`Definitions/Def_AlgebraicCurve_Differentials.lean:42`). -/
theorem ordDiff_def (ω : Ω[F⁄K]) : v.ordDiff ω = v.ord (diffCoeff v.uniformizer_alt ω) := rfl

end Place

/-! ### The regular differentials

The pin's second half of the same definition module: a differential is *regular* when its
order is nonnegative at every place, and `regularDiffs` is the `K`-span of those. That the
spanning set is already a `K`-submodule — i.e. that `ω ∈ regularDiffs` *is* the pointwise
condition — is the pin's next node, proved where its prelude lives.

The pin has a second spelling of regularity elsewhere: locally a multiple of `dCoord` by an
element of the valuation ring (`regularDifferentials`, from
`Definitions/Def_AlgebraicCurve_RegularDifferentials.lean`). It is a separate development;
this section is the pointwise one. -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
/-- Pin `IsRegularDiff` (`Definitions/Def_AlgebraicCurve_Differentials.lean:48`). -/
def IsRegularDiff (ω : Ω[F⁄K]) : Prop :=
  ∀ v : Place K F, 0 ≤ v.ordDiff ω

/-- Pin `isRegularDiff_iff` (`Definitions/Def_AlgebraicCurve_Differentials.lean:51`). -/
theorem isRegularDiff_iff (ω : Ω[F⁄K]) :
    IsRegularDiff K F ω ↔ ∀ v : Place K F, 0 ≤ v.ordDiff ω := Iff.rfl

variable (K F) in
/-- Pin `regularDiffs` (`Definitions/Def_AlgebraicCurve_Differentials.lean:56`): the span of
the regular differentials. -/
def regularDiffs : Submodule K Ω[F⁄K] :=
  Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω}

/-- Pin `mem_regularDiffs_of_isRegularDiff`
(`Definitions/Def_AlgebraicCurve_Differentials.lean:59`). -/
theorem mem_regularDiffs_of_isRegularDiff {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    ω ∈ regularDiffs K F :=
  Submodule.subset_span h

/-- Pin `regularDiffs_eq_span` (`Definitions/Def_AlgebraicCurve_Differentials.lean:63`). -/
theorem regularDiffs_eq_span :
    regularDiffs K F = Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω} := rfl

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

/-! ### Nonzero order at a place, in characteristic zero

The pin states the coefficient facts twice, and the two hypothesis sets are
incomparable, so both are kept: at a uniformiser of a *perfect* field (`ord t = 1`,
above — a perfect field may have characteristic `p`) and at any element of *nonzero*
order over a field of characteristic zero (below). In characteristic zero separability
is free — `isSeparable_adjoin_of_ord_ne_zero` is "algebraic, then `infer_instance`" — so
this half of the family carries none of the `p`-th-power machinery and every proof below
is a few lines on the vocabulary the section above introduced.

Two naming notes. The pin's `S_` copy of the `g`-form is called
`diffCoeff_smul_of_ord_ne_zero`; the node name `diffCoeff_smul_D_eq` is the name the
pin's `Theorems/` wrapper gives that statement, and it is the one the port keeps.
`ordDiff_smul_D_uniformizer` is the pin's prelude, repeated in every one of the six files
(private in the perfect-field one, public in the rest): the computation of `v.ordDiff` on
the generator `D t`, of which `ordDiff_zero` and `ordDiff_D_uniformizer` are the `g = 0`
and `g = 1` cases. -/

-- The pin states its private prelude in a section, so the binder block is the section's;
-- the same here, and for the `ordDiff` generator lemmas below, to keep the checked text
-- identical. The check is textual, so it also keeps the pin's own spelling `D` (the
-- file's `open KaehlerDifferential` makes it the same term as `KaehlerDifferential.D`,
-- and the two spellings do *not* compare equal).
section SeparableAdjoin

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
/-- The pin's private `isSeparable_adjoin`, promoted: in characteristic zero nonzero
order already separates, with no perfectness and no `p`-th-power argument. -/
theorem AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x (v.transcendental_of_ord_ne_zero ht)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  infer_instance

end SeparableAdjoin

theorem AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    KaehlerDifferential.D K F t ≠ 0 :=
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero x v ht
  KaehlerDifferential.D_ne_zero_of_transcendental K t (v.transcendental_of_ord_ne_zero ht)

theorem AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • KaehlerDifferential.D K F t := by
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero ht)
  have hω : ω ∈ Submodule.span F {KaehlerDifferential.D K F t} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩

theorem AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω :=
  AlgebraicCurve.Place.diffCoeff_smul_D
    (AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x v ht ω)

theorem AlgebraicCurve.Place.diffCoeff_smul_D_eq {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g :=
  smul_left_injective F (AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero x v ht)
    (AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, rfl⟩)

section OrdDiffGenerator

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem AlgebraicCurve.Place.ordDiff_smul_D_uniformizer (v : AlgebraicCurve.Place K F) (g : F) :
    v.ordDiff (g • D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  rw [AlgebraicCurve.Place.ordDiff_def,
    AlgebraicCurve.Place.diffCoeff_smul_D_eq x v (by rw [h1]; exact one_ne_zero)]

include x in
theorem AlgebraicCurve.Place.ordDiff_D_uniformizer (v : AlgebraicCurve.Place K F) :
    v.ordDiff (D K F v.uniformizer_alt) = 0 := by
  simpa using AlgebraicCurve.Place.ordDiff_smul_D_uniformizer x v 1

end OrdDiffGenerator

theorem AlgebraicCurve.Place.ordDiff_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  simpa using AlgebraicCurve.Place.ordDiff_smul_D_uniformizer x v 0

/-- `ordDiff` on the generator over a *perfect* field, where `ord t = 1` itself
separates (`Place.isSeparable_adjoin_of_ord_eq_one`) — no characteristic-zero
hypothesis, so this is the char-`p` sibling of `ordDiff_smul_D_uniformizer` and the
body of the pin's private copy in `S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField`.
Both are needed: a perfect field may have characteristic `p`. -/
theorem AlgebraicCurve.Place.ordDiff_smul_D_uniformizer_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) (g : F) :
    v.ordDiff (g • KaehlerDifferential.D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v h1
  have hDt : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K v.uniformizer_alt
      (v.transcendental_of_ord_ne_zero (by rw [h1]; exact one_ne_zero))
  rw [AlgebraicCurve.Place.ordDiff_def,
    smul_left_injective F hDt (AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, rfl⟩)]

theorem AlgebraicCurve.Place.ordDiff_zero_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  simpa using AlgebraicCurve.Place.ordDiff_smul_D_uniformizer_of_perfectField x v 0

/-! ### `ordDiff` of a scalar multiple

`v.ordDiff (g • ω) = v.ord g + v.ordDiff ω` for `g ≠ 0` and `ω ≠ 0`: the coefficient of
`g • ω` against the uniformiser is `g` times the coefficient of `ω`, and `ord` is additive
on nonzero factors. Both flavours are pinned (the nonzero-order one needs the `ord t ≠ 0`
siblings above; the perfect-field one is the pin's private `H1_impl`, made public here
because the pin names it as a node and its next consumers want it). -/

theorem AlgebraicCurve.Place.ordDiff_smul {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have h1 : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩]
    exact one_ne_zero
  set a := AlgebraicCurve.Place.diffCoeff v.uniformizer_alt ω with ha
  have hωa : a • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_ne_zero x v h1 ω
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hωa
    exact hω hωa.symm
  rw [AlgebraicCurve.Place.ordDiff_def, AlgebraicCurve.Place.ordDiff_def, ← ha, ← hωa, smul_smul,
    AlgebraicCurve.Place.diffCoeff_smul_D_eq x v h1, v.ord_mul hg ha0]

theorem AlgebraicCurve.Place.ordDiff_smul_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.uniformizer_alt = 1 :=
    v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  have hrep : AlgebraicCurve.Place.diffCoeff v.uniformizer_alt ω
      • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one x v ht ω
  have hgo : g • ω = (g * AlgebraicCurve.Place.diffCoeff v.uniformizer_alt ω)
      • KaehlerDifferential.D K F v.uniformizer_alt := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : AlgebraicCurve.Place.diffCoeff v.uniformizer_alt (g • ω)
      = g * AlgebraicCurve.Place.diffCoeff v.uniformizer_alt ω := by
    rw [hgo]
    exact AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht _
  have hc0 : AlgebraicCurve.Place.diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [AlgebraicCurve.Place.ordDiff_def, AlgebraicCurve.Place.ordDiff_def, hco, v.ord_mul hg hc0]

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

/-- **The integrality headline over a field of characteristic zero.** The pin proves it in
`S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean` (508 lines) by hand: a `RatFunc` tower,
`IsLocalization` at the fibre centre of the valuation rings and a `FormallyUnramified`
argument, only to conclude. None of that is needed — a field of characteristic zero is
perfect (`PerfectField.ofCharZero`), so this is the perfect-field node above one instance
up. -/
theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) :=
  AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht hf

/-! ### The order of `D f`

The last piece of the differential calculus with the vocabulary above: the order of the
differential of a function. `ordDiff (D f) = ord f - 1` at every place where `f` has
nonzero order, and `ordDiff (D f) ≥ 0` whenever `0 ≤ ord f` (no zeros, no poles, so `D f`
is regular). The two statements are the sharp form of the different's effectivity: the
other module holds the *inequality* for a perfect base field, this one the equality over a
field of characteristic zero.

Two supporting lemmas: `ord_diffCoeff_D_eq_zero` (the coefficient between two
uniformisers has order zero — the two are mutual inverses by `diffCoeff_smul_D_eq` and both
coefficients are integral), and `ordDiff_eq_ord_diffCoeff` (the order of a differential
does not depend on which uniformiser the coefficient is read against). The pin states the
`ordDiff`-of-`D f` computation twice, in two files whose text is identical apart from their
last declaration; the port writes it once. -/

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
/-- The coefficient between two uniformisers is a unit at the place. -/
theorem ord_diffCoeff_D_eq_zero (v : Place K F) {t t' : F} (ht : v.ord t = 1) (ht' : v.ord t' = 1) :
    v.ord (Place.diffCoeff t (D K F t')) = 0 := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have ht0' : v.ord t' ≠ 0 := by rw [ht']; exact one_ne_zero
  set c := diffCoeff t (D K F t') with hc
  set c' := diffCoeff t' (D K F t) with hc'
  have h1 : c • D K F t = D K F t' := diffCoeff_smul_D_of_ord_ne_zero x v ht0 _
  have h2 : c' • D K F t' = D K F t := diffCoeff_smul_D_of_ord_ne_zero x v ht0' _
  have hcc : c * c' = 1 := by
    have h3 : (c * c') • D K F t' = (1 : F) • D K F t' := by
      rw [one_smul, ← smul_smul, h2, h1]
    exact smul_left_injective F (D_ne_zero_of_ord_ne_zero x v ht0') h3
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc0' : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have hsum : v.ord c + v.ord c' = 0 := by rw [← v.ord_mul hc0 hc0', hcc, v.ord_one]
  have hge : 0 ≤ v.ord c := ord_diffCoeff_D_nonneg x v ht (by rw [ht']; exact zero_le_one)
  have hge' : 0 ≤ v.ord c' := ord_diffCoeff_D_nonneg x v ht' (by rw [ht]; exact zero_le_one)
  omega

include x in
/-- **The order of a differential does not depend on the uniformiser** the coefficient is
read against. -/
theorem ordDiff_eq_ord_diffCoeff (v : Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ord (Place.diffCoeff t ω) := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have hu : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  have hu0 : v.ord v.uniformizer_alt ≠ 0 := by rw [hu]; exact one_ne_zero
  set a := diffCoeff t ω with ha
  set c := diffCoeff v.uniformizer_alt (D K F t) with hc
  have hω : a • D K F t = ω := diffCoeff_smul_D_of_ord_ne_zero x v ht0 ω
  have hDt : c • D K F v.uniformizer_alt = D K F t :=
    diffCoeff_smul_D_of_ord_ne_zero x v hu0 _
  have hc0 : c ≠ 0 := by
    rintro h; rw [h, zero_smul] at hDt; exact D_ne_zero_of_ord_ne_zero x v ht0 hDt.symm
  have hcord : v.ord c = 0 := ord_diffCoeff_D_eq_zero x v hu ht
  rw [ordDiff_def, ← hω, ← hDt, smul_smul, diffCoeff_smul_D_eq x v hu0]
  rcases eq_or_ne a 0 with h0 | ha0
  · rw [h0, zero_mul]
  · rw [v.ord_mul ha0 hc0, hcord, add_zero]

include x in
/-- `D f` is regular wherever `f` has no poles. -/
theorem ordDiff_D_nonneg (v : Place K F) {f : F} (hf : 0 ≤ v.ord f) : 0 ≤ v.ordDiff (D K F f) := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  rw [ordDiff_eq_ord_diffCoeff x v ht]
  exact ord_diffCoeff_D_nonneg x v ht hf

include x in
/-- **The sharp bound at a zero**: `ord (D f) = ord f - 1`, from `f = u π ^ n`. -/
theorem ordDiff_D_of_ord_pos (v : Place K F) {f : F} (hf : 0 < v.ord f) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : v.ord (π : F) ≠ 0 := by rw [hπord]; exact one_ne_zero
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v.ord f = n := ⟨(v.ord f).toNat, (Int.toNat_of_nonneg hf.le).symm⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp [hn] at hf
  rw [hn, zpow_natCast] at hu
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  set uF : F := ((u : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by
    intro h; apply hf0; rw [hu, h, zero_mul]
  have hπF : (π : F) ≠ 0 := by
    intro h; rw [h, v.ord_zero] at hπord; exact zero_ne_one hπord
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have huord : v.ord uF = 0 := v.ord_coe_unit u
  have hnat : v.ord (n : F) = 0 := by
    rw [← map_natCast (algebraMap K F) n]; exact v.ord_algebraMap (n : K)

  set cu := diffCoeff (π : F) (D K F uF) with hcu
  have hcu_ge : 0 ≤ v.ord cu := ord_diffCoeff_D_nonneg x v hπord huord.ge
  have hDu : cu • D K F (π : F) = D K F uF := diffCoeff_smul_D_of_ord_ne_zero x v hπ0 _

  have hDf : D K F f = (uF * (n * (π : F) ^ (n - 1)) + (π : F) ^ n * cu) • D K F (π : F) := by
    rw [hu, Derivation.leibniz, Derivation.leibniz_pow, ← hDu, ← Nat.cast_smul_eq_nsmul F]
    simp only [smul_smul]
    rw [← add_smul]
  rw [ordDiff_eq_ord_diffCoeff x v hπord, hDf, diffCoeff_smul_D_eq x v hπ0, hn]

  have hπn1 : v.ord ((π : F) ^ (n - 1)) = ((n - 1 : ℕ) : ℤ) := by
    rw [← zpow_natCast, v.ord_zpow, hπord, mul_one]
  have hA0 : uF * (n * (π : F) ^ (n - 1)) ≠ 0 :=
    mul_ne_zero huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF))
  have hA : v.ord (uF * (n * (π : F) ^ (n - 1))) = ((n - 1 : ℕ) : ℤ) := by
    rw [v.ord_mul huF0 (mul_ne_zero hnF (pow_ne_zero _ hπF)), huord, zero_add,
      v.ord_mul hnF (pow_ne_zero _ hπF), hnat, zero_add, hπn1]
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]; simp
  rcases eq_or_ne cu 0 with hcu0 | hcu0
  · rw [hcu0, mul_zero, add_zero, hA, hsub]
  · have hB : v.ord ((π : F) ^ n * cu) = (n : ℤ) + v.ord cu := by
      rw [v.ord_mul (pow_ne_zero _ hπF) hcu0, ← zpow_natCast, v.ord_zpow, hπord, mul_one]
    rw [ord_add_eq_of_lt v hA0 (mul_ne_zero (pow_ne_zero _ hπF) hcu0) (by rw [hA, hB, hsub]; omega),
      hA, hsub]

include x in
/-- **`ordDiff (D f) = ord f - 1` at every place where `f` has nonzero order.** -/
theorem ordDiff_D_eq_ord_sub_one (v : Place K F) {f : F} (hf : v.ord f ≠ 0) :
    v.ordDiff (D K F f) = v.ord f - 1 := by
  rcases lt_or_gt_of_ne hf with hneg | hpos
  · have hf0 : f ≠ 0 := by rintro rfl; simp at hneg
    have hinv : 0 < v.ord f⁻¹ := by rw [v.ord_inv]; omega
    have hinv0 : v.ord f⁻¹ ≠ 0 := hinv.ne'
    have hDf : D K F f = (-(f ^ 2)) • D K F f⁻¹ := by
      rw [Derivation.leibniz_inv, smul_smul]
      have : -(f ^ 2) * -(f⁻¹ ^ 2) = 1 := by field_simp
      rw [this, one_smul]
    rw [hDf, ordDiff_smul x v (neg_ne_zero.mpr (pow_ne_zero 2 hf0))
      (D_ne_zero_of_ord_ne_zero x v hinv0), ordDiff_D_of_ord_pos x v hinv, v.ord_neg,
      ← zpow_natCast, v.ord_zpow, v.ord_inv]
    push_cast
    ring
  · exact ordDiff_D_of_ord_pos x v hpos

include x in
/-- The same bound read at a translate of `f`. -/
theorem ordDiff_D_eq_ord_sub_algebraMap_sub_one (v : Place K F) {f : F} {c : K}
    (hfc : v.ord (f - algebraMap K F c) ≠ 0) :
    v.ordDiff (D K F f) = v.ord (f - algebraMap K F c) - 1 := by
  have : D K F f = D K F (f - algebraMap K F c) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  rw [this, ordDiff_D_eq_ord_sub_one x v hfc]

end Place

end AlgebraicCurve
