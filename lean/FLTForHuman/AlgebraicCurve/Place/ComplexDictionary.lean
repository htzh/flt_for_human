/-
The complex place dictionary: the place space of a function field over `ℂ` is connected,
and the meromorphic order of a function at a charted point is the order of the
corresponding place.

Let `F` be a function field of one variable over `ℂ` (a transcendental `x` with
`ℂ⟮x⟯ / F` finite), with `Place ℂ F` carrying a compact charted-space structure over
`ℂ`.  Suppose that for every nonzero `f : F` and every place `v` the reading
`z ↦ Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f` is meromorphic near the image of
`v`, with meromorphic order equal to `v.ord f`.  Then `Place ℂ F` is connected.

The proof is the maximum modulus principle.  If `U` is a nonempty clopen set with a point
outside it, then `Uᶜ` is compact and closed.  Riemann–Roch at the divisor `(g + 1) • v₀`
supplies a nonconstant `f` in the `L`-space of that divisor; the divisor vanishes away
from `v₀`, so `f` is integral at every place of `Uᶜ`, and `f` is not a constant because it
is not in the image of `algebraMap ℂ F`.  The
continuous function `w ↦ ‖w.evalAt f‖` attains a maximum at some `w₀ ∈ Uᶜ`; in the chart
at `w₀` the reading of `f` is analytic and maximal in modulus at the image of `w₀`, hence
constant on a neighbourhood of that point.  Pulling that neighbourhood back through the
chart gives an infinite set of places of `Uᶜ` where `f - c` has positive order, so every
one of them is a pole of `f - c`; but a nonzero element of a function field has only
finitely many poles.  The hypothesis on the charted readings is what identifies the
order used in the argument with `meromorphicOrderAt` of the reading.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.lean

spec-pin: Theorems/Thm_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.lean
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.ComplexLineIntegral
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.Place.OrderArithmetic
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

set_option linter.style.haveILetI false

open Filter Topology
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace Place

namespace ConnectedOfCharted

section Elementary

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The set of places where a nonzero element has nonzero order is finite, i.e. a
function has only finitely many poles and zeros. -/
theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine D.support.finite_toSet.subset fun w hw => ?_
  simpa [Finsupp.mem_support_iff, hD w] using hw

/-- Riemann–Roch for a function field over an algebraically closed field, from the curve
axioms alone: the separating transcendental generator supplies the `RatFunc` tower. -/
private theorem functionFieldRiemannRoch [IsAlgClosed K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    FunctionFieldRiemannRoch K F := by
  obtain ⟨t, ht, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht hfd

/-- A nonconstant element integral at every place away from a prescribed place: the
`L`-space of `(g + 1) • v₀` has dimension at least two, so it contains an element outside
the constants; subtracting its value at `v₀` keeps it nonconstant and makes it regular
everywhere away from `v₀`. -/
theorem exists_nonconst_mem_of_ne [IsAlgClosed K] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (v₀ : Place K F) :
    ∃ f : F, f ∉ Set.range (algebraMap K F) ∧
      ∀ w : Place K F, w ≠ v₀ → f ∈ w.toValuationSubring := by
  classical
  haveI : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨η, hη⟩ := exists_ne (0 : Ω[F⁄K])
  set D : Divisor K F := Finsupp.single v₀ ((genus K F : ℤ) + 1) with hD
  have hRR := functionFieldRiemannRoch (K := K) (F := F) hη D
  have hdeg : Divisor.degree D = (genus K F : ℤ) + 1 := by
    rw [hD, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v₀]
    simp
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have : (0 : ℤ) ≤ (ell (canonicalDivisorOf hη - D) : ℤ) := Nat.cast_nonneg _
    rw [hdeg] at hRR
    linarith

  have hnot : ¬ ((LSpace D : Set F) ⊆ Set.range (algebraMap K F)) := by
    intro hle
    have hle' : LSpace D ≤ LinearMap.range (Algebra.linearMap K F) := fun f hf => by
      obtain ⟨c, hc⟩ := hle hf
      exact ⟨c, hc⟩
    haveI : Module.Finite K (LinearMap.range (Algebra.linearMap K F)) :=
      Module.Finite.range (Algebra.linearMap K F)
    have h1 : Module.finrank K (LSpace D)
        ≤ Module.finrank K (LinearMap.range (Algebra.linearMap K F)) :=
      Submodule.finrank_mono hle'
    have h2 : Module.finrank K (LinearMap.range (Algebra.linearMap K F)) ≤ 1 := by
      simpa using LinearMap.finrank_range_le (Algebra.linearMap K F)
    have h3 : (ell D : ℤ) ≤ 1 := by
      have : ell D ≤ 1 := h1.trans h2
      exact_mod_cast this
    linarith
  obtain ⟨f, hfL, hfc⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfc, fun w hw => ?_⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hfc ⟨0, by simp⟩
  have hford := ((mem_lSpace_iff_ord (D := D)).mp hfL).resolve_left hf0 w
  have hDw : D w = 0 := by
    rw [hD]
    exact Finsupp.single_eq_of_ne hw
  exact mem_of_ord_nonneg w hf0 (by simpa [hDw] using hford)

end Elementary

section Chart

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

/-- The reading of `f : F` in the chart at a place `v`, the pin's `reading`: the value of
`evalAt` at the place corresponding to a chart coordinate `z`.  The port's public
`Place.chartRead` is the same definition under the port's name; this one is the pin's, and
is an `rfl`-level alias of it, kept public because the pin's statements are spelled with it. -/
def reading (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  v.chartRead f

variable (F) in
/-- The analytic hypothesis of the complex dictionary: every nonzero element reads as a
meromorphic function at every charted place, with meromorphic order equal to the order of
the place.  This is the hypothesis of the headline theorem, stated through `reading`. -/
def OrderHypothesis : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

end Chart

section Analytic

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem reading_center (v : Place ℂ F) (f : F) :
    reading v f (extChartAt 𝓘(ℂ, ℂ) v v) = v.evalAt f := by
  simp [reading, chartRead]

theorem eventually_mem_chart (v : Place ℂ F) {f : F}
    (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
  have hc := continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v
  rw [ContinuousAt, extChartAt_to_inv] at hc
  exact hc.eventually hreg

theorem tendsto_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F)
    {f : F} (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    Tendsto (reading v f) (𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)) (𝓝 (v.evalAt f)) := by
  set c := v.evalAt f with hc_def
  have hv : f ∈ v.toValuationSubring := hreg.self_of_nhds
  have hrat : ∀ w : Place ℂ F, w.IsRational := isRational_of_isCurveOver
  have heq : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
      reading v (f - algebraMap ℂ F c) z = reading v f z - c := by
    refine ((eventually_mem_chart v hreg).filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_
    exact evalAt_sub_algebraMap _ (hrat _) hz c
  by_cases h0 : f - algebraMap ℂ F c = 0
  · have hcst : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v), reading v f z = c := by
      refine heq.mono fun z hz => ?_
      rw [h0] at hz
      have : reading v (0 : F) z = 0 := evalAt_zero ((extChartAt 𝓘(ℂ, ℂ) v).symm z)
      rw [this] at hz
      exact (sub_eq_zero.mp hz.symm)
    exact tendsto_const_nhds.congr' (hcst.mono fun z hz => hz.symm)
  · have hpos : 0 < v.ord (f - algebraMap ℂ F c) := by
      refine ord_pos_of_evalAt_eq_zero v (hrat v) h0 (sub_mem hv (v.algebraMap_mem' c)) ?_
      rw [evalAt_sub_algebraMap v (hrat v) hv c, hc_def, sub_self]
    have hordW : (0 : WithTop ℤ) <
        meromorphicOrderAt (reading v (f - algebraMap ℂ F c)) (extChartAt 𝓘(ℂ, ℂ) v v) := by
      rw [(hF _ h0 v).2]
      exact_mod_cast hpos
    have ht := tendsto_zero_of_meromorphicOrderAt_pos hordW
    have ht' : Tendsto (fun z => reading v f z - c) (𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)) (𝓝 0) :=
      ht.congr' heq
    have := ht'.add (tendsto_const_nhds (x := c))
    simpa only [sub_add_cancel, zero_add] using this

theorem continuousAt_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F)
    {f : F} (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ContinuousAt (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, reading_center]
  exact tendsto_reading hF v hreg

theorem analyticAt_reading [IsCurveOver ℂ F] (hF : OrderHypothesis F) (v : Place ℂ F)
    {f : F} (hf0 : f ≠ 0) (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    AnalyticAt ℂ (reading v f) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  (hF f hf0 v).1.analyticAt (continuousAt_reading hF v hreg)

theorem continuousAt_evalAt [IsCurveOver ℂ F] (hF : OrderHypothesis F)
    (v : Place ℂ F) {f : F} (hreg : ∀ᶠ w in 𝓝 v, f ∈ w.toValuationSubring) :
    ContinuousAt (fun w : Place ℂ F => w.evalAt f) v := by
  have h1 : ContinuousAt (reading v f ∘ extChartAt 𝓘(ℂ, ℂ) v) v :=
    ContinuousAt.comp (continuousAt_reading hF v hreg) (continuousAt_extChartAt v)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v] with w hw
  simp only [Function.comp_apply, reading, chartRead, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]

theorem false_of_isClopen [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [CompactSpace (Place ℂ F)] (hF : OrderHypothesis F)
    {U : Set (Place ℂ F)} (hU : IsClopen U) (v₀ : Place ℂ F) (hv₀ : v₀ ∈ U)
    (hne : Uᶜ.Nonempty) : False := by
  have hrat : ∀ w : Place ℂ F, w.IsRational := isRational_of_isCurveOver
  obtain ⟨f, hfc, hfreg⟩ := exists_nonconst_mem_of_ne (K := ℂ) (F := F) v₀
  have hf0 : f ≠ 0 := fun h => hfc ⟨0, by simp [h]⟩
  have hVo : IsOpen Uᶜ := hU.compl.isOpen
  have hVc : IsCompact Uᶜ := hU.compl.isClosed.isCompact
  have hregV : ∀ w ∈ Uᶜ, f ∈ w.toValuationSubring := fun w hw =>
    hfreg w (fun h => hw (h ▸ hv₀))
  have hev : ∀ w ∈ Uᶜ, ∀ᶠ w' in 𝓝 w, f ∈ w'.toValuationSubring := fun w hw =>
    Filter.eventually_of_mem (hVo.mem_nhds hw) hregV

  have hcont : ContinuousOn (fun w : Place ℂ F => ‖w.evalAt f‖) Uᶜ := fun w hw =>
    ((continuousAt_evalAt hF w (hev w hw)).norm).continuousWithinAt
  obtain ⟨w₀, hw₀, hmax⟩ := hVc.exists_isMaxOn hne hcont
  have hloc : IsLocalMax (fun w : Place ℂ F => ‖w.evalAt f‖) w₀ :=
    hmax.isLocalMax (hVo.mem_nhds hw₀)

  have hsymm : Tendsto (extChartAt 𝓘(ℂ, ℂ) w₀).symm
      (𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)) (𝓝 w₀) := by
    have hc := continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w₀
    rwa [ContinuousAt, extChartAt_to_inv] at hc
  have hloc' : IsLocalMax (norm ∘ reading w₀ f) (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) := by
    have h1 : IsMaxFilter (fun w : Place ℂ F => ‖w.evalAt f‖)
        (𝓝 ((extChartAt 𝓘(ℂ, ℂ) w₀).symm (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)))
        ((extChartAt 𝓘(ℂ, ℂ) w₀).symm (extChartAt 𝓘(ℂ, ℂ) w₀ w₀)) := by
      rw [extChartAt_to_inv]; exact hloc
    have h2 := h1.comp_tendsto (by rw [extChartAt_to_inv]; exact hsymm)
    exact h2
  have han : AnalyticAt ℂ (reading w₀ f) (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) :=
    analyticAt_reading hF w₀ hf0 (hev w₀ hw₀)
  have hdiff : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀),
      DifferentiableAt ℂ (reading w₀ f) z :=
    han.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hconst := Complex.eventually_eq_of_isLocalMax_norm hdiff hloc'
  set c := reading w₀ f (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) with hc_def

  set S : Set ℂ := {z | z ∈ (extChartAt 𝓘(ℂ, ℂ) w₀).target ∧
    (extChartAt 𝓘(ℂ, ℂ) w₀).symm z ∈ Uᶜ ∧ reading w₀ f z = c} with hS_def
  have hS : S ∈ 𝓝 (extChartAt 𝓘(ℂ, ℂ) w₀ w₀) := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) w₀,
      hsymm.eventually_mem (hVo.mem_nhds hw₀), hconst] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hSinf : S.Infinite := infinite_of_mem_nhds _ hS
  have hinj : Set.InjOn (extChartAt 𝓘(ℂ, ℂ) w₀).symm S := fun a ha b hb h => by
    have := congrArg (extChartAt 𝓘(ℂ, ℂ) w₀) h
    rwa [(extChartAt 𝓘(ℂ, ℂ) w₀).right_inv ha.1,
      (extChartAt 𝓘(ℂ, ℂ) w₀).right_inv hb.1] at this
  have himg : ((extChartAt 𝓘(ℂ, ℂ) w₀).symm '' S).Infinite := hSinf.image hinj

  have hg0 : f - algebraMap ℂ F c ≠ 0 := fun h => hfc ⟨c, (sub_eq_zero.mp h).symm⟩
  refine himg ((finite_setOf_ord_ne_zero (K := ℂ) hg0).subset ?_)
  rintro w ⟨z, hz, rfl⟩
  have hw : f ∈ ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).toValuationSubring := hregV _ hz.2.1
  have hpos : 0 < ((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).ord (f - algebraMap ℂ F c) := by
    refine ord_pos_of_evalAt_eq_zero _ (hrat _) hg0
      (sub_mem hw (((extChartAt 𝓘(ℂ, ℂ) w₀).symm z).algebraMap_mem' c)) ?_
    rw [evalAt_sub_algebraMap _ (hrat _) hw c]
    exact sub_eq_zero.mpr hz.2.2
  exact hpos.ne'

end Analytic

end ConnectedOfCharted

open ConnectedOfCharted in
/-- **The place space of a complex function field is connected.**  If every nonzero
element reads as a meromorphic function at every charted place, with meromorphic order
the order of the place, then `Place ℂ F` is connected: a nonconstant function regular on
a compact piece of the place space attains its maximum modulus there, and the maximum
modulus principle forces it to be constant. -/
theorem connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [CompactSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)) :
    ConnectedSpace (Place ℂ F) := by
  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI := hxfd
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  have hF' : OrderHypothesis F := hF

  obtain ⟨v₁, -⟩ := exists_ord_neg_of_transcendental (K := ℂ) x hx
  haveI : Nonempty (Place ℂ F) := ⟨v₁⟩

  have hpre : PreconnectedSpace (Place ℂ F) := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    by_contra hcon
    obtain ⟨hne, hnu⟩ := not_or.mp hcon
    obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hcne : Uᶜ.Nonempty := Set.nonempty_compl.mpr hnu
    exact false_of_isClopen hF' hU v₀ hv₀ hcne
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

end Place

end AlgebraicCurve

end
