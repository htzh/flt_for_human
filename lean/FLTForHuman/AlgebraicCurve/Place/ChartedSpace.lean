/-
The charted space on the places over `ℂ`.

Let `F` be a function field of one variable over `ℂ`: an element `x` transcendental over
`ℂ` with `ℂ⟮x⟯ → F` finite, and `F` a curve over `ℂ`.  Then the set `Place ℂ F` of
places of `F` over `ℂ` carries the structure of a connected compact Hausdorff complex
manifold, and the chart at a place `v` is the one in which the reading of `f : F`

`z ↦ Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f`

is a meromorphic function near the image of `v`, with meromorphic order `v.ord f`.

The construction is the pin's.  A `ParamData` bundle carries, at every place `v`, a
radius `ρ v > 0` and a branch `γ v : ℂ → Place ℂ F` of the local-parameter
correspondence, with `γ v 0 = v` and `ord_{γ v z}(t v - z) = 1` on the disc
`ball 0 (ρ v)`, together with the meromorphic-order dictionary for every nonzero
`f : F` and its analyticity where the order is nonnegative.  The chart at `v` is
`w ↦ w.evalAt (t v)`, with inverse `γ v`; the transition functions are analytic by the
branch-uniqueness theorem, so the charts form a `C^ω` atlas (`isManifold`).  A finite
cover by closed discs (the compactness of the pin's finite-cover engine) makes
`Place ℂ F` compact; the order function separates two places, and small discs at two
places on which `ord s = 1` and `ord s = -1` hold are disjoint because `evalAt s` and
`evalAt s⁻¹` are reciprocal there — that is the Hausdorff property.  Connectedness is
the maximum-modulus argument of the complex dictionary, fed by the order clause.  The
headline then packs `topology`, `charted`, `isManifold`, `compactSpace`, `t2Space`,
`connectedSpace` and `orderClause` into the wrapper's statement.

The shared place calculus of the `localParam` family — `adicValuation_le_one_of_mem`,
`adicValuation_eq_exp_neg_ord`, `mem_of_ord_nonneg`, `ord_nonneg_of_mem`,
`ord_pos_of_mem_maximalIdeal`, `residue_eq_zero_of_ord_pos`, `isRational_of_isCurveOver`,
`residue_algebraMap`, `evalAt_algebraMap`, `evalAt_sub_algebraMap`, `evalAt_mul`,
`evalAt_eq_zero_of_ord_pos`, `ord_pos_of_evalAt_eq_zero`,
`evalAt_eq_of_ord_sub_algebraMap_eq_one`, `mem_of_ord_sub_algebraMap_eq_one` and
`ne_zero_of_ord_eq_one` — is already public under these names and is imported, not
restated.  The declarations below are the `ParamData` / charted-space layer and the
headline.

The pin's `S_` file opens with three `attribute [-instance]` / `attribute [-simp]`
walls (≈150 names) that switch off instances the pin installs globally; they are not
carried, because the port does not install those instances in the first place.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Place.Approximation
import FLTForHuman.AlgebraicCurve.Place.BranchUniqueness
import FLTForHuman.AlgebraicCurve.Place.ComplexDictionary
import FLTForHuman.AlgebraicCurve.Place.FiniteCover
import FLTForHuman.AlgebraicCurve.Place.LocalParamDatum
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

noncomputable section

-- The charted structure is installed by `letI := P.topology; letI := P.charted` in each
-- declaration, inside the statements as well as the proofs; those instance walls are
-- the pin's and are load-bearing, so the style linter's `let`/`letI` preference is
-- narrowed here rather than applied.
set_option linter.style.haveILetI false

open Filter Set Metric Topology
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace Place

namespace RiemannSurfaceGlue

section Data

variable (F : Type*) [Field F] [Algebra ℂ F]

/-- The chart data of the place space over `ℂ`: at every place `v` a radius `ρ v`, a
branch `γ v` of the local-parameter correspondence on the disc of radius `ρ v`
through `v`, a local parameter `t v`, and the meromorphic-order dictionary for the
readings along `γ v`. -/
structure ParamData where

  ρ : Place ℂ F → ℝ

  γ : Place ℂ F → ℂ → Place ℂ F

  t : Place ℂ F → F
  ρ_pos : ∀ v, 0 < ρ v
  γ_zero : ∀ v, γ v 0 = v
  ord_t : ∀ v, ∀ z ∈ ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1
  pkg : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ ball (0 : ℂ) (ρ v),
    MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
    meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
    (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)

variable {F}

/-- The chart data exist: a local parameter at each place (a place's order function
takes the value `1`) and the local-parameter engine's disc. -/
theorem nonempty_paramData
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] : Nonempty (ParamData F) := by
  choose t ht using fun v : Place ℂ F => Place.exists_ord_eq_one v
  choose ρ γ hρ h0 hord hpkg using fun v : Place ℂ F =>
    Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex F hfg v (t v) (ht v)
  exact ⟨⟨ρ, γ, t, hρ, h0, hord, hpkg⟩⟩

end Data

namespace ParamData

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] (P : ParamData F)

/-- Over an algebraically closed base every place is rational: the residue field is a
finite integral extension of `ℂ`. -/
theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isCurveOver w

omit [IsCurveOver ℂ F] in
/-- The local parameter at a place is nonzero. -/
theorem t_ne_zero (v : Place ℂ F) : P.t v ≠ 0 := by
  have h := P.ord_t v 0 (mem_ball_self (P.ρ_pos v))
  simp only [map_zero, sub_zero] at h
  exact ne_zero_of_ord_eq_one _ h

/-- The reading of the local parameter along the branch is the chart coordinate. -/
theorem evalAt_γ_t (v : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v)) :
    (P.γ v z).evalAt (P.t v) = z :=
  evalAt_eq_of_ord_sub_algebraMap_eq_one _ (isRational _) _ _ (P.ord_t v z hz)

omit [IsCurveOver ℂ F] in

/-- The local parameter is integral at every place of the branch. -/
theorem t_mem (v : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v)) :
    P.t v ∈ (P.γ v z).toValuationSubring :=
  mem_of_ord_sub_algebraMap_eq_one _ _ _ (P.ord_t v z hz)

/-- The branch is injective on its disc: the chart coordinate of the branch is the
identity. -/
theorem γ_injOn (v : Place ℂ F) : InjOn (P.γ v) (ball (0 : ℂ) (P.ρ v)) := by
  intro z hz z' hz' h
  rw [← P.evalAt_γ_t v hz, ← P.evalAt_γ_t v hz', h]

/-- The chart at a place `v`, with coordinate the reading of the local parameter
`t v` and inverse the branch `γ v` on the disc of radius `ρ v`. -/
def chart (v : Place ℂ F) : PartialEquiv (Place ℂ F) ℂ where
  toFun w := w.evalAt (P.t v)
  invFun := P.γ v
  source := P.γ v '' ball (0 : ℂ) (P.ρ v)
  target := ball (0 : ℂ) (P.ρ v)
  map_source' := by
    rintro w ⟨z, hz, rfl⟩
    rw [P.evalAt_γ_t v hz]; exact hz
  map_target' := fun z hz => ⟨z, hz, rfl⟩
  left_inv' := by
    rintro w ⟨z, hz, rfl⟩
    rw [P.evalAt_γ_t v hz]
  right_inv' := fun z hz => P.evalAt_γ_t v hz

@[scoped simp] theorem chart_apply (v w : Place ℂ F) : P.chart v w = w.evalAt (P.t v) := rfl
@[scoped simp] theorem chart_symm_apply (v : Place ℂ F) (z : ℂ) : (P.chart v).symm z = P.γ v z := rfl
theorem chart_source (v : Place ℂ F) : (P.chart v).source = P.γ v '' ball (0 : ℂ) (P.ρ v) := rfl
@[scoped simp] theorem chart_target (v : Place ℂ F) : (P.chart v).target = ball (0 : ℂ) (P.ρ v) := rfl

/-- A place lies in the source of its own chart. -/
theorem mem_chart_source (v : Place ℂ F) : v ∈ (P.chart v).source :=
  ⟨0, mem_ball_self (P.ρ_pos v), P.γ_zero v⟩

/-- The image of a place in its own chart is the origin. -/
theorem chart_self (v : Place ℂ F) : P.chart v v = 0 := by
  have h := P.evalAt_γ_t v (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero v] at h
  exact h

/-- **Analyticity of the transition functions.**  The reading of the local parameter
at `v'` along the branch at `v` is analytic at every point whose image lies in the
source of the chart at `v'`. -/
theorem analyticAt_transition (v v' : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v))
    (hz' : P.γ v z ∈ (P.chart v').source) :
    AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt (P.t v')) z := by
  obtain ⟨z', hz'm, hzz'⟩ := hz'
  refine (P.pkg v (P.t v') (P.t_ne_zero v') z hz).2.2 (ord_nonneg_of_mem _ ?_)
  rw [← hzz']
  exact P.t_mem v' hz'm

/-- The source of a transition function, as a set of chart coordinates. -/
theorem trans_source (v v' : Place ℂ F) :
    ((P.chart v).symm.trans (P.chart v')).source =
      {z | z ∈ ball (0 : ℂ) (P.ρ v) ∧ P.γ v z ∈ (P.chart v').source} := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]; rfl

/-- The source of a transition function is open. -/
theorem isOpen_trans_source (v v' : Place ℂ F) :
    IsOpen ((P.chart v).symm.trans (P.chart v')).source := by
  rw [P.trans_source, isOpen_iff_mem_nhds]
  rintro z₁ ⟨hz₁, z₁', hz₁', hγ⟩

  have hB := Place.localParam_eventually_eq_comp_evalAt_complex F (P.γ v') (P.γ v) (P.t v')
    (ball (0 : ℂ) (P.ρ v')) (ball (0 : ℂ) (P.ρ v)) z₁' z₁ (isOpen_ball.mem_nhds hz₁')
    (isOpen_ball.mem_nhds hz₁) hγ.symm (P.ord_t v') (P.pkg v') (P.pkg v)

  have hh : AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt (P.t v')) z₁ :=
    P.analyticAt_transition v v' hz₁ ⟨z₁', hz₁', hγ⟩
  have hval : (P.γ v z₁).evalAt (P.t v') = z₁' := by rw [← hγ]; exact P.evalAt_γ_t v' hz₁'
  have hin : ∀ᶠ u in 𝓝 z₁, (P.γ v u).evalAt (P.t v') ∈ ball (0 : ℂ) (P.ρ v') := by
    apply hh.continuousAt.preimage_mem_nhds
    rw [hval]; exact isOpen_ball.mem_nhds hz₁'
  filter_upwards [hB, hin, isOpen_ball.mem_nhds hz₁] with u hu hu' hu''
  exact ⟨hu'', _, hu', hu.symm⟩

/-- The transition functions are analytic on their sources. -/
theorem analyticOnNhd_trans (v v' : Place ℂ F) :
    AnalyticOnNhd ℂ ((P.chart v).symm.trans (P.chart v'))
      ((P.chart v).symm.trans (P.chart v')).source := by
  intro z hz
  rw [P.trans_source] at hz
  exact P.analyticAt_transition v v' hz.1 hz.2

/-- The charted-space core of the place space: the atlas of the charts `P.chart v`. -/
def core : ChartedSpaceCore ℂ (Place ℂ F) where
  atlas := range P.chart
  chartAt := P.chart
  mem_chart_source := P.mem_chart_source
  chart_mem_atlas v := ⟨v, rfl⟩
  open_source := by
    rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
    exact P.isOpen_trans_source v v'
  continuousOn_toFun := by
    rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
    exact (P.analyticOnNhd_trans v v').continuousOn

/-- The topology generated by the atlas. -/
@[reducible] def topology : TopologicalSpace (Place ℂ F) := P.core.toTopologicalSpace

/-- The charted-space structure generated by the atlas. -/
@[reducible] def charted : @ChartedSpace ℂ _ (Place ℂ F) P.topology := P.core.toChartedSpace

section Structure

/-- The atlas of the charted place space is exactly the atlas of the core. -/
theorem mem_atlas_iff (e : @OpenPartialHomeomorph (Place ℂ F) ℂ P.topology _) :
    (letI := P.topology; letI := P.charted; e ∈ atlas ℂ (Place ℂ F)) ↔
      ∃ v, e = P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩ := by
  letI := P.topology; letI := P.charted
  change e ∈ ⋃ (e : PartialEquiv (Place ℂ F) ℂ) (he : e ∈ P.core.atlas),
    {P.core.openPartialHomeomorph e he} ↔ _
  simp only [mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩

/-- **The place space is a complex manifold.**  The transition functions of the
atlas are analytic, hence smooth. -/
theorem isManifold :
    letI := P.topology; letI := P.charted; IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F) := by
  letI := P.topology; letI := P.charted
  refine isManifold_of_contDiffOn 𝓘(ℂ, ℂ) ω (Place ℂ F) fun e e' he he' => ?_
  obtain ⟨v, rfl⟩ := (P.mem_atlas_iff e).mp he
  obtain ⟨v', rfl⟩ := (P.mem_atlas_iff e').mp he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, range_id, inter_univ, preimage_id_eq, id]
  exact (P.analyticOnNhd_trans v v').contDiffOn_of_completeSpace

/-- The inverse of the extended chart at a place is its branch. -/
theorem extChartAt_symm_apply (v : Place ℂ F) (z : ℂ) :
    (letI := P.topology; letI := P.charted; (extChartAt 𝓘(ℂ, ℂ) v).symm z) = P.γ v z := by
  letI := P.topology; letI := P.charted
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  rfl

/-- The image of a place in its own extended chart is the origin. -/
theorem extChartAt_self (v : Place ℂ F) :
    (letI := P.topology; letI := P.charted; extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
  letI := P.topology; letI := P.charted
  rw [extChartAt_coe, modelWithCornersSelf_coe]
  exact P.chart_self v

/-- **The meromorphic-order clause.**  Every nonzero function reads, in every chart,
as a meromorphic function whose meromorphic order at the image of the place is the
order of the place. -/
theorem orderClause :
    letI := P.topology; letI := P.charted
    ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  letI := P.topology; letI := P.charted
  intro f hf v
  have hfun : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      = fun u : ℂ => (P.γ v u).evalAt f := by
    funext z; rw [P.extChartAt_symm_apply]
  rw [hfun, P.extChartAt_self]
  obtain ⟨h1, h2, -⟩ := P.pkg v f hf 0 (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero] at h2
  exact ⟨h1, h2⟩

/-- The branch at a place is continuous on its disc. -/
theorem continuousOn_γ (v : Place ℂ F) :
    letI := P.topology; ContinuousOn (P.γ v) (ball (0 : ℂ) (P.ρ v)) := by
  letI := P.topology
  exact (P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩).continuousOn_symm

/-- The image under a branch of an open piece of its disc is open. -/
theorem isOpen_image_γ (v : Place ℂ F) {s : Set ℂ} (hs : IsOpen s)
    (hsub : s ⊆ ball (0 : ℂ) (P.ρ v)) :
    IsOpen[P.topology] (P.γ v '' s) := by
  letI := P.topology
  exact (P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩).isOpen_image_symm_of_subset_target
    hs hsub

omit [IsCurveOver ℂ F] in

/-- **A small disc around a zero.**  If a function has positive order at `v`, then on a
small enough disc around `v` the readings of the branch have nonnegative order and
modulus below one. -/
theorem exists_small_disc (v : Place ℂ F) {s : F} (hs : s ≠ 0) (hv : 0 < v.ord s) :
    ∃ δ, 0 < δ ∧ δ ≤ P.ρ v ∧ ∀ z ∈ ball (0 : ℂ) δ,
      0 ≤ (P.γ v z).ord s ∧ ‖(P.γ v z).evalAt s‖ < 1 := by
  set R : ℂ → ℂ := fun u => (P.γ v u).evalAt s with hR
  have h0 := P.pkg v s hs 0 (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero] at h0
  have han : AnalyticAt ℂ R 0 := h0.2.2 hv.le
  have hval : R 0 = 0 := by
    simp only [hR, P.γ_zero]; exact evalAt_eq_zero_of_ord_pos v hs hv

  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), 0 ≤ (P.γ v z).ord s := by
    filter_upwards [han.eventually_analyticAt, isOpen_ball.mem_nhds (mem_ball_self (P.ρ_pos v))]
      with z hz hzb
    have h := (P.pkg v s hs z hzb).2.1
    have hnn : (0 : WithTop ℤ) ≤ meromorphicOrderAt R z := hz.meromorphicOrderAt_nonneg
    rw [h] at hnn
    exact_mod_cast hnn

  have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖R z‖ < 1 := by
    have := han.continuousAt.norm
    rw [ContinuousAt, hval, norm_zero] at this
    exact this.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨min δ (P.ρ v), lt_min hδ (P.ρ_pos v), min_le_right _ _, fun z hz => ?_⟩
  exact hball z (ball_subset_ball (min_le_left _ _) hz)

/-- **The place space is Hausdorff.**  Two places are separated by discs on which a
function of order `1` at one and `-1` at the other has modulus below one, respectively
above one. -/
theorem t2Space : @T2Space (Place ℂ F) P.topology := by
  classical
  letI := P.topology
  refine ⟨fun v v' hne => ?_⟩

  obtain ⟨s, hs0, hs⟩ := Place.exists_forall_ord_eq ({v, v'} : Finset (Place ℂ F))
    (fun w => if w = v then 1 else -1)
  have hv : v.ord s = 1 := by simpa using hs v (by simp)
  have hv' : v'.ord s = -1 := by simpa [hne.symm] using hs v' (by simp)
  have hv'i : v'.ord s⁻¹ = 1 := by rw [Place.ord_inv, hv']; rfl
  obtain ⟨δ, hδ, hδρ, hδp⟩ := P.exists_small_disc v hs0 (by omega)
  obtain ⟨δ', hδ', hδρ', hδp'⟩ := P.exists_small_disc v' (inv_ne_zero hs0) (by omega)
  refine ⟨P.γ v '' ball 0 δ, P.γ v' '' ball 0 δ',
    P.isOpen_image_γ v isOpen_ball (ball_subset_ball hδρ),
    P.isOpen_image_γ v' isOpen_ball (ball_subset_ball hδρ'),
    ⟨0, mem_ball_self hδ, P.γ_zero v⟩, ⟨0, mem_ball_self hδ', P.γ_zero v'⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro w ⟨z, hz, rfl⟩ ⟨z', hz', heq⟩
  obtain ⟨hord, hlt⟩ := hδp z hz
  obtain ⟨hord', hlt'⟩ := hδp' z' hz'
  rw [heq] at hord' hlt'
  have hmem : s ∈ (P.γ v z).toValuationSubring := mem_of_ord_nonneg _ hs0 hord
  have hmem' : s⁻¹ ∈ (P.γ v z).toValuationSubring := mem_of_ord_nonneg _ (inv_ne_zero hs0) hord'
  have hprod : (P.γ v z).evalAt s * (P.γ v z).evalAt s⁻¹ = 1 := by
    rw [← evalAt_mul _ (isRational _) hmem hmem', mul_inv_cancel₀ hs0, Place.evalAt_one]
  have : ‖(P.γ v z).evalAt s * (P.γ v z).evalAt s⁻¹‖ < 1 := by
    rw [norm_mul]
    calc ‖(P.γ v z).evalAt s‖ * ‖(P.γ v z).evalAt s⁻¹‖
        ≤ 1 * ‖(P.γ v z).evalAt s⁻¹‖ := by gcongr
      _ < 1 * 1 := by gcongr
      _ = 1 := one_mul _
  rw [hprod, norm_one] at this
  exact lt_irrefl _ this

/-- **The place space is compact.**  Finitely many closed discs, one for each chart of
the engine's finite cover, cover it. -/
theorem compactSpace
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) :
    @CompactSpace (Place ℂ F) P.topology := by
  letI := P.topology
  obtain ⟨S, r, hr, hcov⟩ := Place.exists_finset_forall_exists_localParam_eq_complex F hfg
    P.ρ P.γ P.t P.ρ_pos P.γ_zero P.ord_t P.pkg
  refine ⟨?_⟩
  have hK : IsCompact (⋃ v ∈ S, P.γ v '' closedBall (0 : ℂ) (r v)) := by
    refine S.finite_toSet.isCompact_biUnion fun v hv => ?_
    exact (isCompact_closedBall (0 : ℂ) (r v)).image_of_continuousOn
      ((P.continuousOn_γ v).mono (closedBall_subset_ball (hr v hv).2))
  refine hK.of_isClosed_subset isClosed_univ fun w _ => ?_
  obtain ⟨v, hv, z, hz, rfl⟩ := hcov w
  exact mem_iUnion₂.mpr ⟨v, hv, z, mem_closedBall_zero_iff.mpr hz, rfl⟩

/-- **The place space is connected**, by the maximum-modulus argument of the complex
dictionary fed with the order clause. -/
theorem connectedSpace
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) :
    @ConnectedSpace (Place ℂ F) P.topology := by
  letI := P.topology; letI := P.charted
  haveI := P.compactSpace hfg
  exact Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex F hfg
    P.orderClause

end Structure

end ParamData

end RiemannSurfaceGlue

open RiemannSurfaceGlue in
/-- **The charted space on the places over `ℂ`.**  Over a one-variable function field
`F` over `ℂ` the place space `Place ℂ F` carries a topology and a complex charted-space
structure making it a connected compact Hausdorff complex manifold, in which every
nonzero `f : F` reads as a meromorphic function of meromorphic order `v.ord f` at the
image of each place `v`. -/
theorem exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] :
    ∃ (_ : TopologicalSpace (Place ℂ F)) (_ : ChartedSpace ℂ (Place ℂ F)),
      IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F) ∧ CompactSpace (Place ℂ F) ∧
      T2Space (Place ℂ F) ∧ ConnectedSpace (Place ℂ F) ∧
      ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
        MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) ∧
        meromorphicOrderAt
            (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  obtain ⟨P⟩ := nonempty_paramData (F := F) hfg
  exact ⟨P.topology, P.charted, P.isManifold, P.compactSpace hfg, P.t2Space,
    P.connectedSpace hfg, P.orderClause⟩

end Place

end AlgebraicCurve

end
