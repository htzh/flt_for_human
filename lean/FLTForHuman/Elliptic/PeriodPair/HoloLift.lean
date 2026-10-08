/-
The ℂ-analytic seam of the `PeriodPair` uniformization: the differentiability of the
isogeny-direction map, and the `ModularCurve.KwD5BetweenCurvesHoloLift` reduction chain
that proves it.

Ported from the pin's

  `P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean`

(`anthropics/fermats-last-theorem@aa2d8b3`), regions `:1112–1189` (the covering-map layer,
which is `private` in the pin), `:1622–1678` (`kw_evalAt_placeOfEquation_mk` and the
℘-differentiability of `evalEval`), `:1903–1925` (`kw_countable_toPointHom_preimage`),
`:2034–2055` (the finite-kernel bridge), `:2323–2643` (the `geomMorphBC` atoms and the
whole `KwD5BetweenCurves{Locally,Cocountable,CocountableAffine,CocountableAffineWeak}`
chain) and `:2658–2673` (the headline, whose statement authority is the `Theorems/`
wrapper).

Everything the pin re-proves from its inlined prelude is **imported, not re-proved**:
the place dictionary and the `placeOfEquation` algebra from
`FLTForHuman/WeierstrassCurve/Place/Dictionary.lean`, the `PeriodPair` prelude from
`FLTForHuman/Elliptic/PeriodPair/`, the `kw_fdn2_qephod_hend7_*`/`mmr73_cs_*` engine and
the gate vocabulary from `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean` and
`FLTForHuman/WeierstrassCurve/Isogeny/NatCard.lean`. In particular
`ModularCurve.KwD5BetweenCurvesHoloLift` — the seam class — is **imported** from
`FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean` (set D-5), never
redeclared; this module *proves* it. Likewise `ModularCurve.kw_fdn2_qephod_hend7_geomMorphBC`
and `…_pmop_eq_geomMorphBC_sub` are the ported (`Isogeny/NatCard.lean`) generalisations
and are used as such, and `PeriodPair.{toPointHom,toPointHom_apply,ker_toPointHom,
toPointAddEquiv,toPointAddEquiv_mk,discriminantNeZero}` are the D-5 §1.5 promotions
(`Elliptic/PeriodPair/Uniformization.lean`).

Mathlib supplies the topology: `IsCoveringMap.existsUnique_continuousMap_lifts`
(`Mathlib/Topology/Homotopy/Lifting.lean`, the `SimplyConnectedSpace` form),
`AddSubgroup.isAddQuotientCoveringMap_of_comm` (`Mathlib/Topology/Covering/AddCircle.lean`),
`PeriodPair.DiscreteTopology`/`IsZLattice` and the ℘-differentiability
(`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`), and
`Set.Countable.isPathConnected_compl_of_one_lt_rank` + `Complex.rank_real_complex`
(`Mathlib/Analysis/Normed/Module/Connected.lean`). Mathlib has **no** covering-map
differentiability lemma, so `differentiable_of_locallyDifferentiable_lift_through_mk`
is the pin's own argument. The pin's `attribute [-instance]`/`attribute [-simp]` blocks
and its `maxHeartbeats` bumps are not transcribed (the port's cap is 4,000,000).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean>
-/
import FLTForHuman.Elliptic.PeriodPair.Basic
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

noncomputable section

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open WeierstrassCurve.Affine.CoordinateRing
/-
`Polynomial.Bivariate` is deliberately **not** opened: its `scoped notation "Y"`
makes `Y` a notation token, which breaks every `∃ X Y : …` binder and `⟨…, X, Y, …⟩`
pattern (the pin opens it only in sections whose statements use no `Y` binder).
The few proof terms that need the bivariate variable spell it
`(Polynomial.X : Polynomial K[X])` instead.
-/
open scoped Polynomial PeriodPair Topology

universe u

/-! ## The covering-map layer

Pin `:1112–1189`, all `private` in the pin: discreteness of the period lattice (mathlib's
own `DiscreteTopology L.lattice`), the covering-map instance for `ℂ → ℂ ⧸ Λ`, the
differentiability transfer through the quotient, and the `rfl` bridge to
`toPointAddEquiv`. Only `differentiable_of_locallyDifferentiable_lift_through_mk` is real
work; it is `Metric.mem_nhds_iff` + `IsPreconnected.constant_of_mapsTo` over a ball. -/

namespace PeriodPair

variable (L : PeriodPair)

private theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
  intro z hz
  obtain ⟨m, n, h⟩ := mem_lattice.mp hz
  exact ⟨(m, n), h⟩

private theorem isDiscrete_lattice : IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) := by
  rw [Submodule.coe_toAddSubgroup, isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

private theorem isCoveringMap_mk_lattice :
    IsCoveringMap (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup)) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm L.lattice.toAddSubgroup
    L.isDiscrete_lattice).isCoveringMap

private theorem differentiable_of_locallyDifferentiable_lift_through_mk
    {F : ℂ → ℂ} (hFc : Continuous F)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z) :
        ℂ ⧸ L.lattice.toAddSubgroup) = QuotientAddGroup.mk (G z)) :
    Differentiable ℂ F := by
  intro z₀
  obtain ⟨U, hU, G, hGd, heq⟩ := hloc z₀
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set V := Metric.ball z₀ ε
  have hVnhds : V ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hε
  have hz₀V : z₀ ∈ V := Metric.mem_ball_self hε
  have hmem : Set.MapsTo (fun z => F z - G z) V (L.lattice.toAddSubgroup : Set ℂ) := by
    intro z hz
    have h0 : (QuotientAddGroup.mk (s := L.lattice.toAddSubgroup) (F z - G z)
        : ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
      rw [QuotientAddGroup.mk_sub, heq z (hεU hz), sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp h0
  have hcont : ContinuousOn (fun z => F z - G z) V :=
    hFc.continuousOn.sub (hGd.mono hεU).continuousOn
  have hconst : ∀ z ∈ V, F z - G z = F z₀ - G z₀ := fun z hz =>
    (convex_ball z₀ ε).isPreconnected.constant_of_mapsTo L.isDiscrete_lattice
      hcont hmem hz hz₀V
  have hFeq : ∀ z ∈ V, F z = F z₀ - G z₀ + G z := fun z hz => by
    rw [← hconst z hz, sub_add_cancel]
  exact (((differentiableOn_const (F z₀ - G z₀)).add (hGd.mono hεU)).congr
    (fun z hz => hFeq z hz)).differentiableAt hVnhds

private theorem toPointHom_eq_toPointAddEquiv_mk (z : ℂ) :
    L.toPointHom z = L.toPointAddEquiv (QuotientAddGroup.mk z) := rfl

private theorem surjective_toPointHom : Function.Surjective L.toPointHom := by
  intro P
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (L.toPointAddEquiv.symm P)
  exact ⟨z, by rw [L.toPointHom_eq_toPointAddEquiv_mk, hz, AddEquiv.apply_symm_apply]⟩

private theorem countable_toPointHom_preimage {T : Set L.weierstrassCurve.toAffine.Point}
    (hT : T.Finite) : (L.toPointHom ⁻¹' T).Countable := by
  have hcov : L.toPointHom ⁻¹' T ⊆ ⋃ t ∈ T, L.toPointHom ⁻¹' {t} := by
    intro z hz; exact Set.mem_biUnion hz rfl
  refine (Set.Countable.biUnion hT.countable fun t _ => ?_).mono hcov
  obtain ⟨w, hw⟩ := L.surjective_toPointHom t
  have hfib : L.toPointHom ⁻¹' {t} = (· + w) '' (L.lattice : Set ℂ) := by
    ext z; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro hz
      refine ⟨z - w, ?_, by ring⟩
      have h0 : L.toPointHom (z - w) = 0 := by rw [map_sub, hz, hw, sub_self]
      rw [← AddMonoidHom.mem_ker, L.ker_toPointHom, Submodule.mem_toAddSubgroup] at h0
      exact h0
    · rintro ⟨l, hl, rfl⟩
      have h0 : L.toPointHom l = 0 := by
        rw [← AddMonoidHom.mem_ker, L.ker_toPointHom, Submodule.mem_toAddSubgroup]
        exact hl
      rw [map_add, hw, h0, zero_add]
  rw [hfib]
  exact L.countable_lattice.image _

end PeriodPair

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- Pin `kw_evalAt_placeOfEquation_mk` (`:1622`): evaluating a coordinate-ring element at
the place of an equation is `evalEval` at the point. -/
theorem kw_evalAt_placeOfEquation_mk {r s : F} (hrs : W.Equation r s) (p : Polynomial F[X]) :
    (placeOfEquation hrs).evalAt
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p))
      = p.evalEval r s := by
  have hmem : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)
      ∈ (placeOfEquation hrs).toValuationSubring := isFinitePlace_placeOfEquation hrs _
  have hdiffFF : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)
        - algebraMap F W.FunctionField (p.evalEval r s)
      = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (p - C (C (p.evalEval r s)))) := by
    rw [map_sub, IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField, ← map_sub,
      show (algebraMap F W.CoordinateRing) (p.evalEval r s)
        = CoordinateRing.mk W (C (C (p.evalEval r s))) from rfl]
  have hmemzero : CoordinateRing.mk W (p - C (C (p.evalEval r s)))
      ∈ XYIdeal W r (C s) := (mk_mem_XYIdeal_iff hrs _).mpr (by simp [evalEval])
  refine ((placeOfEquation hrs).evalAt_congr hmem
    ((placeOfEquation hrs).algebraMap_mem' _) ?_).trans
    ((placeOfEquation hrs).evalAt_algebraMap _)
  rcases eq_or_ne (CoordinateRing.mk W (p - C (C (p.evalEval r s)))) 0 with h0 | hne
  · left; rw [hdiffFF, h0, _root_.map_zero]
  · right; rw [hdiffFF]; exact (ord_placeOfEquation_pos_iff hrs hne).mpr hmemzero

end WeierstrassCurve.Affine

namespace PeriodPair

variable (L : PeriodPair)

/-- Pin `kw_differentiableOn_eval_wp` (`:1654`): a one-variable polynomial in ℘ is
differentiable off the lattice. -/
private theorem differentiableOn_eval_wp (q : ℂ[X]) :
    DifferentiableOn ℂ (fun z => q.eval (℘[L] z)) (L.lattice : Set ℂ)ᶜ := by
  have hP : DifferentiableOn ℂ ℘[L] (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_weierstrassP.differentiableOn
  induction q using Polynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiableOn_const a
  | add p q hp hq => simpa using hp.fun_add hq
  | monomial n a ih =>
    refine (ih.mul hP).congr fun z _ => ?_
    simp only [eval_mul, eval_C, eval_pow, eval_X, pow_succ, Pi.mul_apply]; ring

/-- Pin `kw_differentiableOn_evalEval_wp` (`:1666`): a bivariate polynomial evaluated at
`(℘, ℘'/2)` is differentiable off the lattice. -/
private theorem differentiableOn_evalEval_wp (p : Polynomial ℂ[X]) :
    DifferentiableOn ℂ (fun z => p.evalEval (℘[L] z) (℘'[L] z / 2)) (L.lattice : Set ℂ)ᶜ := by
  have hP' : DifferentiableOn ℂ (fun z => ℘'[L] z / 2) (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.differentiableOn.div_const 2
  induction p using Polynomial.induction_on with
  | C c => simpa [evalEval] using L.differentiableOn_eval_wp c
  | add p q hp hq => simpa [evalEval] using hp.fun_add hq
  | monomial n c ih =>
    refine (ih.mul hP').congr fun z _ => ?_
    simp only [evalEval, eval_mul, eval_pow, eval_C, eval_X, pow_succ, Pi.mul_apply]; ring

end PeriodPair

/-! ## The `geomMorphBC` atoms

Pin `:2323–2432`. The pin's section carries `IsElliptic`/`IsCentred` binders (the
`Theorems/` gate vocabulary); the proofs are the pin's, and reduce to
`mmr73_cs_evalAt_eq_of_ord_sub_pos` (`IsogenyEndDatum/Engine.lean`) and
`Place.restrict_fiber_finite`. -/

namespace ModularCurve

section GeomMorphBCAtoms

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
  [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E'] [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral)

local notation "gBC" => kw_fdn2_qephod_hend7_geomMorphBC ι hι

/-- Pin `kw_surgehgf4_hH2f_geomMorphBC_ne_zero` (`:2334`). -/
theorem kw_surgehgf4_hH2f_geomMorphBC_ne_zero (Q : E.Point)
    (hx : ι (polyToFunctionField E' X) ∈ (placeOfPoint Q).toValuationSubring) :
    gBC Q ≠ 0 := by
  intro hcon
  have hseam := kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι Q
  rw [hcon, Point.zero_def, placeOfPoint_zero] at hseam
  have hxmem : polyToFunctionField E' X
      ∈ ((placeOfPoint Q).restrictAlong ι hι).toValuationSubring :=
    (Place.mem_restrictAlong_iff ι hι (placeOfPoint Q)
      (polyToFunctionField E' X)).mpr hx
  rw [hseam] at hxmem
  exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hxmem)

open ModularCurve.Mmr73 in
/-- Pin `kw_surgehgf4_hH2f_geomMorphBC_some_coords` (`:2348`). -/
theorem kw_surgehgf4_hH2f_geomMorphBC_some_coords (Q : E.Point)
    {a b : K} {hab : E'.Nonsingular a b}
    (hQ : gBC Q = Point.some a b hab)
    (hx : ι (polyToFunctionField E' X) ∈ (placeOfPoint Q).toValuationSubring)
    (hy : ι (yGen E') ∈ (placeOfPoint Q).toValuationSubring) :
    (placeOfPoint Q).evalAt (ι (polyToFunctionField E' X)) = a
      ∧ (placeOfPoint Q).evalAt (ι (yGen E')) = b := by
  have hrat : (placeOfPoint Q).IsRational :=
    (placeOfPoint Q).isRational_of_deg_eq_one (deg_placeOfPoint Q)
  have hseam := kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι Q
  rw [hQ, placeOfPoint_some] at hseam
  have hXsub_eq : polyToFunctionField E' X - algebraMap K E'.FunctionField a
      = algebraMap E'.CoordinateRing E'.FunctionField
          (CoordinateRing.mk E' (C (X - C a))) := by
    rw [← polyToFunctionField_C (W := E') a, ← map_sub, polyToFunctionField_apply,
      algebraMap_polynomial_eq_mk_C]
  have hXmk_ne : CoordinateRing.mk E' (C (X - C a)) ≠ 0 := by
    intro hcon
    apply polyToFunctionField_ne_zero (W := E') (Polynomial.X_sub_C_ne_zero a)
    rw [polyToFunctionField_apply, algebraMap_polynomial_eq_mk_C, hcon, _root_.map_zero]
  have hposX : 0 < (placeOfEquation hab.left).ord
      (polyToFunctionField E' X - algebraMap K E'.FunctionField a) := by
    rw [hXsub_eq, ord_placeOfEquation_pos_iff hab.left hXmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwX : 0 < (placeOfPoint Q).ord
      (ι (polyToFunctionField E' X) - algebraMap K E.FunctionField a) := by
    have hmap : ι (polyToFunctionField E' X) - algebraMap K E.FunctionField a
        = ι (polyToFunctionField E' X - algebraMap K E'.FunctionField a) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong ι hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos ι hι (placeOfPoint Q))
      hposX
  have hYsub_eq : yGen E' - algebraMap K E'.FunctionField b
      = algebraMap E'.CoordinateRing E'.FunctionField
          (CoordinateRing.mk E' ((Polynomial.X : Polynomial K[X]) - C (C b))) := by
    have h2 : algebraMap K E'.FunctionField b
        = algebraMap E'.CoordinateRing E'.FunctionField
            (CoordinateRing.mk E' (C (C b))) := by
      rw [← polyToFunctionField_C (W := E') b, polyToFunctionField_apply,
        algebraMap_polynomial_eq_mk_C]
    unfold yGen yCoord
    rw [h2, ← map_sub, ← map_sub]
  have hYmk_ne : CoordinateRing.mk E' ((Polynomial.X : Polynomial K[X]) - C (C b)) ≠ 0 := by
    intro hcon
    have hrep : CoordinateRing.mk E' ((Polynomial.X : Polynomial K[X]) - C (C b))
        = (-(C b) : K[X]) • (1 : E'.CoordinateRing)
          + (1 : K[X]) • CoordinateRing.mk E' (Polynomial.X : Polynomial K[X]) := by
      rw [one_smul, Algebra.smul_def, mul_one, algebraMap_polynomial_eq_mk_C,
        map_sub, _root_.map_neg, _root_.map_neg]
      ring
    rw [hrep] at hcon
    exact one_ne_zero (CoordinateRing.smul_basis_eq_zero hcon).2
  have hposY : 0 < (placeOfEquation hab.left).ord
      (yGen E' - algebraMap K E'.FunctionField b) := by
    rw [hYsub_eq, ord_placeOfEquation_pos_iff hab.left hYmk_ne,
      mk_mem_XYIdeal_iff hab.left]
    simp [Polynomial.evalEval]
  have hposwY : 0 < (placeOfPoint Q).ord
      (ι (yGen E') - algebraMap K E.FunctionField b) := by
    have hmap : ι (yGen E') - algebraMap K E.FunctionField b
        = ι (yGen E' - algebraMap K E'.FunctionField b) := by
      rw [map_sub, AlgHom.commutes]
    rw [hmap, Place.ord_restrictAlong ι hι (placeOfPoint Q), hseam]
    exact mul_pos
      (by exact_mod_cast Place.ramificationIndexAlong_pos ι hι (placeOfPoint Q))
      hposY
  exact ⟨mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hx hposwX,
    mmr73_cs_evalAt_eq_of_ord_sub_pos (placeOfPoint Q) hrat hy hposwY⟩

/-- Pin `kw_surgehgf4_hH2f_finite_geomMorphBC_preimage` (`:2419`). -/
theorem kw_surgehgf4_hH2f_finite_geomMorphBC_preimage (t : E'.Point) :
    {P : E.Point | gBC P = t}.Finite := by
  have hT : {w : AlgebraicCurve.Place K E.FunctionField |
      w.restrictAlong ι hι = placeOfPoint t}.Finite := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI := isIntegral_along ι hι
    exact Place.restrict_fiber_finite (placeOfPoint t)
  refine (Set.Finite.preimage (placeOfPoint_injective (W := E)).injOn hT).subset
    fun P hP => ?_
  exact (kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι hι P).trans
    (congrArg placeOfPoint hP)

end GeomMorphBCAtoms

/-! ## The finite-kernel bridge

Pin `:2034–2055`: `finrankAlong` is positive, so the kernel of the pushforward is
finite. The pin's `kw_fdn2_qephod_hend7_pmopKerCard_proved` is the port's
`KwD5PointMapOfPushforwardKerCard` (`Isogeny/NatCard.lean`), which carries an extra
`hsep`; the general direction is derived here with the same `normFormulaAlong_of_elliptic`
argument the pin's `IsogenyEndDatum` engine already uses. -/

section Fintype

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {E E' : Affine K} [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E]
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E]
  [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E']
  [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E'] [WeierstrassCurve.Affine.AbelTheorem E']
variable (ι : E'.FunctionField →ₐ[K] E.FunctionField)
variable (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)

include hfin in
/-- Pin `kw_fdn2_qephod_hend10_finrankAlong_pos` (`:2042`). -/
theorem kw_fdn2_qephod_hend10_finrankAlong_pos : 0 < finrankAlong K ι := by
  unfold finrankAlong
  letI := algebraAlong ι
  haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
  exact Module.finrank_pos

/-- Pin `kw_fdn2_qephod_hend10_kerPMOP_finite` (`:2048`). -/
theorem kw_fdn2_qephod_hend10_kerPMOP_finite :
    Finite ↥(AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) := by
  haveI : HasPrincipalDivisors K E.FunctionField := hasPrincipalDivisors_functionField E
  haveI : HasPrincipalDivisors K E'.FunctionField := hasPrincipalDivisors_functionField E'
  have hsep : SeparableAlong K ι := by
    haveI : CharZero E'.FunctionField :=
      charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
    show Algebra.IsSeparable E'.FunctionField E.FunctionField
    infer_instance
  refine Nat.finite_of_card_ne_zero ?_
  rw [ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved K E E' ι hι hfin hsep
    (normFormulaAlong_of_elliptic ι hfin)]
  exact (kw_fdn2_qephod_hend10_finrankAlong_pos ι hfin).ne'

end Fintype

end ModularCurve

/-! ## The seam chain

Pin `:1524–2300` and `:2436–2643`. The four `Prop`s of the chain, the reductions
`Weak → Coords → Cocountable → Locally → HoloLift` (each stated at its pin name), and the
constructive proof of `Weak`. `ModularCurve.KwD5BetweenCurvesHoloLift` itself is imported
from `KernelBaseChange.lean`; `kw_surgehgf4_hH2f_betweenCurvesHoloLift` below proves it. -/

namespace ModularCurve

section Chain

/-- Pin `KwD5BetweenCurvesLocallyHoloLift` (`:1525`). -/
def KwD5BetweenCurvesLocallyHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'') (z₀ : ℂ),
    ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, L'.toPointHom (G z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z)

/-- Pin `kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo` (`:1536`). -/
theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo
    (hH2c : KwD5BetweenCurvesLocallyHoloLift) :
    KwD5BetweenCurvesHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  set ψ := pointMapOfPushforward ι'' hι'' hfin'' (normFormulaAlong_of_elliptic ι'' hfin'')
    with hψdef
  set g : ℂ → ℂ ⧸ L'.lattice.toAddSubgroup :=
    fun z => L'.toPointAddEquiv.symm (ψ (L.toPointHom z)) with hg
  have hgloc : ∀ z₀ : ℂ, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, g z = QuotientAddGroup.mk (G z) := fun z₀ => by
    obtain ⟨U, hU, G, hGd, hGint⟩ := hH2c L L' ι'' hι'' hfin'' z₀
    exact ⟨U, hU, G, hGd, fun z hz => by
      show L'.toPointAddEquiv.symm (ψ (L.toPointHom z)) = _
      rw [hψdef, ← hGint z hz, L'.toPointHom_eq_toPointAddEquiv_mk,
        AddEquiv.symm_apply_apply]⟩
  have hmkc : Continuous (QuotientAddGroup.mk (s := L'.lattice.toAddSubgroup)) :=
    L'.isCoveringMap_mk_lattice.continuous
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun z₀ => by
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ((hmkc.comp_continuousOn hGd.continuousOn).congr
      (fun z hz => heq z hz)).continuousAt hU
  have hg0 : (QuotientAddGroup.mk (0 : ℂ) : ℂ ⧸ L'.lattice.toAddSubgroup)
      = (⟨g, hgc⟩ : C(ℂ, ℂ ⧸ L'.lattice.toAddSubgroup)) 0 := by
    simp only [ContinuousMap.coe_mk, hg, _root_.map_zero, QuotientAddGroup.mk_zero]
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ :=
    L'.isCoveringMap_mk_lattice.existsUnique_continuousMap_lifts ⟨g, hgc⟩ 0 0 hg0
  have hFliftz : ∀ z, (QuotientAddGroup.mk (F z) : ℂ ⧸ L'.lattice.toAddSubgroup) = g z :=
    fun z => congrFun hFlift z
  refine ⟨F, ?_, ?_, ?_⟩
  ·
    refine L'.differentiable_of_locallyDifferentiable_lift_through_mk F.continuous
      (fun z₀ => ?_)
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ⟨U, hU, G, hGd, fun z hz => (hFliftz z).trans (heq z hz)⟩
  ·
    rw [hF0]; exact Submodule.zero_mem L'.lattice
  ·
    intro z
    rw [L'.toPointHom_eq_toPointAddEquiv_mk, hFliftz z, hg, AddEquiv.apply_symm_apply]

/-- Pin `KwD5BetweenCurvesCocountableHoloLift` (`:1953`). -/
def KwD5BetweenCurvesCocountableHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, L'.toPointHom (G z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z)

/-- Pin `kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable` (`:1965`). -/
theorem kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable
    (hH2d : KwD5BetweenCurvesCocountableHoloLift) :
    KwD5BetweenCurvesLocallyHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin'' z₀
  obtain ⟨S, hSc, hgen⟩ := hH2d L L' ι'' hι'' hfin''
  obtain ⟨w, hw⟩ : ∃ w, z₀ + w ∉ S := by
    obtain ⟨ζ, hζ⟩ := (hSc.isPathConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex])).nonempty
    refine ⟨ζ - z₀, ?_⟩
    have hzw : z₀ + (ζ - z₀) = ζ := by ring
    rwa [hzw]
  obtain ⟨U', hU', G', hG'd, hG'int⟩ := hgen (z₀ + w) hw
  obtain ⟨cw, hcw⟩ := L'.surjective_toPointHom
    ((pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom w))
  refine ⟨(· + w) ⁻¹' U',
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hU',
    fun z => G' (z + w) - cw,
    (hG'd.comp (differentiable_id.add_const w).differentiableOn
      (Set.mapsTo_preimage _ _)).sub_const cw,
    fun z hz => ?_⟩
  rw [map_sub, hcw, hG'int (z + w) hz,
    ← map_sub (pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')),
    ← map_sub L.toPointHom, add_sub_cancel_right]

/-- Pin `kw_surgehgf4_hH2_betweenCurvesHoloLift_of_cocountable` (`:1989`). -/
theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_cocountable
    (hH2d : KwD5BetweenCurvesCocountableHoloLift) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo
    (kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable hH2d)

/-- Pin `KwD5BetweenCurvesCocountableAffineHoloCoords` (`:2112`). -/
def KwD5BetweenCurvesCocountableAffineHoloCoords : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, Y z ≠ 0 ∧
        ∃ h, (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z)
          = Point.some (X z) (Y z) h

/-- Pin `kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords`
(`:2126`). -/
theorem kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords
    (hH2e : KwD5BetweenCurvesCocountableAffineHoloCoords) :
    KwD5BetweenCurvesCocountableHoloLift := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  obtain ⟨S, hSc, hgen⟩ := hH2e L L' ι'' hι'' hfin''
  refine ⟨S, hSc, fun z₀ hz₀ => ?_⟩
  obtain ⟨U, hU, X, Y, hXd, hYd, hcoord⟩ := hgen z₀ hz₀
  obtain ⟨U', hU'U, hU'open, hz₀U'⟩ := mem_nhds_iff.mp hU
  obtain ⟨hYz₀, hnsz₀, hcoord₀⟩ := hcoord z₀ (hU'U hz₀U')
  obtain ⟨w₀, hw₀⟩ := L'.surjective_toPointHom (.some (X z₀) (Y z₀) hnsz₀)
  have hw₀Λ : w₀ ∉ L'.lattice := by
    intro hmem
    have h0 : L'.toPointHom w₀ = 0 := by
      rw [← AddMonoidHom.mem_ker, L'.ker_toPointHom]; exact hmem
    exact Point.some_ne_zero _ (hw₀ ▸ h0)
  have hPw₀ : ℘[L'] w₀ = X z₀ ∧ ℘'[L'] w₀ / 2 = Y z₀ := by
    have h := hw₀
    rwa [L'.toPointHom_apply, L'.toPoint_of_notMem _ hw₀Λ, Point.some.injEq] at h
  have hder : deriv ℘[L'] w₀ ≠ 0 := by
    simp only [PeriodPair.deriv_weierstrassP]
    exact fun h0 => hYz₀ (by rw [← hPw₀.2, h0, zero_div])
  have hPa : AnalyticAt ℂ ℘[L'] w₀ := L'.analyticOnNhd_weierstrassP w₀ hw₀Λ
  set ψ := hPa.hasStrictDerivAt.localInverse ℘[L'] (deriv ℘[L'] w₀) w₀ hder with hψdef
  have hψa : AnalyticAt ℂ ψ (X z₀) := hPw₀.1 ▸ hPa.analyticAt_localInverse hder
  have hψw₀ : ψ (X z₀) = w₀ :=
    hPw₀.1 ▸ HasStrictFDerivAt.localInverse_apply_image _
  set G := ψ ∘ X with hGdef
  have hXcont : ContinuousAt X z₀ := (hXd.differentiableAt hU).continuousAt
  have hGcont : ContinuousAt G z₀ := hψa.continuousAt.comp hXcont
  have hGz₀ : G z₀ = w₀ := hψw₀
  have hevΛ : ∀ᶠ z in 𝓝 z₀, G z ∉ L'.lattice :=
    hGcont.eventually (L'.isClosed_lattice.isOpen_compl.mem_nhds (hGz₀ ▸ hw₀Λ))
  have hevR : ∀ᶠ z in 𝓝 z₀, ℘[L'] (G z) = X z := by
    have h := hPw₀.1 ▸ hPa.hasStrictDerivAt.eventually_right_inverse hder
    exact hXcont.eventually h
  have hevψd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ ψ (X z) :=
    hXcont.eventually
      ((AnalyticAt.eventually_analyticAt hψa).mono fun _ hy => hy.differentiableAt)
  have hevXd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ X z :=
    Filter.eventually_of_mem (hU'open.mem_nhds hz₀U') fun z hz =>
      (hXd.mono hU'U).differentiableAt (hU'open.mem_nhds hz)
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U :=
    Filter.eventually_of_mem (hU'open.mem_nhds hz₀U') hU'U
  have hevSgn : ∀ᶠ z in 𝓝 z₀, ℘'[L'] (G z) / 2 + Y z ≠ 0 := by
    have hP'cont : ContinuousAt ℘'[L'] (G z₀) := by
      rw [hGz₀]; exact (L'.analyticOnNhd_derivWeierstrassP w₀ hw₀Λ).continuousAt
    have hcont : ContinuousAt (fun z => ℘'[L'] (G z) / 2 + Y z) z₀ :=
      ((hP'cont.comp hGcont).div_const 2).add (hYd.differentiableAt hU).continuousAt
    refine hcont.eventually (isOpen_ne.mem_nhds ?_)
    show ℘'[L'] (G z₀) / 2 + Y z₀ ≠ 0
    rw [hGz₀, hPw₀.2, ← two_mul]; exact mul_ne_zero two_ne_zero hYz₀
  obtain ⟨V, hVmem, hVopen, hVz₀⟩ := eventually_nhds_iff.mp
    (((((hevΛ.and hevR).and hevψd).and hevXd).and hevU).and hevSgn)
  refine ⟨V, hVopen.mem_nhds hVz₀, G, ?_, fun z hz => ?_⟩
  ·
    exact fun z hz =>
      ((hVmem z hz).1.1.1.2.comp z (hVmem z hz).1.1.2).differentiableWithinAt
  ·
    obtain ⟨⟨⟨⟨⟨hGzΛ, hPGz⟩, -⟩, -⟩, hzU⟩, hsgn⟩ := hVmem z hz
    obtain ⟨hYz, hnsz, hcoordz⟩ := hcoord z hzU
    have hPGy : ℘'[L'] (G z) / 2 = Y z := by
      have h1 : (℘'[L'] (G z) / 2) ^ 2 = Y z ^ 2 := by
        have hG := (WeierstrassCurve.Affine.equation_iff _ _).mp
          (hPGz ▸ L'.equation_weierstrassP hGzΛ)
        have hY := (WeierstrassCurve.Affine.equation_iff _ _).mp hnsz.1
        simp only [L'.weierstrassCurve_a₁, L'.weierstrassCurve_a₂, L'.weierstrassCurve_a₃,
          zero_mul, add_zero] at hG hY
        exact hG.trans hY.symm
      have hfac : (℘'[L'] (G z) / 2 - Y z) * (℘'[L'] (G z) / 2 + Y z) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hsgn
    rw [L'.toPointHom_apply, L'.toPoint_of_notMem _ hGzΛ, hcoordz, Point.some.injEq]
    exact ⟨hPGz, hPGy⟩

/-- Pin `kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords` (`:2202`). -/
theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords
    (hH2e : KwD5BetweenCurvesCocountableAffineHoloCoords) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_cocountable
    (kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords hH2e)

/-- Pin `KwD5BetweenCurvesCocountableAffineHoloCoordsWeak` (`:2232`). -/
def KwD5BetweenCurvesCocountableAffineHoloCoordsWeak : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ S : Set ℂ, S.Countable ∧
    ∀ z₀ ∉ S, ∃ U ∈ nhds z₀, ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h, (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z)
          = Point.some (X z) (Y z) h

/-- Pin `kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak` (`:2245`). -/
theorem kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak
    (hH2f : KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    KwD5BetweenCurvesCocountableAffineHoloCoords := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  obtain ⟨S, hSc, hgen⟩ := hH2f L L' ι'' hι'' hfin''
  set K : Set L.weierstrassCurve.toAffine.Point :=
    {P | (pointMapOfPushforward ι'' hι'' hfin''
      (normFormulaAlong_of_elliptic ι'' hfin'')) P = 0} with hKdef
  have hKfin : K.Finite := by
    have hfin := kw_fdn2_qephod_hend10_kerPMOP_finite
      (K := ℂ) (E := L.weierstrassCurve.toAffine) (E' := L'.weierstrassCurve.toAffine)
      ι'' hι'' hfin''
    have heq : K = ((AddMonoidHom.ker (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin''))) : Set _) := by
      ext P; simp only [hKdef, Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_ker]
    rw [heq]; exact Set.finite_coe_iff.mp hfin
  set S' : Set ℂ := (fun z => (2 : ℂ) * z) ⁻¹' (L.toPointHom ⁻¹' K)
  have hS'c : S'.Countable :=
    (L.countable_toPointHom_preimage hKfin).preimage
      (mul_right_injective₀ two_ne_zero)
  refine ⟨S ∪ S', hSc.union hS'c, fun z₀ hz₀ => ?_⟩
  have hz₀S : z₀ ∉ S := fun h => hz₀ (Or.inl h)
  have hz₀S' : z₀ ∉ S' := fun h => hz₀ (Or.inr h)
  obtain ⟨U, hU, X, Y, hXd, hYd, hcoord⟩ := hgen z₀ hz₀S
  obtain ⟨hns₀, hcoord₀⟩ := hcoord z₀ (mem_of_mem_nhds hU)
  have hYz₀ : Y z₀ ≠ 0 := by
    intro hY0
    apply hz₀S'
    show (pointMapOfPushforward ι'' hι'' hfin'' (normFormulaAlong_of_elliptic ι'' hfin''))
      (L.toPointHom (2 * z₀)) = 0
    rw [two_mul, map_add, map_add, hcoord₀, add_eq_zero_iff_eq_neg, Point.neg_some,
      Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [hY0]
    simp only [negY, L'.weierstrassCurve_a₁, L'.weierstrassCurve_a₃,
      zero_mul, _root_.neg_zero, sub_zero]
  set V := U ∩ {z | Y z ≠ 0}
  have hVnhds : V ∈ nhds z₀ :=
    Filter.inter_mem hU ((hYd.continuousOn.continuousAt hU).preimage_mem_nhds
      (isOpen_ne.mem_nhds hYz₀))
  refine ⟨V, hVnhds, X, Y, hXd.mono Set.inter_subset_left,
    hYd.mono Set.inter_subset_left, fun z hz => ?_⟩
  obtain ⟨hns, hc⟩ := hcoord z hz.1
  exact ⟨hz.2, hns, hc⟩

/-- Pin `kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak` (`:2290`). -/
theorem kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak
    (hH2f : KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords
    (kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak hH2f)

open WeierstrassCurve.Affine.CoordinateRing in
/-- Pin `kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak` (`:2436`): the
constructive base of the chain. -/
theorem kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak :
    KwD5BetweenCurvesCocountableAffineHoloCoordsWeak := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin''
  let W := L.weierstrassCurve.toAffine
  let W' := L'.weierstrassCurve.toAffine
  set ξ := ι'' (polyToFunctionField W' X) with hξdef
  set η := ι'' (yGen W') with hηdef
  set c₀ := kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' 0 with hc₀def
  obtain ⟨pξ, qξ, hqξ, hξeq⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) ξ
  obtain ⟨pη, qη, hqη, hηeq⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) η
  obtain ⟨pξ', rfl⟩ := AdjoinRoot.mk_surjective pξ
  obtain ⟨qξ', rfl⟩ := AdjoinRoot.mk_surjective qξ
  obtain ⟨pη', rfl⟩ := AdjoinRoot.mk_surjective pη
  obtain ⟨qη', rfl⟩ := AdjoinRoot.mk_surjective qη
  have hqξ0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hqξ)
  have hqη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hqη)
  set Tq : Set W.Point := placeOfPoint ⁻¹'
    ({v | v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ')) ≠ 0} ∪
     {v | v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη')) ≠ 0})
  have hfin_ord : ∀ {f : W.FunctionField}, f ≠ 0 →
      {v : Place ℂ W.FunctionField | v.ord f ≠ 0}.Finite := by
    intro f hf
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf
    exact Df.support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.mpr (hDf v ▸ hv)
  have hTq_fin : Tq.Finite := Set.Finite.preimage placeOfPoint_injective.injOn
    ((hfin_ord hqξ0).union (hfin_ord hqη0))
  set Tc : Set W.Point := {P | kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' P = c₀}
    ∪ {P | kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' P = -c₀}
  have hTc_fin : Tc.Finite :=
    (kw_surgehgf4_hH2f_finite_geomMorphBC_preimage ι'' hι'' c₀).union
      (kw_surgehgf4_hH2f_finite_geomMorphBC_preimage ι'' hι'' (-c₀))
  set S : Set ℂ := (L.lattice : Set ℂ) ∪ L.toPointHom ⁻¹' (Tq ∪ Tc) with hSdef
  have hSc : S.Countable := L.countable_lattice.union
    (L.countable_toPointHom_preimage (hTq_fin.union hTc_fin))
  refine ⟨S, hSc, fun z₀ hz₀ => ?_⟩
  simp only [hSdef, Set.mem_union, Set.mem_preimage, not_or] at hz₀
  obtain ⟨hz₀Λ, hz₀Tq, hz₀Tc⟩ := hz₀
  set A : ℂ → ℂ := fun z =>
    pξ'.evalEval (℘[L] z) (℘'[L] z / 2) / qξ'.evalEval (℘[L] z) (℘'[L] z / 2) with hAdef
  set B : ℂ → ℂ := fun z =>
    pη'.evalEval (℘[L] z) (℘'[L] z / 2) / qη'.evalEval (℘[L] z) (℘'[L] z / 2) with hBdef
  set U₁ : Set ℂ :=
    ((L.lattice : Set ℂ)ᶜ ∩ (fun z => qξ'.evalEval (℘[L] z) (℘'[L] z / 2)) ⁻¹' {0}ᶜ) ∩
    ((L.lattice : Set ℂ)ᶜ ∩ (fun z => qη'.evalEval (℘[L] z) (℘'[L] z / 2)) ⁻¹' {0}ᶜ)
    with hU₁def
  have hU₁open : IsOpen U₁ :=
    ((L.differentiableOn_evalEval_wp qξ').continuousOn.isOpen_inter_preimage
      L.isClosed_lattice.isOpen_compl isOpen_compl_singleton).inter
    ((L.differentiableOn_evalEval_wp qη').continuousOn.isOpen_inter_preimage
      L.isClosed_lattice.isOpen_compl isOpen_compl_singleton)
  have hU₁Λ : U₁ ⊆ (L.lattice : Set ℂ)ᶜ := fun z hz => hz.1.1
  have hAd : DifferentiableOn ℂ A U₁ :=
    ((L.differentiableOn_evalEval_wp pξ').mono hU₁Λ).div
      ((L.differentiableOn_evalEval_wp qξ').mono hU₁Λ) fun z hz => hz.1.2
  have hBd : DifferentiableOn ℂ B U₁ :=
    ((L.differentiableOn_evalEval_wp pη').mono hU₁Λ).div
      ((L.differentiableOn_evalEval_wp qη').mono hU₁Λ) fun z hz => hz.2.2
  have hgeom : ∀ z ∈ U₁, ∃ hns : W'.Nonsingular (A z) (B z),
      kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.toPointHom z)
        = Point.some (A z) (B z) hns := by
    intro z hz
    have hzΛ : z ∉ L.lattice := hU₁Λ hz
    have hqξz : qξ'.evalEval (℘[L] z) (℘'[L] z / 2) ≠ 0 := hz.1.2
    have hqηz : qη'.evalEval (℘[L] z) (℘'[L] z / 2) ≠ 0 := hz.2.2
    set hrs := L.equation_weierstrassP hzΛ with hrs_def
    have hplace : placeOfPoint (W := W) (L.toPointHom z) = placeOfEquation hrs := by
      rw [L.toPointHom_apply, L.toPoint_of_notMem _ hzΛ]; exact placeOfPoint_some _
    have hordqξ : (placeOfEquation hrs).ord
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qξ')) = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hqξz ?_) (ord_placeOfEquation_nonneg hrs _)
      exact (mk_mem_XYIdeal_iff hrs qξ').mp
        ((ord_placeOfEquation_pos_iff hrs (nonZeroDivisors.ne_zero hqξ)).mp hlt)
    have hordqη : (placeOfEquation hrs).ord
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W qη')) = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hqηz ?_) (ord_placeOfEquation_nonneg hrs _)
      exact (mk_mem_XYIdeal_iff hrs qη').mp
        ((ord_placeOfEquation_pos_iff hrs (nonZeroDivisors.ne_zero hqη)).mp hlt)
    have hιinj : Function.Injective ι'' := RingHom.injective ι''.toRingHom
    have hξne : ξ ≠ 0 := fun h => polyToFunctionField_ne_zero (W := W') X_ne_zero
      (hιinj (h.trans (_root_.map_zero _).symm))
    have hyGen_ne : yGen W' ≠ 0 := by
      have hmkY : (CoordinateRing.mk W' (Polynomial.X : Polynomial ℂ[X]) :
          W'.CoordinateRing) ≠ 0 := fun h => one_ne_zero
        (CoordinateRing.smul_basis_eq_zero
        (show (0 : ℂ[X]) • (1 : W'.CoordinateRing) + (1 : ℂ[X]) • CoordinateRing.mk W' _ = 0 by
          rw [zero_smul, one_smul, zero_add]; exact h)).2
      exact (map_ne_zero_iff _ (IsFractionRing.injective W'.CoordinateRing W'.FunctionField)).mpr
        hmkY
    have hηne : η ≠ 0 := fun h => hyGen_ne (hιinj (h.trans (_root_.map_zero _).symm))
    have hpξ0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W pξ') ≠ 0 :=
      fun h => hξne (hξeq ▸ by rw [h, zero_div])
    have hpη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W pη') ≠ 0 :=
      fun h => hηne (hηeq ▸ by rw [h, zero_div])
    have hξmem : ξ ∈ (placeOfEquation hrs).toValuationSubring := by
      refine (placeOfEquation hrs).mem_of_ord_nonneg hξne ?_
      rw [← hξeq, (placeOfEquation hrs).ord_div hpξ0 hqξ0, hordqξ, sub_zero]
      exact ord_placeOfEquation_nonneg hrs _
    have hηmem : η ∈ (placeOfEquation hrs).toValuationSubring := by
      refine (placeOfEquation hrs).mem_of_ord_nonneg hηne ?_
      rw [← hηeq, (placeOfEquation hrs).ord_div hpη0 hqη0, hordqη, sub_zero]
      exact ord_placeOfEquation_nonneg hrs _
    have hgm_ne : kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.toPointHom z) ≠ 0 :=
      kw_surgehgf4_hH2f_geomMorphBC_ne_zero ι'' hι'' _ (hplace ▸ hξmem)
    obtain ⟨a, b, hab, hgm_eq⟩ : ∃ a b hab,
        kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.toPointHom z)
          = Point.some a b hab := by
      rcases hP : kw_fdn2_qephod_hend7_geomMorphBC ι'' hι'' (L.toPointHom z) with
        _ | ⟨a, b, hab⟩
      · exact absurd hP hgm_ne
      · exact ⟨a, b, hab, rfl⟩
    have hrat := isRational_placeOfEquation hrs
    obtain ⟨ha, hb⟩ := kw_surgehgf4_hH2f_geomMorphBC_some_coords ι'' hι'' _ hgm_eq
      (hplace ▸ hξmem) (hplace ▸ hηmem)
    rw [hplace, ← hξdef] at ha
    rw [hplace, ← hηdef] at hb
    have hAz : A z = a := by
      simp only [hAdef]
      rw [← ha, ← hξeq, (placeOfEquation hrs).evalAt_div' hrat
          (isFinitePlace_placeOfEquation hrs _) hqξ0 hordqξ,
        kw_evalAt_placeOfEquation_mk hrs pξ', kw_evalAt_placeOfEquation_mk hrs qξ']
    have hBz : B z = b := by
      simp only [hBdef]
      rw [← hb, ← hηeq, (placeOfEquation hrs).evalAt_div' hrat
          (isFinitePlace_placeOfEquation hrs _) hqη0 hordqη,
        kw_evalAt_placeOfEquation_mk hrs pη', kw_evalAt_placeOfEquation_mk hrs qη']
    obtain ⟨rfl, rfl⟩ : a = A z ∧ b = B z := ⟨hAz.symm, hBz.symm⟩
    exact ⟨hab, hgm_eq⟩
  have hplace₀ : placeOfPoint (W := W) (L.toPointHom z₀)
      = placeOfEquation (L.equation_weierstrassP hz₀Λ) := by
    rw [L.toPointHom_apply, L.toPoint_of_notMem _ hz₀Λ]; exact placeOfPoint_some _
  have hz₀Tq' := hz₀Tq; rw [show Tq = _ from rfl, Set.mem_preimage, Set.mem_union, not_or,
    Set.mem_setOf_eq, Set.mem_setOf_eq, not_ne_iff, not_ne_iff, hplace₀] at hz₀Tq'
  have hz₀U₁ : z₀ ∈ U₁ := by
    refine ⟨⟨hz₀Λ, fun h => ?_⟩, hz₀Λ, fun h => ?_⟩
    · exact (((ord_placeOfEquation_pos_iff (L.equation_weierstrassP hz₀Λ)
        (nonZeroDivisors.ne_zero hqξ)).mpr
        ((mk_mem_XYIdeal_iff (L.equation_weierstrassP hz₀Λ) qξ').mpr
          (Set.mem_singleton_iff.mp h))).ne' hz₀Tq'.1).elim
    · exact (((ord_placeOfEquation_pos_iff (L.equation_weierstrassP hz₀Λ)
        (nonZeroDivisors.ne_zero hqη)).mpr
        ((mk_mem_XYIdeal_iff (L.equation_weierstrassP hz₀Λ) qη').mpr
          (Set.mem_singleton_iff.mp h))).ne' hz₀Tq'.2).elim
  have hU₁nhds : U₁ ∈ nhds z₀ := hU₁open.mem_nhds hz₀U₁
  rcases hc₀cases : c₀ with _ | ⟨x₀, y₀, h₀⟩
  ·
    refine ⟨U₁, hU₁nhds, A, B, hAd, hBd, fun z hz => ?_⟩
    obtain ⟨hns, heq⟩ := hgeom z hz
    refine ⟨hns, ?_⟩
    rw [kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin''), ← hc₀def, hc₀cases,
      ← Point.zero_def, sub_zero, heq]
  ·
    set U : Set ℂ := U₁ ∩ A ⁻¹' {x₀}ᶜ with hUdef
    have hUopen : IsOpen U := by
      have h := hAd.continuousOn.isOpen_inter_preimage hU₁open
        (isOpen_compl_singleton (x := x₀))
      rw [show U = U₁ ∩ (U₁ ∩ A ⁻¹' {x₀}ᶜ) by rw [hUdef, ← Set.inter_assoc,
        Set.inter_self]]
      exact hU₁open.inter h
    have hz₀U : z₀ ∈ U := by
      refine ⟨hz₀U₁, fun hA0 => hz₀Tc ?_⟩
      obtain ⟨hns₀, hgm₀⟩ := hgeom z₀ hz₀U₁
      have hXeq := (Point.X_eq_iff (h₁ := hns₀) (h₂ := h₀)).mp (Set.mem_singleton_iff.mp hA0)
      rw [← hgm₀, ← hc₀cases] at hXeq
      exact hXeq.imp id id
    set ℓ : ℂ → ℂ := fun z => W'.slope (A z) x₀ (B z) (W'.negY x₀ y₀) with hℓdef
    set X' : ℂ → ℂ := fun z => W'.addX (A z) x₀ (ℓ z) with hX'def
    set Y' : ℂ → ℂ := fun z => W'.addY (A z) x₀ (B z) (ℓ z) with hY'def
    have hℓd : DifferentiableOn ℂ ℓ U :=
      ((((hBd.mono Set.inter_subset_left).sub (differentiableOn_const _)).div
        ((hAd.mono Set.inter_subset_left).sub (differentiableOn_const _))
        fun z hz => sub_ne_zero.mpr hz.2) :
          DifferentiableOn ℂ (fun z => (B z - W'.negY x₀ y₀) / (A z - x₀)) U).congr
        fun z hz => slope_of_X_ne hz.2
    have hX'd : DifferentiableOn ℂ X' U :=
      ((((hℓd.pow 2).add ((differentiableOn_const W'.a₁).mul hℓd)).sub
        (((differentiableOn_const W'.a₂).add (hAd.mono Set.inter_subset_left)).add
          (differentiableOn_const x₀))) :
          DifferentiableOn ℂ (fun z => ℓ z ^ 2 + W'.a₁ * ℓ z - (W'.a₂ + A z + x₀)) U).congr
        fun z hz => by
          simp only [hX'def, addX, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
          ring
    have hY'd : DifferentiableOn ℂ Y' U :=
      ((((hℓd.mul (hX'd.sub (hAd.mono Set.inter_subset_left))).add
        (hBd.mono Set.inter_subset_left)).neg.sub
        ((differentiableOn_const W'.a₁).mul hX'd) |>.sub (differentiableOn_const W'.a₃)) :
          DifferentiableOn ℂ
            (fun z => -(ℓ z * (X' z - A z) + B z) - W'.a₁ * X' z - W'.a₃) U).congr
        fun z hz => by
          simp only [hY'def, hX'def, addY, negY, negAddY, Pi.add_apply, Pi.sub_apply,
            Pi.mul_apply, Pi.neg_apply]
    refine ⟨U, hUopen.mem_nhds hz₀U, X', Y', hX'd, hY'd, fun z hz => ?_⟩
    obtain ⟨hns, heq⟩ := hgeom z hz.1
    have hXne : A z ≠ x₀ := hz.2
    have hpeq : pointMapOfPushforward ι'' hι'' hfin''
          (normFormulaAlong_of_elliptic ι'' hfin'') (L.toPointHom z)
        = Point.some (A z) (B z) hns + Point.some x₀ (W'.negY x₀ y₀)
            ((nonsingular_neg ..).mpr h₀) := by
      rw [kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι'' hι'' hfin''
          (normFormulaAlong_of_elliptic ι'' hfin''), ← hc₀def,
        hc₀cases, heq, sub_eq_add_neg, Point.neg_some]
    rw [hpeq, Point.add_of_X_ne hXne]
    exact ⟨_, rfl⟩

/-- Pin `kw_surgehgf4_hH2f_betweenCurvesHoloLift` (`:2640`): the seam class, proved. -/
theorem kw_surgehgf4_hH2f_betweenCurvesHoloLift :
    KwD5BetweenCurvesHoloLift :=
  kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak
    kw_surgehgf4_hH2f_betweenCurvesCocountableAffineHoloCoordsWeak

end Chain

end ModularCurve

/-! ## The headline

Pin `:2658`; the binders are the `Theorems/` wrapper's verbatim. `KwD5BetweenCurvesHoloLift`
is stated with `toPointHom`; the two occurrences are rewritten to `toPoint` by the ported
`PeriodPair.toPointHom_apply`, and the `hN` argument is passed through (both are `Prop`
proofs, so the `normFormulaAlong_of_elliptic` the chain uses is definitionally the same). -/

namespace PeriodPair

theorem exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z) = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) := by
  obtain ⟨F, hF, hF0, hFz⟩ := ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift L L' ι hι hfin
  refine ⟨F, hF, hF0, fun z => ?_⟩
  have h := hFz z
  rw [PeriodPair.toPointHom_apply, PeriodPair.toPointHom_apply] at h
  exact h

end PeriodPair

end
