/-
  Cross-module wire test for **S-1**, the ℂ-analytic seam
  (`FLTForHuman/Elliptic/PeriodPair/HoloLift.lean`): the four
  `ModularCurve.KwD5BetweenCurves*HoloLift` chain `Prop`s and the
  `kw_surgehgf4_hH2*` reduction that proves
  `ModularCurve.KwD5BetweenCurvesHoloLift`, and the headline
  `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`.

  A `spec/` probe, not a library module: it is outside every lake target and is run with
  `lake env lean`, so a green library build stays meanwhat it says. Deleting
  `HoloLift.lean` makes every zone fail (no other module declares any of the names used
  here except the imported `ModularCurve.KwD5BetweenCurvesHoloLift` seam and the
  `PeriodPair` promotion set, which the zones only *consume*).

  Executed zones (each a real composition, no `#check`, no `sorry`):

  * zone 1 — the headline at a **concrete** `PeriodPair`, the `ofTau`-style lattice
    `PeriodPair.ofTau τ`; the ellipticity/gate/`AbelTheorem` instances are hypotheses
    (the port has no `IsElliptic` instance for a concrete `ofTau` — that is the
    `DiscriminantNeZero` arithmetic of set S-2 — and the gate producers are not
    co-importable with `Engine.lean`);
  * zone 2 — the same F composed with the ported `PeriodPair.toPointHom_apply` /
    `toPointAddEquiv_mk` API, recovering the `toPointHom` form the chain is stated in;
  * zone 3 — the chain itself: the top seam `kw_surgehgf4_hH2f_betweenCurvesHoloLift` and
    each of the reduction steps, from a proof of the upstream class;
  * zone 4 — the module's other pin-public atoms: the finite-kernel bridge
    `kw_fdn2_qephod_hend10_kerPMOP_finite`, the `geomMorphBC` fibre finiteness
    `kw_surgehgf4_hH2f_finite_geomMorphBC_preimage`, and the place/evaluation bridge
    `WeierstrassCurve.Affine.kw_evalAt_placeOfEquation_mk`.
-/
import FLTForHuman.Elliptic.PeriodPair.HoloLift

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open AlgebraicCurve
open WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open scoped UpperHalfPlane PeriodPair

universe u

namespace PeriodPairHoloLiftConsumer

/-! ### Zone 1 — the headline at the concrete `ofTau` lattice -/

/-- The headline at `L = L' = PeriodPair.ofTau τ`, with a general isogeny-direction
algebra homomorphism. The named instances are hypotheses, as the work order §8 provides. -/
example (τ τ' : ℍ)
    (hL : (PeriodPair.ofTau τ).DiscriminantNeZero)
    (hL' : (PeriodPair.ofTau τ').DiscriminantNeZero)
    [((PeriodPair.ofTau τ).weierstrassCurve).IsElliptic]
    [((PeriodPair.ofTau τ').weierstrassCurve).IsElliptic]
    [GenusOnePlaceGate (PeriodPair.ofTau τ).weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred (PeriodPair.ofTau τ).weierstrassCurve.toAffine]
    [AbelTheorem (PeriodPair.ofTau τ).weierstrassCurve.toAffine]
    [GenusOnePlaceGate (PeriodPair.ofTau τ').weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred (PeriodPair.ofTau τ').weierstrassCurve.toAffine]
    [AbelTheorem (PeriodPair.ofTau τ').weierstrassCurve.toAffine]
    (ι : (PeriodPair.ofTau τ').weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      (PeriodPair.ofTau τ).weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ (PeriodPair.ofTau τ').lattice ∧
      ∀ z : ℂ, (PeriodPair.ofTau τ').toPoint hL' (F z)
        = pointMapOfPushforward ι hι hfin hN ((PeriodPair.ofTau τ).toPoint hL z) :=
  PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    (PeriodPair.ofTau τ) (PeriodPair.ofTau τ') hL hL' ι hι hfin hN

/-- The same headline at an arbitrary pair of `PeriodPair`s, hypothesis form: the
`L'.lattice` member and the `∀ z` identity both come out of the theorem. -/
example (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z : ℂ, L'.toPoint hL' (F z)
        = pointMapOfPushforward ι hι hfin hN (L.toPoint hL z) :=
  PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
    L L' hL hL' ι hι hfin hN

/-! ### Zone 2 — the headline composed with the `PeriodPair` promotion set -/

/-- The headline's `F` re-expressed through the additive packaging the chain is stated
in: `toPointHom_apply` turns `L'.toPoint hL'` into `L'.toPointHom`, and `toPointAddEquiv_mk`
identifies the quotient class. -/
example (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine]
    [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin) :
    ∃ (F : ℂ → ℂ), Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      (∀ z : ℂ, L'.toPointHom (F z)
        = (pointMapOfPushforward ι hι hfin hN) (L.toPointHom z)) ∧
      (∀ z : ℂ, L'.toPointAddEquiv (QuotientAddGroup.mk (F z))
        = (pointMapOfPushforward ι hι hfin hN)
            (L.toPointAddEquiv (QuotientAddGroup.mk z))) := by
  obtain ⟨F, hF, hF0, hFz⟩ :=
    PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
      L L' hL hL' ι hι hfin hN
  refine ⟨F, hF, hF0, fun z => ?_, fun z => ?_⟩
  · rw [L'.toPointHom_apply, L.toPointHom_apply]; exact hFz z
  · rw [L'.toPointAddEquiv_mk, L.toPointAddEquiv_mk]; exact hFz z

/-! ### Zone 3 — the chain: each reduction at its pin name -/

/-- The proved seam class, from the constructive base. -/
example : ModularCurve.KwD5BetweenCurvesHoloLift :=
  ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift

/-- `Weak → HoloLift` (the full chain in one step). -/
example (h : ModularCurve.KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    ModularCurve.KwD5BetweenCurvesHoloLift :=
  ModularCurve.kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoordsWeak h

/-- `Locally → HoloLift`. -/
example (h : ModularCurve.KwD5BetweenCurvesLocallyHoloLift) :
    ModularCurve.KwD5BetweenCurvesHoloLift :=
  ModularCurve.kw_surgehgf4_hH2_betweenCurvesHoloLift_of_locallyHolo h

/-- `Cocountable → Locally`. -/
example (h : ModularCurve.KwD5BetweenCurvesCocountableHoloLift) :
    ModularCurve.KwD5BetweenCurvesLocallyHoloLift :=
  ModularCurve.kw_surgehgf4_hH2c_betweenCurvesLocallyHoloLift_of_cocountable h

/-- `Coords → Cocountable → HoloLift`. -/
example (h : ModularCurve.KwD5BetweenCurvesCocountableAffineHoloCoords) :
    ModularCurve.KwD5BetweenCurvesHoloLift :=
  ModularCurve.kw_surgehgf4_hH2_betweenCurvesHoloLift_of_affineHoloCoords h

/-- `Weak → Coords` (the step that removes the `Y z ≠ 0` defect). -/
example (h : ModularCurve.KwD5BetweenCurvesCocountableAffineHoloCoordsWeak) :
    ModularCurve.KwD5BetweenCurvesCocountableAffineHoloCoords :=
  ModularCurve.kw_surgehgf4_hH2e_betweenCurvesCocountableAffineHoloCoords_of_weak h

/-! ### Zone 4 — the module's other pin-public atoms -/

/-- The finite-kernel bridge: `finrankAlong` is positive, so `ker (pointMapOfPushforward …)`
is finite. -/
example {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {E E' : Affine K} [E.IsElliptic] [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E]
    [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E']
    [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    Finite ↥(AddMonoidHom.ker
      (pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic ι hfin))) :=
  ModularCurve.kw_fdn2_qephod_hend10_kerPMOP_finite ι hι hfin

/-- The `geomMorphBC` fibre over a point is finite. -/
example {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {E E' : Affine K} [E.IsElliptic] [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E]
    [AbelTheorem E] [E'.IsElliptic] [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E']
    [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (t : E'.Point) :
    {P : E.Point | ModularCurve.kw_fdn2_qephod_hend7_geomMorphBC ι hι P = t}.Finite :=
  ModularCurve.kw_surgehgf4_hH2f_finite_geomMorphBC_preimage ι hι t

/-- The place/evaluation bridge `kw_evalAt_placeOfEquation_mk`. -/
example {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]
    {r s : F} (hrs : W.Equation r s) (p : Polynomial F[X]) :
    (placeOfEquation hrs).evalAt
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p))
      = p.evalEval r s :=
  kw_evalAt_placeOfEquation_mk hrs p

end PeriodPairHoloLiftConsumer
