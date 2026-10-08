/-
  Cross-module wire test for **S-2**, the lattice/index arithmetic
  (`FLTForHuman/Elliptic/PeriodPair/LatticeIndex.lean`): the two headlines
  `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_{natCard_ker,and_isAddCyclic_sublatticeQuotient}`,
  the three `ModularCurve` classes, the shared `hID_*` block and the `kqe_*` engine.

  A `spec/` probe, not a library module: it is outside every lake target and is run with
  `lake env lean`, so a green library build stays meaningful. Deleting `LatticeIndex.lean`
  makes every zone fail: no other module declares any of the names used below (the imports
  supply the `PeriodPair` promotion set and S-1's `kw_surgehgf4_hH2f_betweenCurvesHoloLift`,
  which the zones only *consume*).

  Executed zones (each a real composition, no `#check`, no `sorry`):

  * zone 1 — the 2,021 headline (index pinned to `N`, quotient cyclic) at a **concrete**
    `PeriodPair.ofTau` lattice; the ellipticity/gate/`AbelTheorem` instances are
    hypotheses (the port has no `IsElliptic` instance for a concrete `ofTau`, and the gate
    producers are not co-importable with `Engine.lean`);
  * zone 2 — the 978 headline at `ofTau`, composed with the ported
    `PeriodPair.toPointHom_apply` / `ker_toPointHom` API and the `PeriodPair.sublatticeIndex`
    conclusion;
  * zone 3 — the S-1 → S-2 hand-off: S-1's `kw_surgehgf4_hH2f_betweenCurvesHoloLift` and
    this module's `hID`/`kqe` feed `kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three`, both
    abstractly and applied at a concrete `ofTau` pair;
  * zone 4 — the `zlattice` torsion count and the index/scale API at arbitrary pairs.
-/
import FLTForHuman.Elliptic.PeriodPair.LatticeIndex

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open scoped UpperHalfPlane PeriodPair

namespace PeriodPairLatticeIndexConsumer

/-! ### Zone 1 — the 2,021 headline at the concrete `ofTau` lattice -/

/-- The 2,021 headline at `L = PeriodPair.ofTau τ`, `L' = PeriodPair.ofTau τ'`, with the
gate/`AbelTheorem` instances as hypotheses. -/
example (τ τ' : ℍ)
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
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    ∃ β : ℂˣ, (((PeriodPair.ofTau τ').scale β).lattice : Set ℂ) ⊆ (PeriodPair.ofTau τ).lattice ∧
      PeriodPair.sublatticeIndex (PeriodPair.ofTau τ) ((PeriodPair.ofTau τ').scale β) = N ∧
      IsAddCyclic (PeriodPair.sublatticeQuotient (PeriodPair.ofTau τ) ((PeriodPair.ofTau τ').scale β)) :=
  PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
    (PeriodPair.ofTau τ) (PeriodPair.ofTau τ') ι hι hfin hN N hcyc hcard

/-! ### Zone 2 — the 978 headline composed with the `toPointHom` promotion set -/

/-- The 978 headline at `ofTau`, and its inclusion re-expressed through
`PeriodPair.toPointHom_apply`/`ker_toPointHom`: `β` makes `L.toPoint` vanish on
`(L'.scale β).lattice`. -/
example (τ τ' : ℍ)
    [((PeriodPair.ofTau τ).weierstrassCurve).IsElliptic]
    [((PeriodPair.ofTau τ').weierstrassCurve).IsElliptic]
    (α : ℂˣ)
    (ψ : (PeriodPair.ofTau τ).weierstrassCurve.toAffine.Point →+
      (PeriodPair.ofTau τ').weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, (PeriodPair.ofTau τ').toPoint (PeriodPair.ofTau τ').discriminantNeZero
        ((α : ℂ) * z)
      = ψ ((PeriodPair.ofTau τ).toPoint (PeriodPair.ofTau τ).discriminantNeZero z)) :
    ∃ β : ℂˣ, (((PeriodPair.ofTau τ').scale β).lattice : Set ℂ) ⊆ (PeriodPair.ofTau τ).lattice ∧
      PeriodPair.sublatticeIndex (PeriodPair.ofTau τ) ((PeriodPair.ofTau τ').scale β)
        = Nat.card ψ.ker ∧
      ∀ z ∈ ((PeriodPair.ofTau τ').scale β).lattice,
        (PeriodPair.ofTau τ).toPoint (PeriodPair.ofTau τ).discriminantNeZero z = 0 := by
  obtain ⟨β, hsub, hidx⟩ :=
    PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
      (PeriodPair.ofTau τ) (PeriodPair.ofTau τ')
      (PeriodPair.ofTau τ).discriminantNeZero (PeriodPair.ofTau τ').discriminantNeZero
      α ψ hψ
  refine ⟨β, hsub, hidx, ?_⟩
  intro z hz
  have h0 : (PeriodPair.ofTau τ).toPointHom z = 0 := by
    rw [← AddMonoidHom.mem_ker, PeriodPair.ker_toPointHom]
    exact hsub hz
  rwa [PeriodPair.toPointHom_apply] at h0

/-! ### Zone 3 — the S-1 → S-2 hand-off feeding the 2,021 route -/

/-- The three-way assembly: S-1's `hH2`, this module's `hID` and `hKQE`. -/
example : ModularCurve.KwD5BetweenCurvesPointHomSublatticeCyclic :=
  ModularCurve.kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three
    ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift
    ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved
    ModularCurve.kw_surgehgf4_kqe_proved

/-- The hand-off applied at a concrete `ofTau` pair: the assembled class produces the
existential whose `ψ` is `pointMapOfPushforward ι hι hfin (normFormulaAlong_of_elliptic …)`. -/
example (τ τ' : ℍ)
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
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin
      (normFormulaAlong_of_elliptic ι hfin)).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin
      (normFormulaAlong_of_elliptic ι hfin)).ker = N) :
    ∃ β : ℂˣ, (((PeriodPair.ofTau τ').scale β).lattice : Set ℂ) ⊆ (PeriodPair.ofTau τ).lattice ∧
      PeriodPair.sublatticeIndex (PeriodPair.ofTau τ) ((PeriodPair.ofTau τ').scale β) = N ∧
      IsAddCyclic (PeriodPair.sublatticeQuotient (PeriodPair.ofTau τ) ((PeriodPair.ofTau τ').scale β)) :=
  (ModularCurve.kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three
    ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift
    ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved
    ModularCurve.kw_surgehgf4_kqe_proved)
    (PeriodPair.ofTau τ) (PeriodPair.ofTau τ') ι hι hfin N hcyc hcard

/-! ### Zone 4 — the torsion count and the index/scale API -/

/-- `#(ℂ/Λ)[n] = n ^ finrank ℝ ℂ`: the ported `zlattice` count at an arbitrary
`PeriodPair` lattice (`IsZLattice ℝ`/`DiscreteTopology` are mathlib instances). -/
example (M : PeriodPair) {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (ℂ ⧸ M.lattice.toAddSubgroup) (n : ℤ)) = n ^ 2 := by
  rw [ModularCurve.kw_card_torsionBy_zlatticeQuotient_finrank_real M.lattice hn,
    Complex.finrank_real_complex]

/-- The sublattice index is invariant under rescaling both pairs. -/
example (L L' : PeriodPair) (α : ℂˣ) :
    PeriodPair.sublatticeIndex (L.scale α) (L'.scale α) = PeriodPair.sublatticeIndex L L' :=
  ModularCurve.kwSublatticeIndex_scale L L' α

/-- Two rescalings compose. -/
example (L : PeriodPair) (α β : ℂˣ) :
    ((L.scale α).scale β).lattice = (L.scale (β * α)).lattice :=
  PeriodPair.gate_scale_mul L α β

/-- The 978 class at its pin name. -/
example : ModularCurve.KwD5BetweenCurvesIndexDual :=
  ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved

/-- The kernel-quotient engine at its pin name. -/
example : ModularCurve.KwD5BetweenCurvesKerQuotEquivBC :=
  ModularCurve.kw_surgehgf4_kqe_proved

end PeriodPairLatticeIndexConsumer

end
