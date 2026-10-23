/-
  A degree-`N` endomorphism of an elliptic curve over an algebraically closed field of
  characteristic 0 forces `Φ_N(j(E), j(E)) = 0`.

  The mathematics: `D : IsogenyEndDatum W.toAffine` with `finrankAlong K D.ι = N` is a finite
  self-embedding of the function field of index `N`.  Descend it to a countable subfield `K₀`
  (`exists_intermediateField_countable_map_eq_and_finrankAlong_eq`), embed `AlgebraicClosure K₀`
  into `ℂ` (`nonemptyRingHom_algebraicClosure` below), base-change the datum to `ℂ`
  (`exists_algHom_functionField_baseChange_finrankAlong_eq`), uniformise the resulting complex curve
  as `ℂ / Λ` for a period pair `L` (`exists_variableChange_smul_weierstrassCurve_eq`), and conj the
  self-isogeny through the function-field isomorphism
  (`functionField_algEquiv_of_variableChange`) so that it becomes a lattice endomorphism.  Its
  kernel is cyclic of order `N` (`IsAddCyclic.of_squarefree_natCard` on the kernel's cardinality),
  so `L` has a cyclic index-`N` sublattice — a rescale `L.scale β` — and
  `ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic` gives `Φ_N(j(Λ), j(Λ)) = 0`, which
  `jLattice_scale` and `s13_j_weierstrassCurve_eq_jLattice` transport back to `W.j`.

  **This module is an assembly, not a transcription.** 37 of the pin's 55 declarations already have
  their statement in the port and are *imported* here (`port_advise`'s substitution table); 21 more
  were `private` elsewhere and were promoted to their subject homes on 2026-10-23
  (`Elliptic/PeriodPair/{Lattice,Uniformization,Discriminant}.lean`, which were wired to the
  `spec-pin:` protocol in the same pass). What is written here is the part the port did not have:
  the algebraic-closure embedding, the three `PeriodPair` instances the pin's file carries, the two
  `s13_*` lemmas, a public `jLattice_scale` (its only other home is a `private` copy in the still
  frozen `ModularCurve/ModularPolynomialEvalJ.lean`), and the headline.

  Transcribed from the two pin copies (pinned `aa2d8b3`):

  * `Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean`
    (21 lines) — the statement, verbatim (the `universe u` belongs to it);
  * `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean`
    (647 lines, 55 declarations) — the proof; its `solution` (570–647) is inlined into the headline.

  The pin's `kw_` names are rectified (`nonemptyRingHom_algebraicClosure`, `aleph0_lt_mk_transcendenceBasis`,
  `countable_algebraicClosure`, `instIsElliptic_of_discriminantNeZero`, `instInfinite_quotientLattice`,
  `instInfinite_point`); `jLattice_scale`, `conjSeam*` and `normFormulaAlong_of_elliptic` are
  imported from their public homes (`Lattice`, `Isogeny/KernelCyclicTransfer`,
  `IsogenyEndDatum/Engine`).  The pin's `P2MW.S_<stem>` wrapper namespace, its `p2m_*` staging and its
  two `[-ext]`/`[-instance]` attribute blocks are dropped, as are its heartbeat bumps
  (`maxHeartbeats 6400000`, `synthInstance.maxHeartbeats 1600000` and the per-declaration
  `synthInstance.maxHeartbeats 6400000 in` on `nonemptyRingHom_algebraicClosure`: the file closes at
  200,000). Its two `linter.*` suppressions are kept, being pin facts.

  **Wiring.** This module carries its own wire, so `spec/check_port.py` diffs every public
  declaration it makes (11: the six rectified names match the pin's `kw_` names by statement):

  spec-pin: Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean
-/
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.Elliptic.PeriodPair.HoloLift
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.Elliptic.PeriodPair.LatticeIndex
import FLTForHuman.Elliptic.PeriodPair.PrimCosetReps
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.GroupTheory.SpecificGroups.CyclicSquarefree
import FLTForHuman.ModularCurve.ModularPolynomialEvalJ
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChangeAlgHom
import FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField
import FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer
import FLTForHuman.WeierstrassCurve.Isogeny.VariableChangeAlgEquiv
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Vocabulary
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.Continuum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace ModularCurve

open Cardinal IntermediateField

/-- The `ℚ`-algebra equivalence between two fields, stripped to a ring equivalence (the pin's
`kw_d5eu_ratEquivStrip`). -/
private def ratEquivStrip {A B : Type*} [Semiring A] [Semiring B]
    {iA : Algebra ℚ A} {iB : Algebra ℚ B} (e : @AlgEquiv ℚ A B _ _ _ iA iB) :
    A ≃+* B :=
  @AlgEquiv.toRingEquiv ℚ A B _ _ _ iA iB e

/-- The algebraic closure of a countable field is countable. -/
theorem countable_algebraicClosure (K₀ : Type u) [Field K₀] [Countable K₀] :
    Countable (AlgebraicClosure K₀) :=
  Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max K₀ (AlgebraicClosure K₀)).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))

/-
-/
set_option linter.style.haveILetI false in
/-- A transcendence basis of `ℂ` over `ℚ` is uncountable. -/
theorem aleph0_lt_mk_transcendenceBasis
    {t : Set ℂ} (ht : IsTranscendenceBasis ℚ ((↑) : t → ℂ)) : ℵ₀ < #t := by
  rw [← not_le]
  intro h
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ℂ := ht.isAlgebraic_field
  have hadj : #(IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ≤ ℵ₀ :=
    (IntermediateField.cardinalMk_adjoin_le ℚ _).trans
      (max_le (max_le Cardinal.mk_le_aleph0 (Cardinal.mk_range_le.trans h)) le_rfl)
  have hℂ : #ℂ ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max _ ℂ).trans (max_le hadj le_rfl)
  exact absurd hℂ <| not_le.mpr <| Cardinal.aleph0_lt_continuum.trans_le
    (Cardinal.mk_real ▸ Cardinal.mk_le_of_injective Complex.ofReal_injective)

set_option linter.style.haveILetI false in
/-- A countable field's algebraic closure embeds into `ℂ`: the embedding is forced by comparing
transcendence degrees. -/
theorem nonemptyRingHom_algebraicClosure (K₀ : Type u) [Field K₀] [Algebra ℚ K₀]
    [Countable K₀] : Nonempty (AlgebraicClosure K₀ →+* ℂ) := by
  let ACK := AlgebraicClosure K₀
  haveI : Countable ACK := countable_algebraicClosure K₀
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (A := ACK)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ (A := ℂ)

  have hcard : Cardinal.lift.{0, u} #s ≤ Cardinal.lift.{u, 0} #t := by
    have h1 : Cardinal.lift.{0, u} #s ≤ ℵ₀ := Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
    have h2 : ℵ₀ ≤ Cardinal.lift.{u, 0} #t :=
      Cardinal.aleph0_le_lift.mpr (le_of_lt (aleph0_lt_mk_transcendenceBasis ht))
    exact h1.trans h2
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hcard
  have hf_indep : AlgebraicIndependent ℚ (fun i : s => ((f i : t) : ℂ)) :=
    ht.1.comp f f.injective
  let Qs : IntermediateField ℚ ACK := adjoin ℚ (Set.range ((↑) : s → ACK))
  let φQs : Qs →+* ℂ :=
    ((adjoin ℚ (Set.range (fun i : s => ((f i : t) : ℂ)))).val.toRingHom.comp
      (ratEquivStrip hf_indep.aevalEquivField).toRingHom).comp
        (ratEquivStrip hs.1.aevalEquivField).symm.toRingHom
  have hφinj : Function.Injective φQs := by
    rw [RingHom.injective_iff_ker_eq_bot]
    rcases Ideal.eq_bot_or_top (RingHom.ker φQs) with h | h
    · exact h
    · exfalso
      have hone : (1 : Qs) ∈ RingHom.ker φQs := h ▸ Submodule.mem_top
      simp at hone
  letI : Algebra Qs ℂ := φQs.toAlgebra
  haveI : Module.IsTorsionFree ↥Qs ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr hφinj
  haveI : Algebra.IsAlgebraic Qs ACK := hs.isAlgebraic_field
  exact ⟨(IsAlgClosed.lift (R := Qs) (M := ℂ) (S := ACK)).toRingHom⟩

end ModularCurve

namespace PeriodPair

open Complex Filter Set

variable (L : PeriodPair)
/-- A period pair with nonzero discriminant has an elliptic Weierstrass curve (the pin's
`kw_instIsElliptic`, scoped). -/
scoped instance instIsElliptic_of_discriminantNeZero : L.weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (discriminantNeZero L).weierstrassCurve_Δ_ne_zero⟩

set_option linter.style.haveILetI false in
/-- `ℂ / Λ` is infinite. -/
scoped instance instInfinite_quotientLattice : Infinite (ℂ ⧸ L.lattice.toAddSubgroup) := by
  rw [← not_finite_iff_infinite]; intro hfin
  haveI : Countable L.lattice.toAddSubgroup :=
    Set.countable_coe_iff.mpr L.countable_lattice
  haveI : Countable ((ℂ ⧸ L.lattice.toAddSubgroup) × L.lattice.toAddSubgroup) := inferInstance
  have hCc : Countable ℂ :=
    Countable.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup
      (s := L.lattice.toAddSubgroup)).symm
  haveI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact absurd hCc not_countable

/-- The point group of the uniformised curve is infinite. -/
scoped instance instInfinite_point : Infinite L.weierstrassCurve.toAffine.Point :=
  L.toPointAddEquiv.toEquiv.infinite_iff.mp inferInstance

end PeriodPair

namespace WeierstrassCurve.Affine.IsogenyEndDatum

/-- Evaluating the diagonal `Φ(X, X)` at `a` is evaluating the coefficient-mapped `Φ` at `a`:
the ring-homomorphism identity behind the capstone's last rewrite. -/
theorem s13_aeval_diag_eq_eval_map {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    Polynomial.aeval a (Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X)
      = (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).eval a := by
  let lhs : Polynomial (Polynomial ℤ) →+* R :=
    (Polynomial.aeval (R := ℤ) a).toRingHom.comp (Polynomial.eval₂RingHom (RingHom.id (Polynomial ℤ)) Polynomial.X)
  let rhs : Polynomial (Polynomial ℤ) →+* R :=
    (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom R) a))
  have h : lhs = rhs := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [lhs, rhs, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        RingHom.id_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_def]
      simp
    · simp [lhs, rhs]
  exact RingHom.congr_fun h Φ

/-- The `j`-invariant of a period pair's curve is its lattice `j`. -/
theorem s13_j_weierstrassCurve_eq_jLattice (L : PeriodPair) [L.weierstrassCurve.IsElliptic] :
    L.weierstrassCurve.j = L.jLattice := by
  rw [PeriodPair.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ',
    div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val]

set_option linter.style.haveILetI false in
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve PeriodPair ModularCurve in
/-- A degree-`N` self-isogeny forces `Φ_N(j(E), j(E)) = 0`: the pin's capstone
`IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`, stated verbatim from the wrapper. -/
theorem aeval_j_diag_eq_zero_of_finrankAlong_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : Squarefree N) (data : ModularCurve.ModularPolynomialData N)
    (D : IsogenyEndDatum W.toAffine) (hdeg : finrankAlong K D.ι = N) :
    Polynomial.aeval W.j (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0 := by
  classical

  obtain ⟨K₀, hK₀c, E₀, hE₀e, hE₀map, ι₀, hι₀, hfin₀, hrk₀⟩ :=
    WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq W D.ι D.hι D.hfin
  haveI := hE₀e
  haveI : Countable K₀ := hK₀c
  haveI : CharZero (AlgebraicClosure K₀) :=
    charZero_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective

  obtain ⟨σ⟩ := nonemptyRingHom_algebraicClosure (↥K₀)
  letI : Algebra (AlgebraicClosure K₀) ℂ := σ.toAlgebra
  letI : Algebra (↥K₀) ℂ := (σ.comp (algebraMap (↥K₀) (AlgebraicClosure K₀))).toAlgebra
  haveI : IsScalarTower (↥K₀) (AlgebraicClosure K₀) ℂ := IsScalarTower.of_algebraMap_eq' rfl

  obtain ⟨ι₁, hι₁, hfin₁, hrk₁⟩ :=
    WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq E₀
      (AlgebraicClosure K₀) ℂ ι₀ hι₀ hfin₀
  have hN₁ : finrankAlong ℂ ι₁ = N := hrk₁.trans (hrk₀.trans hdeg)

  have hjK : W.j = algebraMap (↥K₀) K E₀.j := by
    subst hE₀map
    exact E₀.map_j (algebraMap (↥K₀) K)
  haveI hE1inst : (E₀.baseChange ℂ).IsElliptic :=
    inferInstanceAs (E₀.map (algebraMap (↥K₀) ℂ)).IsElliptic
  have hjC : (E₀.baseChange ℂ).j = algebraMap (↥K₀) ℂ E₀.j := E₀.map_j (algebraMap (↥K₀) ℂ)

  set d := data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X with hd
  suffices hℂ : Polynomial.aeval (E₀.baseChange ℂ).j d = 0 by

    have h0 : Polynomial.aeval E₀.j d = 0 := by
      apply (algebraMap (↥K₀) ℂ).injective
      rw [map_zero, ← Polynomial.aeval_algebraMap_apply, ← hjC]
      exact hℂ
    rw [hjK, Polynomial.aeval_algebraMap_apply, h0, map_zero]
  generalize hE1 : E₀.baseChange ℂ = E₁ at ι₁ hι₁ hfin₁ hN₁ hE1inst
  obtain ⟨L, C, hC⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq E₁
  subst hC

  have hL : L.DiscriminantNeZero := PeriodPair.discriminant_ne_zero L
  haveI hLe : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hL.weierstrassCurve_Δ_ne_zero⟩
  haveI : IsDedekindDomain L.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L.weierstrassCurve
  haveI : HasPrincipalDivisors ℂ L.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g, hgc, hga⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := L.weierstrassCurve.toAffine)
  letI := g
  haveI := hgc
  haveI := hga

  obtain ⟨eE⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L.weierstrassCurve C
  let ι₂ := ModularCurve.conjSeam eE eE ι₁
  have hι₂ : ι₂.toRingHom.IsIntegral := ModularCurve.conjSeam_isIntegral eE eE ι₁ hι₁
  have hfin₂ : FiniteAlong ℂ ι₂ := ModularCurve.conjSeam_finiteAlong eE eE ι₁ hfin₁
  have hrk₂ : finrankAlong ℂ ι₂ = N := (ModularCurve.finrankAlong_conj eE eE ι₁).trans hN₁

  have hN₂ : NormFormulaAlong ℂ ι₂ hfin₂ := WeierstrassCurve.Affine.normFormulaAlong_of_elliptic ι₂ hfin₂
  have hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N :=
    (WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong _ _ ι₂ hι₂ hfin₂ hN₂).trans hrk₂
  have hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker :=
    IsAddCyclic.of_squarefree_natCard (hcard.symm ▸ hN)

  obtain ⟨β, hsub, hidx, hcq⟩ :=
    PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
      L L ι₂ hι₂ hfin₂ hN₂ N hcyc hcard
  have hroot := ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic N data L (L.scale β)
    hsub hidx hcq
  rw [PeriodPair.jLattice_scale] at hroot

  rw [WeierstrassCurve.variableChange_j, s13_j_weierstrassCurve_eq_jLattice, s13_aeval_diag_eq_eval_map]
  exact hroot

end WeierstrassCurve.Affine.IsogenyEndDatum
