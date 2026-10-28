/-
  Consumer specification for SET 5 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed with the place/differential API across
  modules, expressed in Lean so that each is either bound or not. It is a deliverable measure,
  not a proof obligation. It is **not part of any library** (`lake build` does not see `spec/`);
  run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet5Consumer.lean 2>&1 | grep -c error

  The error count is the metric; deleting any one module must make it fail.

  ZONES
  -----
    [chart]    ZONE A — `Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex`
               (PC1) produces a charted-space structure whose order clause is exactly
               `Place.ConnectedOfCharted.OrderHypothesis` (`Place/ComplexDictionary.lean`,
               SET 4), and `reading_center` evaluates `reading` at the chart's centre. The bridge
               is `rfl`-level (`reading v f = v.chartRead f`), so the capstone's clause *is* the
               dictionary's hypothesis — the two modules were written a wave apart.
    [orderMap] ZONE C — `Place.exists_of_orderMap_rat` (RB1's new engine) realises a rational
               order map as a place and its order; a positive value of the map is then membership
               in that place's valuation ring. Engine and conclusion are in different modules
               (`Place/ValueDictionary.lean` and `Defs/PushPull.lean`).
    [residue]  ZONE B — `RegularProlongation.eq_integers_of_forall_mem_adjoin_iff` (RP2) turns an
               agreement-on-the-adjoin hypothesis into an equality of valuation subrings, and the
               equality then carries the membership of the prolongation's integers.
-/

import FLTForHuman.AlgebraicCurve.Place.ChartedSpace
import FLTForHuman.AlgebraicCurve.Place.ComplexDictionary
import FLTForHuman.AlgebraicCurve.RegularProlongationFinrank
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.AlgebraicCurve.Defs.HahnSeriesRamificationBound
import FLTForHuman.AlgebraicCurve.Defs.PushPull

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open scoped Manifold ContDiff

universe u v w

/-! ## Zone A — `[chart]` the capstone's order clause is the dictionary's hypothesis -/

theorem set5_chart_dictionary {F : Type*} [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] :
    ∃ (t : TopologicalSpace (Place ℂ F)) (c : ChartedSpace ℂ (Place ℂ F)),
      (letI := t; letI := c; Place.ConnectedOfCharted.OrderHypothesis F) ∧
      (letI := t; letI := c; ∀ (v : Place ℂ F) (f : F),
        Place.ConnectedOfCharted.reading v f (extChartAt 𝓘(ℂ, ℂ) v v) = v.evalAt f) := by
  obtain ⟨t, c, _hm, _hc, _h2, _hconn, hord⟩ :=
    Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F hfg
  refine ⟨t, c, hord, ?_⟩
  intro v f
  exact Place.ConnectedOfCharted.reading_center v f

/-! ## Zone C — `[orderMap]` a positive value of a rational order map is integral at its place -/

theorem set5_orderMap_membership {K F : Type*} [Field K] [Field F] [Algebra K F]
    (μ : F → WithTop ℚ) (h_top : ∀ x, μ x = ⊤ ↔ x = 0)
    (h_mul : ∀ x y, μ (x * y) = μ x + μ y) (h_add : ∀ x y, min (μ x) (μ y) ≤ μ (x + y))
    (h_const : ∀ c : K, c ≠ 0 → μ (algebraMap K F c) = 0)
    (h_nontriv : ∃ x, 0 < μ x ∧ μ x ≠ ⊤)
    (d : ℕ) (hd : 0 < d)
    (h_den : ∀ x, μ x ≠ ⊤ → ∃ k : ℤ, μ x = ((k : ℚ) / (d : ℚ) : ℚ))
    {x : F} (hx : 0 < μ x) :
    ∃ P : Place K F, x ∈ P.toValuationSubring := by
  obtain ⟨P, _g, _hg, hiff, _hval⟩ :=
    Place.exists_of_orderMap_rat μ h_top h_mul h_add h_const h_nontriv d hd h_den
  exact ⟨P, (hiff x).mpr hx.le⟩

/-! ## Zone B — `[residue]` the integers of a prolongation, and the membership they carry -/

theorem set5_residue_eq_integers_and_membership {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers ∧ (x : F) ∈ V := by
  have hEq : V = R.integers :=
    RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R x hx hfin hdeg V hV
  exact ⟨hEq, hEq ▸ x.2⟩
