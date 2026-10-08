/-
  Cross-module wire test for **SC**, row S's terminal set: the two landed leaves

    `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq`
      (`FLTForHuman/Elliptic/PeriodPair/VariableChange.lean`),
    `Field.nonempty_ringHom_complex_of_countable`
      (`FLTForHuman/FieldTheory/NonemptyRingHomComplex.lean`),

  and the capstone `FLTForHuman/ModularCurve/ModularPolynomialEvalJ.lean` holding
  `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`
  together with the pin's `conjSeam` / char-`0` bridge / `solution0` surface.

  A `spec/` probe, not a library module: it is outside every lake target and is run with
  `lake env lean`, so a green library build stays meaningful.  Deleting any of the three
  modules makes it fail: every zone's imports and names vanish.

  Executed zones (each a real composition, no `#check`, no unfinished proof):

  * zone 1 — the **two leaves**: the variable-change leaf at the concrete `ofTau` curve of
    a point `τ : ℍ`, and the field-embedding leaf at `ℚ`, extracted and evaluated;
  * zone 2 — **the capstone at `K = ℂ`** with the gate package as hypotheses (the shape
    `complexCase` itself consumes), applied through the wrapper headline;
  * zone 3 — **D-6's headline into the capstone's hypotheses**: run the countable descent
    (`exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`)
    at the capstone's own hypotheses, build the descended `NormFormulaAlong` by the capstone's
    `normFormulaAlong_of_charZero`, read off the descended `hcyc`/`hcard`, and consume them
    with the capstone's `solution0` at the descended `AlgebraicClosure K₀`.

  **Bound.**  The `timeout 90` the S-1/S-2/S-3 probes fit does not fit this cone.  SC's
  import graph is the gate producer + `IsogenyEndDatum/Engine` + `TwoCurveDescent` + the whole
  `ModularForm` layer (~4.4 GB RSS cold, ~80 s warm); a concrete-`ofTau`-curve application of
  the headline costs minutes more still, because elaborating `FunctionField (ofTau τ)` forces
  the `PeriodPair.weierstrassCurve`/`AdjoinRoot` defeq stack and its instance search.  The
  probe therefore uses hypothesis-form zones for the headline and is run under a widened,
  explicitly reported bound; see `topics/velu/WORKORDER-SC-capstone.md` §7.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean>
-/
import FLTForHuman.Elliptic.PeriodPair.VariableChange
import FLTForHuman.FieldTheory.NonemptyRingHomComplex
import FLTForHuman.ModularCurve.ModularPolynomialEvalJ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open scoped WeierstrassCurve.Affine UpperHalfPlane

namespace ModularPolynomialCapstoneConsumer

/-! ### Zone 1 — the two leaves -/

/-- **The variable-change leaf at a concrete `ofTau` curve**: over `ℂ`, a Weierstrass curve
is a change of variables of the one attached to a period lattice.  The `IsElliptic` instance
is the capstone's `scoped instance instIsEllipticWeierstrassCurve`, activated by
`open scoped WeierstrassCurve.Affine`. -/
example (τ : ℍ) :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
      C • L.weierstrassCurve = (PeriodPair.ofTau τ).weierstrassCurve :=
  PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (PeriodPair.ofTau τ).weierstrassCurve

/-- **The field-embedding leaf at `ℚ`**, extracted and evaluated: a countable field of
characteristic `0` has a ring homomorphism into `ℂ`. -/
example : ∃ φ : ℚ →+* ℂ, φ 1 = 1 := by
  obtain ⟨φ⟩ := Field.nonempty_ringHom_complex_of_countable ℚ
  exact ⟨φ, map_one φ⟩

/-! ### Zone 2 — the capstone at the concrete ground field `K = ℂ` -/

/-- **The wrapper headline over `ℂ`** (`K = ℂ` fixed concretely), with the gate package and
the along-map data as hypotheses — exactly the binder package `complexCase` consumes. -/
example (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin)
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) E.j)).eval E'.j = 0 :=
  WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    ℂ E E' ι hι hfin hN N hcyc hcard data

/-- The same conclusion through the capstone's `complexCase` directly (the `solution0`
route's terminal call), so both the wrapper name and the internal case are wired. -/
example (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin)
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) E.j)).eval E'.j = 0 :=
  WeierstrassCurve.Affine.complexCase E E' ι hι hfin hN N hcyc hcard data

/-! ### Zone 3 — D-6's headline into the capstone's hypotheses -/

/-- **The countable descent feeding the capstone.**  At the capstone's own abstract
hypotheses, run D-6's headline; at the descended `AlgebraicClosure K₀`, build the
`NormFormulaAlong` by the capstone's `normFormulaAlong_of_charZero`, read D-6's descended
`hcyc`/`hcard`, and close with the capstone's `solution0`.  The conclusion is the
*descended* vanishing, so this really consumes D-6's output rather than restating the
headline. -/
example {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ι) (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E'),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure K₀))
          (E₀.baseChange (AlgebraicClosure K₀)).toAffine.j)).eval
        (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.j = 0 := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  obtain ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hE, hE', hEb, hEb', ι₀, hι₀, hfin₀, H⟩ :=
    WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
      E E' ι hι hfin hN N hcyc hcard
  haveI := hE₀
  haveI := hE₀'
  haveI := hEb
  haveI := hEb'
  haveI : Countable K₀ := hK₀
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero
  haveI : CharZero (AlgebraicClosure K₀) :=
    charZero_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective
  haveI : DecidableEq (AlgebraicClosure K₀) := Classical.decEq _

  haveI : IsDedekindDomain (E₀.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : IsDedekindDomain (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀)
      (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀)
      (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g₁, c₁, a₁⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀.baseChange (AlgebraicClosure K₀)).toAffine)
  obtain ⟨g₂, c₂, a₂⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀'.baseChange (AlgebraicClosure K₀)).toAffine)
  letI := g₁
  letI := g₂
  haveI := c₁
  haveI := a₁
  haveI := c₂
  haveI := a₂

  have hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀ := normFormulaAlong_of_charZero ι₀ hfin₀
  obtain ⟨hcyc₀, hcard₀⟩ := H hN₀
  have hres := WeierstrassCurve.Affine.solution0
    (E₀.baseChange (AlgebraicClosure K₀)).toAffine (E₀'.baseChange (AlgebraicClosure K₀)).toAffine
    ι₀ hι₀ hfin₀ hN₀ N hcyc₀ hcard₀ data
  exact ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hE, hE', hres⟩

end ModularPolynomialCapstoneConsumer

end
